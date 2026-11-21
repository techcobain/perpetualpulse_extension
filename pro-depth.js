// pro-depth.js — Lighter: a "Pro" switch on the Price tab's Depth view that swaps Lighter's
// depth chart for one showing who provides the book's liquidity, as depth stacked by owner.
// Owners come from public REST GET /orderBookOrders (the best 250 orders per side, no auth).
// Depth past those orders comes from the order_book socket and stacks on top as
// "Not attributed", so the layers always add up to the whole book.
// Account labels are the user's own, imported into chrome.storage.local for this site only.

(function () {
    "use strict";

    const BACKEND = _PP_lighterBackend;
    const API = BACKEND.api;
    const ORDER_LIMIT = 250; // server max
    const POLL_MS = 5_000;
    const RATE_LIMIT_PAUSE_MS = 60_000;
    const ERROR_RETRY_MS = 15_000;
    const MARKETS_RETRY_MS = 30_000;
    const TICK_MS = 500;
    const SOCKET_RETRY_MS = 3_000;
    // Public names and owner wallets, for accounts the imported labels don't cover. Each is
    // one REST request against the limit Lighter's app shares, so they go one at a time.
    const LOOKUP_INTERVAL_MS = 6_000;
    const LOOKUP_RETRY_MS = 10 * 60_000;
    const LOOKUP_TOP_ACCOUNTS = 10;
    const MIN_SUB_ACCOUNT_INDEX = 2 ** 47;
    const SITE_SUFFIX = BACKEND.isMainnet ? "" : "_robinhood"; // account indexes differ per site
    const LABELS_KEY = "pp_account_labels" + SITE_SUFFIX;
    const PUBLIC_KEY = "pp_account_public" + SITE_SUFFIX;
    const PREFS_KEY = "pp_depth_prefs";
    const RANGES = [0.1, 0.25, 0.5, 1, 2, 5];
    const MAX_RANGE = 100; // thin books can need far more than the presets

    // "fixed": a preset or typed range, the same on both sides. The "visible" modes follow the
    // book: each side reaches its last known order ("visibleSides"), or both sides reach the
    // nearer of the two ("visibleMin"). They change with every refresh.
    const RANGE_MODES = ["fixed", "visibleSides", "visibleMin"];

    function validRange(v) {
        return typeof v === "number" && v > 0 && v <= MAX_RANGE;
    }
    const L1_RE = /^0x[0-9a-fA-F]{40}$/;
    const ZERO_L1 = /^0x0{40}$/i; // protocol accounts share it
    const OTHERS = "others";
    const UNATTRIBUTED = "unattributed";
    const TIP_MEMBERS = 3;
    // An owner needs this share of the attributed depth in range for its own line; smaller
    // ones stack as Others, so near-empty lines don't sit on top of the ones that matter.
    const MIN_LAYER_SHARE = 0.02;
    const TIP_MEMBERS_BUSY = 2; // per layer, once many layers are in view

    // Categorical slots, distinct on adjacent pairs in each theme. A group keeps its slot while
    // it stays in the top set and layers stack in slot order, so nothing repaints on rank changes.
    const PALETTE = {
        dark: ["#2a78d6", "#d85a28", "#1baf7a", "#bd8400", "#c9668a", "#6a5ade", "#e34948"],
        light: ["#2a78d6", "#eb6834", "#1baf7a", "#eda100", "#e87ba4", "#6250d6", "#e34948"],
    };
    const OTHERS_COLOR = { dark: "#8a8f98", light: "#a3a8b0" };

    const state = {
        open: false, // the panel is showing
        pro: false, // off on every page load
        market: null, // { id, symbol, priceDecimals }
        snap: null,
        error: null,
        rateLimited: false,
        fetching: false,
        nextPollAt: 0,
        prefs: { range: 0.5, rangeMode: "fixed" },
        focus: null,
        slots: new Map(), // group key -> palette slot
        labels: { accounts: {}, l1: {} },
        pub: {}, // account index -> { name, l1 } from the public account endpoint
        model: null,
        hoverX: null,
    };

    const book = { marketId: null, ready: false, bids: new Map(), asks: new Map() };
    let socket = null;
    let socketRetryAt = 0;
    let markets = null; // UPPERCASE symbol -> market
    let marketsLoading = false;
    let marketsFailedAt = 0;
    const lookupFailedAt = {};
    let lastLookupAt = 0;
    let lookupPausedUntil = 0;
    let pubSaveTimer = null;
    let ui = null;

    // ---------- Storage ----------
    function storageGet(keys) {
        return new Promise((resolve) => {
            try { chrome.storage.local.get(keys, (d) => resolve(d || {})); } catch (e) { resolve({}); } // extension was reloaded
        });
    }

    function storageSet(items) {
        try { chrome.storage.local.set(items); } catch (e) {}
    }

    storageGet([LABELS_KEY, PUBLIC_KEY, PREFS_KEY]).then((d) => {
        state.labels = normalizeLabels(d[LABELS_KEY]);
        state.pub = d[PUBLIC_KEY] || {};
        const prefs = d[PREFS_KEY] || {};
        if (validRange(prefs.range)) state.prefs.range = prefs.range;
        if (RANGE_MODES.includes(prefs.rangeMode)) state.prefs.rangeMode = prefs.rangeMode;
        refresh();
    });

    try {
        chrome.storage.onChanged.addListener((changes, area) => {
            if (area !== "local" || !changes[LABELS_KEY]) return;
            state.labels = normalizeLabels(changes[LABELS_KEY].newValue);
            refresh();
            renderLabelsPanel();
        });
    } catch (e) {}

    function savePrefs() {
        storageSet({ [PREFS_KEY]: state.prefs });
    }

    function savePublicSoon() {
        if (pubSaveTimer) return;
        pubSaveTimer = setTimeout(() => {
            pubSaveTimer = null;
            storageSet({ [PUBLIC_KEY]: state.pub });
        }, 5_000);
    }

    // ---------- Labels ----------
    // {
    //   "accounts": { "<account index>": { "l1": "0x…", "type": 0, "master": 123, "name": "…" } },
    //   "l1":       { "0x…": { "name": "…", "x": "…", "telegram": "…", "discord": "…", "description": "…", "apiTrader": true } }
    // }
    // Every field is optional; anything else in the file is ignored.
    function cleanText(v, max) {
        return typeof v === "string" && v.trim() ? v.trim().slice(0, max) : null;
    }

    function normalizeLabels(data) {
        const out = { accounts: {}, l1: {} };
        if (!data || typeof data !== "object") return out;
        for (const [key, v] of Object.entries(data.accounts || {})) {
            const idx = Number(key);
            if (!Number.isSafeInteger(idx) || idx < 0 || !v || typeof v !== "object") continue;
            const rec = {};
            if (typeof v.l1 === "string" && L1_RE.test(v.l1)) rec.l1 = v.l1.toLowerCase();
            if (Number.isInteger(v.type) && v.type >= 0) rec.type = v.type;
            if (Number.isSafeInteger(v.master) && v.master >= 0) rec.master = v.master;
            const name = cleanText(v.name, 64);
            if (name) rec.name = name;
            if (Object.keys(rec).length) out.accounts[idx] = rec;
        }
        for (const [key, v] of Object.entries(data.l1 || {})) {
            if (!L1_RE.test(key) || !v || typeof v !== "object") continue;
            const rec = {};
            for (const field of ["name", "x", "telegram", "discord"]) {
                const text = cleanText(v[field], 64);
                if (text) rec[field] = text;
            }
            const description = cleanText(v.description, 280);
            if (description) rec.description = description;
            if (v.apiTrader === true) rec.apiTrader = true;
            if (Object.keys(rec).length) out.l1[key.toLowerCase()] = rec;
        }
        return out;
    }

    function saveLabels(labels) {
        state.labels = labels;
        storageSet({ [LABELS_KEY]: labels });
        refresh();
        renderLabelsPanel();
    }

    function truncate(s, max) {
        return s.length > max ? `${s.slice(0, max - 1)}…` : s;
    }

    function shortAddress(l1) {
        return l1 ? `${l1.slice(0, 6)}…${l1.slice(-4)}` : "—";
    }

    function l1Of(acct) {
        const l1 = state.labels.accounts[acct]?.l1 || state.pub[acct]?.l1 || "";
        return l1 && !ZERO_L1.test(l1) ? l1.toLowerCase() : "";
    }

    function walletMeta(acct) {
        const l1 = l1Of(acct);
        return l1 ? state.labels.l1[l1] : undefined;
    }

    function accountKind(acct) {
        const type = state.labels.accounts[acct]?.type;
        if (type !== undefined) return type === 1 ? "sub" : type === 2 ? "pool" : type >= 3 ? "system" : null;
        return acct >= MIN_SUB_ACCOUNT_INDEX ? "sub" : null;
    }

    function accountLabel(acct) {
        const own = state.labels.accounts[acct]?.name;
        if (own) return truncate(own, 24);
        const pub = state.pub[acct]?.name;
        if (pub) {
            // "Lighter Liquidity Provider (LLP)" -> "LLP"
            return pub.match(/\(([^)]+)\)\s*$/)?.[1] ?? truncate(pub, 20);
        }
        const kind = accountKind(acct);
        const name = walletMeta(acct)?.name;
        const base = name ? truncate(name, 24) : `#${acct}`;
        return kind ? `${base} (${kind})` : base;
    }

    /** Named accounts group by name (any case), pools and system accounts stand alone, the rest by wallet. */
    function ownerKey(acct) {
        const own = state.labels.accounts[acct];
        if (own?.name) return `n:${own.name.toLowerCase()}`;
        if (state.pub[acct]?.name || own?.type >= 2) return `a:${acct}`;
        const name = walletMeta(acct)?.name;
        if (name) return `n:${name.toLowerCase()}`;
        const l1 = l1Of(acct);
        return l1 ? `l:${l1}` : `a:${acct}`;
    }

    function groupLabel(group) {
        if (group.members.length === 1) return accountLabel(group.members[0].acct);
        const count = ` (${group.members.length})`;
        if (group.key.startsWith("n:")) {
            const first = group.members[0].acct;
            const name = state.labels.accounts[first]?.name || walletMeta(first)?.name || group.key.slice(2);
            return `${truncate(name, 24)}${count}`;
        }
        if (group.key.startsWith("l:")) return `${shortAddress(group.key.slice(2))}${count}`;
        return accountLabel(group.members[0].acct);
    }

    // ---------- Public account lookups ----------
    function wantsLookup(acct) {
        const own = state.labels.accounts[acct];
        if (own?.name || own?.l1 || state.pub[acct]) return false;
        return Date.now() - (lookupFailedAt[acct] || 0) >= LOOKUP_RETRY_MS;
    }

    async function lookupNext() {
        const model = state.model;
        if (!model || Date.now() < lookupPausedUntil || Date.now() - lastLookupAt < LOOKUP_INTERVAL_MS) return;
        const acct = model.lookupCandidates.find(wantsLookup);
        if (acct === undefined) return;
        lastLookupAt = Date.now();
        try {
            const resp = await fetch(`${API}/account?by=index&value=${acct}`);
            if (resp.status === 429) {
                lookupPausedUntil = Date.now() + RATE_LIMIT_PAUSE_MS;
                return;
            }
            const body = await resp.json();
            const a = body.accounts?.[0];
            if (!a) throw new Error("no account");
            state.pub[acct] = { name: a.name || "", l1: L1_RE.test(a.l1_address || "") ? a.l1_address.toLowerCase() : "" };
            savePublicSoon();
            refresh();
        } catch (e) {
            lookupFailedAt[acct] = Date.now();
        }
    }

    // ---------- Markets ----------
    async function loadMarkets() {
        if (markets || marketsLoading || Date.now() - marketsFailedAt < MARKETS_RETRY_MS) return;
        marketsLoading = true;
        try {
            const resp = await fetch(`${API}/orderBookDetails`);
            const body = await resp.json();
            if (body.code !== 200) throw new Error(body.message || `code ${body.code}`);
            const map = {};
            for (const m of [...(body.order_book_details || []), ...(body.spot_order_book_details || [])]) {
                const market = { id: m.market_id, symbol: m.symbol, priceDecimals: m.supported_price_decimals ?? 2 };
                // The site shows rhQQQ as QQQ and 1000PEPE as kPEPE; spot pairs use "_" in the URL
                const upper = m.symbol.toUpperCase();
                for (const name of [upper, upper.replace(/^RH/, ""), upper.replace(/^1000/, "K")]) {
                    map[name] ??= market;
                    map[name.replace("/", "_")] ??= market;
                }
            }
            markets = map;
        } catch (e) {
            marketsFailedAt = Date.now();
        } finally {
            marketsLoading = false;
        }
    }

    function currentMarket() {
        if (!markets) return null;
        const seg = location.pathname.match(/\/trade\/(.+?)\/?$/)?.[1];
        const fromUrl = seg && markets[decodeURIComponent(seg).toUpperCase()];
        if (fromUrl) return fromUrl;
        // "1,757.62 • ETH • Lighter"
        const fromTitle = document.title.split("•").map((s) => s.trim().toUpperCase())[1];
        return (fromTitle && markets[fromTitle]) || null;
    }

    // ---------- Orders (REST) ----------
    async function pollOrders() {
        const market = state.market;
        state.fetching = true;
        try {
            const resp = await fetch(`${API}/orderBookOrders?market_id=${market.id}&limit=${ORDER_LIMIT}`);
            if (resp.status === 429) {
                state.rateLimited = true;
                state.nextPollAt = Date.now() + RATE_LIMIT_PAUSE_MS;
                return;
            }
            const body = await resp.json();
            if (body.code !== 200) throw new Error(body.message || `code ${body.code}`);
            if (state.market !== market) return; // switched while loading
            const parse = (list) => (list || []).map((o) => {
                const price = parseFloat(o.price);
                return { acct: o.owner_account_index, price, usd: price * parseFloat(o.remaining_base_amount), pct: 0 };
            });
            const bids = parse(body.bids).sort((a, b) => b.price - a.price);
            const asks = parse(body.asks).sort((a, b) => a.price - b.price);
            const mid = bids.length && asks.length ? (bids[0].price + asks[0].price) / 2 : bids[0]?.price ?? asks[0]?.price ?? 0;
            if (mid > 0) for (const o of [...bids, ...asks]) o.pct = ((o.price - mid) / mid) * 100;
            state.snap = {
                bids,
                asks,
                mid,
                truncated: { bids: bids.length >= ORDER_LIMIT, asks: asks.length >= ORDER_LIMIT },
                total: book.ready && book.marketId === market.id ? bookLevels(mid) : null,
            };
            state.error = null;
            state.rateLimited = false;
            state.nextPollAt = Date.now() + POLL_MS;
        } catch (e) {
            state.error = e instanceof Error ? e.message : String(e);
            state.nextPollAt = Date.now() + ERROR_RETRY_MS;
        } finally {
            state.fetching = false;
            refresh();
        }
    }

    // ---------- Full book (socket) ----------
    function bookLevels(mid) {
        const side = (levels, desc) => {
            let cum = 0;
            return [...levels]
                .sort((a, b) => (desc ? b[0] - a[0] : a[0] - b[0]))
                .map(([price, size]) => {
                    cum += price * size;
                    return { pct: ((price - mid) / mid) * 100, cum };
                });
        };
        return {
            bids: side(book.bids, true).filter((l) => l.pct <= 0),
            asks: side(book.asks, false).filter((l) => l.pct >= 0),
        };
    }

    function applyLevels(target, levels) {
        for (const { price, size } of levels || []) {
            const p = parseFloat(price), s = parseFloat(size);
            if (!(p > 0)) continue;
            if (s > 0) target.set(p, s);
            else target.delete(p);
        }
    }

    function subscribeBook(marketId) {
        if (book.marketId !== null && book.marketId !== marketId) {
            socket.send(JSON.stringify({ type: "unsubscribe", channel: `order_book/${book.marketId}` }));
        }
        book.marketId = marketId;
        book.ready = false;
        book.bids.clear();
        book.asks.clear();
        socket.send(JSON.stringify({ type: "subscribe", channel: `order_book/${marketId}` }));
    }

    function ensureSocket() {
        const wanted = state.open && state.market ? state.market.id : null;
        if (wanted === null) {
            closeSocket();
            return;
        }
        if (!socket) {
            if (Date.now() < socketRetryAt) return;
            try {
                socket = new WebSocket(`${BACKEND.stream}?encoding=json&readonly=true`);
            } catch (e) {
                socketRetryAt = Date.now() + SOCKET_RETRY_MS;
                return;
            }
            const ws = socket;
            ws.onopen = () => {
                if (socket === ws && state.market) subscribeBook(state.market.id);
            };
            ws.onmessage = (event) => {
                if (socket !== ws) return;
                let msg;
                try { msg = JSON.parse(event.data); } catch (e) { return; }
                if (msg.type === "ping") {
                    ws.send(JSON.stringify({ type: "pong" }));
                    return;
                }
                if (msg.type !== "subscribed/order_book" && msg.type !== "update/order_book") return;
                if (msg.channel !== `order_book:${book.marketId}`) return;
                if (msg.type === "subscribed/order_book") {
                    book.bids.clear();
                    book.asks.clear();
                    book.ready = true;
                }
                applyLevels(book.bids, msg.order_book?.bids);
                applyLevels(book.asks, msg.order_book?.asks);
            };
            ws.onclose = () => {
                if (socket !== ws) return;
                socket = null;
                book.marketId = null;
                book.ready = false;
                socketRetryAt = Date.now() + SOCKET_RETRY_MS;
            };
            return;
        }
        if (socket.readyState === WebSocket.OPEN && book.marketId !== wanted) subscribeBook(wanted);
    }

    function closeSocket() {
        if (!socket) return;
        const ws = socket;
        socket = null;
        book.marketId = null;
        book.ready = false;
        book.bids.clear();
        book.asks.clear();
        try { ws.close(); } catch (e) {}
    }

    // ---------- Model ----------
    function theme() {
        return document.documentElement.dataset.theme === "light" ? "light" : "dark";
    }

    /** Colour slots: keep those of groups still in the top set; newcomers take the lowest free slot. */
    function assignSlots(prev, top, size) {
        const next = new Map();
        for (const key of top) if (prev.has(key)) next.set(key, prev.get(key));
        const used = new Set(next.values());
        let free = 0;
        for (const key of top) {
            if (next.has(key)) continue;
            while (used.has(free)) free++;
            if (free >= size) break;
            next.set(key, free);
            used.add(free);
        }
        return next;
    }

    /** How far from mid (in %, positive) each side's known orders reach, or null with no orders. */
    function visibleEdges(snap) {
        const edge = (orders) => (orders.length ? Math.abs(orders.at(-1).pct) : null);
        let bid = edge(snap.bids), ask = edge(snap.asks);
        bid ??= ask;
        ask ??= bid;
        return bid > 0 && ask > 0 ? { bid, ask } : null;
    }

    /** The chart's extent on each side of mid, in % (positive). */
    function resolveRange(snap) {
        const fixed = { bid: state.prefs.range, ask: state.prefs.range };
        const edges = state.prefs.rangeMode === "fixed" ? null : visibleEdges(snap);
        if (!edges) return fixed;
        if (state.prefs.rangeMode === "visibleMin") {
            const nearer = Math.min(edges.bid, edges.ask);
            return { bid: nearer, ask: nearer };
        }
        return edges;
    }

    function buildModel() {
        const snap = state.snap;
        if (!snap || !(snap.mid > 0)) return null;
        const { bid: bidPct, ask: askPct } = resolveRange(snap);
        const palette = PALETTE[theme()];

        // Resting USD per account within range
        const byAcct = new Map();
        const rowOf = (acct) => {
            let r = byAcct.get(acct);
            if (!r) byAcct.set(acct, (r = { acct, bid: 0, ask: 0 }));
            return r;
        };
        for (const o of snap.bids) {
            if (o.pct < -bidPct) break;
            rowOf(o.acct).bid += o.usd;
        }
        for (const o of snap.asks) {
            if (o.pct > askPct) break;
            rowOf(o.acct).ask += o.usd;
        }

        const groupMap = new Map();
        for (const r of byAcct.values()) {
            const key = ownerKey(r.acct);
            let g = groupMap.get(key);
            if (!g) groupMap.set(key, (g = { key, members: [], bid: 0, ask: 0 }));
            g.members.push(r);
            g.bid += r.bid;
            g.ask += r.ask;
        }
        const total = (x) => x.bid + x.ask;
        const groups = [...groupMap.values()].sort((a, b) => total(b) - total(a));
        for (const g of groups) g.members.sort((a, b) => total(b) - total(a));

        const attributedAll = groups.reduce((sum, g) => sum + total(g), 0);
        const layered = groups.filter((g) => total(g) >= MIN_LAYER_SHARE * attributedAll).slice(0, palette.length);
        state.slots = assignSlots(state.slots, layered.map((g) => g.key), palette.length);
        const groupOfAcct = new Map();
        for (const g of groups) for (const r of g.members) groupOfAcct.set(r.acct, g);
        const layerOfGroup = new Map([...state.slots].map(([key, slot]) => [key, `L${slot}`]));
        const layerOfAcct = (acct) => layerOfGroup.get(groupOfAcct.get(acct)?.key) ?? OTHERS;

        // Where the 250 orders run out on each side, when the response was cut off
        const reach = {
            bid: snap.truncated.bids && snap.bids.length ? snap.bids.at(-1).pct : null,
            ask: snap.truncated.asks && snap.asks.length ? snap.asks.at(-1).pct : null,
        };
        const fullBook = snap.total !== null;
        const reachInRange = (reach.bid !== null && reach.bid > -bidPct) || (reach.ask !== null && reach.ask < askPct);
        // Largest owner at the bottom of the stack; colours stay with their owner across refreshes
        const slotLayers = [...state.slots.entries()]
            .map(([key, slot]) => ({ key, layer: `L${slot}`, slot }))
            .sort((a, b) => total(groupMap.get(b.key)) - total(groupMap.get(a.key)));
        const hasOthers = groups.length > slotLayers.length;
        const keys = [...slotLayers.map((s) => s.layer), ...(hasOthers ? [OTHERS] : []), ...(fullBook && reachInRange ? [UNATTRIBUTED] : [])];

        // Legend: colour, label and group per layer. Accounts of one owner can share a name.
        const layers = {
            [OTHERS]: { color: OTHERS_COLOR[theme()], label: "Others" },
            [UNATTRIBUTED]: { color: "var(--color-meta, #8a8f98)", label: "Not attributed" },
        };
        const named = slotLayers.map((s) => groupLabel(groupMap.get(s.key)));
        slotLayers.forEach((s, i) => {
            const group = groupMap.get(s.key);
            const dup = named.indexOf(named[i]) !== named.lastIndexOf(named[i]);
            layers[s.layer] = { color: palette[s.slot], label: dup ? `${named[i]} #${group.members[0].acct}` : named[i], group };
        });

        // Price points: every order and book level in range, plus the edges and mid
        const xs = new Set([-bidPct, 0, askPct]);
        for (const o of snap.bids) if (o.pct >= -bidPct) xs.add(o.pct);
        for (const o of snap.asks) if (o.pct <= askPct) xs.add(o.pct);
        for (const l of snap.total?.bids || []) if (l.pct >= -bidPct) xs.add(l.pct);
        for (const l of snap.total?.asks || []) if (l.pct <= askPct) xs.add(l.pct);
        const sorted = [...xs].sort((a, b) => a - b);
        let peak = 0;
        const eps = 1e-12;

        // Sweep a side outward from mid: per-layer sums, plus the full book's depth past the
        // last known order. Up to there the orders are the whole book; comparing the two
        // closer in would only show the gap between the socket and the REST snapshot.
        const sweep = (orders, levels, xsOut, reached, reachPct) => {
            const sums = new Map();
            const pts = [];
            let oi = 0, li = 0, bookCum = 0, bookAtReach = 0;
            if (reachPct !== null) {
                for (const l of levels) {
                    if (!reached(l.pct, reachPct)) break;
                    bookAtReach = l.cum;
                }
            }
            for (const x of xsOut) {
                while (oi < orders.length && reached(orders[oi].pct, x)) {
                    const k = layerOfAcct(orders[oi].acct);
                    sums.set(k, (sums.get(k) || 0) + orders[oi].usd);
                    oi++;
                }
                while (li < levels.length && reached(levels[li].pct, x)) bookCum = levels[li++].cum;
                const vals = [];
                let base = 0;
                for (const k of keys) {
                    const past = reachPct !== null && !reached(x, reachPct) && x !== reachPct;
                    const v = k === UNATTRIBUTED ? (past ? Math.max(0, bookCum - bookAtReach) : 0) : sums.get(k) || 0;
                    vals.push(v);
                    base += v;
                }
                pts.push({ x, vals, top: base });
                peak = Math.max(peak, base);
            }
            return pts;
        };
        const bidReached = (pct, x) => pct >= x - eps;
        const askReached = (pct, x) => pct <= x + eps;
        const bidPts = sweep(snap.bids, snap.total?.bids || [], sorted.filter((x) => x <= 0).reverse(), bidReached, reach.bid);
        const askPts = sweep(snap.asks, snap.total?.asks || [], sorted.filter((x) => x >= 0), askReached, reach.ask);

        const attributed = { bids: 0, asks: 0 };
        for (const r of byAcct.values()) {
            attributed.bids += r.bid;
            attributed.asks += r.ask;
        }
        const inRange = { bids: bidPts.at(-1)?.top || 0, asks: askPts.at(-1)?.top || 0 };
        const totals = {
            bids: Math.max(attributed.bids, inRange.bids),
            asks: Math.max(attributed.asks, inRange.asks),
        };
        totals.unattributed = totals.bids + totals.asks - attributed.bids - attributed.asks;

        const lookupCandidates = [
            ...slotLayers.flatMap((s) => groupMap.get(s.key).members.slice(0, 3).map((r) => r.acct)),
            ...[...byAcct.values()].sort((a, b) => total(b) - total(a)).slice(0, LOOKUP_TOP_ACCOUNTS).map((r) => r.acct),
        ];

        return {
            bidPct, askPct, span: bidPct + askPct, keys, layers, groups, groupOfAcct, layerOfAcct, bidPts, askPts,
            maxY: peak * 1.05 || 1, totals, reach, fullBook, lookupCandidates,
            bidReached, askReached,
        };
    }

    // ---------- Formatting ----------
    function formatUSD(value) {
        if (value >= 999_500) return `$${(value / 1_000_000).toFixed(value >= 99_950_000 ? 0 : 1)}M`;
        if (value >= 1000) return `$${(value / 1000).toFixed(0)}K`;
        return `$${value.toFixed(0)}`;
    }

    function formatPct(value, decimals) {
        const text = `${Math.abs(value).toFixed(decimals)}%`;
        return value < 0 && Number(text.slice(0, -1)) !== 0 ? `−${text}` : text;
    }

    /** Compact % for range labels: 0.042, 0.42, 4.2, 42. */
    function shortPct(value) {
        return value < 0.1 ? value.toFixed(3) : value < 10 ? value.toFixed(2) : value.toFixed(1);
    }

    function rangeText(bidPct, askPct) {
        return bidPct === askPct ? `±${shortPct(bidPct)}%` : `−${shortPct(bidPct)}% / +${shortPct(askPct)}%`;
    }

    function formatPrice(value) {
        const decimals = Math.min(state.market?.priceDecimals ?? 2, 8);
        return value.toLocaleString("en-US", { minimumFractionDigits: decimals, maximumFractionDigits: decimals });
    }

    function niceStep(max, count) {
        const raw = max / count;
        const pow = 10 ** Math.floor(Math.log10(raw));
        const n = raw / pow;
        return (n <= 1 ? 1 : n <= 2 ? 2 : n <= 2.5 ? 2.5 : n <= 5 ? 5 : 10) * pow;
    }

    // ---------- Styles ----------
    function injectStyles() {
        if (document.getElementById("pp-depth-style")) return;
        const style = document.createElement("style");
        style.id = "pp-depth-style";
        style.textContent = `
.pp-dt { position: absolute; left: 0; right: 0; bottom: 0; z-index: 20; display: flex; flex-direction: column; min-height: 0;
  background: linear-gradient(var(--color-fill, transparent), var(--color-fill, transparent)), var(--color-bg, #06060c);
  color: var(--color-ink, #f3f3f3); font-size: 12px; line-height: 16px; font-variant-numeric: tabular-nums; }
.pp-dt button { font: inherit; }
.pp-dt-head { display: flex; align-items: center; justify-content: space-between; gap: 8px 16px; flex-wrap: wrap; padding: 8px 10px 4px 12px; }
.pp-dt-title { font-weight: var(--font-weight-medium, 485); color: color-mix(in oklab, var(--color-ink, #f3f3f3) 80%, transparent); white-space: nowrap; }
.pp-dt-meta { color: var(--color-meta, #8a8f98); white-space: nowrap; }
.pp-dt-meta b { font-weight: var(--font-weight-medium, 485); color: var(--color-dim, #b5b8bd); }
.pp-dt-controls { display: flex; align-items: center; gap: 4px; flex-wrap: wrap; }
.pp-dt-sep { width: 0.5px; height: 14px; background: var(--color-line, #ffffff12); margin: 0 4px; }
.pp-dt-btn { position: relative; padding: 2px 7px; border: 0; border-radius: var(--radius-card, 4px); background: transparent; cursor: pointer; white-space: nowrap;
  color: color-mix(in oklab, var(--color-ink, #f3f3f3) 80%, transparent); transition: color .15s, background-color .15s; }
.pp-dt-btn:hover { color: var(--color-ink, #f3f3f3); background: color-mix(in oklab, var(--color-ink, #f3f3f3) 5%, transparent); }
.pp-dt-btn[aria-pressed="true"] { color: var(--color-ink, #f3f3f3); font-weight: var(--font-weight-medium, 485); background: var(--color-fill, #ffffff0d);
  box-shadow: inset 0 var(--hl-y, .4px) 0 0 var(--hl-top, #ffffff14), 0 0 0 .5px var(--ring-crisp, #000), 0 1px 0 0 var(--edge-under, transparent); }
:root[data-theme="light"] .pp-dt-btn[aria-pressed="true"] { background: var(--color-surface, #fff); box-shadow: inset 0 0 0 .5px var(--ring-crisp, #0002); }
.pp-dt-legend { display: flex; flex-wrap: wrap; gap: 4px 14px; padding: 2px 12px 6px; }
.pp-dt-leg { display: flex; align-items: center; gap: 6px; padding: 0; border: 0; background: none; cursor: pointer; color: var(--color-dim, #b5b8bd); transition: opacity .15s; max-width: 220px; }
.pp-dt-leg span:last-child { overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
.pp-dt-leg:hover { color: var(--color-ink, #f3f3f3); }
.pp-dt-leg.pp-dim { opacity: .4; }
.pp-dt-sw { width: 8px; height: 8px; border-radius: 2px; flex: none; }
.pp-dt-sw.pp-hatch { border: 1px dashed var(--color-meta, #8a8f98); background: none !important; }
.pp-dt-note { padding: 0 12px 4px; color: var(--color-warn, #f5b83d); }
.pp-dt-note.pp-err { color: var(--color-down, #ea5455); }
.pp-dt-chart { position: relative; flex: 1; min-height: 120px; }
.pp-dt-chart svg { position: absolute; inset: 0; width: 100%; height: 100%; display: block; overflow: visible; }
.pp-dt-chart text { fill: var(--color-meta, #8a8f98); font-size: 10px; font-variant-numeric: tabular-nums; }
.pp-dt-empty { position: absolute; inset: 0; display: flex; align-items: center; justify-content: center; text-align: center; padding: 0 24px; color: var(--color-meta, #8a8f98); }
.pp-dt-tip { position: absolute; z-index: 2; pointer-events: none; min-width: 210px; max-width: 320px; max-height: calc(100% - 8px); overflow: hidden; display: flex; flex-direction: column; gap: 3.5px;
  padding: 7px 10.5px; border: .5px solid var(--color-line, #ffffff12); border-radius: var(--radius-card, 4px); font-size: 11px; line-height: 1.15;
  color: var(--color-muted, var(--color-meta, #8a8f98)); background: var(--color-overlay, var(--color-elevated, #26262c)); box-shadow: var(--shadow-elevate-popover, 0 4px 8px #0008); }
.pp-dt-tip-kv { display: flex; justify-content: space-between; gap: 17.6px; }
.pp-dt-tip-kv b { font-weight: var(--font-weight-medium, 485); }
.pp-dt-tip-kv b.pp-up { color: var(--color-up, #26c281); }
.pp-dt-tip-kv b.pp-down { color: var(--color-down, #ea5455); }
.pp-dt-tip-sep { height: .5px; margin: 2px 0; background: var(--color-line, #ffffff12); }
.pp-dt-tip-row { display: flex; align-items: center; gap: 6px; }
.pp-dt-tip-row .pp-lbl { color: var(--color-dim, #b5b8bd); }
.pp-dt-tip-row .pp-lbl { flex: 1; min-width: 0; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
.pp-dt-tip-row .pp-usd { font-weight: var(--font-weight-medium, 485); }
.pp-dt-tip-row .pp-pct { width: 30px; text-align: right; color: var(--color-meta, #8a8f98); }
.pp-dt-tip-sub { padding-left: 14px; }
.pp-dt-tip-sub .pp-lbl { color: var(--color-muted, var(--color-meta, #8a8f98)); }
.pp-dt-tip-sub .pp-usd { font-weight: 400; }
.pp-dt-tip-idx { color: var(--color-meta, #8a8f98); margin-left: 4px; }
.pp-pro { display: inline-flex; align-items: center; gap: 6px; padding: 0; border: 0; background: none; cursor: pointer; font: inherit; font-size: 12px; line-height: 14px;
  color: color-mix(in oklab, var(--color-ink, #f3f3f3) 50%, transparent); transition: color .15s; white-space: nowrap; }
.pp-pro:hover, .pp-pro[aria-pressed="true"] { color: var(--color-ink, #f3f3f3); }
.pp-pro-track { position: relative; width: 22px; height: 12px; border-radius: 6px; background: var(--color-fill, #ffffff0d); box-shadow: inset 0 0 0 .5px var(--color-line, #ffffff12); transition: background-color .15s; }
.pp-pro-knob { position: absolute; top: 2px; left: 2px; width: 8px; height: 8px; border-radius: 50%; background: color-mix(in oklab, var(--color-ink, #f3f3f3) 60%, transparent); transition: transform .15s, background-color .15s; }
.pp-pro[aria-pressed="true"] .pp-pro-track { background: var(--color-up, #26c281); box-shadow: none; }
.pp-pro[aria-pressed="true"] .pp-pro-knob { transform: translateX(10px); background: var(--color-bg, #06060c); }
.pp-dt-pop { position: absolute; z-index: 3; width: 360px; max-width: calc(100% - 20px); max-height: calc(100% - 60px); overflow: auto;
  display: flex; flex-direction: column; gap: 10px; padding: 12px; border-radius: 6px;
  background: var(--color-elevated, #26262c); box-shadow: var(--shadow-elevate-popover, 0 4px 8px #0008); }
.pp-dt-pop p { margin: 0; color: var(--color-meta, #8a8f98); }
.pp-dt-pop-row { display: flex; gap: 6px; align-items: center; flex-wrap: wrap; }
.pp-dt-range { width: 52px; box-sizing: border-box; margin-left: 2px; padding: 1px 6px; font: inherit; text-align: center; color: var(--color-ink, #f3f3f3);
  background: transparent; border: .5px solid var(--color-line, #ffffff12); border-radius: var(--radius-card, 4px); outline: none; }
.pp-dt-range::placeholder { color: var(--color-meta, #8a8f98); }
.pp-dt-range:focus { border-color: var(--color-meta, #8a8f98); }
.pp-dt-range.pp-on { font-weight: var(--font-weight-medium, 485); background: var(--color-fill, #ffffff0d);
  box-shadow: inset 0 var(--hl-y, .4px) 0 0 var(--hl-top, #ffffff14), 0 0 0 .5px var(--ring-crisp, #000); border-color: transparent; }
.pp-dt-pop input, .pp-dt-pop textarea { font: inherit; color: var(--color-ink, #f3f3f3); background: var(--color-fill, #ffffff0d); border: .5px solid var(--color-line, #ffffff12);
  border-radius: var(--radius-card, 4px); padding: 4px 6px; outline: none; min-width: 0; }
.pp-dt-pop input:focus, .pp-dt-pop textarea:focus { border-color: var(--color-meta, #8a8f98); }
.pp-dt-pop textarea { width: 100%; box-sizing: border-box; min-height: 110px; resize: vertical; font-family: ui-monospace, SFMono-Regular, Menlo, monospace; font-size: 11px; }
.pp-dt-pop pre { margin: 0; padding: 8px; border-radius: var(--radius-card, 4px); background: var(--color-fill, #ffffff0d); color: var(--color-dim, #b5b8bd);
  font: 11px/15px ui-monospace, SFMono-Regular, Menlo, monospace; white-space: pre; overflow: auto; }
.pp-dt-pop summary { cursor: pointer; color: var(--color-dim, #b5b8bd); }
.pp-dt-pop details[open] summary { margin-bottom: 6px; }
.pp-dt-cta { padding: 3px 10px; border: 0; border-radius: var(--radius-card, 4px); cursor: pointer; background: var(--color-ink, #f3f3f3); color: var(--color-bg, #06060c); font-weight: var(--font-weight-medium, 485); }
.pp-dt-cta:disabled { opacity: .4; cursor: default; }
.pp-dt-status { color: var(--color-up, #26c281) !important; }
.pp-dt-status.pp-err { color: var(--color-down, #ea5455) !important; }
.pp-dt-danger { color: var(--color-down, #ea5455) !important; }
`;
        (document.head || document.documentElement).appendChild(style);
    }

    // ---------- DOM helpers ----------
    function el(tag, props = {}, children = []) {
        const node = document.createElement(tag);
        for (const [k, v] of Object.entries(props)) {
            if (k === "class") node.className = v;
            else if (k === "text") node.textContent = v;
            else if (k.startsWith("on")) node.addEventListener(k.slice(2), v);
            else node.setAttribute(k, v);
        }
        for (const child of [].concat(children)) if (child) node.append(child);
        return node;
    }

    function svgEl(tag, attrs = {}) {
        const node = document.createElementNS("http://www.w3.org/2000/svg", tag);
        for (const [k, v] of Object.entries(attrs)) node.setAttribute(k, v);
        return node;
    }

    function swatch(key, color) {
        const sw = el("span", { class: `pp-dt-sw${key === UNATTRIBUTED ? " pp-hatch" : ""}` });
        sw.style.backgroundColor = color;
        return sw;
    }

    // ---------- Lighter's Depth view ----------
    // The Price tab's view buttons (TradingView / Original / Depth) mark the selected one
    // with text-ink, the others with text-ink/50.
    function findViewButtons() {
        for (const btn of document.querySelectorAll("button:not([data-pp-pro])")) {
            if (btn.textContent.trim() !== "TradingView") continue;
            const row = btn.parentElement;
            const depth = [...row.querySelectorAll(":scope > button:not([data-pp-pro])")].find((b) => b.textContent.trim() === "Depth");
            if (depth) return { row, depth };
        }
        return null;
    }

    function ensureProSwitch(depthBtn, depthView) {
        let pro = depthBtn.parentElement.querySelector(":scope > [data-pp-pro]");
        if (!pro) {
            pro = el("button", {
                type: "button",
                class: "pp-pro",
                "data-pp-pro": "",
                title: "Pro: depth stacked by owner (Perpetualpulse)",
                onclick: (e) => {
                    e.preventDefault();
                    e.stopPropagation();
                    state.pro = !state.pro;
                    tick();
                },
            }, [el("span", { class: "pp-pro-track" }, [el("span", { class: "pp-pro-knob" })]), el("span", { text: "Pro" })]);
        }
        if (pro.previousElementSibling !== depthBtn) depthBtn.after(pro);
        pro.style.display = depthView ? "" : "none";
        pro.setAttribute("aria-pressed", String(state.pro));
    }

    function setShowing(show) {
        if (show === state.open) return;
        state.open = show;
        if (show) {
            state.nextPollAt = 0;
            return;
        }
        hideTip();
        closeSocket();
        ui?.root.remove();
    }

    // ---------- Panel ----------
    function buildUI() {
        const rangeInput = el("input", {
            class: "pp-dt-range",
            type: "text",
            inputmode: "decimal",
            placeholder: "±%",
            title: `Custom range, 0–${MAX_RANGE}% from mid. Enter to apply.`,
            "aria-label": "Custom range in % from mid",
        });
        const applyCustom = () => {
            const v = Number(rangeInput.value.trim().replace(/^±/, "").replace(/%$/, "").replace(",", "."));
            if (validRange(v)) setRange(Math.round(v * 1000) / 1000);
            renderHeader(); // shows the applied range, or puts back the last one
        };
        rangeInput.addEventListener("keydown", (e) => {
            e.stopPropagation(); // keep Lighter's and the extension's hotkeys out of it
            if (e.key === "Enter") rangeInput.blur();
            if (e.key === "Escape") {
                rangeInput.value = "";
                rangeInput.blur();
            }
        });
        rangeInput.addEventListener("blur", applyCustom);
        const rangeSeg = el("div", { class: "pp-dt-controls" }, [
            ...RANGES.map((r) => el("button", { class: "pp-dt-btn", "data-range": String(r), text: `±${r}%`, onclick: () => setRange(r) })),
            el("button", { class: "pp-dt-btn", "data-mode": "visibleSides", text: "Attributed", onclick: () => setRangeMode("visibleSides") }),
            el("button", { class: "pp-dt-btn", "data-mode": "visibleMin", text: "Attributed ±", onclick: () => setRangeMode("visibleMin") }),
            rangeInput,
        ]);
        const labelsBtn = el("button", { class: "pp-dt-btn", text: "Labels", onclick: () => toggleLabelsPanel() });
        const head = el("div", { class: "pp-dt-head" }, [rangeSeg, labelsBtn]);
        const legend = el("div", { class: "pp-dt-legend" });
        const notes = el("div");
        const svg = svgEl("svg");
        const empty = el("div", { class: "pp-dt-empty" });
        const tip = el("div", { class: "pp-dt-tip" });
        tip.style.display = "none";
        const chart = el("div", { class: "pp-dt-chart" }, [svg, empty, tip]);
        const pop = el("div", { class: "pp-dt-pop" });
        pop.style.display = "none";
        const root = el("div", { class: "pp-dt" }, [head, legend, notes, chart, pop]);

        chart.addEventListener("mousemove", (e) => {
            const model = state.model;
            if (!model || !ui.geom) return;
            const rect = svg.getBoundingClientRect();
            const { left, width } = ui.geom;
            const px = e.clientX - rect.left;
            if (px < left || px > left + width) {
                hideTip();
                return;
            }
            state.hoverX = ((px - left) / width) * model.span - model.bidPct;
            renderTip(e.clientX - rect.left, e.clientY - rect.top);
        });
        chart.addEventListener("mouseleave", hideTip);
        new ResizeObserver(() => renderChart()).observe(chart);

        return { root, rangeSeg, rangeInput, labelsBtn, legend, notes, svg, empty, tip, chart, pop, wrapper: null, geom: null, popStatus: null };
    }

    function hideTip() {
        state.hoverX = null;
        if (!ui) return;
        ui.tip.style.display = "none";
        ui.svg.querySelector(".pp-cross")?.remove();
    }

    function setRange(value) {
        if (state.prefs.rangeMode === "fixed" && state.prefs.range === value) return;
        state.prefs.range = value;
        state.prefs.rangeMode = "fixed";
        savePrefs();
        refresh();
    }

    function setRangeMode(mode) {
        if (state.prefs.rangeMode === mode) return;
        state.prefs.rangeMode = mode;
        state.focus = null;
        savePrefs();
        refresh();
    }

    /** Lays the panel over the chart area under the tab row, where Lighter draws its depth chart. */
    function mountPanel(viewRow) {
        const tabPanel = viewRow.parentElement?.parentElement;
        const wrapper = tabPanel?.parentElement;
        if (!wrapper) return false;
        ui ??= buildUI();
        if (getComputedStyle(wrapper).position === "static") wrapper.style.position = "relative";
        if (ui.root.parentElement !== wrapper) wrapper.appendChild(ui.root);
        const top = `${Math.max(0, tabPanel.getBoundingClientRect().bottom - wrapper.getBoundingClientRect().top)}px`;
        if (ui.root.style.top !== top) ui.root.style.top = top;
        return true;
    }

    // ---------- Render ----------
    function refresh() {
        if (!state.open || !ui) return;
        state.model = buildModel();
        renderHeader();
        renderChart();
        if (state.hoverX !== null && ui.lastTipPos) renderTip(ui.lastTipPos.x, ui.lastTipPos.y);
    }

    function renderHeader() {
        const model = state.model;
        const mode = state.prefs.rangeMode;
        const fixed = mode === "fixed";
        // The Attributed buttons' hover text says where the known orders end right now
        const edges = state.snap ? visibleEdges(state.snap) : null;
        const nearer = edges && Math.min(edges.bid, edges.ask);
        const now = (text) => (edges ? ` Now ${text}.` : "");
        for (const b of ui.rangeSeg.querySelectorAll("button")) {
            const on = b.dataset.mode ? b.dataset.mode === mode : fixed && Number(b.dataset.range) === state.prefs.range;
            b.setAttribute("aria-pressed", String(on));
            if (b.dataset.mode === "visibleSides") {
                b.title = `Each side out to its last known order (the best ${ORDER_LIMIT} per side), so every order shown has an owner.${now(edges && rangeText(edges.bid, edges.ask))}`;
            }
            if (b.dataset.mode === "visibleMin") {
                b.title = `Both sides out to the nearer side's last known order, so every order shown has an owner.${now(edges && rangeText(nearer, nearer))}`;
            }
        }
        // The box shows a custom range while it's the one in use
        const custom = fixed && !RANGES.includes(state.prefs.range);
        if (document.activeElement !== ui.rangeInput) ui.rangeInput.value = custom ? `±${state.prefs.range}%` : "";
        ui.rangeInput.classList.toggle("pp-on", custom);
        ui.labelsBtn.setAttribute("aria-pressed", String(ui.pop.style.display !== "none"));

        // Legend
        ui.legend.replaceChildren();
        if (model) {
            if (state.focus && !model.keys.includes(state.focus)) state.focus = null;
            for (const k of model.keys) {
                const layer = model.layers[k];
                const btn = el("button", {
                    class: `pp-dt-leg${state.focus && state.focus !== k ? " pp-dim" : ""}`,
                    title: k === UNATTRIBUTED ? `Depth past the best ${ORDER_LIMIT} orders per side, whose owners aren't known` : layer.label,
                    onclick: () => {
                        state.focus = state.focus === k ? null : k;
                        refresh();
                    },
                }, [swatch(k, layer.color), el("span", { text: layer.label })]);
                ui.legend.append(btn);
            }
        }

        // Notes
        ui.notes.replaceChildren();
        const note = (text, err) => ui.notes.append(el("div", { class: `pp-dt-note${err ? " pp-err" : ""}`, text }));
        if (state.rateLimited) note("Lighter is rate limiting this browser; retrying in a minute.", true);
        else if (state.error) note(`Couldn't load orders: ${state.error}. Retrying.`, true);
        if (model) {
            const reachBid = model.reach.bid !== null && model.reach.bid > -model.bidPct ? model.reach.bid : null;
            const reachAsk = model.reach.ask !== null && model.reach.ask < model.askPct ? model.reach.ask : null;
            if (reachBid !== null || reachAsk !== null) {
                const where = [reachBid !== null && `bids to ${formatPct(reachBid, 3)}`, reachAsk !== null && `asks to ${formatPct(reachAsk, 3)}`].filter(Boolean).join(", ");
                const all = model.totals.bids + model.totals.asks;
                note(model.fullBook
                    ? `Owners are only known for the best ${ORDER_LIMIT} orders per side (${where}). Deeper depth is Not attributed: ${all ? ((model.totals.unattributed / all) * 100).toFixed(0) : 0}% of depth within ${rangeText(model.bidPct, model.askPct)}.`
                    : `Owners are only known for the best ${ORDER_LIMIT} orders per side (${where}); depth past them is still loading.`);
            }
        }
    }

    function renderChart() {
        if (!ui || !state.open) return;
        const model = state.model;
        const svg = ui.svg;
        svg.replaceChildren();
        ui.geom = null;
        if (!model) {
            ui.empty.textContent = state.market ? "Loading orders…" : "Loading markets…";
            ui.empty.style.display = "";
            return;
        }
        ui.empty.style.display = "none";
        const W = ui.chart.clientWidth, H = ui.chart.clientHeight;
        if (W < 50 || H < 50) return;
        const m = { left: 8, right: 62, top: 12, bottom: 24 };
        const width = W - m.left - m.right, height = H - m.top - m.bottom;
        ui.geom = { left: m.left, top: m.top, width, height };
        const X = (x) => m.left + ((x + model.bidPct) / model.span) * width;
        const Y = (v) => m.top + height - (v / model.maxY) * height;
        const fmt = (n) => n.toFixed(1);

        const text = (x, y, anchor, value) => {
            const t = svgEl("text", { x: fmt(x), y: fmt(y), "text-anchor": anchor });
            t.textContent = value;
            svg.append(t);
        };

        // Dashed grid with labels on the right axis, as on Lighter's depth chart
        const step = niceStep(model.maxY, 4);
        for (let i = 1; i * step <= model.maxY; i++) {
            const y = Y(i * step);
            svg.append(svgEl("line", { x1: m.left, x2: m.left + width, y1: fmt(y), y2: fmt(y), stroke: "var(--color-line, #ffffff12)", "stroke-dasharray": "3 3" }));
            text(m.left + width + 6, y + 3, "start", formatUSD(i * step));
        }
        svg.append(svgEl("line", { x1: m.left + width, x2: m.left + width, y1: m.top, y2: m.top + height, stroke: "var(--color-line, #ffffff12)" }));
        svg.append(svgEl("line", { x1: m.left, x2: m.left + width, y1: m.top + height, y2: m.top + height, stroke: "var(--color-line, #ffffff12)" }));

        // Price axis: the range's edge prices at the ends, round prices between
        const mid = state.snap.mid;
        const lowPrice = Math.max(0, mid * (1 - model.bidPct / 100));
        const highPrice = mid * (1 + model.askPct / 100);
        const XP = (price) => X((price / mid - 1) * 100);
        const priceStep = niceStep(highPrice - lowPrice, Math.max(2, Math.floor(width / 110)));
        const first = Math.ceil(lowPrice / priceStep);
        for (let i = first; i * priceStep <= highPrice; i++) {
            const px = XP(i * priceStep);
            if (px - m.left < 56 || m.left + width - px < 56) continue;
            text(px, H - 8, "middle", formatPrice(i * priceStep));
        }
        text(m.left, H - 8, "start", formatPrice(lowPrice));
        text(m.left + width, H - 8, "end", formatPrice(highPrice));

        // Each layer is the line at its cumulative top, no fill: the gap between two lines is that
        // layer's depth. A step holds its value until the next price point outward. A line starts
        // where its layer first adds depth, rising from the line below; before that it would only
        // trace that line. Drawn top of the stack first, so where lines touch the lower, larger
        // layer stays visible.
        const dim = (k) => state.focus !== null && state.focus !== k;
        [...model.keys.entries()].reverse().forEach(([ki, k]) => {
            const layer = model.layers[k];
            for (const pts of [model.bidPts, model.askPts]) {
                if (!pts.length) continue;
                const lo = pts.map((p) => p.vals.slice(0, ki).reduce((s, v) => s + v, 0));
                const hi = pts.map((p, i) => lo[i] + p.vals[ki]);
                const first = pts.findIndex((p) => p.vals[ki] > 0); // sums only grow outward from mid
                if (first < 0) continue;
                let top = `M${fmt(X(pts[first].x))},${fmt(Y(lo[first]))}V${fmt(Y(hi[first]))}`;
                for (let i = first + 1; i < pts.length; i++) top += `H${fmt(X(pts[i].x))}V${fmt(Y(hi[i]))}`;
                const unattributed = k === UNATTRIBUTED;
                svg.append(svgEl("path", {
                    d: top,
                    fill: "none",
                    stroke: unattributed ? "var(--color-meta, #8a8f98)" : layer.color,
                    "stroke-width": state.focus === k ? 2.25 : 1.5,
                    "stroke-linejoin": "round",
                    "stroke-dasharray": unattributed ? "4 3" : "",
                    "stroke-opacity": dim(k) ? 0.2 : 1,
                }));
            }
        });

        // Where the known orders run out
        for (const reach of [model.reach.bid, model.reach.ask]) {
            if (reach === null || reach <= -model.bidPct || reach >= model.askPct) continue;
            svg.append(svgEl("line", { x1: fmt(X(reach)), x2: fmt(X(reach)), y1: m.top, y2: m.top + height, stroke: "var(--color-warn, #f5b83d)", "stroke-dasharray": "2 4" }));
        }
    }

    /** Value of each layer at a % from mid, and who is behind it. */
    function stackAt(x) {
        const model = state.model;
        const bid = x < 0;
        const pts = bid ? model.bidPts : model.askPts;
        let point = null;
        for (const p of pts) {
            if (bid ? p.x >= x : p.x <= x) point = p;
            else break;
        }
        if (!point) return null;
        const reached = bid ? model.bidReached : model.askReached;
        const perAcct = new Map();
        for (const o of bid ? state.snap.bids : state.snap.asks) {
            if (!reached(o.pct, x)) break;
            perAcct.set(o.acct, (perAcct.get(o.acct) || 0) + o.usd);
        }
        const membersOf = new Map(); // layer -> [[acct, usd]]
        for (const [acct, usd] of perAcct) {
            const k = model.layerOfAcct(acct);
            if (!membersOf.has(k)) membersOf.set(k, []);
            membersOf.get(k).push([acct, usd]);
        }
        for (const list of membersOf.values()) list.sort((a, b) => b[1] - a[1]);
        return { bid, point, membersOf };
    }

    function renderTip(px, py) {
        const model = state.model;
        if (!ui || !model || state.hoverX === null || !ui.geom) return;
        ui.lastTipPos = { x: px, y: py };
        const x = state.hoverX;
        const stack = Math.abs(x) < 1e-9 ? null : stackAt(x);
        ui.svg.querySelector(".pp-cross")?.remove();
        if (!stack || !(stack.point.top > 0)) {
            ui.tip.style.display = "none";
            return;
        }
        const { left, top, width, height } = ui.geom;
        const cx = left + ((x + model.bidPct) / model.span) * width;
        ui.svg.append(svgEl("line", { class: "pp-cross", x1: cx.toFixed(1), x2: cx.toFixed(1), y1: top, y2: top + height, stroke: "var(--color-meta, #8a8f98)", "stroke-opacity": 0.6, "stroke-dasharray": "3 3" }));

        const decimals = model.span < 0.1 ? 4 : model.span < 1 ? 3 : 2;
        const price = state.snap.mid * (1 + x / 100);
        const total = stack.point.top;
        const rows = model.keys
            .map((k, i) => ({ k, v: stack.point.vals[i] }))
            .filter((r) => r.v > 0)
            .sort((a, b) => b.v - a.v);

        const tip = ui.tip;
        const kv = (label, value, cls = "") => el("div", { class: "pp-dt-tip-kv" }, [el("span", { text: label }), el("b", { class: cls, text: value })]);
        tip.replaceChildren(
            kv("Price", `${stack.bid ? "≥" : "≤"} ${formatPrice(price)}`),
            kv("Total Depth", formatUSD(total), stack.bid ? "pp-up" : "pp-down"),
            kv("Range", formatPct(x, decimals)),
            el("div", { class: "pp-dt-tip-sep" }),
        );
        for (const { k, v } of rows) {
            const layer = model.layers[k];
            const members = stack.membersOf.get(k) || [];
            const single = members.length === 1 && k !== OTHERS ? members[0][0] : null;
            const label = el("span", { class: "pp-lbl", text: layer.label });
            if (single !== null && !layer.label.startsWith("#")) label.append(el("span", { class: "pp-dt-tip-idx", text: `#${single}` }));
            tip.append(el("div", { class: "pp-dt-tip-row" }, [
                swatch(k, layer.color),
                label,
                el("span", { class: "pp-usd", text: formatUSD(v) }),
                el("span", { class: "pp-pct", text: `${((v / total) * 100).toFixed(0)}%` }),
            ]));
            if (single !== null || k === UNATTRIBUTED) continue;
            // Inside one owner the name is already on the row above: just tell its accounts apart
            const ownGroup = k !== OTHERS;
            const shown = rows.length > 5 ? TIP_MEMBERS_BUSY : TIP_MEMBERS;
            for (const [acct, usd] of members.slice(0, shown)) {
                const kind = accountKind(acct);
                const name = ownGroup ? (kind ? `${kind} #${acct}` : `#${acct}`) : accountLabel(acct);
                const sub = el("span", { class: "pp-lbl", text: name });
                if (!ownGroup && !name.startsWith("#")) sub.append(el("span", { class: "pp-dt-tip-idx", text: `#${acct}` }));
                tip.append(el("div", { class: "pp-dt-tip-row pp-dt-tip-sub" }, [sub, el("span", { class: "pp-usd", text: formatUSD(usd) }), el("span", { class: "pp-pct" })]));
            }
            if (members.length > shown) {
                tip.append(el("div", { class: "pp-dt-tip-row pp-dt-tip-sub" }, [el("span", { class: "pp-lbl", text: `+${members.length - shown} more accounts` })]));
            }
        }

        tip.style.display = "";
        const W = ui.chart.clientWidth, H = ui.chart.clientHeight;
        const tw = tip.offsetWidth, th = tip.offsetHeight;
        const tx = px + 14 + tw > W ? px - 14 - tw : px + 14;
        const ty = Math.min(Math.max(4, py - th / 2), Math.max(4, H - th - 4));
        tip.style.left = `${Math.max(4, tx)}px`;
        tip.style.top = `${ty}px`;
    }

    // ---------- Labels panel ----------
    const FORMAT_EXAMPLE = `{
  "accounts": {
    "<main account index>": { "l1": "<wallet>", "type": 0, "master": <main account index> },
    "<sub-account index>": { "l1": "<wallet>", "type": 1, "master": <main account index> },
    "<another account index>": { "name": "My desk" }
  },
  "l1": {
    "<wallet>": {
      "name": "Market Maker A",
      "x": "@handle",
      "telegram": "@handle",
      "description": "Free text"
    }
  }
}`;

    function toggleLabelsPanel(force) {
        if (!ui) return;
        const show = force ?? ui.pop.style.display === "none";
        ui.pop.style.display = show ? "" : "none";
        ui.popStatus = null;
        ui.confirmClear = false;
        if (show) {
            const left = ui.labelsBtn.getBoundingClientRect().left - ui.root.getBoundingClientRect().left;
            const top = ui.labelsBtn.getBoundingClientRect().bottom - ui.root.getBoundingClientRect().top + 6;
            ui.pop.style.left = `${Math.max(10, Math.min(left, ui.root.clientWidth - ui.pop.offsetWidth - 10))}px`;
            ui.pop.style.top = `${top}px`;
            renderLabelsPanel();
        }
        renderHeader();
    }

    function setPopStatus(text, err) {
        ui.popStatus = { text, err };
        renderLabelsPanel();
    }

    function importText(text) {
        let data;
        try {
            data = JSON.parse(text);
        } catch (e) {
            setPopStatus(`Not valid JSON: ${e.message}`, true);
            return;
        }
        if (!data || typeof data !== "object" || Array.isArray(data) || (!data.accounts && !data.l1)) {
            setPopStatus('Expected an object with "accounts" and/or "l1".', true);
            return;
        }
        const incoming = normalizeLabels(data);
        const accounts = Object.keys(incoming.accounts).length;
        const wallets = Object.keys(incoming.l1).length;
        if (!accounts && !wallets) {
            setPopStatus("Nothing usable in that file. Check the format below.", true);
            return;
        }
        // Merge: imported entries win, field by field
        const merged = { accounts: { ...state.labels.accounts }, l1: { ...state.labels.l1 } };
        for (const [k, v] of Object.entries(incoming.accounts)) merged.accounts[k] = { ...merged.accounts[k], ...v };
        for (const [k, v] of Object.entries(incoming.l1)) merged.l1[k] = { ...merged.l1[k], ...v };
        ui.pasteOpen = false;
        saveLabels(merged);
        setPopStatus(`Imported ${accounts} accounts and ${wallets} wallets.`);
    }

    function exportLabels() {
        const blob = new Blob([JSON.stringify(state.labels, null, 2)], { type: "application/json" });
        const url = URL.createObjectURL(blob);
        const a = el("a", { href: url, download: `lighter-account-labels${SITE_SUFFIX}.json` });
        document.body.append(a);
        a.click();
        a.remove();
        setTimeout(() => URL.revokeObjectURL(url), 1_000);
    }

    function renderLabelsPanel() {
        if (!ui || ui.pop.style.display === "none") return;
        const pop = ui.pop;
        const accounts = Object.keys(state.labels.accounts).length;
        const wallets = Object.keys(state.labels.l1).length;
        const site = BACKEND.isMainnet ? "app.lighter.xyz" : "robinhoodchain.lighter.xyz";

        const fileInput = el("input", { type: "file", accept: ".json,application/json" });
        fileInput.style.display = "none";
        fileInput.addEventListener("change", async () => {
            const file = fileInput.files?.[0];
            if (file) importText(await file.text());
        });

        const textarea = el("textarea", { placeholder: "Paste labels JSON", spellcheck: "false" });
        const pasteBox = ui.pasteOpen
            ? el("div", { class: "pp-dt-pop-row" }, [textarea, el("button", { class: "pp-dt-cta", text: "Import", onclick: () => importText(textarea.value) })])
            : null;

        const idxInput = el("input", { placeholder: "Account index", inputmode: "numeric", size: "14" });
        const nameInput = el("input", { placeholder: "Name", size: "16" });
        const saveOne = () => {
            const idx = Number(idxInput.value.trim());
            if (!Number.isSafeInteger(idx) || idx < 0 || !idxInput.value.trim()) {
                setPopStatus("Account index must be a whole number.", true);
                return;
            }
            const name = cleanText(nameInput.value, 64);
            const accountsCopy = { ...state.labels.accounts };
            const rec = { ...accountsCopy[idx] };
            if (name) rec.name = name;
            else delete rec.name;
            if (Object.keys(rec).length) accountsCopy[idx] = rec;
            else delete accountsCopy[idx];
            saveLabels({ ...state.labels, accounts: accountsCopy });
            setPopStatus(name ? `#${idx} is now "${name}".` : `Removed the name of #${idx}.`);
        };
        nameInput.addEventListener("keydown", (e) => { if (e.key === "Enter") saveOne(); });

        const clearBtn = el("button", {
            class: `pp-dt-btn${ui.confirmClear ? " pp-dt-danger" : ""}`,
            text: ui.confirmClear ? "Click again to clear" : "Clear",
            onclick: () => {
                if (!ui.confirmClear) {
                    ui.confirmClear = true;
                    renderLabelsPanel();
                    return;
                }
                ui.confirmClear = false;
                saveLabels({ accounts: {}, l1: {} });
                setPopStatus("Labels cleared.");
            },
        });

        const children = [
            el("div", { class: "pp-dt-pop-row" }, [
                el("span", { class: "pp-dt-title", text: "Account labels" }),
                el("span", { class: "pp-dt-meta", text: `${accounts} accounts · ${wallets} wallets` }),
            ]),
            el("p", { text: `Names for account indexes on ${site}. Kept only in this browser's extension storage; never uploaded.` }),
            el("div", { class: "pp-dt-pop-row" }, [
                el("button", { class: "pp-dt-cta", text: "Import file", onclick: () => fileInput.click() }),
                el("button", { class: "pp-dt-btn", "aria-pressed": String(!!ui.pasteOpen), text: "Paste JSON", onclick: () => { ui.pasteOpen = !ui.pasteOpen; renderLabelsPanel(); } }),
                el("button", { class: "pp-dt-btn", text: "Export", onclick: exportLabels }),
                clearBtn,
                fileInput,
            ]),
            pasteBox,
            ui.popStatus ? el("p", { class: `pp-dt-status${ui.popStatus.err ? " pp-err" : ""}`, text: ui.popStatus.text }) : null,
            el("div", { class: "pp-dt-pop-row" }, [idxInput, nameInput, el("button", { class: "pp-dt-btn", text: "Save", onclick: saveOne })]),
            el("p", { text: "Imports merge into what's stored. Accounts that share a name, or a wallet, stack as one owner." }),
            el("details", {}, [
                el("summary", { text: "File format" }),
                el("p", { text: 'A JSON object with "accounts" (account index → wallet, type, master account, name) and "l1" (wallet → name and socials). Every field is optional; other fields are ignored. type: 0 main, 1 sub-account, 2 public pool, 3+ system.' }),
                el("p", { text: "Replace each <…> with real values: indexes as numbers (keys in quotes), wallets as 0x addresses." }),
                el("pre", { text: FORMAT_EXAMPLE }),
            ]),
        ];
        pop.replaceChildren(...children.filter(Boolean));
        if (ui.pasteOpen) textarea.focus();
    }

    // ---------- Loop ----------
    function tick() {
        const onTrade = /\/trade(\/|$)/.test(location.pathname);
        const views = onTrade ? findViewButtons() : null; // only on the Price tab
        if (!views) {
            setShowing(false);
            return;
        }
        injectStyles();
        const depthView = views.depth.classList.contains("text-ink");
        ensureProSwitch(views.depth, depthView);
        setShowing(depthView && state.pro);
        if (!state.open || !mountPanel(views.row)) return;

        loadMarkets();
        const market = currentMarket();
        if (market?.id !== state.market?.id) {
            state.market = market;
            state.snap = null;
            state.model = null;
            state.error = null;
            state.slots = new Map();
            state.focus = null;
            state.nextPollAt = 0;
            hideTip();
            refresh();
        }
        ensureSocket();
        const visible = document.visibilityState === "visible";
        if (state.market && visible && !state.fetching && Date.now() >= state.nextPollAt) pollOrders();
        if (visible) lookupNext();
        if (!state.model) renderChart(); // "Loading…" until the first snapshot
    }

    setInterval(tick, TICK_MS);
})();
