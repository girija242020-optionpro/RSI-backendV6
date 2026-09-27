import express from "express";
import cors from "cors";
import http from "http";
import WebSocket, { WebSocketServer } from "ws";
import { authenticator } from "otplib";
import webpush from "web-push";

const env = process.env;
const PORT = Number(env.PORT || 10000);
const HOST = env.HOST || "0.0.0.0";
const CORS_ORIGIN = env.CORS_ORIGIN || "*";
const CLIENT_ID = (env.DHAN_CLIENT_ID || "").trim();
const PIN = (env.DHAN_PIN || "").trim();
const TOTP_SECRET = (env.DHAN_TOTP_SECRET || "").replace(/\s+/g, "").toUpperCase();
const STATIC_TOKEN = (env.DHAN_ACCESS_TOKEN || "").trim();
const VAPID_PUBLIC_KEY = (env.VAPID_PUBLIC_KEY || "").trim();
const VAPID_PRIVATE_KEY = (env.VAPID_PRIVATE_KEY || "").trim();
const VAPID_SUBJECT = (env.VAPID_SUBJECT || "mailto:alerts@example.com").trim();
const ENABLE_LIVE_FEED = String(env.ENABLE_LIVE_FEED ?? "true").toLowerCase() !== "false";
const ENABLE_20_DEPTH = String(env.ENABLE_20_DEPTH ?? "true").toLowerCase() !== "false";
const AUTO_SUBSCRIBE_INDICES = String(env.AUTO_SUBSCRIBE_INDICES ?? "true").toLowerCase() !== "false";
const MAX_CLIENTS = Math.max(1, Number(env.MAX_CLIENTS || 20));
const MAX_SUBSCRIPTIONS = Math.max(100, Number(env.MAX_SUBSCRIPTIONS || 5000));
const MAX_TICKS = Math.max(100, Number(env.MAX_TICKS_PER_INSTRUMENT || 3000));
const MAX_CANDLES = Math.max(100, Number(env.MAX_CANDLES_PER_INSTRUMENT || 2000));
const TICK_BUFFER_SIZE = Math.max(1000, Number(env.TICK_BUFFER_SIZE || 10000));
const TICK_STALE_MS = Math.max(1000, Number(env.TICK_STALE_MS || 15000));
const STALE_AFTER_MS = Math.max(1000, Number(env.STALE_AFTER_MS || 5000));
const HISTORY_REFRESH_MS = Math.max(3000, Number(env.LIVE_HISTORY_REFRESH_MS || 10000));
const CANDLE_MS = Math.max(10000, Number(env.CANDLE_TIMEFRAME_MS || 60000));
const CHAIN_REFRESH_MS = Math.max(3000, Number(env.OPTION_CHAIN_REFRESH_MS || 3200));
const DEPTH_MAX = Math.min(50, Math.max(1, Number(env.DEPTH_MAX_INSTRUMENTS || 50)));

const INDEXES = {
  NIFTY: { securityId: String(env.NIFTY_SECURITY_ID || "13"), segment: "IDX_I", step: 50 },
  BANKNIFTY: { securityId: String(env.BANKNIFTY_SECURITY_ID || "25"), segment: "IDX_I", step: 100 },
  FINNIFTY: { securityId: String(env.FINNIFTY_SECURITY_ID || "27"), segment: "IDX_I", step: 50 },
  MIDCPNIFTY: { securityId: String(env.MIDCPNIFTY_SECURITY_ID || "442"), segment: "IDX_I", step: 25 },
  SENSEX: { securityId: String(env.SENSEX_SECURITY_ID || "51"), segment: "IDX_I", step: 100 }
};
let selectedIndex = String(env.DEFAULT_INDEX || "NIFTY").toUpperCase();
if (!INDEXES[selectedIndex]) selectedIndex = "NIFTY";

if (VAPID_PUBLIC_KEY && VAPID_PRIVATE_KEY) {
  webpush.setVapidDetails(VAPID_SUBJECT, VAPID_PUBLIC_KEY, VAPID_PRIVATE_KEY);
}

const app = express();
app.use(cors({ origin: CORS_ORIGIN === "*" ? true : CORS_ORIGIN }));
app.use(express.json({ limit: "2mb" }));
app.use((req, res, next) => { res.setHeader("Cache-Control", "no-store"); next(); });

const startedAt = Date.now();
const clients = new Set();
const pushSubs = new Map();
const ticks = new Map();
const tickHist = new Map();
const candleStore = new Map();
const candleStore30s = new Map();
const depthStore = new Map();
const instruments = new Map();
const optionStore = new Map();
const subscriptions = new Map();
let chain = { updatedAt: null, expiry: null, spot: null, rows: [], analytics: null };
let expiryList = [];
let expiryFetchedAt = 0;
let chainError = null;
let accessToken = STATIC_TOKEN;
let tokenExpiry = 0;
let authStatus = STATIC_TOKEN ? "STATIC_TOKEN" : "WAITING_FOR_AUTH";
let authError = null;
let dhanWs = null;
let depthWs = null;
let dhanReconnectTimer = null;
let depthReconnectTimer = null;
let chainTimer = null;
let expiryTimer = null;
let staleTimer = null;
let instrumentTimer = null;
let historyTimer = null;
let chainBusy = false;
let lastFeedMessage = 0;
let lastDepthMessage = 0;
let packets = 0;
let depthPackets = 0;
let reconnects = 0;
let droppedClients = 0;
let marketStatus = "UNKNOWN";
let lastDhanPacket = null;

function n(v, d = null) { const x = Number(v); return Number.isFinite(x) ? x : d; }
function key(seg, sec) { return `${seg}:${sec}`; }
function clone(x) { return JSON.parse(JSON.stringify(x)); }
function sleep(ms) { return new Promise(r => setTimeout(r, ms)); }
function log(...a) { console.log(new Date().toISOString(), ...a); }
function segmentName(code) { return ({ 0: "IDX_I", 1: "NSE_EQ", 2: "NSE_FNO", 3: "NSE_CURRENCY", 4: "BSE_EQ", 5: "MCX_COMM", 7: "BSE_CURRENCY", 8: "BSE_FNO" })[Number(code)] || String(code); }
function now() { return Date.now(); }
function istParts(ts = now()) { const s = new Intl.DateTimeFormat("en-IN", { timeZone: "Asia/Kolkata", hour12: false, year: "numeric", month: "2-digit", day: "2-digit", hour: "2-digit", minute: "2-digit", second: "2-digit", weekday: "short" }).formatToParts(ts); const o = Object.fromEntries(s.map(x => [x.type, x.value])); return o; }
function marketSessionState() {
  const p = istParts(); const wd = ["Sat", "Sun"].includes(p.weekday); const mins = Number(p.hour) * 60 + Number(p.minute);
  if (wd) return "CLOSED";
  if (mins < 9 * 60 + 15) return "PREOPEN";
  if (mins <= 15 * 60 + 30) return "OPEN";
  return "CLOSED";
}
function updateMarketStatus() {
  const session = marketSessionState();
  const age = lastFeedMessage ? now() - lastFeedMessage : Infinity;
  marketStatus = session === "OPEN" && age <= TICK_STALE_MS ? "LIVE" : session === "OPEN" ? "OPEN_NO_FRESH_TICKS" : session;
}
function broadcast(msg) { const s = JSON.stringify(msg); for (const ws of clients) if (ws.readyState === WebSocket.OPEN) ws.send(s); }
function send(ws, msg) { if (ws.readyState === WebSocket.OPEN) ws.send(JSON.stringify(msg)); }
function publicState() {
  updateMarketStatus();
  const ix = INDEXES[selectedIndex]; const tk = ticks.get(key(ix.segment, ix.securityId));
  return { version: "6.0.0", index: selectedIndex, securityId: ix.securityId, exchangeSegment: ix.segment, marketStatus, chainError, indiaTime: new Date().toLocaleString("en-IN", { timeZone: "Asia/Kolkata", hour12: false }), dhanConnected: !!dhanWs && dhanWs.readyState === WebSocket.OPEN, depthConnected: !!depthWs && depthWs.readyState === WebSocket.OPEN, feedLastMessage: lastFeedMessage || null, feedAgeMs: lastFeedMessage ? now() - lastFeedMessage : null, feedStale: !lastFeedMessage || now() - lastFeedMessage > TICK_STALE_MS, depthAgeMs: lastDepthMessage ? now() - lastDepthMessage : null, spot: tk?.ltp ?? chain.spot ?? null, lastTick: tk || null, chainUpdatedAt: chain.updatedAt, expiry: chain.expiry, subscriptions: subscriptions.size, packets, depthPackets, reconnects, clients: clients.size, pushDevices: pushSubs.size, marketSession: marketSessionState(), authStatus, authError, serverUptimeMs: now() - startedAt, decoder: "Dhan v2 little-endian binary", packet: lastDhanPacket };
}

async function getToken() {
  if (STATIC_TOKEN) { authStatus = "STATIC_TOKEN"; return STATIC_TOKEN; }
  if (!CLIENT_ID || !PIN || !TOTP_SECRET) { authStatus = "MISSING_CREDENTIALS"; throw new Error("Set DHAN_ACCESS_TOKEN or DHAN_CLIENT_ID + DHAN_PIN + DHAN_TOTP_SECRET"); }
  if (accessToken && now() < tokenExpiry - 60000) return accessToken;
  const totp = authenticator.generate(TOTP_SECRET);
  const url = `https://auth.dhan.co/app/generateAccessToken?dhanClientId=${encodeURIComponent(CLIENT_ID)}&pin=${encodeURIComponent(PIN)}&totp=${encodeURIComponent(totp)}`;
  const r = await fetch(url, { method: "POST", headers: { Accept: "application/json", "Content-Type": "application/json" } });
  const txt = await r.text(); let j; try { j = JSON.parse(txt); } catch { j = {}; }
  if (!r.ok || !j.accessToken) { authStatus = `AUTH_FAILED_${r.status}`; authError = j.errorMessage || j.message || txt.slice(0, 250); throw new Error(authError); }
  accessToken = j.accessToken; tokenExpiry = j.expiryTime ? new Date(j.expiryTime).getTime() : now() + 23 * 3600000; authStatus = "AUTHENTICATED"; authError = null; return accessToken;
}
async function dhanPost(path, body) {
  const token = await getToken();
  const headers = { "Content-Type": "application/json", Accept: "application/json", "access-token": token };
  if (CLIENT_ID) headers["client-id"] = CLIENT_ID;
  const r = await fetch(`https://api.dhan.co/v2${path}`, { method: "POST", headers, body: JSON.stringify(body) });
  const txt = await r.text(); let j; try { j = JSON.parse(txt); } catch { j = { raw: txt }; }
  if (!r.ok) throw new Error(`Dhan ${r.status}: ${txt.slice(0, 500)}`);
  return j;
}

function csvLine(line) { const out = []; let cur = "", q = false; for (let i = 0; i < line.length; i++) { const c = line[i]; if (c === '"') { if (q && line[i + 1] === '"') { cur += '"'; i++; } else q = !q; } else if (c === "," && !q) { out.push(cur); cur = ""; } else cur += c; } out.push(cur); return out; }
async function loadInstruments() {
  const r = await fetch("https://images.dhan.co/api-data/api-scrip-master-detailed.csv"); if (!r.ok) throw new Error(`Instrument master HTTP ${r.status}`);
  const text = await r.text(); const lines = text.split(/\r?\n/).filter(Boolean); const headers = csvLine(lines[0]).map(x => x.trim()); const ix = name => headers.indexOf(name);
  const I = { exch: ix("EXCH_ID"), seg: ix("SEGMENT"), id: ix("SECURITY_ID"), inst: ix("INSTRUMENT"), und: ix("UNDERLYING_SYMBOL"), undId: ix("UNDERLYING_SECURITY_ID"), sym: ix("SYMBOL_NAME"), trading: ix("SEM_TRADING_SYMBOL"), custom: ix("DISPLAY_NAME"), expiry: ix("SM_EXPIRY_DATE"), strike: ix("STRIKE_PRICE"), opt: ix("OPTION_TYPE"), lot: ix("LOT_SIZE"), tick: ix("TICK_SIZE") };
  instruments.clear();
  for (let i = 1; i < lines.length; i++) {
    const c = csvLine(lines[i]); if (c.length < 10) continue; const ex = c[I.exch], sg = c[I.seg];
    const es = ex === "NSE" && sg === "I" ? "IDX_I" : ex === "NSE" && sg === "D" ? "NSE_FNO" : ex === "NSE" && sg === "E" ? "NSE_EQ" : ex === "BSE" && sg === "I" ? "BSE_IDX" : ex === "BSE" && sg === "D" ? "BSE_FNO" : ex === "BSE" && sg === "E" ? "BSE_EQ" : ex === "MCX" && sg === "M" ? "MCX_COMM" : null;
    if (!es) continue; const id = c[I.id]; if (!id) continue;
    instruments.set(key(es, id), { securityId: String(id), exchangeSegment: es, exchange: ex, segment: sg, instrument: c[I.inst] || null, underlying: c[I.und] || null, underlyingSecurityId: c[I.undId] || null, symbol: c[I.sym] || null, tradingSymbol: c[I.trading] || null, displayName: c[I.custom] || null, expiry: c[I.expiry] || null, strike: n(c[I.strike], null), optionType: c[I.opt] || null, lotSize: n(c[I.lot], 1), tickSize: n(c[I.tick], null) });
  }
  log(`Instrument master loaded: ${instruments.size}`);
}

function indexInfo() { return INDEXES[selectedIndex]; }
function pushTick(t) {
  const k = key(t.exchangeSegment, t.securityId);
  ticks.set(k, t); let h = tickHist.get(k); if (!h) { h = []; tickHist.set(k, h); } h.push(t); if (h.length > Math.min(MAX_TICKS, TICK_BUFFER_SIZE)) h.splice(0, h.length - Math.min(MAX_TICKS, TICK_BUFFER_SIZE));
  if (t.exchangeSegment === "IDX_I" && String(t.securityId) === String(indexInfo().securityId)) lastFeedMessage = now();
}
function updateCandleStore(store, t, bucketMs) {
  const k = key(t.exchangeSegment, t.securityId); let arr = store.get(k); if (!arr) { arr = []; store.set(k, arr); }
  const ts = Math.floor((t.timestamp || now()) / bucketMs) * bucketMs; let c = arr[arr.length - 1];
  if (!c || c.time !== ts) { c = { time: ts, open: t.ltp, high: t.ltp, low: t.ltp, close: t.ltp, volume: Number(t.volumeDelta || t.ltq || 0), tickCount: 1 }; arr.push(c); }
  else { c.high = Math.max(c.high, t.ltp); c.low = Math.min(c.low, t.ltp); c.close = t.ltp; c.volume += Number(t.volumeDelta || t.ltq || 0); c.tickCount++; }
  if (arr.length > MAX_CANDLES) arr.splice(0, arr.length - MAX_CANDLES); return c;
}
function updateCandle(t) {
  updateCandleStore(candleStore, t, CANDLE_MS);
  updateCandleStore(candleStore30s, t, 30000);
}
function normalizeFeedPacket(buf) {
  if (!(buf instanceof Uint8Array) || buf.length < 8) return null;
  const dv = new DataView(buf.buffer, buf.byteOffset, buf.byteLength); const code = dv.getUint8(0); const messageLength = dv.getUint16(1, true); const seg = dv.getUint8(3); const sec = dv.getUint32(4, true); const segment = segmentName(seg);
  const f = o => dv.getFloat32(o, true); const i = o => dv.getInt32(o, true); const u = o => dv.getUint32(o, true); const i16 = o => dv.getInt16(o, true); const u16 = o => dv.getUint16(o, true);
  const base = { code, messageLength, exchangeSegmentCode: seg, exchangeSegment: segment, securityId: String(sec) };
  if (code === 1 && buf.length >= 12) return { ...base, type: "index", ltp: f(8), timestamp: now() };
  if (code === 2 && buf.length >= 16) return { ...base, type: "ticker", ltp: f(8), ltt: u(12), timestamp: u(12) * 1000 };
  if (code === 4 && buf.length >= 51) return { ...base, type: "quote", ltp: f(8), ltq: u16(12), ltt: u(14), timestamp: u(14) * 1000, avgPrice: f(18), volume: u(22), sellQty: u(26), buyQty: u(30), open: f(34), close: f(38), high: f(42), low: f(46) };
  if (code === 5 && buf.length >= 12) return { ...base, type: "oi", oi: u(8), timestamp: now() };
  if (code === 6 && buf.length >= 16) return { ...base, type: "prev", prevClose: f(8), prevOI: u(12), timestamp: now() };
  if (code === 7) return { ...base, type: "marketStatus", statusCode: buf.length >= 10 ? u16(8) : null, timestamp: now() };
  if (code === 8 && buf.length >= 163) {
    const depth = []; for (let z = 0; z < 5; z++) { const o = 63 + z * 20; depth.push({ bidQty: i(o), askQty: i(o + 4), bidOrders: i16(o + 8), askOrders: i16(o + 10), bid: f(o + 12), ask: f(o + 16) }); }
    return { ...base, type: "full", ltp: f(8), ltq: u16(12), ltt: u(14), timestamp: u(14) * 1000, avgPrice: f(18), volume: u(22), sellQty: u(26), buyQty: u(30), oi: u(34), oiHigh: u(38), oiLow: u(42), open: f(46), close: f(50), high: f(54), low: f(58), depth5: depth };
  }
  return { ...base, type: "unknown", rawBytes: buf.length, timestamp: now() };
}
function handleFeedBuffer(data) {
  const buf = data instanceof ArrayBuffer ? new Uint8Array(data) : data instanceof Uint8Array ? data : new Uint8Array(data);
  const p = normalizeFeedPacket(buf); if (!p) return;
  packets++; lastDhanPacket = { code: p.code, type: p.type, segment: p.exchangeSegment, securityId: p.securityId, bytes: buf.length, receivedAt: now() };
  const old = ticks.get(key(p.exchangeSegment, p.securityId)) || {};
  if (["ticker", "quote", "full", "index"].includes(p.type) && Number.isFinite(p.ltp)) {
    const t = { ...old, securityId: p.securityId, exchangeSegment: p.exchangeSegment, ltp: p.ltp, timestamp: p.timestamp || now(), receivedAt: now(), ltt: p.ltt || null, ltq: p.ltq || 0, volume: p.volume ?? old.volume ?? 0, volumeDelta: p.volume != null && old.volume != null ? Math.max(0, p.volume - old.volume) : (p.ltq || 0), avgPrice: p.avgPrice ?? old.avgPrice ?? null, sellQty: p.sellQty ?? old.sellQty ?? null, buyQty: p.buyQty ?? old.buyQty ?? null, open: p.open ?? old.open ?? null, high: p.high ?? old.high ?? null, low: p.low ?? old.low ?? null, prevClose: p.close ?? old.prevClose ?? null, oi: p.oi ?? old.oi ?? null, oiHigh: p.oiHigh ?? old.oiHigh ?? null, oiLow: p.oiLow ?? old.oiLow ?? null, depth5: p.depth5 ?? old.depth5 ?? null };
    pushTick(t); updateCandle(t);
    if (p.type === "full") broadcast({ type: "tick", data: t }); else if (p.exchangeSegment === indexInfo().segment && p.securityId === indexInfo().securityId) broadcast({ type: "tick", data: t });
  } else if (p.type === "oi") {
    const t = { ...old, securityId: p.securityId, exchangeSegment: p.exchangeSegment, oi: p.oi, receivedAt: now(), timestamp: now() }; ticks.set(key(p.exchangeSegment, p.securityId), t); broadcast({ type: "oi", data: t });
  }
}

function sendSubs(ws, list, code) {
  if (!ws || ws.readyState !== WebSocket.OPEN || !list.length) return;
  const unique = [...new Map(list.map(x => [key(x.ExchangeSegment, x.SecurityId), x])).values()];
  for (let i = 0; i < unique.length; i += 100) { const a = unique.slice(i, i + 100); try { ws.send(JSON.stringify({ RequestCode: code, InstrumentCount: a.length, InstrumentList: a })); } catch {} }
}
function subscribeFeed(list) {
  for (const x of list) { if (subscriptions.size >= MAX_SUBSCRIPTIONS && !subscriptions.has(key(x.ExchangeSegment, x.SecurityId))) break; subscriptions.set(key(x.ExchangeSegment, x.SecurityId), x); }
  sendSubs(dhanWs, list, 21);
}
function connectFeed() {
  if (!ENABLE_LIVE_FEED) return;
  clearTimeout(dhanReconnectTimer);
  getToken().then(token => {
    const url = `wss://api-feed.dhan.co?version=2&token=${encodeURIComponent(token)}&clientId=${encodeURIComponent(CLIENT_ID)}&authType=2`;
    dhanWs = new WebSocket(url); dhanWs.binaryType = "arraybuffer";
    dhanWs.on("open", () => { authStatus = STATIC_TOKEN ? "STATIC_TOKEN" : "AUTHENTICATED"; log("Dhan market feed connected"); const base = Object.values(INDEXES).map(x => ({ ExchangeSegment: x.segment, SecurityId: x.securityId })); sendSubs(dhanWs, base, 15); if (chain.rows.length) subscribeFeed(chain.rows.slice(0, 1000).map(x => ({ ExchangeSegment: "NSE_FNO", SecurityId: x.securityId }))); broadcast({ type: "state", state: publicState() }); });
    dhanWs.on("message", data => handleFeedBuffer(data));
    dhanWs.on("close", () => { log("Dhan feed closed"); dhanWs = null; reconnects++; clearTimeout(dhanReconnectTimer); dhanReconnectTimer = setTimeout(connectFeed, Math.min(30000, 1000 + reconnects * 1000)); broadcast({ type: "state", state: publicState() }); });
    dhanWs.on("error", e => { authError = e.message; log("Dhan feed error", e.message); });
  }).catch(e => { authError = e.message; authStatus = "AUTH_ERROR"; clearTimeout(dhanReconnectTimer); dhanReconnectTimer = setTimeout(connectFeed, 10000); });
}
function parseDepthBuffer(data) {
  const buf = data instanceof ArrayBuffer ? new Uint8Array(data) : data instanceof Uint8Array ? data : new Uint8Array(data); if (buf.length < 12) return;
  const dv = new DataView(buf.buffer, buf.byteOffset, buf.byteLength); let off = 0;
  // 20-depth packet: 12-byte header, then one 16-byte bid block and one 16-byte ask block per instrument.
  while (off + 12 <= buf.length) {
    const len = dv.getInt16(off, true); const code = dv.getUint8(off + 2); const seg = dv.getUint8(off + 3); const sec = dv.getInt32(off + 4, true); const packetLen = Math.max(12, len || buf.length - off); const bodyEnd = Math.min(buf.length, off + packetLen);
    if (code !== 41 && code !== 51) { off += packetLen; continue; }
    const side = code === 41 ? "bid" : "ask"; const levels = [];
    for (let p = off + 12; p + 16 <= bodyEnd; p += 16) levels.push({ price: dv.getFloat64(p, true), quantity: dv.getUint32(p + 8, true), orders: dv.getUint32(p + 12, true) });
    const k = key(segmentName(seg), String(sec)); const old = depthStore.get(k) || { securityId: String(sec), exchangeSegment: segmentName(seg), bid: [], ask: [], updatedAt: null };
    old[side] = levels.slice(0, 20); old.updatedAt = now(); depthStore.set(k, old); lastDepthMessage = now(); depthPackets++; broadcast({ type: "depth", data: old }); off += packetLen;
  }
}
function connectDepth() {
  if (!ENABLE_20_DEPTH) return;
  getToken().then(token => {
    const url = `wss://depth-api-feed.dhan.co/twentydepth?token=${encodeURIComponent(token)}&clientId=${encodeURIComponent(CLIENT_ID)}&authType=2`;
    depthWs = new WebSocket(url); depthWs.binaryType = "arraybuffer";
    depthWs.on("open", () => { log("Dhan 20-depth connected"); syncDepth(); });
    depthWs.on("message", data => parseDepthBuffer(data));
    depthWs.on("close", () => { depthWs = null; clearTimeout(depthReconnectTimer); depthReconnectTimer = setTimeout(connectDepth, 5000); });
    depthWs.on("error", e => log("Depth error", e.message));
  }).catch(e => { log("Depth auth", e.message); clearTimeout(depthReconnectTimer); depthReconnectTimer = setTimeout(connectDepth, 10000); });
}
function syncDepth() {
  if (!depthWs || depthWs.readyState !== WebSocket.OPEN) return;
  const rows = chain.rows.filter(x => x.type === "CE" || x.type === "PE").sort((a, b) => Math.abs(a.strike - (chain.analytics?.atm ?? chain.spot ?? 0)) - Math.abs(b.strike - (chain.analytics?.atm ?? chain.spot ?? 0))).slice(0, DEPTH_MAX);
  if (!rows.length) return;
  const list = rows.map(x => ({ ExchangeSegment: "NSE_FNO", SecurityId: x.securityId }));
  try { depthWs.send(JSON.stringify({ RequestCode: 23, InstrumentCount: list.length, InstrumentList: list })); } catch {}
}

function bsT(expiry) { return Math.max((new Date(`${expiry}T15:30:00+05:30`).getTime() - now()) / 31557600000, 1 / 31557600000); }
function pdf(x) { return Math.exp(-x * x / 2) / Math.sqrt(2 * Math.PI); }
function cdf(x) { const a1=.254829592,a2=-.284496736,a3=1.421413741,a4=-1.453152027,a5=1.061405429,p=.3275911; const s=x<0?-1:1,t=1/(1+p*Math.abs(x)); const y=1-(((((a5*t+a4)*t)+a3)*t+a2)*t+a1)*t*Math.exp(-x*x); return .5*(1+s*y); }
function derivedGreeks(S,K,iv,expiry,type) {
  const sigma = Math.max(Number(iv) / 100, 0.0001), T = bsT(expiry); if (!(S > 0 && K > 0)) return {};
  const d1 = (Math.log(S / K) + (0.06 + sigma*sigma/2)*T) / (sigma*Math.sqrt(T)); const d2=d1-sigma*Math.sqrt(T); const g=pdf(d1)/(S*sigma*Math.sqrt(T)); const v=S*pdf(d1)*Math.sqrt(T)/100; const delta=type === "CE" ? cdf(d1) : cdf(d1)-1; const vanna=-pdf(d1)*d2/sigma/100; const vomma=v*d1*d2/sigma; return { delta, gamma:g, vega:v, vanna, vomma };
}
function buildAnalytics(rows, spot) {
  const ce=rows.filter(x=>x.type==="CE"), pe=rows.filter(x=>x.type==="PE"); const sum=(a,k)=>a.reduce((s,x)=>s+(Number(x[k])||0),0); const callOI=sum(ce,"oi"),putOI=sum(pe,"oi"); const strikes=[...new Set(rows.map(x=>x.strike))].sort((a,b)=>a-b); let painStrike=null,painVal=Infinity;
  for(const k of strikes){let pain=0;for(const x of ce)pain+=Math.max(0,k-x.strike)*x.oi;for(const x of pe)pain+=Math.max(0,x.strike-k)*x.oi;if(pain<painVal){painVal=pain;painStrike=k;}}
  const atm=rows.reduce((a,b)=>!a||Math.abs(b.strike-spot)<Math.abs(a.strike-spot)?b:a,null)?.strike??null; const callWall=ce.reduce((a,b)=>!a||b.oi>a.oi?b:a,null)?.strike??null; const putWall=pe.reduce((a,b)=>!a||b.oi>a.oi?b:a,null)?.strike??null;
  return { atm, pcr: callOI ? putOI/callOI : null, callOI, putOI, callChangeOI:sum(ce,"changeOI"), putChangeOI:sum(pe,"changeOI"), callVolume:sum(ce,"volume"), putVolume:sum(pe,"volume"), callChangeVolume:sum(ce,"changeVolume"), putChangeVolume:sum(pe,"changeVolume"), callOIWall:callWall, putOIWall:putWall, maxPain:painStrike, maxPainValue:painVal===Infinity?null:painVal, atmIV: rows.filter(x=>x.strike===atm).reduce((s,x)=>s+(x.iv||0),0)/(rows.filter(x=>x.strike===atm).length||1) };
}
function normalizeOption(strike, type, leg, expiry, spot) {
  if (!leg) return null; const meta=instruments.get(key("NSE_FNO",leg.security_id)); const oi=n(leg.oi,0); const prevOI=n(leg.previous_oi,0); const iv=n(leg.implied_volatility,0); const g=derivedGreeks(spot,strike,iv,expiry,type);
  return { strike, type, securityId:String(leg.security_id), tradingSymbol:meta?.tradingSymbol||null, ltp:n(leg.last_price,0), oi, previousOI:prevOI, changeOI:oi-prevOI, volume:n(leg.volume,0), previousVolume:n(leg.previous_volume,0), changeVolume:n(leg.volume,0)-n(leg.previous_volume,0), iv, bid:n(leg.top_bid_price,0), ask:n(leg.top_ask_price,0), bidQty:n(leg.top_bid_quantity,0), askQty:n(leg.top_ask_quantity,0), averagePrice:n(leg.average_price,0), greeks:leg.greeks||{}, hiddenGreeks:g, lotSize:meta?.lotSize||1 };
}
async function refreshExpiryList(force=false) {
  if (!force && expiryFetchedAt && now() - expiryFetchedAt < 10 * 60 * 1000) return expiryList;
  const ix=indexInfo();
  const exp=await dhanPost("/optionchain/expirylist",{UnderlyingScrip:Number(ix.securityId),UnderlyingSeg:ix.segment});
  expiryList=Array.isArray(exp.data)?exp.data:[]; expiryFetchedAt=now();
  if(!chain.expiry || !expiryList.includes(chain.expiry)) chain.expiry=expiryList[0]||null;
  return expiryList;
}
function marketOpenForChain() { return ["OPEN","LIVE"].includes(marketSessionState()); }
async function refreshOptionChain(force=false) {
  if (chainBusy || (!force && !marketOpenForChain())) return; chainBusy=true;
  try {
    await refreshExpiryList(false);
    if(!chain.expiry) return;
    const ix=indexInfo(); const r=await dhanPost("/optionchain",{UnderlyingScrip:Number(ix.securityId),UnderlyingSeg:ix.segment,Expiry:chain.expiry}); const spot=n(r?.data?.last_price) || n(ticks.get(key(ix.segment,ix.securityId))?.ltp) || chain.spot; if(spot) chain.spot=spot;
    const raw=[]; for(const [ks,v] of Object.entries(r?.data?.oc||{})){const strike=Number(ks);const ce=normalizeOption(strike,"CE",v.ce,chain.expiry,chain.spot);const pe=normalizeOption(strike,"PE",v.pe,chain.expiry,chain.spot);if(ce){raw.push(ce);optionStore.set(key("NSE_FNO",ce.securityId),ce);}if(pe){raw.push(pe);optionStore.set(key("NSE_FNO",pe.securityId),pe);}}
    const strikes=[...new Set(raw.map(x=>x.strike))].sort((a,b)=>a-b); const atmStrike=strikes.reduce((best,k)=>best==null||Math.abs(k-chain.spot)<Math.abs(best-chain.spot)?k:best,null);
    const idx=strikes.indexOf(atmStrike); const allowed=new Set(strikes.slice(Math.max(0,idx-10),idx+11)); const rows=raw.filter(x=>allowed.has(x.strike));
    chain.rows=rows; chain.analytics=buildAnalytics(rows,chain.spot); chain.updatedAt=now(); chainError=null;
    const subs=rows.slice().sort((a,b)=>Math.abs(a.strike-chain.analytics.atm)-Math.abs(b.strike-chain.analytics.atm)); subscribeFeed(subs.map(x=>({ExchangeSegment:"NSE_FNO",SecurityId:x.securityId}))); syncDepth();
    broadcast({type:"optionChain",data:{...clone(chain),rows:rows.slice().sort((a,b)=>a.strike-b.strike)}});
  } catch(e) { chainError=e.message; log("Option chain",e.message); } finally { chainBusy=false; }
}
async function bootstrapHistory() {
  try {
    const ix=indexInfo(); const d=new Date(); const yyyy=d.getFullYear(),mm=String(d.getMonth()+1).padStart(2,"0"),dd=String(d.getDate()).padStart(2,"0"); const from=`${yyyy}-${mm}-${dd} 09:15:00`, to=`${yyyy}-${mm}-${dd} 15:35:00`;
    const j=await dhanPost("/charts/intraday",{securityId:ix.securityId,exchangeSegment:ix.segment,instrument:"INDEX",interval:"1",oi:false,fromDate:from,toDate:to});
    const ts=j.timestamp||[]; const arr=[]; for(let i=0;i<ts.length;i++) arr.push({time:Number(ts[i])*1000,open:n(j.open?.[i]),high:n(j.high?.[i]),low:n(j.low?.[i]),close:n(j.close?.[i]),volume:n(j.volume?.[i],0),tickCount:0}); candleStore.set(key(ix.segment,ix.securityId),arr.slice(-MAX_CANDLES));
    broadcast({type:"history",data:arr.slice(-MAX_CANDLES)});
  } catch(e) { log("History bootstrap",e.message); }
}

function rowsLive() { return chain.rows.map(x=>{const t=ticks.get(key("NSE_FNO",x.securityId));return t?{...x,ltp:t.ltp,volume:t.volume??x.volume,oi:t.oi??x.oi,bid:t.depth5?.[0]?.bid??x.bid,ask:t.depth5?.[0]?.ask??x.ask}:x;}); }
function serializeCandles(tf=1) {
  const arr=candleStore.get(key(indexInfo().segment,indexInfo().securityId))||[]; if(tf===1)return arr;
  const ms=tf*60000,map=new Map();for(const c of arr){const t=Math.floor(c.time/ms)*ms;let x=map.get(t);if(!x){x={time:t,open:c.open,high:c.high,low:c.low,close:c.close,volume:c.volume,tickCount:c.tickCount||0};map.set(t,x);}else{x.high=Math.max(x.high,c.high);x.low=Math.min(x.low,c.low);x.close=c.close;x.volume+=c.volume;x.tickCount+=(c.tickCount||0);}}return [...map.values()];
}

app.get("/",(req,res)=>res.type("html").send(`<!doctype html><html><head><meta name="viewport" content="width=device-width,initial-scale=1"><title>Dhan Gateway v6</title><style>body{margin:0;background:#07101d;color:#e7edf7;font:16px system-ui;padding:24px}main{max-width:760px;margin:auto;background:#0e1a2b;padding:24px;border-radius:20px}b{color:#5ee69a}.bad{color:#ff647c}.muted{color:#8fa0b8}code{word-break:break-all}</style></head><body><main><h1>Dhan Universal Market Gateway v6.1</h1><p><b id="m">CHECKING…</b></p><p>Backend is data-only. Strategy logic belongs in the PWA.</p><pre id="j" class="muted">loading</pre></main><script>async function f(){try{let j=await fetch('/api/health').then(r=>r.json());m.textContent=j.marketStatus+' · Dhan '+(j.dhanConnected?'CONNECTED':'DISCONNECTED');m.className=j.marketStatus==='LIVE'?'':'bad';document.getElementById('j').textContent=JSON.stringify(j,null,2)}catch(e){m.textContent='ERROR'}}f();setInterval(f,2000)</script></body></html>`));
app.get("/health",(req,res)=>res.type("text").send("OK\nDhan Universal Market Gateway v6.1\n"));
app.get("/api/health",(req,res)=>res.json({ok:true,...publicState()}));
app.get("/api/status",(req,res)=>res.json(publicState()));
app.get("/api/state",(req,res)=>res.json({ok:true,...publicState(),chain:{updatedAt:chain.updatedAt,expiry:chain.expiry,spot:chain.spot,analytics:chain.analytics}}));
app.get("/api/config",(req,res)=>res.json({ok:true,version:"6.0.0",indexes:INDEXES,vapidPublicKey:VAPID_PUBLIC_KEY,features:["tick","quote","full","oi","volume","ohlc","5-depth","20-depth","option-chain","change-oi","greeks","derived-hidden-greeks","gex-proxy","pcr","max-pain","intraday-history","websocket","web-push","instrument-master"]}));
app.get("/api/push/public-key",(req,res)=>res.json({ok:true,publicKey:VAPID_PUBLIC_KEY}));
app.get("/api/ticks",(req,res)=>res.json({ok:true,data:[...ticks.values()]}));
app.get("/api/tick-history",(req,res)=>{const k=key(req.query.segment||indexInfo().segment,String(req.query.securityId||indexInfo().securityId));res.json({ok:true,data:tickHist.get(k)||[]});});
app.get("/api/candles",(req,res)=>{const tf=String(req.query.timeframe||"1"); if(tf==="30s") return res.json({ok:true,timeframe:"30s",data:candleStore30s.get(key(indexInfo().segment,indexInfo().securityId))||[]}); res.json({ok:true,timeframe:tf,data:serializeCandles(Number(tf.replace("m",""))||1)});});
app.get("/api/history",(req,res)=>res.json({ok:true,data:candleStore.get(key(indexInfo().segment,indexInfo().securityId))||[]}));
app.get("/api/chart",(req,res)=>res.json({ok:true,spot:ticks.get(key(indexInfo().segment,indexInfo().securityId))||null,candles:serializeCandles(Number(req.query.timeframe||1))}));
app.get("/api/depth",(req,res)=>{const seg=req.query.segment||"NSE_FNO",sec=String(req.query.securityId||"");res.json({ok:true,data:depthStore.get(key(seg,sec))||null});});
app.get("/api/option-chain",(req,res)=>res.json({ok:true,...clone(chain),error:chainError,marketSession:marketSessionState(),rows:rowsLive()}));
app.get("/api/analytics",(req,res)=>res.json({ok:true,spot:chain.spot,analytics:chain.analytics}));
app.get("/api/expiries",(req,res)=>res.json({ok:true,data:expiryList,selected:chain.expiry}));
app.get("/api/instruments",(req,res)=>{const q=String(req.query.search||"").toUpperCase();const lim=Math.min(1000,Math.max(1,Number(req.query.limit||100)));const data=[...instruments.values()].filter(x=>!q||JSON.stringify(x).toUpperCase().includes(q)).slice(0,lim);res.json({ok:true,count:data.length,data});});
app.post("/api/market-quote",async(req,res)=>{try{const body=req.body||{};const j=await dhanPost("/marketfeed/quote",body);res.json({ok:true,data:j});}catch(e){res.status(502).json({ok:false,error:e.message});}});
app.post("/api/ltp",async(req,res)=>{try{const j=await dhanPost("/marketfeed/ltp",req.body||{});res.json({ok:true,data:j});}catch(e){res.status(502).json({ok:false,error:e.message});}});
app.post("/api/ohlc",async(req,res)=>{try{const j=await dhanPost("/marketfeed/ohlc",req.body||{});res.json({ok:true,data:j});}catch(e){res.status(502).json({ok:false,error:e.message});}});
app.post("/api/index",async(req,res)=>{const x=String(req.body?.index||"NIFTY").toUpperCase();if(!INDEXES[x])return res.status(400).json({ok:false,error:"Unknown index"});selectedIndex=x;chain={updatedAt:null,expiry:null,spot:null,rows:[],analytics:null};expiryFetchedAt=0;await bootstrapHistory();await refreshOptionChain(true);res.json({ok:true,state:publicState()});broadcast({type:"state",state:publicState()});});
app.post("/api/expiry",async(req,res)=>{const e=String(req.body?.expiry||"");await refreshExpiryList(true);if(!expiryList.includes(e))return res.status(400).json({ok:false,error:"Expiry not found"});chain.expiry=e;await refreshOptionChain(true);res.json({ok:true,selected:e});});
app.post("/api/subscribe",(req,res)=>{const list=Array.isArray(req.body?.instruments)?req.body.instruments:[];subscribeFeed(list.map(x=>({ExchangeSegment:String(x.ExchangeSegment||x.exchangeSegment),SecurityId:String(x.SecurityId||x.securityId)})).filter(x=>x.ExchangeSegment&&x.SecurityId));res.json({ok:true,count:subscriptions.size});});
app.post("/api/push/subscribe",(req,res)=>{const s=req.body;if(!s?.endpoint)return res.status(400).json({ok:false,error:"endpoint required"});pushSubs.set(s.endpoint,s);res.json({ok:true,devices:pushSubs.size});});
app.post("/api/push/test",async(req,res)=>{if(!VAPID_PUBLIC_KEY||!VAPID_PRIVATE_KEY)return res.status(503).json({ok:false,error:"VAPID not configured"});let sent=0;for(const [k,s] of pushSubs){try{await webpush.sendNotification(s,JSON.stringify({title:"Dhan Terminal Test",body:"Push channel is working."}));sent++;}catch(e){if([404,410].includes(e.statusCode))pushSubs.delete(k);}}res.json({ok:true,sent,devices:pushSubs.size});});

const server=http.createServer(app);const wss=new WebSocketServer({server,path:"/ws"});
wss.on("connection",ws=>{if(clients.size>=MAX_CLIENTS){droppedClients++;ws.close(1013,"MAX_CLIENTS");return;}clients.add(ws);send(ws,{type:"hello",version:"6.0.0",vapidPublicKey:VAPID_PUBLIC_KEY});send(ws,{type:"state",state:publicState()});if(chain.rows.length)send(ws,{type:"optionChain",data:{...clone(chain),rows:rowsLive()}});const k=key(indexInfo().segment,indexInfo().securityId);if(ticks.has(k))send(ws,{type:"tick",data:ticks.get(k)});ws.on("message",raw=>{try{const m=JSON.parse(raw.toString());if(m.type==="ping")send(ws,{type:"pong",time:now()});if(m.type==="subscribe"&&INDEXES[String(m.index||"").toUpperCase()]){selectedIndex=String(m.index).toUpperCase();send(ws,{type:"state",state:publicState()});}}catch{}});ws.on("close",()=>clients.delete(ws));});

async function boot(){
  try{await loadInstruments();}catch(e){log("Instrument master",e.message);}
  try{await bootstrapHistory();}catch{}
  if(AUTO_SUBSCRIBE_INDICES) subscribeFeed(Object.values(INDEXES).map(x=>({ExchangeSegment:x.segment,SecurityId:x.securityId})));
  if(ENABLE_LIVE_FEED) connectFeed(); if(ENABLE_20_DEPTH) connectDepth();
  if (marketOpenForChain()) { try{await refreshOptionChain(true);}catch(e){log("Chain startup",e.message);} }
  chainTimer=setInterval(()=>refreshOptionChain(false).catch(()=>{}),Math.max(CHAIN_REFRESH_MS,3500));
  expiryTimer=setInterval(()=>refreshExpiryList(true).catch(()=>{}),10*60*1000);
  staleTimer=setInterval(()=>{updateMarketStatus();broadcast({type:"state",state:publicState()});},1000);
  historyTimer=setInterval(()=>{const k=key(indexInfo().segment,indexInfo().securityId);broadcast({type:"candles",data:candleStore.get(k)||[]});},HISTORY_REFRESH_MS);
  instrumentTimer=setInterval(()=>loadInstruments().catch(()=>{}),6*3600000);
}
server.listen(PORT,HOST,()=>{log(`Dhan Universal Market Gateway v6.1 listening on ${HOST}:${PORT}`);boot();});
process.on("SIGTERM",()=>{clearInterval(chainTimer);clearInterval(expiryTimer);clearInterval(staleTimer);clearInterval(historyTimer);clearInterval(instrumentTimer);try{dhanWs?.close();depthWs?.close();}catch{}server.close(()=>process.exit(0));});
