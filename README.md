# Dhan Universal Market Gateway v6.1

Backend-only market-data gateway for a mobile PWA. It keeps broker credentials server-side and exposes normalized WebSocket/REST data to the PWA.

## Dhan v2 data used
- Tick-by-tick LTP/timestamp
- Quote: LTP, LTQ, ATP, volume, buy/sell quantity, OHLC
- OI
- Full packet: quote + OI + 5-level depth
- 20-level full market depth through Dhan's separate depth websocket
- Option-chain snapshots including OI, change in OI where supplied, volume, bid/ask and Dhan Greeks
- Derived Black-Scholes vanna/vomma and GEX proxy when IV is available
- Intraday 1-minute bootstrap candles
- Dhan instrument master mapping

Dhan v2 currently documents the live feed binary header as byte 0 response code, bytes 1-2 message length, byte 3 exchange segment, and bytes 4-7 security ID. Multi-byte fields are little-endian. The 20-level depth feed has a 12-byte header and 20 x 16-byte depth rows per bid/ask side.

## Render
Root Directory: `.`
Build Command: `npm install`
Start Command: `npm start`

## Important
Never put `DHAN_ACCESS_TOKEN`, PIN/TOTP secret, or `VAPID_PRIVATE_KEY` into the frontend.

## Main endpoints
- `/api/health`
- `/api/status`
- `/api/state`
- `/api/config`
- `/api/ticks`
- `/api/candles`
- `/api/history`
- `/api/depth`
- `/api/option-chain`
- `/api/analytics`
- `/api/instruments`
- `/api/expiries`
- `/api/chart`
- `/api/push/public-key`
- `/ws`

## Push
The included VAPID pair is in `.env.example`. Replace the subject email with your email. Keep the private key only on Render.
