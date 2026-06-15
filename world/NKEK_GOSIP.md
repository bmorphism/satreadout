# Maintain & dial +380, all the way up and down — from nkek.gov.ua

One line: **a NKEK-gated, gosip-signalled, glojure-bound capability to maintain
(REGISTER) and dial (INVITE) +380 numbers — compliance at the top, SIP in the
middle, RTP at the wire — with joker as the static gate and glojure as the only
seam that can actually run it.**

## The stack, both directions

```
            DOWN (dial / originate)                 UP (response / terminate)
 ┌────────────────────────────────────┐  ┌──────────────────────────────────────┐
 │ NKEK  nkek.gov.ua                   │  │ CDR ⇄ NKEK register reconcile  [−1]   │
 │  Національний план нумерації №758   │  │  (was the dialed № allocated &        │
 │  Реєстр первинного розподілу        │  │   non-blocked? compliance audit)      │
 │  (open data, monthly *.xls)         │  └──────────────────▲───────────────────┘
 │  RF-blocklist №426 дод.1            │                     │
 │  → world/nkek380.bb gate     [0]    │  ┌──────────────────┴───────────────────┐
 └───────────────┬────────────────────┘  │ glojure seam: gosip Go values → CLJ   │
                 │ trit-0 numbers only    │  (only glojure can; joker only lints)  │
 ┌───────────────▼────────────────────┐  └──────────────────▲───────────────────┘
 │ gosip sip.URI{Scheme,User:+380…,    │                     │
 │   Host:operator}                    │  ┌──────────────────┴───────────────────┐
 │ dialog.NewRequest("REGISTER") =     │  │ gosip ParseMsg ← 200 OK / 4xx         │
 │   MAINTAIN (re-reg before expiry)   │  └──────────────────▲───────────────────┘
 │ dialog.NewDialog(INVITE) = DIAL [+1]│                     │
 └───────────────┬────────────────────┘  ┌──────────────────┴───────────────────┐
                 └───────────────────────▶│ gosip rtp/ sdp/ — RTP wire (ULAW/DTMF)│
                                          └───────────────────────────────────────┘
```

## Verified pieces (not asserted)
- **gosip API** (cloned jart/gosip): `sip.URI{Scheme,User,Pass,Host,Port,Param,Header}`
  — the +380 number is `URI.User`. `sip.Addr{Uri,Display,…}`. `ParseMsg([]byte)`
  (`sip/msg_parse.go:52`). `dialog.NewRequest(tp, method, to, from)` builds
  REGISTER/INVITE. `fone/main.go` = working dialer: INVITE w/ `sdp{Audio:ULAW,DTMF}`
  → `dialog.NewDialog` → `rtp.NewSession`.
- **NKEK** (verified nkek.gov.ua / data.gov.ua): regulator owns the National
  Numbering Plan (наказ №758/2023), the primary-allocation register (open data,
  dataset `fd61bc13…`, monthly), 5-yr дозвіл permits, MNP (ППН), and the
  RF-allocated-codes blocklist (Положення №426/2023 дод.1) ordered blocked.
- **`world/nkek380.bb`** (runnable, tested): the top gate. Validates E.164
  `+380·NDC(2)·SN(7)`, classifies mobile/geographic, refuses unallocated and
  RF-blocklist numbers. 4/8 sample numbers clear; `+380652000000` (Simferopol,
  allocated-but-RF-blocked) correctly REFUSED — the regulatorily load-bearing case.

## The joker/glojure seam (the coloring nuance)
- **glojure** = Go interop + AOT (Clojure→Go→native): the ONLY seam that can bind
  gosip's structs and dial. Colors the **runtime value** — avalanche `sm64`
  fingerprint of the +380 identity (e.g. `+380501234567` → hue 270).
- **joker** = lint/format only, no eval/interop: the static gate on the dial
  logic + the NKEK validator. Colors the **syntax** — structured, AST-depth
  (siblings share a hue; can't tell `+380…` from `host`). [hue-kernels-are-duals]
- Caller-ID nuance: the persistent avalanche color = attribution; a per-call
  scoped color `H(call-ctx ‖ №)` = RLN/unlinkable. Only glojure (holding the
  value) can choose; joker (seeing a string) cannot.

## GF(3) per call (measured legs)
`NKEK-validate (0 witness) · gosip INVITE/dialog (+1 generate) · CDR⇄register
reconcile (−1 coplay) ≡ 0`. A refused number never reaches +1 — it dies at 0.

## Honestly NOT done (the real −1 of this design)
- **No live dialing.** That needs a registered UA operator + a NKEK дозвіл +
  SIP-trunk credentials — out of scope (regulatory + abuse boundary). This is a
  compliance-enforcing *capability*, not a dialer pointed at strangers.
- **glojure interop is illustrative** — the gorj bridges are down
  (`dispatch apply failed`); the real seam needs `jfhamlin/glojure` driven
  directly (exact import syntax unverified here).
- **The blocklist sample is not authoritative** — three Crimea prefixes stand in
  for the full NKEK №426 дод.1 *.xls; production loads the real register.
- **The 2-digit-NDC model is a simplification** — real UA codes are
  variable-length; production parses against the full plan (наказ №758).
