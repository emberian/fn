# Public exposure: the limits of a reader port that faces strangers (2026-09-26)

Lane `public-exposure`, branch `lane/public-exposure` from dev `0d211647`.
Registry: NNT-031, PRF-161, SCN-091, PKT-404 to PKT-406. Mandate §4
(capacity versus work) and §11 ("loopback-only unless a separate exposure
design is selected"): this section 1 is that design, and section 6 is the
packet ember decides from. Nothing here exposes a node: every run below is
loopback on hbox scratch, and the live node was not touched.

## 1. The design

### 1.1 What changes when the port faces strangers

On loopback every client is the operator's. Off loopback the node answers
anyone who can route a SYN to it, so every resource a connection can hold
needs a bound that the operator chose and ACL2 decides, and every refusal
needs an answer RFC 3977 names. The shape that already existed: a total
connection bound (`fn-own-open`'s `max-conns`, fn.toml's fixed default of
32) that refused past the bound by **closing the socket with no reply**, a
worker thread per accepted socket, a 1 s receive poll with no idle close,
per-read work bounded by the host read size, the profile's command-line and
article bounds (books/wire.lisp), and AUTHINFO/STARTTLS with `[auth]
required`/`protected_only`.

What this lane adds is one ACL2 book, `books/public-exposure.lisp`, whose
functions the host calls at accept, before and after every served step, on
every receive timeout and at close; and seven limit rows plus one policy row
of the live configuration, set with `fn operator CONFIG policy set SLOT
VALUE` and applied to the running owner like every configuration record
(books/native-admin.lisp, the `:set-exposure` and `:set-policy` plans). The
host counts nothing: it passes the kernel's `(family . address)`, the
connection id, the octets the served step already rendered and the owner's
monotonic clock; it sends the line, waits, or closes as the answer says.

### 1.2 Threat and cost model

| Threat | The limit | Decided in | The client sees | The operator sees |
| --- | --- | --- | --- | --- |
| Connection flood, one source | `exposure-per-address` (public default 8) | `fn-exp-open` (ACL2, at accept) | `400 too many connections from this address; try again later`, then close (RFC 3977 §5.1.1 note 2) | `health`: `refused-address`, `exposure pressure held` |
| Connection flood, many sources | `exposure-connections`, never above the run's max (default 32) | `fn-exp-open` | `400 too many connections; try again later`, then close | `refused-busy`; pressure held at 90 % of the total |
| Slowloris, silent | `exposure-first-seconds` (60) before the first command, `exposure-idle-seconds` (600) after | `fn-exp-idle` on every 1 s receive timeout | close with no response (RFC 3977 §3.1) | `idle-closed` |
| Slowloris, slow send | progress is an answered command or 512 octets consumed since the last progress, so one octet a second never resets the timer | `fn-exp-observe` (progress) and `fn-exp-idle` | close with no response | `idle-closed` |
| Oversized command line | RFC 3977 §3.1's 512 octets (books/nntp-syntax.lisp, unchanged) | the served wire machine | its 5xx line (measured below) | nothing new |
| Oversized article | the profile's article bound (books/owner-served-bound.lisp, unchanged) | the served wire machine | `441` naming the size, then close | the service log's 441 line |
| Anonymous reader hammering ARTICLE/OVER | `exposure-steps-per-second` (64): served steps one address starts per 1000 ms; one step is one fn-owner-chunk over at most one host read (D27: work, not data) | `fn-exp-charge` before every step | nothing: the connection's next read waits for the next quantum (TCP backpressure); nothing is refused or cut | `deferred` |
| Anonymous access at all | policy `anonymous`: `none` (default off loopback) or `open` | `fn-exp-pinned-acfg`, pinned at accept, then books/nntp-auth.lisp's gate | `480 authentication required` for every reader and posting command (RFC 4643 §2.2); CAPABILITIES, HELP, DATE, MODE, QUIT, AUTHINFO, STARTTLS still answer | `anonymous=` in `health` |
| Credential guessing | `exposure-auth-failures` (10 per address per minute) | `fn-exp-observe` counts the `481` lines the step rendered | `400 too many authentication failures; closing connection`; the next connection from the address in that minute gets `400 ... from this address` at the greeting | `auth-closed`, `refused-auth` |
| A principal posting too fast | `exposure-posts-per-minute` (60) | `fn-exp-observe` counts submissions, `fn-exp-charge` waits | nothing: the principal's connections wait for the next minute | `deferred` |
| TLS renegotiation / handshake cost | OpenSSL 3.5's server context: TLS 1.3 has no renegotiation, and OpenSSL 3 refuses client-initiated renegotiation on TLS 1.2 unless enabled (it is not); the handshake itself is inside the 10 s send/receive timeouts of the host | host trust (host/native/tls.lisp), not a theorem | handshake failure closes that connection only | `owner TLS connection:` log line |
| A hostile peer on the transit port | a configured peer is resolved by source address and admitted by the same `fn-exp-open` (it counts against the total and its address); its offers are decided by `fn-peer-step` against its record (inbound groups, `inbound-max-octets`) | ACL2 (existing peering books) | `437`/`438`/`439` per offer | the service log |

The brief's "per-address command rate" and "per-connection work budget
per quantum" are one row here: a step is the unit of work (one fn-owner-chunk
over at most one host read of `+fnn-max-read+` octets, however many
pipelined commands it holds), and every connection's steps count against its
address, so no connection can exceed the budget its address has. A separate
per-connection row would only ever be tighter than that and was not needed
by any phase of the campaign.

Two limits are deliberately waits, not refusals: the step budget and the
post rate. A refusal would either cut a command in the middle (the step is
the host read, not a command) or invent a reply code RFC 3977 does not give
for "slow down"; waiting stops reading the socket, which TCP turns into
backpressure on the sender, and nothing the client sent is lost (D27:
"exhausting a work quantum yields or resumes, it never silently truncates").

### 1.3 What is decided where, and the host lines

- `fn-exp-open` (host/owner-host.lisp `fn-owner-exposure-open`, called by
  host/native/owner.lisp `fnn-owner-serve-client` at accept) replaces the
  host's choice between `fn-owner-open` and `fn-owner-open-peer`: it admits
  or refuses, and opens through `fn-ocfg-open`/`fn-ocfg-open-peer` with the
  pinned AUTHINFO configuration, in one ACL2 call under the owner mutex. A
  refused connection is sent ACL2's 400 line and closed.
- `fn-exp-charge` (`fn-owner-exposure-charge`, `fnn-owner-exposure-wait`)
  runs before every `fnn-owner-handle-chunk`.
- `fn-exp-observe` runs inside `fn-owner-chunk`, over the step's own effects
  and consumed count; a close decision is appended by
  `fnn-owner-handle-chunk` from `fn-owner-exposure-close`.
- `fn-exp-idle` (`fn-owner-exposure-idle`) runs on every 1 s receive
  timeout; `fn-exp-release` in the serve loop's unwind.
- `fn-exp-limits` reads the LIVE configuration at every call, so a `policy
  set` the owner published is in force for the next accept and step.
- `fn-exp-address-publicp` reads the listener the run binds
  (`fn-owner-exposure-install`, after recovery and before listen): a listener
  outside 127.0.0.0/8 and `::1` takes the public defaults for absent rows;
  loopback keeps every earlier behaviour.

### 1.4 Certificates: a real CA or self-signed and pinned

| | ACME (a public CA, e.g. Let's Encrypt) | Self-signed, pinned by peers and readers |
| --- | --- | --- |
| Needs | a DNS name for the node; port 80 reachable (HTTP-01) or DNS API access (DNS-01); a renewal job every 60 days | nothing public: `openssl req -x509 -newkey ...` once (tools/runbooks/hbox-node-deploy.sh already does this) |
| Readers | any newsreader verifies it out of the box | each reader must import the certificate or its fingerprint once; tin/slrn users must configure a CA file |
| Peers | verify by name | pin the certificate (the pull profile's CA path, specs/peering.md 1.2.8) |
| Operator steps | install an ACME client (certbot or lego) outside fn; point `[listener] tls_cert`/`tls_key` at the issued files; restart the owner on renewal (fn reads the pair at `run`; there is no live reload) | generate the pair; distribute `cert.pem` over an authenticated channel (the invitation flow is the natural carrier later) |
| Risk | CA and DNS are new trust roots; renewal failure takes readers down | a stolen or unpinned first contact is trusted on first use; rotation is manual |

### 1.5 The public IP or a reverse proxy

- **Direct public IPv4** (`[listener] host = "<public address>"`): per-address
  limits see the real client address; the node's own TLS terminates.
  Requires a firewall rule and the certificate choice above.
- **A reverse proxy** (e.g. HAProxy or nginx `stream` in front,
  TCP passthrough): the proxy can terminate TLS or pass it through, and can
  rate-limit at the edge; but fn does not speak the PROXY protocol, so
  **every client arrives from the proxy's address**: `exposure-per-address`
  and `exposure-auth-failures` collapse into one bucket for everyone, and a
  single abuser locks out all readers. With a proxy, set per-address to the
  total and rely on the proxy's per-source limits; or build PROXY-protocol
  v2 support (a small ACL2 parser of the header before the greeting) first.

## 2. What was proved (PRF-161)

The subjects are the functions the host calls (1.3). Book
`books/public-exposure.lisp`, rows `books/public-exposure-rows.lisp`, teeth
`tests/acl2/public-exposure-tests.lisp`.

- **fn-exp-open-admits-within-the-limits-in-force** (KEYSTONE): an open that
  returns an id happened only with the owner below the total and the address
  below its per-address limit in force, and leaves the address at most one
  higher and within the limit.
- **fn-exp-open-never-exceeds-a-limit-in-force**: no open carries an address
  past max(what it held, the limit in force): a limit lowered by
  reconfiguration closes nothing and admits nothing more from that address.
- **fn-exp-open-refusal-is-a-400-and-opens-nothing**, and
  **fn-exp-release-never-raises-a-count**.
- **fn-exp-charge-bounds-steps-per-quantum** (KEYSTONE): under a positive
  steps row a step proceeds only while its address has started fewer than
  the budget in this quantum, and leaves the count within it;
  **fn-exp-charge-waits-and-never-closes**: exhaustion is `(:defer MS)` with
  MS positive, never a close.
- **fn-exp-anonymous-none-gates-every-restricted-command** (KEYSTONE): under
  the `none` policy the pinned configuration requires authentication
  (**fn-exp-pinned-acfg-requires-authentication**, and it keeps the
  operator's credentials, protected-only bit and TLS availability), and for
  any session carrying it with no subject, every restricted command (POST
  among them: `fn-exp-post-is-restricted`) answers 480, submits nothing and
  leaves the session unchanged. It composes books/nntp-auth.lisp's keystone
  `fn-auth-gated-command-is-refused-and-not-performed`.
- **fn-exp-limits-never-drop-a-connection** (KEYSTONE): for any limits (the
  next call after a reconfiguration simply receives new ones), open, charge,
  observe and idle keep every registered connection; only release removes.
  **fn-exp-idle-closes-only-silence** and
  **fn-exp-observe-closes-only-on-a-failed-login** name the only two closes
  the book asks for: silence for the configured timer, and a step that
  itself answered 481 and reached the failed-login limit. So an
  authenticated session making progress is never closed by a limit or a
  reconfiguration.

Teeth (tests/acl2/public-exposure-tests.lisp): a reachable witness for each
keystone over a real owner (`fn-ocfg-open` runs; the greeting is the served
machine's), and one ground instance per hypothesis that keeps the others,
falsifies it and falsifies the conclusion (`must-fail` of the conclusion's
assertion). The anonymous keystone reuses tests/acl2/nntp-auth-teeth-tests.lisp's
fixtures: `*aut-s-req*` is exactly the session pinned for `*aut-required*`
under `none`, so its H1-H7 counter-values carry over, with the pinned
configuration checked on each.

The assurance chain: native accept (`fnn-owner-serve-client`) ->
`fn-owner-exposure-open` -> `fn-exp-open` (executed as is: every function is
guard t, `:logic` mode, run in the image) -> no refinement step (the
executed function is the subject) -> the maintained relation is the
exposure state's registered connections, established empty at
`fn-owner-exposure-install` and changed only by open (adds one) and release
(removes one) -> the keystones above -> the observed 400 lines and closes in
section 4.

What is NOT proved: that the pinned configuration becomes the session's
through `fn-ocfg-open` (fn-auth-open-session puts it there and
books/served.lisp states the pin for both roles; no composed theorem over
fn-ocfg-open is stated here); that the host loop makes exactly these calls
(source, and the native campaign); the count of the exposure state against
the owner's own connection list (the host registers and releases on the
same paths; not a theorem); anything about TLS.

## 3. Certification

Farm on hbox (`/tank/fn/toolchains/w28/acl2-literal-4g`, cache
`/tank/fn/certcache`, 2 jobs, 300 s), affected roots only:

| Run | Roots | Result | Manifest |
| --- | --- | --- | --- |
| run-20260926T074003Z-eca2 | `--affected-by books/public-exposure-rows.lisp --affected-by books/public-exposure.lisp` (15 roots; 17 certified, 186 installed) | passed, no book over 10 s | `planning/evidence/manifests/certify-20260926T074028Z-855253.json` |
| run-20260926T075300Z-3f74 | `--affected-by books/public-exposure.lisp` after the operator-slot reservation (2 certified) | passed, no book over 10 s | `planning/evidence/manifests/certify-20260926T075324Z-901451.json` |

Book times at two jobs (run 1 for the rows and native-admin, run 2 for the
book and tests): books/public-exposure 9.09 s, tests 1.72 s,
books/public-exposure-rows 0.72 s, books/native-admin 9.33 s (the two new
`policy set` arms), books/native-operator 7.79 s. The two near 10 s are not
over; they are the next cost work if either moves (D26). Discovery ran in a
live `tools/proof_repl.py` session on hbox; the first draft of
`fn-exp-limits-never-drop-a-connection` took 64 s and was split into three
equalities (1.7 s together) before any certification.

## 4. Native campaign on hbox (SCN-091)

`tools/hbox_native.sh --label r4 . tests.test_native_public_exposure` at the
worktree (dev `0d211647` + this lane's edits), developer image, MemoryMax
24G, scratch `/tank/fn/scratch/public-exposure/native-r4`: **OK, 1 test,
52.8 s**. One owner on 127.0.0.1 (`max_connections` 32); rows before start:
connections 32, per-address 8, steps 20/s, first 5 s, idle 8 s,
auth-failures 10, anonymous none (short timers so the campaign runs in a
minute; the public defaults are section 1.2's). Strangers are other loopback
source addresses. The full report is
`planning/evidence/public-exposure-2026-09-26-report.json`.

| Phase | Outcome |
| --- | --- |
| 500 connections from 127.0.0.2 at once | 8 admitted, 492 `400 ... from this address`; all 500 answered; the 8 closed with no reply by the 5 s first-command timer |
| per-address set LIVE to 1, first-command LIVE to 30 s; 10 each from 127.0.1.1-50 | 30 admitted (31 socket slots, one held by the legit reader), 261 `400 ... from this address`, 209 `400 too many connections`; a fresh legit connection during it: `400 too many connections`; after the flood's connections timed out (29.9 s): admitted |
| 4 silent + 4 one-octet-a-second connections | all closed with no reply at 5.0 s |
| command lines of 600, 4096 and 65536 octets | `501 syntax error` each (the served machine's RFC 3977 §3.1 bound); owner up |
| anonymous under `none` | greeting 201; GROUP, ARTICLE, LIST, POST `480 authentication required`; CAPABILITIES 101 |
| `anonymous open` set LIVE; 120 `STAT 1` | GROUP `211`; 120 answered in 5.46 s = 22.0/s against a budget of 20/s (the first quantum's burst); 6 waits counted |
| AUTHINFO guessing, ~100/s from 127.0.0.7 | 10 `481`, then `400 too many authentication failures; closing connection` and EOF; the next connection from the address: `400 too many authentication failures from this address; try again later` |
| `operator CONFIG health` | `exposure pressure held connections=2 total=31 per-address=8 recent=1017`; `admitted=54 refused-busy=210 refused-address=753 refused-auth=1 deferred=6 idle-closed=46 auth-closed=1`; exit 22 is the developer profile's `unqualified-profile`, not exposure |

The authenticated reader on 127.0.0.1, DATE every 100 ms through the whole
campaign, **0 failures**:

| Phase | n | p50 ms | p95 ms | max ms |
| --- | --- | --- | --- | --- |
| baseline | 30 | 0.3 | 0.4 | 0.4 |
| flood, one address | 51 | 0.3 | 0.5 | 3.9 |
| flood, 50 addresses | 301 | 0.3 | 0.4 | 3.7 |
| slowloris | 50 | 0.3 | 0.4 | 0.6 |
| anonymous | 56 | 0.3 | 0.4 | 0.5 |
| credential guessing | 2 | 0.3 | 0.2 | 0.3 |
| after | 20 | 0.4 | 0.4 | 0.7 |

(The credential phase is two samples long because the guesser is closed
after ten attempts.)

SHA-256 (hbox, `native-r4/SHA256SUMS`):

```
2e189ffe2d5fcb468e5e5d36c8adf7c3dbde7d7c7954275171f3fd05473d92a2  tree/build/fn-host-developer
7dceb13f00087334f8e102f7e8b75e3c763b04910f783b0cd4c6cdf411195a35  tree/build/fn-host-developer.core
bedf021458af9cf2a889f5b807759c5e5d96be0bda8b35f948af70f816b676b4  logs/native-build-developer.log
6509ea853d7306eb22b7520e6477be7aa35bbb7d6775d8149be97a31cac3e1de  logs/test-tests.test_native_public_exposure.log
```

Three findings on the way, each classified:

1. **Implementation (host, pre-existing): a refused connection got no
   reply.** `fn-owner-open` returned NIL past `max-conns` and the host
   closed the socket silently, against RFC 3977 §5.1.2 ("MUST present a 400
   or 502 greeting"). Now the refusal is ACL2's 400 line.
2. **Environment/host (pre-existing): the listen backlog of 16.** In run r3
   69 of the 500 one-address flood connections read nothing for 10 s: the
   kernel held them half-open for its SYN-ACK retries while the accept
   thread drained (image r1, two runs). `+fnn-owner-listen-backlog+` is 128
   now; from image r3 on, all 500 were answered. The queue still decides nothing.
3. **Implementation (pre-existing): a full reader port locked the operator
   out.** The live `policy set` stages through a private logical owner
   connection (host/native/admin.lisp `fnn-owner-live-reconfigure-locked`);
   with every one of the 32 slots held by the flood it was refused
   `:no-such-connection` (run r3: `refused operator policy`). Sockets now
   hold at most one fewer than the bound (`fn-exp-socket-cap`), so the
   operator can always change the limits that answer a flood; r4 lowered
   and raised them live mid-flood.

Three harness defects were fixed on image r1 and are not behaviour: the
image path variable (the module skipped); the fresh legit connection tried
while 127.0.0.1 was at its own per-address limit of 1 (the legit reader
holds one); and the guessing loop reading the closing 400 as the reply to
the next USER.

**Regression modules on image r4** (`--no-build`): tests.test_native_owner
17 of 18 after updating two structure checks this lane moved (the serve
loop's cleanup now has the exposure release; the raw chunk-loop stubs name
the exposure calls, and a chunk now takes two clock readings, the charge's
and the step's: a waiting connection must see the clock move). The one
failure, `test_developer_selectors_gate_arm_the_owner_and_stop_synchronously`,
is `undefined variable *FNN-SIGHUP-COUNT*` while its raw script evaluates
`fnn-main`: host/native/io.lisp, which this lane does not touch; harness,
pre-existing at `0d211647`, left to its owner. tests.test_native_tls_transport
OK (2); tests.test_native_auth and tests.test_native_protected_peering
skipped without their environment (not evidence either way).

## 5. Not done, and why

- **A read-only anonymous level and a public-groups level.** The brief asks
  for `nothing / read public groups / read all`. `none` is built and proved.
  `open` is the existing behaviour (anonymous reads everything and posts as
  `[posting]` says), so it is not "read all": on a node with posting enabled
  an anonymous `open` session can POST. A read-only level needs
  books/nntp-auth.lisp to decouple `fn-auth-postingp`'s unauthenticated arm
  from `requiredp` (one field of the AUTHINFO configuration), and a
  public-groups level needs the gate to read the command's group; both
  change a book with 281 dependents (every served, owner and native book
  above it), which is a coordinated recertification at a convergence, not a
  lane run. PKT-405 below carries the choice. Classification: unexercised
  capability.
- **The post rate on the native campaign.** `exposure-posts-per-minute` is
  proved (the charge waits) and witnessed in the test book (a principal's
  second submission in a minute waits 54.5 s); the native campaign does not
  wait a minute to show it.
- **PROXY protocol.** Behind a reverse proxy every client is one address
  (1.5); fn does not parse PROXY v2. Unexercised capability, PKT-406.
- **The exposure state against the owner's connection list** is maintained
  by the host calling open and release on the same paths; no theorem ties
  `fn-exp-conns` to `fn-own-conns`.
- **No deployment.** The live node was not touched and nothing listens off
  loopback; ember's packet decides whether and how.

## 6. The packet for ember

Nothing here blocks the wave: every default below is implemented on the
branch, and a node on loopback behaves exactly as before.

### PKT-404: how does a node face the internet, and with which certificate?

**The trace.** Section 4: a loopback owner under the flood campaign stayed
within every limit and answered every stranger with a named 400, while the
authenticated reader was answered in every phase. The live node listens on
loopback behind ssh and has a self-signed certificate
(tools/runbooks/hbox-node-deploy.sh).

**Constraints already selected.** Mandate §11: loopback-only unless a
separate exposure design is selected (this record is that design); §2: no
public exposure without ember. `[auth] protected_only` off loopback
(fn.toml.example).

**Proposed default (a).** Direct public IPv4 on hbox's own address with
`[auth] required = true`, `protected_only = true`, a **self-signed
certificate pinned by readers and peers**, the public defaults of section 1.2
(absent rows), and `anonymous none`. Operator steps: open TCP 119 (or 563 for
implicit TLS, which fn does not serve: STARTTLS on 119 is what exists) in the
firewall; `fn operator CONFIG` with `[listener] host = "<public ipv4>"`;
restart; hand each reader the certificate's SHA-256 fingerprint.

**Alternatives.** (b) the same with an ACME certificate: needs a DNS name,
port 80 or DNS-01, and a renewal job outside fn that restarts the owner (no
live reload of the pair); cost: two new trust roots (CA, DNS) and a renewal
failure mode, gain: readers need no fingerprint. (c) A reverse proxy in
front: per-address and failed-login limits collapse to one bucket for every
client (fn does not speak PROXY v2, PKT-406); only sensible with the proxy
doing per-source limiting and fn's per-address set to the total.

**Affected:** no format, no proof; `[listener] host` and the firewall.
**What continues without it:** everything; nothing listens publicly.

### PKT-405: what may an anonymous reader do?

**The trace.** `none` answers 480 to GROUP, ARTICLE, LIST and POST (section
4); `open` answers GROUP 211 and serves a STAT loop at the step budget.

**Proposed default (a).** `none` off loopback (implemented: the default of
an absent row on a public listener), `open` only by explicit `policy set
anonymous open` on a node whose `[posting]` is disabled or whose operator
accepts anonymous posting.

**Alternatives.** (b) build `read` (anonymous reads everything, never
posts): a one-field change to the AUTHINFO configuration in
books/nntp-auth.lisp (the posting allowance's unauthenticated arm), 281
dependent books recertified at a convergence; (c) build `public-groups`
(anonymous reads only groups the operator marks public): (b) plus a group
check in the gate for GROUP/LISTGROUP/ARTICLE/HEAD/BODY/STAT/OVER/HDR and a
filtered LIST and NEWNEWS; larger. **Recommendation:** (b) at the next
convergence if ember wants an anonymous public reading room; (c) only if
some groups must stay private on a node that also has public ones.

### PKT-406: the public defaults and PROXY protocol

**Proposed default (a):** the numbers in section 1.2's public column
(per-address 8, 64 steps a second, first command 60 s, idle 600 s, 10
failed logins a minute, 60 posts a minute), applied only to absent rows on a
listener off loopback, and no PROXY protocol. **Alternative (b):** build
PROXY v2 (an ACL2 parser of the fixed header before the greeting, bounded at
its 232-octet maximum, accepted only from a configured proxy address) so
that a proxy keeps per-address accounting. Cost: one small book and a host
read before the greeting; gain: option (c) of PKT-404 becomes sound.
