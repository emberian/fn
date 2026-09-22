# The hbox node from the dabebb84 image — 2026-09-22

The first native fn node anyone can post to, and the first full v0 matrix on
an image built from `dev` rather than the 915 image of 2026-09-20. Every
number below is a tool's; the invocations are in the run directory and the
probe record beside this file.

## The image

`dabebb845adc3e3d6e8dc93c620782f54e6b106a`, frozen under
`/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb84.../` on hbox after
one closure run at that origin certified all 165 books
(`manifests/certify-20260922T200011Z-3216833.json`, toolchain
`/tank/fn/toolchains/w28/acl2-literal-4g`); the build-source manifest's
sha256 is `56f7e3d013e457633ea0b0fa86bf06ed6fa69179ed4408f2385aeb340c57ba12`
(`native-freeze-dabebb84-2026-09-22.md`). The build needed OpenSSL 3.5 for
ML-DSA-65; the lane built 3.5.8 from the release tarball into
`/tank/fn/toolchains/openssl-3.5.8`, inside the TLS and signature trust
boundary, for ember to approve. A running image reads `FN_OPENSSL_PREFIX`.

## The deploy

`tools/runbooks/hbox-node-deploy.sh /tank/fn/gates/freeze-dev-28fb4bd0
dabebb84 192.168.50.39` on hbox: image installed under
`/tank/fn/node/fn-dabebb84`, store initialised, path identity
`hbox.ember.software`, groups `fn.agents`, `fn.humans`, `fn.announce`,
principals `ember`, `yue`, `tulip` with posting (passwords only in
`/tank/fn/node/credentials.txt`, mode 0600), a self-signed TLS pair, and the
user unit `fn-node.service`. The first `run` answered
`usage operator run UNSUPPORTED-PROFILE`: `fn-native-config-operator-availablep`
(books/native-config.lisp) refuses a `[log] path` and any posting agent but
the default. Both keys were removed from the configuration and the runbook
(a0ffa4c9); the node then listened on 192.168.50.39:1119 with STARTTLS and
`[auth] required = true, protected_only = true`. The old Codex-era
Python-host unit `fn.service` was disabled. A lane (T6b) makes the operator
honour the two keys.

## The probe from a Mac on the LAN

`tools/node_probe.py 192.168.50.39 1119 --cafile <the node's cert> --group
fn.agents` as `ember` (record: `node-hbox-dabebb84-2026-09-22/probe.json`):
every assertion held on both connections. STARTTLS offered; AUTHINFO before
the layer answered 483; 382 and a TLS 1.3 handshake verified against the
pinned certificate; STARTTLS withdrawn and AUTHINFO offered after it; 281;
POST offered only after the login; GROUP 211; a post accepted 240; the
article read back byte-identical on a fresh connection. The greeting is
201 until the login, which the probe first read as a violation and which is
the greeting keystone's behaviour (0a8b592b corrected the probe). Exit 0.

## The full v0 matrix on the image

`tools/v0_matrix.py dev --host hbox --backend native-operator` over two
loopback stores provisioned from the same image
(`v0-runs/20260922T204325.546307Z-0a8b592-0bffc80c1571/`): 206 rows, 126 accepted, 34 refused, 3 uncertain, 38 not
exercised, 5 not built; 2 disagreements. The uncertain rows are
`V0-OUT-UNCERTAIN-A/B`, the developer image's one-shot fault, which agree
with their expectation, and `V0-CFG-LIVE`, which does not. The not-exercised
rows are the phases the native slice does not drive (the crash campaign, BP,
statements, INN, scale, slrn) and the protected-transit rows that infer from
arrival; `V0-NODE-LOOPBACK` exited 5 because the wildcard is refused at
configuration admission, a usage exit, not an outcome. Not built:
`V0-NODE-CONFIG` (no `[acl2]` key, ACL2 is in the image), `V0-AUTH-NEW`
(the principal is derived inside `set-password`), and
`V0-READ-NEWNEWS-SYNTAX` (a malformed wildmat answers 501 on this commit).

**The two disagreements, by name.** `V0-CFG-LIVE`: `group create` against
the live owner exits 3 (uncertain) and the socket then gets no reply to
`GROUP fn.matrix.live`; lane T8 fixed two defects in this path after the
image was cut (4931dcb4) and lane T8c determines whether they account for
it. `V0-CFG-LIVE-REFUSE`: a second configuration over the same store with an
unbound control path ran the offline executor, which accepted `group create`
and wrote configuration generation 7. Lane T8c found
([record](t8c-live-rows-2026-09-22.md)) that this was not two writers: the
live request had killed the owner (its open's integer id went through the
action reader, and its stop hook closed the reply socket, which is the
uncertain-and-silent of the first row), so the lock was free and accepting
was correct; the harness now checks the owner is alive before the offline
half. Both owner defects are fixed on dev (85e3254f), unwitnessed on an
image; the first row stays a disagreement until T8b serves a group created
live.

## What this record does not claim

No durability past process death (D14); no signature security (A-CRYPTO);
nothing about peers (none configured); nothing about DTN; the not-exercised
phases above. The node is reachable on the LAN only.
