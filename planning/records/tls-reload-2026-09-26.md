# `tls reload`: a renewed certificate without a restart (2026-09-26)

Lane `tls-reload` (Opus), branch `lane/tls-reload` from dev `5684b2f8b`
(merged with dev `1183f4bc3` to reach public-node's runbook). It closes
public-node's gap (c) (planning/evidence/public-node-2026-09-26.md): the
node read its certificate only at `run`, so every Let's Encrypt renewal
restarted the public node and dropped its sessions.

Ids: PRF-212, HST-020, SCN-143. Wire codes: FNCT kind 19 (request: the word
`reload` or `status`) and FNCT kind 20 (reply: status, reason word, served
line). FNCT 1 to 18 were taken on dev (books/native-control-reason.lisp's
header); FNBS 19 and 20 are another magic.

## What now works

- `fn operator CONFIG tls reload` asks the running owner, over its control
  socket, to re-read the `tls_cert`/`tls_key` paths `run` loaded. New
  connections (STARTTLS and the implicit-TLS listener) get the new pair;
  a session already open keeps the context it handshook with. The command
  prints the served line and exits 0, or is refused by name (exit 1,
  `refused operator tls REASON`) with the old certificate still served.
- `status` against a running owner prints one more line after its report:
  `tls names=A,B not-after=YYYY-MM-DDTHH:MM:SSZ` (`tls none` without TLS,
  `names=none` for a CN-only leaf, `tls unknown REASON` when the owner
  did not answer, e.g. `owner-lacks-tls-reload` from an older owner).
- public-node's renewal hook (`tools/runbooks/public-node/acme/fn-cert-install.sh`)
  now runs `tls reload` instead of restarting. On a refusal it exits 1 and
  does not restart (a restart would serve the material the node refused);
  only when the owner cannot be asked (exit 2 or more) does it restart.

## Assurance chain

native entry `fnn-tls-control-handle` (host/native/tls-reload.lisp, on the
hybrid control chain, request kind 19 decoded by ACL2
`fn-tlsr-request-decode`) -> `fnn-tls-owner-reload` builds the candidate
(`fnn-tls-server-candidate`, host/native/tls.lisp) and copies the library's
observations (`fnn-tls-leaf-facts`: SSL_CTX_get0_certificate,
X509_get0_notBefore/notAfter, the subjectAltName extension's octets; the
chain, key and match booleans; the clock) -> executed ACL2 subject
`fn-tlsr-decide` through host/tls-reload-host.lisp `fn-tlsr-host-decide`
-> keystones below -> the host swaps exactly on `:accept`
(`fnn-tls-context-swap`) -> observed in tests/test_native_tls_reload.py.

The maintained relation is the context's: `served` holds the facts of the
material in `pointer`. It is established lazily from the pointer `run`
opened (`fnn-tls-served-facts`, under the context lock) and preserved by the
swap, which sets both under that lock. `fnn-tls-accept` takes the same lock
across `SSL_new`, so after the swap returns no session can start on the old
pointer; the old SSL_CTX is freed only as the context's reference (each SSL
holds its own, which OpenSSL 3 and LibreSSL take in SSL_new). That last
fact and the library's certificate parse are trusted (HST-016's seam), not
proved.

## Theorems (books/tls-reload.lisp, PRF-212)

- `fn-tlsr-decide-accepts-exactly-loaded-matching-current-covering-material`
  (KEYSTONE, no hypotheses): `(fn-tlsr-acceptp (fn-tlsr-decide facts served))`
  iff the chain loaded, the key loaded, the key matches, the window holds
  (`fn-tlsr-currentp`: both times parse, the clock is an integer,
  notBefore <= now < notAfter), the subjectAltName is not `:malformed`, and
  `(subsetp-equal (fn-tlsr-served-names served) (fn-tlsr-names facts))`.
- `fn-tlsr-decide-carries-the-facts-or-a-named-refusal`: an accepted
  decision is `(:accept NAMES NOT-AFTER)` of the parsed facts; any other is
  `(:refuse R)` with R one of `chain-unreadable key-unreadable key-mismatch
  validity-malformed clock-unusable not-yet-valid expired names-malformed
  names-dropped`.

Host line: host/native/tls-reload.lisp `fnn-tls-owner-reload` calls
`fn-tlsr-host-decide`, then swaps on `fn-tlsr-host-acceptp`.

Teeth (tests/acl2/tls-reload-tests.lisp): the facts are a real EC P-256
certificate's (UTCTime validity, subjectAltName with two dNSNames and an IP
entry that is skipped). A positive witness asserts every conjunct and the
acceptance with the parsed names and notAfter; per conjunct a witness where
it alone fails and the decision refuses by its name (the clock one with a
string clock); per conjunct a `must-fail` of the acceptance with that
conjunct omitted; the window's two ends; covering (a CN-only served
context is covered by anything; a renewal naming only another name is
`names-dropped`); the frames round trip, an old owner's plain refusal reads
as `owner-lacks-tls-reload`, and the served and log lines render.

Admitted: books/tls-reload.lisp (every event), its test book, the changed
books/native-operator.lisp (all 177 forms) and tests/acl2/native-operator-tests.lisp
(the new `tls` assertions) in the persvati REPL (proof_repl, toolchain w25,
sessions `tlsr` and `nop`). Certification is the batch's.

## Decisions a reviewer may want to revisit

- **Names must cover.** A renewal that drops a DNS name the served
  certificate names is refused (`names-dropped`): a peer that verifies this
  node by that name (SSL_set1_host) would fail its next handshake. A
  deliberate change of names is a restart. Rejected alternative: accept any
  names (a wrong-domain certificate installed by a broken hook would then be
  served silently).
- **Startup is unchanged.** `run` still refuses only unloadable or
  mismatched pairs, by the host's OpenSSL checks, and does not apply
  `fn-tlsr-decide` (an expired certificate still starts). Moving startup onto
  the same decision is a behaviour change left as a packet (below).
- **Reload over the control socket, not SIGHUP.** SIGHUP stays the log
  reopen (PKT-101); the verb gives a named, exit-coded answer.

## Native

`tools/hbox_native.sh --images developer,production --label r1 .
tests.test_native_tls_reload tests.test_native_starttls
tests.test_native_implicit_tls` (the last two because host/native/tls.lisp
changed: the candidate builder now serves `run`'s open too).

- r1 (`hbox:/tank/fn/scratch/tls-reload/native-r1`, tree 5684b2f8b+dirty):
  starttls OK (4), implicit_tls OK (3), tls_reload FAILED 2 of 4: the
  accepted reload, the new certificate on new handshakes and the open
  session all held, but the mismatched key was reported `key-unreadable`.
  Classified implementation: SSL_CTX_use_PrivateKey_file after the
  certificate refuses a key that does not match it. Fixed by loading the
  key before the chain (a mismatching key is then dropped when the leaf is
  set and SSL_CTX_check_private_key reports it); `run`'s refusal still says
  `mismatch`.
- r2 (`hbox:/tank/fn/scratch/tls-reload/native-r2`, the committed lane
  after the fix, both images built there): `== modules: 3 OK, 0 SKIPPED,
  0 FAILED`; tls_reload OK (4 ran: both cases on the production and the
  developer image), starttls OK (4), implicit_tls OK (3), on hbox's system
  OpenSSL 3.3.1. Logs in planning/evidence/tls-reload-2026-09-26/ with the
  run's SHA256SUMS: tls_reload
  `6eb74166110306f14e489d1cfc75e251a845b2b4e5b5b3faf7d5d07ed86f409a`,
  starttls `4403fa63484dfe4c015066d266734c94c674150fae4adcf744897b66f90aa0a9`,
  implicit_tls `f1944cded65ed99740cb96c1fe09860d2cac5461778f8e5a471d423ecaeb3847`.
  LibreSSL (the OpenBSD friend node) was not exercised; the eight new
  symbols are LibreSSL 2.7+ API and the start refuses by name if one is
  missing.

## Not done

- PKT-606 (proposed): apply `fn-tlsr-decide` at `run` as well, so an
  expired or name-less pair is refused by the same function at start.
- The peer client's contexts (feed and pull, `fnn-tls-open-client-context`)
  are not reloadable; their trust anchors are the CA roots per the public
  node's runbook, which renewals do not change.

## For the batch

- Changed books: books/tls-reload.lisp (new), books/native-operator.lisp;
  test books tests/acl2/tls-reload-tests.lisp (new),
  tests/acl2/native-operator-tests.lisp, tests/acl2/docs-operator-grammar-tests.lisp.
- Native modules: tests.test_native_tls_reload (needs `--images
  developer,production`); tests.test_native_starttls and
  tests.test_native_implicit_tls for tls.lisp.
- No fixture.
