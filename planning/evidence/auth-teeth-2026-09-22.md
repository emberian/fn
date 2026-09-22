# The login gate and the protected channel, with teeth (T7)

What this file is: the record of lane `t7/auth-teeth`, step T7 of
[the trajectory plan](../plan-2026-09-22-trajectory.md) §3, phase 0. It names
what ran, on what bytes, and what it does not establish. It is not a
certification claim about any revision other than the one below, and it makes
no claim about a deployed node: the `483`-then-login row of
`tools/node_probe.py` is measured on an image, and no image has run it.

## What ran

| fact | value |
| --- | --- |
| host (iteration and local certification) | this laptop, `macOS 26.6.1`, `arm64` |
| python3 | 3.14.7 |
| ACL2, locally | 8.7, built 2026-08-28, on SBCL 2.6.8 |
| host (the certification below) | `persvati` |
| ACL2, on persvati | `/home/ember/fn-gates/toolchains/w25/acl2-literal` |
| branch | `t7/auth-teeth`, worktree `build/lanes/t7-auth-teeth` |
| base | `dev` `722c9566` |
| revision certified | `2ea2706f` |
| run | `run-20260922T171336Z-1c22`, `--closure --jobs 6 --timeout-seconds 1800`, remote root `/home/ember/fn-gates/t7-auth`, cache `/home/ember/fn-certcache` |
| roots | `books/nntp-auth`, `books/nntp-auth-invariants`, `tests/acl2/nntp-auth-teeth-tests`, `tests/acl2/nntp-auth-tests` |
| manifest | `planning/evidence/manifests/certify-20260922T171341Z-2034147.json` |
| result | `passed`; 74 books, no failure; 732.9 s of certification wall at 6 jobs; ACL2 toolchain identity `1b4169e9…`. `books/nntp-auth` 5.7 s, `books/nntp-auth-invariants` 3.4 s, `tests/acl2/nntp-auth-teeth-tests` 1.0 s, `tests/acl2/nntp-auth-tests` 0.7 s. The manifest's `source_digests_sha256` for those four equal this tree's bytes, and its observed success markers equal the expected ones |
| second run | `run-20260922T174206Z-1976`, same box and toolchain, roots `books/served-tls-prefix`, `tests/acl2/served-tests`, `tests/acl2/served-tls-prefix-tests`: the three books that were green on `dev` and whose dependency this lane moved. Manifest `planning/evidence/manifests/certify-20260922T174210Z-2281303.json`, `passed`, 74 books, 732.0 s. After it, `python3 tools/green_check.py --changed-since 722c9566 --strict` still exits 1, and every one of the 17 books it names was already red or never on `dev` at `722c9566`: the store-node cascade and the native-guards reds that other lanes own. The set of books that were green on `dev` and are not green now is EMPTY |

The invocation, exactly:

    python3 tools/farm.py submit persvati books/nntp-auth books/nntp-auth-invariants \
        tests/acl2/nntp-auth-teeth-tests tests/acl2/nntp-auth-tests \
        --closure --jobs 6 --timeout-seconds 1800 \
        --remote-root /home/ember/fn-gates/t7-auth \
        --acl2 /home/ember/fn-gates/toolchains/w25/acl2-literal \
        --cache /home/ember/fn-certcache

Iteration was `tools/proof_repl.py` against the cached closure, a form at a
time, as [how we work](../how-we-work.md) step 2 asks; the local
`tools/certify_books.py` runs above it were there to refresh the two books the
session needed, not to make a claim.

## What is now proved that was not

Five statements, all in `books/nntp-auth.lisp`. The first three are the
plan's P1 said over the function the host calls; the fourth is what turns
PRF-039's open-transition claim into a claim about the connection; the fifth
exists so that two hypotheses with no possible violating value could be
removed rather than left untoothed.

1. `fn-auth-step-protected-only-refuses-authinfo-before-tls`. Eight
   hypotheses. Under a protected-only policy on a connection with no TLS
   layer, an `AUTHINFO` command line -- `USER` or `PASS`, any arguments, a
   configured name or not -- is answered with RFC 4643 §2.3.2's `483`, the
   session is the one the command arrived on, and no submission leaves. The
   secret is never compared, because the branch that would compare it is not
   reached. The subject is `fn-auth-step`, which `books/served.lisp`
   `fn-served-dispatch` calls and which `host/owner-host.lisp`
   `fn-owner-chunk` reaches through `fn-own-read` and `fn-served-step`; the
   native host's socket read is `host/native/owner.lisp` over the same owner
   entry. `fn-auth-protected-only-refuses-authinfo-before-tls`, which the
   tree already had, is the same statement over `fn-auth-authinfo`, which no
   host line calls.
2. `fn-auth-starttls-is-not-advertised-under-tls-on-any-connection` and
   `fn-auth-authinfo-is-not-advertised-once-authenticated-on-any-connection`,
   with `fn-auth-authinfo-is-not-advertised-before-tls-under-protected-only`
   beside them. The subject is `fn-auth-capability-lines-for-peer`, which is
   the list `fn-auth-command` puts in the `101` block; the reader-facing pair
   the tree had are its `record` = `nil` instances. That difference is not
   cosmetic: the owner resolves a connection to a peer by source address
   alone, so on a box with a loopback peer record every client arrives with a
   record, and a keystone stated over the reader entry says nothing about any
   of them (the same shape as the defect PRF-039 records).
   `fn-auth-step-capability-block-unfolds-to-the-peer-aware-lines` is the
   named unfold equating that list to what the step emits, and it is named
   for what it is.
3. What none of those three says: anything about the octets `fn-nntp-multi`
   renders the list into. They are about membership in a list of labels.
4. `fn-auth-step-preserves-the-config`, with no hypothesis at all: for any
   session and any wire event, the step's session carries the same
   `fn-auth-session-config`. Not a login, not the handshake, not a delegated
   reader command and not a command the book does not answer writes that
   field. The header of `books/nntp-auth-invariants.lisp` asked for this by
   name as the first of the three facts `OB-AUTH-FOLD` waits on and described
   it as true by inspection of five branches; it is true of every value, and
   that header now says so.
5. `fn-auth-restricted-keyword-is-a-keyword-token`: every keyword the reader
   gate refuses is an RFC 3977 §9.8 keyword token. With it,
   `(consp (fn-nntp-tokenize line))` and
   `(fn-nntp-keyword-tokenp (car (fn-nntp-tokenize line)))` are consequences
   of the restricted-keyword hypothesis, and they are removed from
   `fn-auth-gated-command-is-refused-and-not-performed`, which is now a
   seven-hypothesis statement in which every hypothesis has a violating
   value.

## The teeth

`tests/acl2/nntp-auth-teeth-tests.lisp`, a new Makefile root beside
`tests/acl2/served-tests`. 23 `must-fail` cases, and beside each the
evaluated value that refutes the dropped-hypothesis statement, over one
archive holding one accepted article in `fn.letters` and one credential
enrolled with `books/auth-secret.lisp` whose digest the book re-derives under
the real SHA-256 attachment.

| keystone | teeth |
| --- | --- |
| `fn-auth-gated-command-is-refused-and-not-performed` | 7, one per hypothesis. The witness is `GROUP fn.letters` on a required-auth connection: `480`, the session unchanged, no offer, no submission -- and the same command authenticated selects the group, so the refusal is of something that would have happened |
| `fn-auth-step-protected-only-refuses-authinfo-before-tls` | 8, one per hypothesis. The witness uses the configured name and the enrolled secret, so the `483` refuses a login that succeeds over TLS on the same policy; nothing is cached, so the `PASS` behind the refused `USER` is `483` again and not `481` |
| the three `-on-any-connection` capability-label keystones | 4, one per hypothesis, each separating on a peer record as well as a reader |
| `fn-auth-starttls-is-not-advertised-without-a-certificate` | its tooth was already in `tests/acl2/nntp-auth-tests.lisp`, in the whole-block transcripts: with a certificate configured and no TLS the label is in the `101` block, and with none it is not. Not repeated here |
| `fn-served-open-greets-200-exactly-when-the-connection-may-post` | no hypothesis: the tooth is the value that separates the two sides (posting allowed in the injection configuration, but a policy requiring a login the connection has not made -- `201`, not `200`) together with a `must-fail` on the statement the definition satisfied before 2026-09-21: that the greeting is `200` exactly when the injection configuration allows posting |
| `fn-served-open-peer-pins-the-configuration`, `fn-served-peer-and-reader-open-under-the-same-policy` | no hypothesis: both arms of the `if` witnessed, the two opens shown to agree on a policy that is not the open one, and a `must-fail` on the pre-repair equality, that the peer open pins `(fn-auth-open-config)` |
| `fn-auth-step-preserves-the-config` | no hypothesis: the config survives a cached username, a login, the handshake, `(:tls-established)` and a delegated command, and the sessions it survives across are shown to be different values |
| K1, `fn-served-dispatch-of-a-refused-post-leaves-the-wire-in-place` | the witness and 2 of its 4 hypotheses; see the limitation below |

## Limitations, stated rather than left to be discovered

- **K1 owes two teeth.** `fn-served-connp` and the not-handshaking
  hypothesis have no `must-fail`. Both are proof support: the not-handshaking
  one because the lift K1 uses carries it, and `fn-served-connp` because
  `fn-auth-step-effects-well-formed` -- the fact that rules a `(:submit ...)`
  out of the effect list at all -- takes `fn-auth-session-consistentp`. K1
  restated without them was attempted on 2026-09-22 and reached one open
  case, a session that is `fn-auth-sessionp` but not consistent with its
  connection's archive; the lane did not weaken K1 to get past it. The teeth
  book says this in place and PRF-031 records it.
- **`OB-AUTH-FOLD` (K2) is still open.** Of the three facts
  `books/nntp-auth-invariants.lisp` says it waits on, this lane proved the
  first; the other two are a wire lemma in `books/wire-invariants` and a
  reader lemma in `books/nntp-post`, neither of which this lane owns.
- **`books/owner-tls-prefix` is not certified here.** It is red only behind
  the store-node cascade (`books/owner-config` to `books/owner` to
  `books/store-node-*`), which another lane owns; this lane changed nothing
  in it and nothing it depends on except `books/nntp-auth`, and it certifies
  when that cascade clears.
- **Nothing here ran on a node.** `tools/node_probe.py` already asserts
  `483`-before-TLS, `STARTTLS` and `281` against a running node
  (`docs/operator.md`, "Reaching it from a laptop"); the image does not exist
  yet, so that row is root's when it does. A passing test is not a proof and
  an ACL2 theorem is not a measurement.
- **A-CRYPTO is untouched.** That a wrong secret fails is second-preimage
  resistance of the attached SHA-256 and is exhibited by witness, not proved.
  `AUTHINFO USER/PASS` remains a cleartext mechanism on the wire; what
  `protected_only` buys is that fn refuses to read one off an unprotected
  channel, not that TLS is confidential, which is a host facility
  (`docs/architecture.md`).
