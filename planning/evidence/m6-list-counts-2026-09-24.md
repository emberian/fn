# M6 server findings: LIST COUNTS, the numbered Message-ID answer, store identity (2026-09-24)

Lane `m6-list-counts`, branch `lane/m6-list-counts` from dev `00d291d0`. It
answers findings 3 to 6 of the [web client record](m6-web-2026-09-24.md) on
the server side.

## What changed

- **LIST COUNTS** (RFC 6048 §2.2, `LIST COUNTS [wildmat]`): name, high, low,
  count, status, rendered by ACL2. The archive fold is
  `fn-nntp-list-counts-command` (`books/nntp-responses.lisp`); the served
  dispatcher `fn-nntp-archive-command-pinned` (`books/nntp.lisp`) answers it
  from the connection's pinned group buckets with `fn-gidx-list-counts-command`.
  CAPABILITIES now lists `LIST ACTIVE ACTIVE.TIMES COUNTS HEADERS NEWSGROUPS
  OVERVIEW.FMT`. The count is **derived from what the view already holds**
  (the pinned bucket of each group), not carried: per group at most B bucket
  headers plus the group's own E_g entries, each entry visited a constant
  number (three) of passes, plus one lookup in the next-number table for an
  empty group. `fn-gidx-counts-work-of-build-bound`: the counted work of one
  reply is at most G·B + M for G distinct listed groups, B buckets and M
  memberships, linear in each; that is a model counter, not a timing.
- **The Message-ID number** (RFC 3977 §6.2.1.2, and §6.2.4.2 for STAT):
  `ARTICLE/HEAD/BODY/STAT <msgid>` answer `fn-nntp-msgid-local-number`, the
  article's available number in the selected group, 0 when no group is
  selected or the article is not in it. It reads the article's membership
  list, never the archive. The session is unchanged, as the section requires.
- **Store identity:** not implemented; recorded as a candidate pending ember
  in [decisions](../decisions.md) ("a store identity on the wire"): no existing
  ACL2 value distinguishes two stores initialised from one configuration, and
  the numbered Message-ID answer already lets a client check a remembered
  (group, number, Message-ID) triple in one command.

## Theorems (subject, statement, host line)

Host line: `host/owner-host.lisp` `fn-owner-chunk` (line 1362,
`fn-scar-ocfg-read-tls-prefix`), which the chain recorded in
`books/owner-verdict-read.lisp` equates with `fn-own-read`;
`fn-own-read-is-served-step-on-pinned-prefix` equates that with
`fn-served-step`.

| Event | Book | Statement |
| --- | --- | --- |
| `fn-served-step-list-counts-is-the-archive-counts` | owner-list-counts-read | one read framing one `LIST COUNTS ...` line answers `fn-nntp-list-counts-command` of the pinned archive, under the trie/bucket relation the owner carries (`fn-olc-buckets-okp`) and a projection archive |
| `fn-served-step-msgid-retrieval-carries-the-local-number` | owner-list-counts-read | one read framing `ARTICLE/HEAD/BODY/STAT <msgid>` answers `fn-nntp-article-response` with `fn-nntp-msgid-local-number` |
| `fn-gidx-list-counts-command-is-the-archive-fold` | nntp-list-counts | bucket reply = archive fold, under projection and buckets = build |
| `fn-nntp-archive-command-pinned-list-counts` | nntp-list-counts | the pinned dispatcher's LIST COUNTS arm is the fold, pinned or not |
| `fn-nntp-group-count-is-listgroup-length` | nntp-list-counts | the count equals the length of LISTGROUP's number list; no hypothesis |
| `fn-gidx-counts-work-of-build-bound` | nntp-list-counts | work ≤ G·B + M for distinct groups |
| `fn-nntp-msgid-number-retrieves-the-same-article` | nntp-list-counts | under `fn-statep`, a positive number sent back as any number token reading as it retrieves the same article in the same group (§6.2.1.2's "second ARTICLE command") |
| `fn-nntp-find-group-number-of-fresh-member` | nntp-list-counts | the lemma doing the work: fresh local numbers make the number scan find the member |

Teeth, `tests/acl2/nntp-list-counts-tests.lisp`: reachable witnesses (two
accepted articles, one cross-posted, one empty group; exact COUNTS lines,
wildmat, 501; STAT answering 2, 1, 0 and 0) and one step-bounded must-fail
per hypothesis: stale buckets and a non-projection archive (a doubled
membership) for the fold; repeated groups for the work bound; a clashing
(group . number), no group selected, a token for another number and a
non-number token for the Message-ID keystone.

## Certification

- persvati `run-20260924T214734Z-a82e`, `--affected-by books/nntp-responses.lisp`
  (198 roots), 2 jobs, 300 s: 196 of 198 passed; `tests/acl2/nntp-tests` and
  `tests/acl2/nntp-reader-profile-tests` failed on pinned bytes this change
  moves (manifest `certify-20260924T214755Z-939221`).
- persvati `run-20260924T220100Z-1101`: reader-profile passed; nntp-tests
  failed on a second pinned CAPABILITIES byte list (manifest
  `certify-20260924T220124Z-1056618`).
- persvati `run-20260924T220307Z-7be0`: passed, `tests/acl2/nntp-tests`
  certified and the other 197 roots installed at their current digests from
  the two runs above (manifest `certify-20260924T220328Z-1075905`). All 198
  roots affected by `books/nntp-responses` are green at these bytes.
- New books: nntp-list-counts 0.3 s, owner-list-counts-read 0.1 s per event
  at most in the REPL; the manifests carry the book times.

## Native (hbox, developer image from this branch)

Image closure certified on hbox (`certify-20260924T214927Z-1980616`, 213
installed, the changed nntp/owner/served/bp books certified, exit 0), image
`build/fn-host-developer`, core sha256
`2c4a508acf85698442e2aef26b52228a34b0d356578477387863f0cc6edcf87e`, built with
`FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8`, in
`/tank/fn/scratch/m6-list-counts/tree`.

| Log | Result | sha256 |
| --- | --- | --- |
| [native-reader.log](m6-list-counts-2026-09-24/native-reader.log) | `tests.test_native_reader_index` 5/5, including the new `test_list_counts_and_numbered_msgid_lookup` (CAPABILITIES, LIST COUNTS with and without wildmat, 501, STAT 0 / 1 / 0 / ARTICLE 2, cursor unmoved, STAT 2 same article, counts after restart) | `3200507e9cf12919c97e8c1e13d567cbf6ce9a1ba717d61ceb1541aa3e0ca6bb` |
| [native-web.log](m6-list-counts-2026-09-24/native-web.log) | `tests.test_fn_web_native` 4/4: the 409 page links `/find?id=..&group=..`, `/find` with the group shows "Local #N in fn.agents" and a resume link, without it none, the home card shows the count | `ea8e5fe5a55a67f1e30d40a7352bc60550cb063cf6a8a069a0764ccffc7573e6` |

Earlier attempts on the same image: the reader helper did not read a 1xx
multi-line reply (test defect, fixed); the web case expected the lookup link
for the wrong Message-ID (test defect, fixed); the first web run lacked
`FN_ACL2` for `set-password` (environment).

## Web client

`Backend.groups` reads LIST COUNTS (LIST ACTIVE on a node that refuses it);
`ReadMarks.unread` is exact: the count filling the water-mark span means every
number holds an article, otherwise the client asks LISTGROUP for that group.
The "upper bound" wording remains only for a node without LIST COUNTS ("at
most N unread"). `/find` takes `group`; `fn_client.show` selects it first.

## Not claimed

HDR/XHDR/GROUP/NEXT/LAST still fold the archive. No timing claim. Not run
against `/tank/fn/node`. The served-step theorems take one framed line and the
owner's relations as hypotheses, as `owner-verdict-read` does.
