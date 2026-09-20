# The farm cache and a run that fails: measured before and after

`tools/farm.py submit` installs a box's certificate cache into the mirrored
tree before the runner starts, and prints `installed N, kept N, uncached N`.
A lane that re-submits into the same remote root should find what the
previous run certified. It did not, and this is the measurement of why.

## What the runner did, and what it does now

`tools/certify_books.py` published to the cache inside `if success:`, and
`success` is a statement about the WHOLE requested batch: every book's exit
code 0, every marker present, every certificate on disk. A wide run on this
tree exits non-zero while any root carries an open theorem
(`books/peer-inbound` and `books/checkpoint-codec` do today), so no wide run
has been seeding the box. `tools/farm.py wait` swept the box afterwards with
`certs.py publish --origin-kind run`, which is why some `run` entries exist
at all -- but only for a lane that reached `wait`; the timeout path returned
3 without fetching, and a killed or unwaited run left nothing.

The runner now publishes each book's pair the moment that book certifies, on
that book's own evidence, and sweeps at the end whatever the run's verdict
was. `tools/farm.py wait` fetches and publishes on its timeout path too, and
says what it left running.

## The reproduction

Isolated cache `/home/ember/fn-certcache-w10tooling` (created empty for each
arm, so no other lane's pairs are in the counts); remote root
`/home/ember/fn-lanes/w10-tooling-repro`; `--jobs 2`; closure over
`books/byte-store-scan`, a root that fails on dev, with its 21 certified
dependencies. Tree: `w10/tooling` off dev `8da8217`. ACL2 Version 8.7 on
persvati (`$HOME/fn-tools/acl2-8.7/saved_acl2`).

The second measurement is `farm.push` followed by `farm.install_from_cache`,
which are the two steps `submit` runs before the runner: the same functions,
the same arguments, without starting a second certification.

| arm | run id | books certified | run exit | cache entries after | second submit's install |
| --- | --- | --- | --- | --- | --- |
| before | `run-20260920T203028Z-d411` | 21 of 22 | 1 | 0 | `installed 0, kept 0, uncached 267` |
| after | `run-20260920T204249Z-470f` | 21 of 22 | 1 | 21 | `installed 21, kept 0, uncached 246` |

Both arms failed on the same book for the same reason
(`books/byte-store-scan`, `book_results` 21 passed / 1 failed). The after
arm's manifest,
`build/acl2/certify-20260920T204421Z-3040894/manifest.json` on persvati,
records `cert_cache.per_book_published 21`, `already_cached 21` at the
end-of-run sweep (every pair was already filed as its book finished), and
`not_published ['books/byte-store-scan']` with the per-book reason
`this book did not pass`. Certify wall 144.046 s at 2 jobs.

`uncached` counts every book in the tree, not only the 22 requested:
267 - 21 = 246.

## What this does not establish

- Nothing here says a book's theorem is what its name suggests. A cached pair
  is a certificate ACL2 wrote, moved to another worktree where ACL2 checks it
  again at include time.
- The 21 installed pairs are still re-certified by a `--closure` run, which
  certifies its whole dependency list unconditionally
  (`certify_books.with_dependencies`). The saving measured here is for a run
  that names roots WITHOUT `--closure`, whose dependencies must already carry
  certificates. Making `--closure` skip a book whose installed certificate is
  current is a separate change and is not made here.
