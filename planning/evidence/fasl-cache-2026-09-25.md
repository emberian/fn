# The certificate cache carries the compiled file (2026-09-25)

Lane `lane/fasl-cache`, from dev `9a92bafd`. Answers the farm finding in
[ten-second-2](ten-second-2-2026-09-25.md): the cache stored `.cert`/`.port`
only, so every book installed from it loaded uncompiled.

## What the cache stores now

- `tools/certify_books.py` records `compiled_digests_sha256` (book to the
  SHA-256 of `<book>.fasl`) for each certified book whose `.fasl` is not older
  than its `.cert`, in the per-book publish manifest and the final manifest.
- `certs.publish` writes `book.fasl` into the same entry as the pair (same
  closure key, same origin, same toolchain identity) only when that manifest
  recorded it and the bytes beside the book still match. The entry's
  `meta.json` binds `fasl_sha256`; `entry_matches_meta` checks it. An older
  manifest without the field publishes the pair alone. A republish of an
  existing entry with a newly recorded fasl adds it (`relabelled`).
- `install_entry` places the fasl only with its pair, and sets its write date
  to the certificate's when it is older; an entry without a fasl installs the
  pair alone and deletes any local `.fasl`. `install-partial`'s miss path,
  `install-set`'s purge and `install`'s foreign removal delete the `.fasl`
  with the pair.
- Reports count `fasl_installed` and `fasl_missing` (install-set and
  install-partial lines end `; fasl N missing M`, after the fields
  `farm.py`'s older patterns read); the runner's `cache_install` and
  `farm.py`'s parsed record carry both.

## Relocatability

Measured on the laptop, Homebrew ACL2 8.7 on SBCL, `tools/acl2`
(`ACL2_BOOK_HASH_ALISTP=NIL`): two books (parent includes child) certified
in directory A; sources copied to B, `.cert`/`.port`/`.fasl` copied with
their dates, A deleted. In B, `(include-book "parent" :load-compiled-file t)`,
which is an error if a compiled file cannot be loaded, succeeded, and both
functions were compiled. The fasl embeds A's path only as SBCL's
`compiled from ".../A/parent@expansion.lsp"` debug string; ACL2 never opens
it. The include-book value and `include-book-alist` name A's paths with or
without the fasl present: that comes from the certificate, as the
[2026-09-23 record](certificate-cache-2026-09-23.md) found, not from the
fasl.

The one condition ACL2 imposes (`interface-raw.lisp`, `load-compiled-book`)
is the write date: a `.fasl` older than its `.cert` is refused with

    Unable to load compiled file for book .../B/child.lisp
    because the file-write-date of ".../B/child.fasl"
    is less than that of ".../B/child.cert".

(reproduced by touching `child.cert`). certify-book writes the certificate
in Step 4 and compiles in Step 5, so a fresh pair is ordered correctly; the
installer keeps it so. A fasl is specific to the SBCL runtime and ACL2 core,
which `toolchain_identity` already names; `install-partial` and `install-set`
select by it. The legacy `install` command does not, for pairs or fasls.

On persvati the same held across run roots: fasls compiled in
`fasl-cache-5d268b56-warm` loaded in `fasl-cache-5d268b56-after` with no
compiled-file warning.

## Runs on persvati

Toolchain `w25/acl2-literal` (identity `1b4169e9…4286`), 2 jobs,
`--timeout-seconds 300`, cache `/home/ember/fn-certcache`, source
`5d268b56`. Roots `books/bp-node-progress-guards` (includes
`bp-report-guards`) and `books/bp-node-rotation` (includes
`bp-fnbs-replay-append`), 194-book closure.

1. Before: `--recertify` both roots, everything else from the cache as it
   was (`fasl_installed 0, fasl_missing 192`)
   ([manifest](manifests/certify-20260925T070913Z-1891411.json)).
2. Warm: `--closure` into a fresh root, certifying all 194 books with this
   runner; 194 per-book publishes, 194 entries now with `book.fasl`
   ([manifest](manifests/certify-20260925T071028Z-1902935.json)).
3. After: run 1 again into another fresh root (`fasl_installed 192,
   fasl_missing 0`, all from the warm origin)
   ([manifest](manifests/certify-20260925T071430Z-1940107.json)).

| | before (1) | after (3) |
|---|---|---|
| `include-book "bp-report-guards"` inside bp-node-progress-guards | 4.45 s | 1.67 s |
| `include-book "bp-fnbs-replay-append"` inside bp-node-rotation | 4.36 s | 1.65 s |
| all four includes, bp-node-progress-guards | 4.68 s | 2.28 s |
| all four includes, bp-node-rotation | 4.67 s | 2.21 s |
| bp-node-progress-guards book wall | 6.05 s | 3.78 s |
| bp-node-rotation book wall | 5.15 s | 2.73 s |
| "Unable to load compiled file" warnings per log | 4 | 0 |

Include times are ACL2's own `Time:` summaries; walls are the manifests'
`book_wall_seconds`. One run each, on a quiet persvati.
In the warm run itself (2) the roots, with every dependency's fasl written
locally, took 2.87 s and 1.87 s, and the two named books certified in 5.28 s
and 1.62 s.

## Findings

- With the fasl, the three small includes after the first cost 0.12 to 0.26 s
  each, where they cost 0.00 to 0.30 s uncompiled; the first include
  dominates either way and falls by 2.7 s. Not investigated.
- The cache on persvati holds fasls only for entries certified by this
  runner. Until entries are recertified, older pairs install without one
  (`fasl_missing` says how many). A gate or closure run rewarms it.

These runs measure include cost at these bytes. They certify no
integrated image.
