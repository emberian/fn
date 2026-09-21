# `stx-carrier` bounded-value proof repair

The focused certification run `run-20260921T190346Z-cabd` certified
`books/stx-carrier` and its nine-book source closure on `persvati`. The
archived manifest is
[`certify-20260921T190349Z-3063692.json`](manifests/certify-20260921T190349Z-3063692.json).

The submitted invocation was:

```text
python3 tools/farm.py submit persvati --jobs 1 --closure \
  --timeout-seconds 600 \
  --acl2 /home/ember/fn-gates/toolchains/w25/acl2-literal \
  books/stx-carrier
```

ACL2 8.7 completed all ten selected books with exit code zero in 66.064
seconds. The launcher SHA-256 was
`346b7ee183e8c291cb61cf31be75a332caf329fa74b4995921cbb224208f2c08`;
the ACL2 core SHA-256 was
`1bc67f611886a0898641bbb0a67a38baddc6b800c1c31a1d757d26e10eda3ffd`.
The scope was only `books/stx-carrier` and its direct source closure. It was
not a certification of the Store, BP, native runtime, or the full Makefile
root set.

The manifest records no Git revision because the farm certifies an uploaded
source tree. To bind that tree to the landed repair, every one of its ten
`source_digests_sha256` entries was independently recomputed with
`git show 90ba73ed:<path>` and SHA-256. All ten match exactly; there are no
differences:

| Source | SHA-256 in manifest and `90ba73ed` |
|---|---|
| `books/article.lisp` | `fa301b728e62c8f5e5f3256da9ae22d3f162215fc63b8c0288b92548d2d1fade` |
| `books/cbor-invariants.lisp` | `999c4e6d08f6cb6ade7ca6b80da1564c4ecd26727a0c5e1c382d7aa7e3a36f64` |
| `books/cbor.lisp` | `210c1103953ee93fdc97bfae0e16ca02d1ab020908d771fee711e8061268e330` |
| `books/crypto-seam.lisp` | `25ab29192bc0d90d93968f41039e61b0333646342721be6fa350b12884038fa1` |
| `books/defrecord.lisp` | `ec4252ef85d2f5d340d8cdefda4f21344c73dfc851daad8d7237f6152cc9d639` |
| `books/records-invariants.lisp` | `bc695e30caa6146495532bd0ca1f9a2dd378ee7a06b2da189f75da8df6fcedbc` |
| `books/records.lisp` | `1e00a6f18b387148b4cb0ae308cd0b2369261067d82256c0052059d0715d987c` |
| `books/statement-invariants.lisp` | `ae9301f03968f83bcfa91f492a616bef7706bd0e7979a50290abdb700dc1c601` |
| `books/statement.lisp` | `48887b25bfe62fa7c820a1348a43849152641813fb834f39368c7f6dbe5aac7a` |
| `books/stx-carrier.lisp` | `1dd4ad390544ddc2efbd9427cada1bfa41d542c9f2c61e4fde94beb7edbdf343` |

The predecessor run is separate failure evidence: Persvati run
`run-20260921T185156Z-c3f5`, manifest directory
`certify-20260921T185201Z-2954647`, first failed at
`FN-STX-BYTES-ITEM-IS-A-CBOR-VALUE` after the repaired statement book passed.
It does not support the passing claim above.
