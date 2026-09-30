# Checkpoint parser completion source API

The source-only supporting books are `store-tree-size`, `history-decode-size` and
`history-decode-completion`. `fn-hds-completion(n, bundle, expected)` accepts
`n=0`, `n=6` or `n=7`. It checks the parser-completion bundle, exact source
token, parser state, epoch and capture lease before delegating to
`fn-hds-result`. Success returns the borrowed descriptor, root carry, selected
field carries, epoch and lease. Pending, refused and unavailable stay distinct.

The checkpoint provider retains the four-result parser continuation and emits
`(:parser-completion source4 parserstate infos nilprefix usable)`. The actual
`fnn-snapshot-job-source-step` consumer retains that completion after the
authenticated source4 row join. Restart/open needs N6 identity or N7 consumer
field carries from this API. The provider must authenticate Store columns,
padding and MKEY before emitting a bundle; this API does not establish those
checks or reconstruct them from a node.

The accompanying original evidence is source admission only. Provider guards,
progress/refinement, native installation, bootstrap and crash/recovery joins
remain open. No certification, image qualification, full restart/install
completion or parser-provenance claim is transferred by this source packet.
