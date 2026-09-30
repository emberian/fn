# Function prefix registry

Every executable definition in `books/` carries a `fn-` prefix followed by a
layer tag. This table is the authoritative map from tag to book and meaning.
Add a row before introducing a tag; a tag with no row is a review finding.
Counts are not maintained here; `tools/ledger.py` reports them.

| Tag | Books | Meaning |
| --- | --- | --- |
| `pgs-dc-`, `pgs-dcr-`, `pgs-dcb-`, `pgs-dbr-` | `pagestore-digest-cursor`, `pagestore-digest-cursor-refinement`, `pagestore-digest-byte-cursor`, `pagestore-digest-byte-refinement` | Bounded page and byte digest continuation; conditional phase/terminal proof vocabulary; full supported trajectory source proofs in pgs-dcs, producer/funding composition remains open. |
| `fn-hsr-` | `history-page-reader`, `history-page-reader-verdict` | Selected page-entry scanner and canonical word verdict components; authentication/controller composition remains open. |
| `fn-rfh-` | `refusal-headroom` | Reference iteration over actual reserve/refuse subjects; exact finite identity consumption, without rescue preservation claim. |
| `fn-nlpc-` | `legacy-parser-composition` | Arbitrary-source acceptance composition of the actual legacy byte machine and article parser; logical proof vocabulary |

- `pgs-dcs-`: proof-only complete page/byte digest cursor semantics and progress
  (`pagestore-digest-cursor-semantics.lisp`); source spans and potentials never
  execute on the served path.
