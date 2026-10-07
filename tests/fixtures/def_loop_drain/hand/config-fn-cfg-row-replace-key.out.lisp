(include-book "records-invariants")
(include-book "def-loop")

(def-loop fn-cfg-row-replace-key (rows row)
  :shape :map :over rows :elt r
  :stop (equal (fn-cfg-row-a r) (fn-cfg-row-a row))
  :stop-value (cons row (cdr rows)) :tail (list row)
  :body r)

; The peer table is the peers row list keyed by row-a (the peer name); one
; peer is the group of rows sharing that key (specs/peering.md section 1.2,
; books/peer-config.lisp decodes the group into the typed record).  Three total
; helpers over a keyed row group: select, remove, and the recognizer that
; every row of a delta names the peer the delta names.
;
; `fn-cfg-rows-with-key' walks the whole peer table (every peer's rows; D27:
; no row cap, PRF-171), so it executes by a loop (lane config-and-legacy,
; after peer-list-depth's twin in books/native-admin-peer-budget): the :logic
; is the recursion, unchanged; the :exec collects onto an accumulator.
(def-loop fn-cfg-rows-with-key (rows a)
  :shape :map :over rows :elt r
  :keep (equal (fn-cfg-row-a r) a)
  :body r)
