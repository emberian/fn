(include-book "records-invariants")

(defun fn-cfg-row-replace-key-loop (rows row acc)
  (declare (xargs :guard t))
  (if (consp rows)
      (if (equal (fn-cfg-row-a (car rows)) (fn-cfg-row-a row))
          (fn-ag-rev-onto acc (cons row (cdr rows)))
        (fn-cfg-row-replace-key-loop (cdr rows) row (cons (car rows) acc)))
    (fn-ag-rev-onto acc (list row))))

(defun fn-cfg-row-replace-key (rows row)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp rows)
           (if (equal (fn-cfg-row-a (car rows)) (fn-cfg-row-a row))
               (cons row (cdr rows))
             (cons (car rows) (fn-cfg-row-replace-key (cdr rows) row)))
         (list row))
       :exec (fn-cfg-row-replace-key-loop rows row nil)))

(defthm fn-cfg-row-replace-key-loop-is-rev-onto
  (equal (fn-cfg-row-replace-key-loop rows row acc)
         (fn-ag-rev-onto acc (fn-cfg-row-replace-key rows row)))
  :hints (("Goal" :induct (fn-cfg-row-replace-key-loop rows row acc)
                  :in-theory (union-theories
                              '(fn-cfg-row-replace-key-loop fn-cfg-row-replace-key fn-ag-rev-onto not car-cons cdr-cons)
                              (theory 'minimal-theory)))))

(verify-guards fn-cfg-row-replace-key
  :hints (("Goal" :in-theory (union-theories
                              '(fn-cfg-row-replace-key fn-ag-rev-onto fn-cfg-row-replace-key-loop-is-rev-onto)
                              (union-theories (theory 'minimal-theory)
                                              (executable-counterpart-theory :here))))))

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
