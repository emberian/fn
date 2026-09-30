; Source constructor census for one actual retained consumer-entry tick.
; This is a proof operational model, not runtime heap/precharge authority.
(in-package "ACL2")
(include-book "consumer-entry-preparation")

; Actual FnCAACListCons invokes FnCAITSize on HEAD twice and selected tail
; once. Each invalid/NIL normalization allocates a fresh fixed3 NIL carry.
; The changed SCS carry and list metadata each allocate another fixed3 spine.
(defun fn-apr-entry-list-cons-cells (head-carry tail-metadata)
 (declare (xargs :guard t))
 (+ 6 (if (fn-scs-carryp head-carry) 0 6)
      (if (fn-scs-carryp (fn-cp-nth 0 tail-metadata)) 0 3)))

; Ghost instrumented boundary: unchanged actual constructor calls/branch order.
; Counts ordinary list/cons constructions of the source step only; the MV
; instrumentation is not served, and its own representation is not counted.
(defun fn-apr-entry-tick-source-execution (cursor)
 (declare (xargs :guard t))
 (let* ((key (fn-cp-nth 1 cursor)) (remaining (fn-cp-nth 2 cursor))
        (rm (fn-cp-nth 3 cursor)) (reversed (fn-cp-nth 4 cursor))
        (vm (fn-cp-nth 5 cursor)) (phase (fn-cp-nth 6 cursor))
        (rebuilt (fn-cp-nth 7 cursor)) (bm (fn-cp-nth 8 cursor))
        (old (fn-cp-nth 9 cursor)) (oc (fn-cp-nth 10 cursor)))
  (cond
   ((eq phase :ready) (mv (list :ready cursor) 2))
   ((eq phase :seek)
    (if (not (consp remaining))
        (mv (list :yield (fn-cep-state key nil nil reversed vm :reverse nil nil nil nil)) 13)
      (let ((head (fn-ag-car remaining)) (hc (fn-cp-nth 1 rm)) (tailm (fn-cp-nth 2 rm)))
       (if (equal key (fn-cp-nth 1 head))
           (mv (list :yield (fn-cep-state key nil nil reversed vm :reverse
                                      (fn-ag-cdr remaining) tailm head hc)) 13)
         (mv (list :yield (fn-cep-state key (fn-ag-cdr remaining) tailm
                                   (cons head reversed) (fn-caac-list-cons hc vm)
                                   :seek nil nil nil nil))
             (+ 14 (fn-apr-entry-list-cons-cells hc vm)))))))
   ((eq phase :reverse)
    (if (not (consp reversed))
        (mv (list :ready (fn-cep-state key nil nil nil nil :ready rebuilt bm old oc)) 13)
      (mv (list :yield (fn-cep-state key nil nil (fn-ag-cdr reversed) (fn-cp-nth 2 vm)
                                :reverse (cons (fn-ag-car reversed) rebuilt)
                                (fn-caac-list-cons (fn-cp-nth 1 vm) bm) old oc))
          (+ 14 (fn-apr-entry-list-cons-cells (fn-cp-nth 1 vm) bm)))))
   (t (mv '(:refused :consumer-preparation-phase) 0)))))

(defthm fn-apr-entry-tick-has-complete-actual-result
 (equal (mv-nth 0 (fn-apr-entry-tick-source-execution cursor)) (fn-cep-tick cursor))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories
   '(fn-apr-entry-tick-source-execution fn-cep-tick fn-ag-car fn-ag-cdr
     mv-nth car-cons cdr-cons) (theory 'minimal-theory)))))

(defthm fn-apr-entry-tick-source-constructors-are-bounded
 (and (natp (mv-nth 1 (fn-apr-entry-tick-source-execution cursor)))
      (<= (mv-nth 1 (fn-apr-entry-tick-source-execution cursor)) 29))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-apr-entry-tick-source-execution
                                    fn-apr-entry-list-cons-cells)
   (fn-cp-nth fn-scs-carryp fn-cep-state fn-caac-list-cons fn-ag-car fn-ag-cdr)))))

; 29 is derived from actual fixed source constructors, not a stored-data cap.
; It excludes numerical temporary allocation/operand widths, bounded-ID
; comparison work, frames, allocator/cache/TLS/GC and issuer/callback spines.
; Borrowed old prefix/suffix/carry roots retain prior ownership through the
; operation's BASE/retirement join. Canonical bytes never price those heaps.
(in-theory (disable fn-apr-entry-list-cons-cells fn-apr-entry-tick-source-execution))
