; Teeth for the FNCR connection class's funding and read admission
; (books/consumer-remote-operation-source.lisp; D48 / PKT-673).
(in-package "ACL2")
(include-book "../../books/consumer-remote-operation-source")

(defconst *crot-stack* 2097152)

; Two sessions: both draw, a third is refused by name with the ledger
; unchanged, a settled one frees its slot, a stale token settles nothing,
; and reads are admitted only on a live draw within the frame bound.
(defun crot-run (fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :verify-guards nil))
  (mv-let (w0 fn-resource-ledger) (fn-crf-install 2 *crot-stack* fn-resource-ledger)
   (mv-let (w1 t1 fn-resource-ledger) (fn-crf-open fn-resource-ledger)
    (mv-let (w2 t2 fn-resource-ledger) (fn-crf-open fn-resource-ledger)
     (mv-let (w3 t3 fn-resource-ledger) (fn-crf-open fn-resource-ledger)
      (let ((header (fn-owner-remote-operation-preflight :remote-header 10 t1 fn-resource-ledger))
            (frame (fn-owner-remote-operation-preflight
                    :remote-frame (- (fn-crf-frame-octets) 10) t1 fn-resource-ledger))
            (over (fn-owner-remote-operation-preflight
                   :remote-frame (- (fn-crf-frame-octets) 9) t1 fn-resource-ledger))
            (kind (fn-owner-remote-operation-preflight :owner-admin 10 t1 fn-resource-ledger))
            (drained-before (fn-crf-drainedp fn-resource-ledger)))
       (mv-let (c1 fn-resource-ledger) (fn-crf-close t1 fn-resource-ledger)
        (let ((stale-read (fn-owner-remote-operation-preflight :remote-header 10 t1
                                                                fn-resource-ledger)))
         (mv-let (c1b fn-resource-ledger) (fn-crf-close t1 fn-resource-ledger)
          (mv-let (w4 t4 fn-resource-ledger) (fn-crf-open fn-resource-ledger)
           (mv-let (c2 fn-resource-ledger) (fn-crf-close t2 fn-resource-ledger)
            (mv-let (c4 fn-resource-ledger) (fn-crf-close t4 fn-resource-ledger)
             (mv (list w0 w1 w2 w3 t3 header frame over kind drained-before c1 stale-read
                       c1b w4 c2 c4 (fn-crf-drainedp fn-resource-ledger)
                       (nth 1 t1) (nth 1 t2) (nth 1 t4))
                 fn-resource-ledger)))))))))))))

(defun crot-answers ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-resource-ledger
    (mv-let (answers fn-resource-ledger) (crot-run fn-resource-ledger)
      answers)))

(assert-event
 (equal (crot-answers)
        (list :installed :drawn :drawn :sessions nil
              '(:admitted) '(:admitted) '(:refused :remote-frame-size)
              '(:refused :remote-operation-kind) nil
              :settled '(:refused :remote-connection-unfunded) :stale
              :drawn :settled :settled t
              2 3 2)))

; An unfunded token: no draw, no read.
(assert-event
 (equal (fn-cro-read-plan :remote-header 10 nil) '(:refused :remote-connection-unfunded)))
; The class refuses an unbounded or empty session count before any store.
(defun crot-install-zero ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-resource-ledger
    (mv-let (w fn-resource-ledger) (fn-crf-install 0 *crot-stack* fn-resource-ledger) w)))
(assert-event (equal (crot-install-zero) :invalid-remote-sessions))
