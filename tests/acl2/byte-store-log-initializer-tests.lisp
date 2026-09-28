; Witnesses for books/byte-store-log-initializer.lisp (lane log-2): the
; format-9 developer initializer's program, run on the empty byte store.
; Its hypotheses (audit packet G4-5, lane audit-fixes): the two staging
; names were dropped from the keystone after proving the weakened theorem;
; the octet frames each have a counterexample (a dotted frame, below); the
; consp conjuncts are redundant (the weakened theorem proved in a REPL probe
; in 90 s, too slow for the book under D26, so they stay in the library
; statement); (posp extent) has no counterexample (extent 0, -3 and 5/2
; each satisfy the conclusion, evaluated below) and its weakened theorem was
; not found (a 105 s search stopped), so it stays, untoothed.
(in-package "ACL2")
(include-book "../../books/byte-store-log-initializer")

(defun bsli-final () (declare (xargs :guard t :verify-guards nil))
  (fn-bsi-log-final '(1 2 3) '(4 5) ".init-1" ".init-2" 16 '(6 7) ".init-3"))

; The theorem's antecedent holds of this input.
(assert-event (and (fn-cbor-octet-listp '(1 2 3)) (fn-cbor-octet-listp '(4 5))
                   (fn-bs-namep ".init-1") (fn-bs-namep ".init-2") (posp 16)))
; Its conclusion, by evaluation of the whole run.
(assert-event
 (let* ((s (bsli-final)) (seg (fn-bs-durable-entry s :journal "000001.log")))
   (and (equal (fn-bs-durable-entry s :root "journal") :journal)
        seg
        (equal (fn-bs-durable-content s seg) (fn-bs-zeros 16))
        (equal (fn-bs-durable-content s (fn-bs-durable-entry s :journal "000000.log")) '(6 7))
        (equal (fn-bs-durable-content s (fn-bs-durable-entry s :root *fn-bs-config-name*)) '(1 2 3))
        (equal (fn-bs-durable-content s (fn-bs-durable-entry s :config *fn-bsi-config-record-name*)) '(4 5))
        (null (fn-bs-durable-entry s :root *fn-bs-frontier-name*))
        (null (fn-bs-durable-entry s :root "transactions")))))
; Every step ran: the run is as long as the program.
(assert-event
 (equal (len (fn-bs-run *fn-bs-empty-store* (fn-sf-initial-state)
                        (fn-bsi-log-init-program '(1 2 3) '(4 5) ".init-1" ".init-2" 16 '(6 7) ".init-3")
                        nil nil nil))
        (len (fn-bsi-log-init-program '(1 2 3) '(4 5) ".init-1" ".init-2" 16 '(6 7) ".init-3"))))
; A death at the history fence (the run's prefix to that cut) leaves no
; segment: the open refuses by name ("no log segment") and init runs again.
(assert-event
 (let* ((prog (fn-bsi-log-init-program '(1 2 3) '(4 5) ".init-1" ".init-2" 16 '(6 7) ".init-3"))
        (k (- (len prog) 30))
        (run (fn-bs-run *fn-bs-empty-store* (fn-sf-initial-state) (take k prog) nil nil nil))
        (s (fn-bs-crash (car (car (last run))) nil)))
   (and (equal (nth (1- k) prog) '(:cut "init-config-history-fenced"))
        (null (fn-bs-durable-entry s :journal "000001.log"))
        (null (fn-bs-durable-entry s :journal "000000.log")))))

; -----------------------------------------------------------------------------
; Audit packet G4-5 (lane audit-fixes).
(defun bsli-concl (config config-record config-stage record-stage extent
                    genesis genesis-stage)
  (declare (xargs :verify-guards nil))
  (let* ((s (fn-bsi-log-final config config-record config-stage record-stage extent
                            genesis genesis-stage))
         (seg (fn-bs-durable-entry s :journal "000001.log")))
    (and (equal (fn-bs-durable-entry s :root "journal") :journal)
         seg
         (equal (fn-bs-durable-content s seg) (fn-bs-zeros extent))
         (equal (fn-bs-durable-content s (fn-bs-durable-entry s :journal "000000.log")) genesis)
         (equal (fn-bs-durable-content s (fn-bs-durable-entry s :root *fn-bs-config-name*)) config)
         (equal (fn-bs-durable-content s (fn-bs-durable-entry s :config *fn-bsi-config-record-name*))
                config-record)
         (null (fn-bs-durable-entry s :root *fn-bs-frontier-name*))
         (null (fn-bs-durable-entry s :root "transactions")))))
(assert-event (bsli-concl '(1 2 3) '(4 5) ".init-1" ".init-2" 16 '(6 7) ".init-3"))
; Removal of (fn-cbor-octet-listp config): a dotted configuration (a cons,
; every other hypothesis holds) is not what the store reads back.
(assert-event (and (not (fn-cbor-octet-listp '(1 2 . 3))) (consp '(1 2 . 3))
                   (not (bsli-concl '(1 2 . 3) '(4 5) ".init-1" ".init-2" 16 '(6 7) ".init-3"))))
; Removal of (fn-cbor-octet-listp config-record): the same for the record.
(assert-event (and (not (fn-cbor-octet-listp '(4 . 5))) (consp '(4 . 5))
                   (not (bsli-concl '(1 2 3) '(4 . 5) ".init-1" ".init-2" 16 '(6 7) ".init-3"))))
; The staging names are free: non-string names still establish the log.
(assert-event (bsli-concl '(1 2 3) '(4 5) 7 'x 16 '(6 7) 9))
; (posp extent) and the consp conjuncts: no counterexample among these.
(assert-event (and (bsli-concl '(1 2 3) '(4 5) ".init-1" ".init-2" 0 '(6 7) ".init-3")
                   (bsli-concl nil '(4 5) ".init-1" ".init-2" 16 '(6 7) ".init-3")))
(defthm bsli-extent-candidates-hold ; ground, by evaluation (guards differ)
  (and (bsli-concl '(1 2 3) '(4 5) ".init-1" ".init-2" -3 '(6 7) ".init-3")
       (bsli-concl '(1 2 3) '(4 5) ".init-1" ".init-2" 5/2 '(6 7) ".init-3"))
  :rule-classes nil)
; Removal of (fn-cbor-octet-listp genesis): a dotted genesis (a cons, every
; other hypothesis holds) is not what the store reads back.
(assert-event (and (not (fn-cbor-octet-listp '(6 . 7))) (consp '(6 . 7))
                   (not (bsli-concl '(1 2 3) '(4 5) ".init-1" ".init-2" 16 '(6 . 7) ".init-3"))))
; The genesis is published before segment 1: a death at its journal/ fence
; leaves the genesis durable and no segment.
(assert-event
 (let* ((prog (fn-bsi-log-init-program '(1 2 3) '(4 5) ".init-1" ".init-2" 16 '(6 7) ".init-3"))
        (k (- (len prog) 16))
        (run (fn-bs-run *fn-bs-empty-store* (fn-sf-initial-state) (take k prog) nil nil nil))
        (s (fn-bs-crash (car (car (last run))) nil)))
   (and (equal (nth (1- k) prog) '(:cut "init-genesis-journal-fenced"))
        (equal (fn-bs-durable-content s (fn-bs-durable-entry s :journal "000000.log")) '(6 7))
        (null (fn-bs-durable-entry s :journal "000001.log")))))
