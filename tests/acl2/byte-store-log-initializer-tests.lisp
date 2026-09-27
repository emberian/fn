; Witnesses for books/byte-store-log-initializer.lisp (lane log-2): the
; format-9 developer initializer's program, run on the empty byte store.
; Its hypotheses are fn-bsi-current-init-program's input contract (octet
; frames, staging names) and a positive extent; no hypothesis-removal
; counterexample was found (extent 0 and non-octet frames still satisfy
; the conclusion concretely) and the weakened theorem was not proved, so
; they stay (AGENTS.md: failed proof search is not a counterexample).
(in-package "ACL2")
(include-book "../../books/byte-store-log-initializer")

(defun bsli-final () (declare (xargs :guard t :verify-guards nil))
  (fn-bsi-log-final '(1 2 3) '(4 5) ".init-1" ".init-2" 16))

; The theorem's antecedent holds of this input.
(assert-event (and (fn-cbor-octet-listp '(1 2 3)) (fn-cbor-octet-listp '(4 5))
                   (fn-bs-namep ".init-1") (fn-bs-namep ".init-2") (posp 16)))
; Its conclusion, by evaluation of the whole run.
(assert-event
 (let* ((s (bsli-final)) (seg (fn-bs-durable-entry s :journal "000001.log")))
   (and (equal (fn-bs-durable-entry s :root "journal") :journal)
        seg
        (equal (fn-bs-durable-content s seg) (fn-bs-zeros 16))
        (equal (fn-bs-durable-content s (fn-bs-durable-entry s :root *fn-bs-config-name*)) '(1 2 3))
        (equal (fn-bs-durable-content s (fn-bs-durable-entry s :config *fn-bsi-config-record-name*)) '(4 5))
        (null (fn-bs-durable-entry s :root *fn-bs-frontier-name*))
        (null (fn-bs-durable-entry s :root "transactions")))))
; Every step ran: the run is as long as the program.
(assert-event
 (equal (len (fn-bs-run *fn-bs-empty-store* (fn-sf-initial-state)
                        (fn-bsi-log-init-program '(1 2 3) '(4 5) ".init-1" ".init-2" 16)
                        nil nil nil))
        (len (fn-bsi-log-init-program '(1 2 3) '(4 5) ".init-1" ".init-2" 16))))
; A death at the history fence (the run's prefix to that cut) leaves no
; segment: the open refuses by name ("no log segment") and init runs again.
(assert-event
 (let* ((prog (fn-bsi-log-init-program '(1 2 3) '(4 5) ".init-1" ".init-2" 16))
        (k (- (len prog) 16))
        (run (fn-bs-run *fn-bs-empty-store* (fn-sf-initial-state) (take k prog) nil nil nil))
        (s (fn-bs-crash (car (car (last run))) nil)))
   (and (equal (nth (1- k) prog) '(:cut "init-config-history-fenced"))
        (null (fn-bs-durable-entry s :journal "000001.log")))))
