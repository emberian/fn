; Witnesses for books/store-open-replay-refusal (a replay that stops refuses
; the open by name).  The history is config-physical-replay-tests' (a
; retention undertaking and its release, then an article of charge 2 at txid
; 7); the configuration decides whether it fits.
;   (1) REACHABLE, the capacity stop: the capacity is decreased to 1 and not
;       raised again; the configured replay stops at the article
;       (:event-refusal) and the refusal names it: its txid, Message-ID,
;       charge 2, the 1 unit held and the capacity 1 (the complete
;       conclusion of fn-sorr-capacity-names-the-retention-state, and
;       reserved + charge > capacity); the operator's line says so.
;   (2) REACHABLE, the open that fits: with the capacity raised to 20 the
;       replay is :ok and there is no refusal (fn-sorr-refusal-only-on-a-stop's
;       contrapositive).
;   (3) REACHABLE, another stop: an event out of sequence stops the replay
;       with :event-sequence and the refusal is :replay-stopped at that
;       position, never :capacity.
(in-package "ACL2")
(include-book "../../books/store-open-replay-refusal")
(include-book "held-rows-tests")

(defconst *sorr-t-stamp* *fn-cfg-default-stamp*)
(defconst *sorr-t-undertake*
  (fn-store-retention-event-make :undertake 0 0 0
                                 "forward-sorr" "subject" "evidence" 10))
(defconst *sorr-t-release*
  (fn-store-retention-event-make :release 1 1 1
                                 "forward-sorr" "subject" "evidence" 0))
(defconst *sorr-t-decrease*
  (fn-cfg-record-make 1 7 2 (list (fn-cfg-set-capacity 1)) *sorr-t-stamp*))
(defconst *sorr-t-increase*
  (fn-cfg-record-make 2 7 3 (list (fn-cfg-set-capacity 20)) *sorr-t-stamp*))
(defconst *sorr-t-article-wire*
  (fn-record-make 2 7 7 "<sorr@example.invalid>" '(65) '("fn.test")
                  "archive-sorr" "subject" "evidence" 2 841000000))
(defconst *sorr-t-events*
  (fn-hrt-rows (list *sorr-t-undertake* *sorr-t-release* *sorr-t-article-wire*) nil 0))

; (1) The capacity stop.
(defconst *sorr-t-tight* (list *fn-cfg-default-record* *sorr-t-decrease*))
(defconst *sorr-t-stopped* (fn-cpr-replay *sorr-t-tight* *sorr-t-events*))
(defconst *sorr-t-refusal* (fn-sorr-refusal *sorr-t-stopped* *sorr-t-events* *sorr-t-tight*))
(assert-event
 (let ((retention (fn-node-retention (fn-cnode-node (fn-replay-result-node *sorr-t-stopped*)))))
   (and (equal (fn-replay-result-kind *sorr-t-stopped*) :fault)
        (equal (fn-replay-result-reason *sorr-t-stopped*) :event-refusal)
        (equal *sorr-t-refusal*
               (list :refused :capacity 7 "<sorr@example.invalid>" 2 1 1))
        (equal (nth 6 *sorr-t-refusal*) (fn-retain-capacity retention))
        (equal (nth 5 *sorr-t-refusal*) (fn-retain-reserved retention))
        (< (nth 6 *sorr-t-refusal*) (+ (nth 5 *sorr-t-refusal*) (nth 4 *sorr-t-refusal*)))
        (equal (fn-sorr-refusal-text *sorr-t-refusal*)
               "open refused reason=capacity: the history's article <sorr@example.invalid> (txid 7) is charged 2 units and the configured capacity 1 already holds 1; this history needs a larger capacity"))))

; (2) The open that fits: no refusal.
(defconst *sorr-t-roomy* (list *fn-cfg-default-record* *sorr-t-decrease* *sorr-t-increase*))
(defconst *sorr-t-open* (fn-cpr-replay *sorr-t-roomy* *sorr-t-events*))
(assert-event
 (and (equal (fn-replay-result-kind *sorr-t-open*) :ok)
      (null (fn-sorr-refusal *sorr-t-open* *sorr-t-events* *sorr-t-roomy*))))

; (3) Another stop: the release out of sequence.
(defconst *sorr-t-swapped*
  (list (car *sorr-t-events*) (caddr *sorr-t-events*) (cadr *sorr-t-events*)))
(defconst *sorr-t-stopped-2* (fn-cpr-replay *sorr-t-roomy* *sorr-t-swapped*))
(defconst *sorr-t-refusal-2* (fn-sorr-refusal *sorr-t-stopped-2* *sorr-t-swapped* *sorr-t-roomy*))
(assert-event
 (and (equal (fn-replay-result-kind *sorr-t-stopped-2*) :fault)
      (not (equal (fn-replay-result-reason *sorr-t-stopped-2*) :event-refusal))
      (equal (car *sorr-t-refusal-2*) :refused)
      (equal (cadr *sorr-t-refusal-2*) :replay-stopped)
      (equal (caddr *sorr-t-refusal-2*) (fn-replay-result-sequence *sorr-t-stopped-2*))
      (stringp (fn-sorr-refusal-text *sorr-t-refusal-2*))))

(assert-event
 (and (eq (symbol-class 'fn-sorr-refusal (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sorr-refusal-text (w state)) :common-lisp-compliant)))
