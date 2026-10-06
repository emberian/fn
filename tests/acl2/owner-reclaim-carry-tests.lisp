; PRF-1060: exact host-called rebuild carry, reachable nonempty ledger.
(in-package "ACL2")
(include-book "../../books/owner-reclaim-carry")
(include-book "../../books/defkeystone")
(include-book "must-fail-checked")
(defconst *orc-carry-events*
  (list (fn-store-retention-event-make :undertake 0 0 0 "forward-carry" "subject" "evidence" 10)
        (fn-store-retention-event-make :release 1 1 1 "forward-carry" "subject" "evidence" 0)))
(defconst *orc-carry-configs*
  (list *fn-cfg-default-record*
        (fn-cfg-record-make 1 7 2 (list (fn-cfg-set-capacity 1)) *fn-cfg-default-stamp*)))
(defconst *orc-carry-rebuilt*
  (fn-owner-orcp-rebuild (fn-sco-capture *orc-carry-configs* *orc-carry-events*)
                         *orc-carry-configs* 8 4))
; Complete unconditional conclusion, plus reachability/nonempty evidence.
(assert-event (not (equal (nth 1 *orc-carry-rebuilt*) :fault)))
(assert-event (fn-prc-carryp (nth 2 *orc-carry-rebuilt*)))
(assert-event (consp (nth 2 *orc-carry-rebuilt*)))
(assert-event (fn-prc-has "forward-carry" (cdr (nth 2 *orc-carry-rebuilt*))))
; Corrupted-state witness: same nonempty ledger, erased index is invalid.
(assert-event (not (fn-prc-carryp (cons (car (nth 2 *orc-carry-rebuilt*)) nil))))
(must-fail-checked
 (assert-event (fn-prc-carryp (cons (car (nth 2 *orc-carry-rebuilt*)) nil))))

; TEETH-62 BEGIN
; fn-owner-orcp-rebuild-of-capture-is-the-full-open with its teeth (TEETH CONTRACT v1).
(defteeth fn-owner-orcp-rebuild-of-capture-is-the-full-open
  :claim (((rows (true-listp rows)))
          (equal (cadr (fn-owner-orcp-rebuild (fn-sco-capture configs rows)
                                               configs frontier max-conns))
                  (fn-ock-recover-full configs frontier rows max-conns)))
  :subject fn-owner-orcp-rebuild
  :witness ((rows *orc-carry-events*) (configs *orc-carry-configs*) (frontier 8) (max-conns 4))
  :breaks ((rows ((rows (append *orc-carry-events* 7)) (configs *orc-carry-configs*) (frontier 8) (max-conns 4)) :logical "a ledger whose tail is not a list: outside the guard of the fold"))
  :mutations ((rebuild-faults
               (:conclusion (equal (cadr (fn-owner-orcp-rebuild (fn-sco-capture configs rows) configs frontier max-conns)) :fault))
               ((rows *orc-carry-events*) (configs *orc-carry-configs*) (frontier 8) (max-conns 4))
               :fault "a rebuild that faults on a reachable ledger")))
