; Teeth for books/resource-vector (lane resource-ledger, 2026-10-01;
; deputy-1 after Codex review r06): a small node's root bank -- the owner's
; baseline and reserve drawn first, a connection's sub-bank partitioned from
; it, reads drawn on the connection with their completion tokens, a refund,
; a settle and its stale second settle, a completion replayed after the slot
; was drawn again (:stale, the ABA), the identity coordinate exhausted while
; every octet has returned, the connection destroyed and exactly its unspent
; budget returning, the reserve growing by dW+ before an acceptance,
; refusals by name with the bank unchanged -- and each keystone with its
; hypotheses shown necessary (defkeystone).
(in-package "ACL2")
(include-book "../../books/resource-vector")
(include-book "../../books/defkeystone")
(include-book "must-fail-checked")
(include-book "std/testing/assert-bang" :dir :system)

(assert! (equal *fn-rv-k* 9))
(assert! (equal (fn-rv-index :resident) 0))
(assert! (equal (fn-rv-index :read-ids) 4))
(assert! (equal (fn-rv-index :work) 8))
(assert! (not (fn-rv-index :tapes)))
(assert! (equal *fn-rv-reusable-mask* '(1 1 1 1 0 0 0 0 0)))

(defconst *rvt-mib* 1048576)

;; B(P): 256 MiB resident, 4 GiB disk, 64 descriptors, 8 workers, 1,000
;; read identities, 10^6 transaction identities, 100 configuration
;; generations, 10^4 connection identities, 10^6 work units.
(defconst *rvt-budget*
  (list (* 256 *rvt-mib*) (* 4096 *rvt-mib*) 64 8 1000 1000000 100 10000 1000000))
;; U, the owner's permanent baseline: the image, the threads, the
;; collector's headroom; the log's descriptor; the owner's worker.
(defconst *rvt-baseline* (list (* 160 *rvt-mib*) 0 1 1 0 0 0 0 0))
;; R, the maintenance reserve: the next image and the active segment, the
;; release record's transaction identity and configuration generation.
(defconst *rvt-reserve* (list (* 16 *rvt-mib*) (* 512 *rvt-mib*) 2 1 0 1 1 0 100000))

(defconst *rvt-root* (cadr (fn-rv-install *rvt-budget* *rvt-baseline* *rvt-reserve* 8)))
(assert! (equal (car (fn-rv-install *rvt-budget* *rvt-baseline* *rvt-reserve* 8)) :installed))
(assert! (fn-rv-okp *rvt-root*))
(assert! (equal (fn-rv-drawn *rvt-root*) (fn-rv-plus *rvt-baseline* *rvt-reserve*)))
;; The rows carry their generation: the first charge of a fresh slot is 1.
(assert! (equal (fn-rv-row 0 *rvt-root*) (list* 1 1 *rvt-baseline*)))
(assert! (equal (fn-rv-row 1 *rvt-root*) (list* 2 1 *rvt-reserve*)))
(assert! (equal (fn-rv-gen 1 *rvt-root*) 1))
(assert! (equal (fn-rv-slot-count *rvt-root*) 8))
;; A start that cannot fund the reserve is refused by the draw's word.
(assert! (equal (identity (fn-rv-install *rvt-baseline* *rvt-baseline* *rvt-reserve* 8))
                (list :resources-unavailable nil)))
(assert! (equal (identity (fn-rv-install *rvt-budget* *rvt-baseline* *rvt-reserve* 1))
                (list :invalid-install nil)))

;; A connection's sub-bank (M7's per-connection budget): 4 MiB resident, no
;; disk, the socket, a worker, ten read identities, one connection identity,
;; 10^4 work.  The open answers the sub-bank's token, generation 1.
(defconst *rvt-conn-budget* (list (* 4 *rvt-mib*) 0 1 1 10 0 0 1 10000))
(defconst *rvt-root2* (cadr (fn-rv-open *rvt-root* 2 *rvt-conn-budget*)))
(assert! (equal (car (fn-rv-open *rvt-root* 2 *rvt-conn-budget*)) :opened))
(assert! (equal (caddr (fn-rv-open *rvt-root* 2 *rvt-conn-budget*)) 1))
(assert! (fn-rv-okp *rvt-root2*))
(assert! (equal (fn-rv-row 2 *rvt-root2*) (list* 2 1 *rvt-conn-budget*)))
;; The connection's own bank, partitioned from the root.
(defconst *rvt-conn* (fn-rv-make *rvt-conn-budget* *fn-rv-zero* (fn-rv-idle-rows 4)))
(assert! (fn-rv-okp *rvt-conn*))

;; A read: 64 KiB resident, one read identity, 1,000 work.  Its token is
;; the slot's new generation, 1.
(defconst *rvt-read* (list 65536 0 0 0 1 0 0 0 1000))
(defconst *rvt-conn1* (cadr (fn-rv-draw *rvt-conn* 0 *rvt-read*)))
(assert! (equal (car (fn-rv-draw *rvt-conn* 0 *rvt-read*)) :drawn))
(assert! (equal (caddr (fn-rv-draw *rvt-conn* 0 *rvt-read*)) 1))
(assert! (fn-rv-okp *rvt-conn1*))
(assert! (equal (fn-rv-drawn *rvt-conn1*) *rvt-read*))
(assert! (fn-rv-drawnp 0 1 *rvt-conn1*))
;; The same slot again: busy, the bank itself returned.
(assert! (equal (identity (fn-rv-draw *rvt-conn1* 0 *rvt-read*)) (list :slot-busy *rvt-conn1*)))
;; Past the budget: refused by name, the bank itself returned; exactly at
;; the budget: admitted.
(defconst *rvt-past* (list (* 4 *rvt-mib*) 0 0 0 0 0 0 0 0))
(defconst *rvt-exact* (list (- (* 4 *rvt-mib*) 65536) 0 0 0 0 0 0 0 0))
(assert! (equal (identity (fn-rv-draw *rvt-conn1* 1 *rvt-past*))
                (list :resources-unavailable *rvt-conn1*)))
(assert! (equal (car (fn-rv-draw *rvt-conn1* 1 *rvt-exact*)) :drawn))
(assert! (equal (fn-rv-slack (cadr (fn-rv-draw *rvt-conn1* 1 *rvt-past*)))
                (fn-rv-slack *rvt-conn1*)))
(assert! (equal (identity (fn-rv-draw *rvt-conn1* 9 *rvt-read*)) (list :invalid-draw *rvt-conn1*)))
(assert! (equal (identity (fn-rv-draw *rvt-conn1* 1 '(1 2 3))) (list :invalid-draw *rvt-conn1*)))

;; Refund: the read needed 4 KiB less than it charged.  The token names it.
(defconst *rvt-conn1r* (cadr (fn-rv-refund *rvt-conn1* 0 1 (list 4096 0 0 0 0 0 0 0 0))))
(assert! (equal (car (fn-rv-refund *rvt-conn1* 0 1 (list 4096 0 0 0 0 0 0 0 0))) :refunded))
(assert! (equal (fn-rv-demand 0 *rvt-conn1r*) (list 61440 0 0 0 1 0 0 0 1000)))
(assert! (equal (fn-rv-drawn *rvt-conn1r*) (list 61440 0 0 0 1 0 0 0 1000)))
(assert! (equal (fn-rv-gen 0 *rvt-conn1r*) 1))
(assert! (fn-rv-okp *rvt-conn1r*))
;; A spent coordinate never refunds; more than the draw holds is refused;
;; a wrong token is :stale.
(assert! (equal (identity (fn-rv-refund *rvt-conn1* 0 1 (list 0 0 0 0 1 0 0 0 0)))
                (list :past-what-it-holds *rvt-conn1*)))
(assert! (equal (identity (fn-rv-refund *rvt-conn1* 0 1 (list 65537 0 0 0 0 0 0 0 0)))
                (list :past-what-it-holds *rvt-conn1*)))
(assert! (equal (identity (fn-rv-refund *rvt-conn1* 1 1 (list 1 0 0 0 0 0 0 0 0)))
                (list :stale *rvt-conn1*)))
(assert! (equal (identity (fn-rv-refund *rvt-conn1* 0 2 (list 1 0 0 0 0 0 0 0 0)))
                (list :stale *rvt-conn1*)))

;; Settle: the octets return; the read identity and the work stay drawn;
;; the slot idles and keeps its generation.
(defconst *rvt-conn2* (cadr (fn-rv-settle *rvt-conn1r* 0 1)))
(assert! (equal (car (fn-rv-settle *rvt-conn1r* 0 1)) :settled))
(assert! (equal (fn-rv-drawn *rvt-conn2*) (list 0 0 0 0 1 0 0 0 1000)))
(assert! (equal (fn-rv-row 0 *rvt-conn2*) (fn-rv-idle-row 1)))
(assert! (equal (fn-rv-phase 0 *rvt-conn2*) 0))
(assert! (fn-rv-okp *rvt-conn2*))
;; Settle once: the second settle is :stale and leaves the bank; so is a
;; settle with the wrong token.
(assert! (equal (identity (fn-rv-settle *rvt-conn2* 0 1)) (list :stale *rvt-conn2*)))
(assert! (equal (identity (fn-rv-settle *rvt-conn1r* 0 2)) (list :stale *rvt-conn1r*)))
(assert! (equal (identity (fn-rv-settle *rvt-conn2* 7 1)) (list :invalid-slot *rvt-conn2*)))

;; The ABA (Codex r06 F2): the slot drawn again (token 2); the first
;; completion (token 1) replayed is :stale and leaves the bank; the live
;; token settles.
(defconst *rvt-conn3* (cadr (fn-rv-draw *rvt-conn2* 0 *rvt-read*)))
(assert! (equal (caddr (fn-rv-draw *rvt-conn2* 0 *rvt-read*)) 2))
(assert! (equal (identity (fn-rv-settle *rvt-conn3* 0 1)) (list :stale *rvt-conn3*)))
(assert! (equal (car (fn-rv-settle *rvt-conn3* 0 2)) :settled))

;; Ten reads spend the ten read identities; the eleventh is refused by that
;; coordinate although every octet has returned (identities never refund).
(defun rvt-read-and-settle (bank n)
  (declare (xargs :mode :program))
  (if (zp n)
      bank
    (let ((d (fn-rv-draw bank 0 *rvt-read*)))
      (rvt-read-and-settle (cadr (fn-rv-settle (cadr d) 0 (caddr d))) (1- n)))))
(defconst *rvt-conn-spent* (rvt-read-and-settle *rvt-conn* 10))
(assert! (fn-rv-okp *rvt-conn-spent*))
(assert! (equal (fn-rv-gen 0 *rvt-conn-spent*) 10))
(assert! (equal (fn-rv-drawn *rvt-conn-spent*) (list 0 0 0 0 10 0 0 0 10000)))
(assert! (equal (identity (fn-rv-draw *rvt-conn-spent* 0 *rvt-read*))
                (list :resources-unavailable *rvt-conn-spent*)))
(assert! (equal (fn-rv-spent (fn-rv-drawn *rvt-conn-spent*)) (list 0 0 0 0 10 0 0 0 10000)))
(assert! (equal (fn-rv-reusable (fn-rv-drawn *rvt-conn-spent*)) *fn-rv-zero*))

;; Destroy: the connection closes.  The root gets back the connection's
;; budget less what it spent (ten read identities, 10^4 work), exactly.
(defconst *rvt-spent* (fn-rv-spent (fn-rv-drawn *rvt-conn-spent*)))
(defconst *rvt-root3* (cadr (fn-rv-destroy *rvt-root2* 2 1 *rvt-spent*)))
(assert! (equal (car (fn-rv-destroy *rvt-root2* 2 1 *rvt-spent*)) :destroyed))
(assert! (fn-rv-okp *rvt-root3*))
(assert! (equal (fn-rv-phase 2 *rvt-root3*) 0))
(assert! (equal (fn-rv-slack *rvt-root3*)
                (fn-rv-plus (fn-rv-slack *rvt-root2*) (fn-rv-monus *rvt-conn-budget* *rvt-spent*))))
(assert! (equal (fn-rv-drawn *rvt-root3*) (fn-rv-plus (fn-rv-drawn *rvt-root*) *rvt-spent*)))
;; Destroying it again, or a drawn slot, or with the wrong token, or with
;; more spent than its budget allowed: refused, the bank itself returned.
(assert! (equal (identity (fn-rv-destroy *rvt-root3* 2 1 *rvt-spent*)) (list :stale *rvt-root3*)))
(assert! (equal (identity (fn-rv-destroy *rvt-root3* 0 1 *fn-rv-zero*)) (list :stale *rvt-root3*)))
(assert! (equal (identity (fn-rv-destroy *rvt-root2* 2 2 *rvt-spent*)) (list :stale *rvt-root2*)))
(assert! (equal (identity (fn-rv-destroy *rvt-root2* 2 1 (list 0 0 0 0 11 0 0 0 0)))
                (list :sub-bank-overspent *rvt-root2*)))
(assert! (equal (identity (fn-rv-destroy *rvt-root2* 2 1 (list 1 0 0 0 0 0 0 0 0)))
                (list :sub-bank-overspent *rvt-root2*)))

;; dW+ before an acceptance: the reserve grows by the checkpoint estimate's
;; 4 KiB of disk and one transaction identity, refused past the budget.
(defconst *rvt-dw* (list 0 4096 0 0 0 1 0 0 0))
(defconst *rvt-root4* (cadr (fn-rv-grow *rvt-root3* 1 1 *rvt-dw*)))
(assert! (equal (car (fn-rv-grow *rvt-root3* 1 1 *rvt-dw*)) :grown))
(assert! (equal (fn-rv-demand 1 *rvt-root4*) (fn-rv-plus *rvt-reserve* *rvt-dw*)))
(assert! (equal (fn-rv-gen 1 *rvt-root4*) 1))
(assert! (fn-rv-okp *rvt-root4*))
(assert! (equal (identity (fn-rv-grow *rvt-root3* 1 1 (list 0 (* 4096 *rvt-mib*) 0 0 0 0 0 0 0)))
                (list :resources-unavailable *rvt-root3*)))
(assert! (equal (identity (fn-rv-grow *rvt-root3* 0 1 *rvt-dw*)) (list :stale *rvt-root3*)))
(assert! (equal (identity (fn-rv-grow *rvt-root3* 1 2 *rvt-dw*)) (list :stale *rvt-root3*)))

;; A user's step never touches the reserve; a run of refused steps leaves
;; the bank, each refusal by name.
(assert! (equal (fn-rv-row 1 (cadr (fn-rv-step *rvt-root4* (list :open 3 *rvt-conn-budget*))))
                (fn-rv-row 1 *rvt-root4*)))
(defconst *rvt-refused-run*
  (list (list :settle 1 1) (list :destroy 0 1 *fn-rv-zero*) (list :draw 1 *rvt-read*)
        (list :grow 0 1 *rvt-dw*) (list :refund 1 1 *rvt-dw*) (list :draw 99 *rvt-read*)
        (list :open 3 *rvt-budget*) (list :settle 0 2) (list :sleep 3)))
(assert! (equal (cadr (fn-rv-run *rvt-root4* *rvt-refused-run*)) *rvt-root4*))
(assert! (equal (car (fn-rv-run *rvt-root4* *rvt-refused-run*))
                '(:stale :stale :slot-busy :stale :stale :invalid-draw
                  :resources-unavailable :stale :unknown-step)))
(assert! (not (fn-rv-any-admittedp (car (fn-rv-run *rvt-root4* *rvt-refused-run*)))))
;; and an admitted run from the root is okp at its end.
(defconst *rvt-admitted-run*
  (list (list :open 3 *rvt-conn-budget*) (list :open 4 *rvt-conn-budget*)
        (list :destroy 3 1 *fn-rv-zero*) (list :grow 1 1 *rvt-dw*)))
(assert! (equal (car (fn-rv-run *rvt-root4* *rvt-admitted-run*))
                '(:opened :opened :destroyed :grown)))
(assert! (fn-rv-okp (cadr (fn-rv-run *rvt-root4* *rvt-admitted-run*))))

;; -----------------------------------------------------------------------------
;; The keystones with their teeth.

;; A bank no transition builds: drawn under-counts a charged row.
(defconst *rvt-corrupt*
  (fn-rv-make *rvt-budget* *fn-rv-zero*
              (update-nth 2 (list* 1 1 *rvt-read*) (fn-rv-idle-rows 8))))
(assert! (not (fn-rv-okp *rvt-corrupt*)))
(assert! (fn-rv-bankp *rvt-corrupt*))

(defkeystone rvt-step-keeps-okp
  (implies (fn-rv-okp bank)
           (fn-rv-okp (cadr (fn-rv-step bank op))))
  :id "PRF-1209"
  :subject fn-rv-step
  :mutations (:deferred "no false neighbour named yet")
  :restates fn-rv-step-keeps-okp
  :hyps (okp)
  :witness ((bank *rvt-root4*) (op (list :open 3 *rvt-conn-budget*)))
  :breaks ((okp ((bank *rvt-corrupt*) (op (list :draw 3 *rvt-read*)))
                :logical "drawn under-counts the row at slot 2; no transition builds it"))
  :hints (("Goal" :by fn-rv-step-keeps-okp)))

(defkeystone rvt-run-keeps-okp
  (implies (fn-rv-okp bank)
           (fn-rv-okp (cadr (fn-rv-run bank ops))))
  :id "PRF-1209"
  :subject fn-rv-run
  :mutations (:deferred "no false neighbour named yet")
  :restates fn-rv-run-keeps-okp
  :hyps (okp)
  :witness ((bank *rvt-root4*) (ops *rvt-admitted-run*))
  :breaks ((okp ((bank *rvt-corrupt*) (ops (list (list :draw 3 *rvt-read*))))
                :logical "drawn under-counts the row at slot 2; no transition builds it"))
  :hints (("Goal" :by fn-rv-run-keeps-okp)))

(defkeystone rvt-step-refused-keeps-the-bank
  (implies (not (fn-rv-admittedp (car (fn-rv-step bank op))))
           (equal (cadr (fn-rv-step bank op)) bank))
  :id "PRF-1209"
  :subject fn-rv-step
  :mutations (:deferred "no false neighbour named yet")
  :restates fn-rv-step-refused-keeps-the-bank
  :hyps (refused)
  :witness ((bank *rvt-root4*) (op (list :draw 1 *rvt-read*)))
  :breaks ((refused ((bank *rvt-root4*) (op (list :open 3 *rvt-conn-budget*)))))
  :hints (("Goal" :by fn-rv-step-refused-keeps-the-bank)))

(defkeystone rvt-refusal-keeps-slack
  (implies (not (fn-rv-admittedp (car (fn-rv-step bank op))))
           (equal (fn-rv-slack (cadr (fn-rv-step bank op))) (fn-rv-slack bank)))
  :id "PRF-1209"
  :subject fn-rv-step
  :mutations (:deferred "no false neighbour named yet")
  :restates fn-rv-refusal-keeps-slack
  :hyps (refused)
  :witness ((bank *rvt-conn1*) (op (list :draw 1 *rvt-past*)))
  :breaks ((refused ((bank *rvt-conn1*) (op (list :draw 1 *rvt-exact*)))))
  :hints (("Goal" :by fn-rv-refusal-keeps-slack)))

(defkeystone rvt-refused-run-keeps-the-bank
  (implies (not (fn-rv-any-admittedp (car (fn-rv-run bank ops))))
           (equal (cadr (fn-rv-run bank ops)) bank))
  :id "PRF-1209"
  :subject fn-rv-run
  :mutations (:deferred "no false neighbour named yet")
  :restates fn-rv-refused-run-keeps-the-bank
  :hyps (all-refused)
  :witness ((bank *rvt-root4*) (ops *rvt-refused-run*))
  :breaks ((all-refused ((bank *rvt-root4*) (ops *rvt-admitted-run*))))
  :hints (("Goal" :by fn-rv-refused-run-keeps-the-bank)))

(defkeystone rvt-draw-admits-exactly-within-the-budget
  (equal (equal (car (fn-rv-draw bank slot demand)) :drawn)
         (and (fn-rv-slotp slot bank) (fn-rv-vectorp demand)
              (equal (fn-rv-phase slot bank) 0)
              (fn-rv-below (fn-rv-plus (fn-rv-drawn bank) demand) (fn-rv-budget bank))))
  :id "PRF-1209"
  :subject fn-rv-draw
  :restates fn-rv-draw-admits-exactly-within-the-budget
  :witness ((bank *rvt-conn1*) (slot 1) (demand *rvt-exact*))
  :mutations ((busy-slot-admitted
               (:conclusion
                (equal (equal (car (fn-rv-draw bank slot demand)) :drawn)
                       (and (fn-rv-slotp slot bank) (fn-rv-vectorp demand)
                            (fn-rv-below (fn-rv-plus (fn-rv-drawn bank) demand) (fn-rv-budget bank)))))
               ((bank *rvt-conn1*) (slot 0) (demand *rvt-read*))
               :fault "a draw admitted on a busy slot")
              (past-the-budget-admitted
               (:conclusion
                (equal (equal (car (fn-rv-draw bank slot demand)) :drawn)
                       (and (fn-rv-slotp slot bank) (fn-rv-vectorp demand)
                            (equal (fn-rv-phase slot bank) 0))))
               ((bank *rvt-conn1*) (slot 1) (demand *rvt-past*))
               :fault "a draw admitted past the budget"))
  :hints (("Goal" :by fn-rv-draw-admits-exactly-within-the-budget)))

(defkeystone rvt-draw-charges-exactly-the-demand
  (implies (equal (car (fn-rv-draw bank slot demand)) :drawn)
           (and (equal (fn-rv-drawn (cadr (fn-rv-draw bank slot demand)))
                       (fn-rv-plus (fn-rv-drawn bank) demand))
                (equal (fn-rv-budget (cadr (fn-rv-draw bank slot demand)))
                       (fn-rv-budget bank))
                (equal (fn-rv-row slot (cadr (fn-rv-draw bank slot demand)))
                       (list* 1 (+ 1 (fn-rv-gen slot bank)) demand))
                (equal (caddr (fn-rv-draw bank slot demand))
                       (+ 1 (fn-rv-gen slot bank)))))
  :id "PRF-1209"
  :subject fn-rv-draw
  :mutations (:deferred "no false neighbour named yet")
  :restates fn-rv-draw-charges-exactly-the-demand
  :hyps (drawn)
  :witness ((bank *rvt-conn2*) (slot 0) (demand *rvt-read*))
  :breaks ((drawn ((bank *rvt-conn1*) (slot 0) (demand *rvt-read*))))
  :hints (("Goal" :by fn-rv-draw-charges-exactly-the-demand)))

(defkeystone rvt-settle-once
  (and (not (equal (car (fn-rv-settle (cadr (fn-rv-settle bank slot gen)) slot gen)) :settled))
       (equal (cadr (fn-rv-settle (cadr (fn-rv-settle bank slot gen)) slot gen))
              (cadr (fn-rv-settle bank slot gen))))
  :id "PRF-1209"
  :subject fn-rv-settle
  :restates fn-rv-settle-once
  :witness ((bank *rvt-conn1r*) (slot 0) (gen 1))
  :mutations ((second-settle-admitted
               (:conclusion
                (equal (car (fn-rv-settle (cadr (fn-rv-settle bank slot gen)) slot gen)) :settled))
               ((bank *rvt-conn1r*) (slot 0) (gen 1))
               :fault "a second settle of the same draw admitted")
              (second-settle-moves-the-bank
               (:conclusion
                (not (equal (cadr (fn-rv-settle (cadr (fn-rv-settle bank slot gen)) slot gen))
                            (cadr (fn-rv-settle bank slot gen)))))
               ((bank *rvt-conn1r*) (slot 0) (gen 1))
               :fault "a second settle that moves the bank"))
  :hints (("Goal" :by fn-rv-settle-once)))

;; The ABA keystone: the first draw's token, a run (its settle), a second
;; admitted draw of the slot; the replayed token is :stale.  The removal
;; witness: a run that does not settle the slot, so the second draw is
;; :slot-busy and the token (still the live one) settles.
(defkeystone rvt-replayed-completion-is-stale
  (implies (equal (car (fn-rv-draw (cadr (fn-rv-run (cadr (fn-rv-draw bank slot d1)) ops))
                                   slot d2))
                  :drawn)
           (let ((again (cadr (fn-rv-draw (cadr (fn-rv-run (cadr (fn-rv-draw bank slot d1)) ops))
                                          slot d2)))
                 (token (caddr (fn-rv-draw bank slot d1))))
             (and (equal (car (fn-rv-settle again slot token)) :stale)
                  (equal (cadr (fn-rv-settle again slot token)) again))))
  :id "PRF-1209"
  :subject fn-rv-settle
  :mutations (:deferred "no false neighbour named yet")
  :restates fn-rv-replayed-completion-is-stale
  :hyps (second-drawn)
  :witness ((bank *rvt-conn*) (slot 0) (d1 *rvt-read*) (ops (list (list :settle 0 1)))
            (d2 *rvt-read*))
  :breaks ((second-drawn ((bank *rvt-conn*) (slot 0) (d1 *rvt-read*) (ops nil) (d2 *rvt-read*))))
  :hints (("Goal" :by fn-rv-replayed-completion-is-stale)))

(defkeystone rvt-step-keeps-the-other-slots
  (implies (and (natp j) (not (equal j (nfix (nth 1 op)))))
           (equal (fn-rv-row j (cadr (fn-rv-step bank op)))
                  (fn-rv-row j bank)))
  :id "PRF-1209"
  :subject fn-rv-step
  :mutations (:deferred "no false neighbour named yet")
  :restates fn-rv-step-keeps-the-other-slots
  :hyps (natp other)
  :witness ((j 1) (bank *rvt-conn*) (op (list :draw 0 *rvt-read*)))
  :breaks ((natp ((j -1) (bank *rvt-conn*) (op (list :draw 0 *rvt-read*))))
           (other ((j 0) (bank *rvt-conn*) (op (list :draw 0 *rvt-read*)))))
  :hints (("Goal" :by fn-rv-step-keeps-the-other-slots)))

(defkeystone rvt-user-steps-keep-the-reserve
  (implies (not (equal (nfix (nth 1 op)) 1))
           (equal (fn-rv-row 1 (cadr (fn-rv-step bank op)))
                  (fn-rv-row 1 bank)))
  :id "PRF-1209"
  :subject fn-rv-step
  :mutations (:deferred "no false neighbour named yet")
  :restates fn-rv-user-steps-keep-the-reserve
  :hyps (a-users-slot)
  :witness ((bank *rvt-root3*) (op (list :open 3 *rvt-conn-budget*)))
  :breaks ((a-users-slot ((bank *rvt-root3*) (op (list :grow 1 1 *rvt-dw*)))))
  :hints (("Goal" :by fn-rv-user-steps-keep-the-reserve)))

(defkeystone rvt-install-reserves-the-owner-first
  (implies (equal (car (fn-rv-install budget baseline reserve nslots)) :installed)
           (and (fn-rv-okp (cadr (fn-rv-install budget baseline reserve nslots)))
                (equal (fn-rv-budget (cadr (fn-rv-install budget baseline reserve nslots)))
                       budget)
                (equal (fn-rv-drawn (cadr (fn-rv-install budget baseline reserve nslots)))
                       (fn-rv-plus baseline reserve))
                (equal (fn-rv-row 0 (cadr (fn-rv-install budget baseline reserve nslots)))
                       (list* 1 1 baseline))
                (equal (fn-rv-row 1 (cadr (fn-rv-install budget baseline reserve nslots)))
                       (list* 2 1 reserve))
                (equal (fn-rv-slot-count (cadr (fn-rv-install budget baseline reserve nslots)))
                       nslots)
                (fn-rv-below (fn-rv-plus baseline reserve) budget)))
  :id "PRF-1209"
  :subject fn-rv-install
  :mutations (:deferred "no false neighbour named yet")
  :restates fn-rv-install-reserves-the-owner-first
  :hyps (installed)
  :witness ((budget *rvt-budget*) (baseline *rvt-baseline*) (reserve *rvt-reserve*) (nslots 8))
  :breaks ((installed ((budget *rvt-baseline*) (baseline *rvt-baseline*) (reserve *rvt-reserve*)
                       (nslots 8))))
  :hints (("Goal" :by fn-rv-install-reserves-the-owner-first)))

;; For the destroy keystone's removal witnesses: a root whose drawn vector
;; under-counts its sub-bank's slot (corrupt); a sub-bank that spent past
;; its budget (corrupt); a root whose slot 0 is a sub-bank, destroyed at a
;; slot that is not a number; a drawn slot named as a sub-bank; a sub-bank
;; larger than the slot it is destroyed at, holding a draw the returned
;; budget cannot cover.
(defconst *rvt-corrupt-root*
  (fn-rv-make *rvt-budget* *fn-rv-zero*
              (update-nth 2 (list* 2 1 *rvt-conn-budget*) (fn-rv-idle-rows 8))))
(defconst *rvt-overspent-sub*
  (fn-rv-make *rvt-conn-budget* (list 0 0 0 0 11 0 0 0 0) (fn-rv-idle-rows 4)))
(defconst *rvt-alt-root*
  (cadr (fn-rv-open (fn-rv-make *rvt-budget* *fn-rv-zero* (fn-rv-idle-rows 4))
                        0 *rvt-conn-budget*)))
(defconst *rvt-baseline-sub* (fn-rv-make *rvt-baseline* *fn-rv-zero* (fn-rv-idle-rows 2)))
(defconst *rvt-big-sub*
  (cadr (fn-rv-draw (fn-rv-make (list (* 16 *rvt-mib*) 0 0 1 10 0 0 1 10000)
                                    *fn-rv-zero* (fn-rv-idle-rows 2))
                        0 (list (* 8 *rvt-mib*) 0 0 1 1 0 0 0 100))))
(assert! (and (not (fn-rv-okp *rvt-corrupt-root*)) (not (fn-rv-okp *rvt-overspent-sub*))
              (fn-rv-okp *rvt-alt-root*) (fn-rv-okp *rvt-baseline-sub*) (fn-rv-okp *rvt-big-sub*)))

(defkeystone rvt-destroy-returns-exactly-the-unsettled-draws
  (implies (and (fn-rv-okp bank) (fn-rv-okp sub)
                (fn-rv-slotp slot bank)
                (fn-rv-sub-bankp slot gen bank)
                (equal (fn-rv-budget sub) (fn-rv-demand slot bank)))
           (and (equal (car (fn-rv-destroy bank slot gen (fn-rv-spent (fn-rv-drawn sub))))
                       :destroyed)
                (equal (fn-rv-slack (cadr (fn-rv-destroy bank slot gen (fn-rv-spent (fn-rv-drawn sub)))))
                       (fn-rv-plus (fn-rv-slack bank)
                                   (fn-rv-monus (fn-rv-demand slot bank)
                                                (fn-rv-spent (fn-rv-drawn sub)))))
                (fn-rv-below (fn-rv-reusable (fn-rv-outstanding (fn-rv-slots sub)))
                             (fn-rv-monus (fn-rv-demand slot bank) (fn-rv-spent (fn-rv-drawn sub))))
                (equal (fn-rv-phase slot (cadr (fn-rv-destroy bank slot gen (fn-rv-spent (fn-rv-drawn sub)))))
                       0)))
  :id "PRF-1209"
  :subject fn-rv-destroy
  :mutations (:deferred "no false neighbour named yet")
  :restates fn-rv-destroy-returns-exactly-the-unsettled-draws
  :hyps (okp-bank okp-sub slotp a-sub-bank budget-is-the-demand)
  :witness ((bank *rvt-root2*) (sub *rvt-conn-spent*) (slot 2) (gen 1))
  :breaks ((okp-bank ((bank *rvt-corrupt-root*) (sub *rvt-conn-spent*) (slot 2) (gen 1))
                     :logical "drawn under-counts the sub-bank's slot; no transition builds it")
           (okp-sub ((bank *rvt-root2*) (sub *rvt-overspent-sub*) (slot 2) (gen 1))
                    :logical "a sub-bank drawn past its budget; no transition builds it")
           (slotp ((bank *rvt-alt-root*) (sub *rvt-conn*) (slot 'a) (gen 1)))
           (a-sub-bank ((bank *rvt-root2*) (sub *rvt-baseline-sub*) (slot 0) (gen 1)))
           (budget-is-the-demand ((bank *rvt-root2*) (sub *rvt-big-sub*) (slot 2) (gen 1))))
  :hints (("Goal" :by fn-rv-destroy-returns-exactly-the-unsettled-draws)))
