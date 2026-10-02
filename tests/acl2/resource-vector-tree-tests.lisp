; Teeth for books/resource-vector-tree (deputy-1, 2026-10-01): a small
; node as one state -- the root installed with its reserve as a sub-bank, a
; connection's sub-bank opened on the root, reads drawn inside it with their
; tokens, a settle and its replay (:stale), the connection destroyed by the
; root and every later step addressed to its token :stale, the slot
; re-opened under a new token, the reserve grown by the root, a nested open
; refused -- and each keystone with its hypotheses shown necessary.
(in-package "ACL2")
(include-book "../../books/resource-vector-tree")
(include-book "../../books/defkeystone")
(include-book "must-fail-checked")
(include-book "std/testing/assert-bang" :dir :system)

(defconst *rtt-mib* 1048576)
(defconst *rtt-budget*
  (list (* 256 *rtt-mib*) (* 4096 *rtt-mib*) 64 8 1000 1000000 100 10000 1000000))
(defconst *rtt-baseline* (list (* 160 *rtt-mib*) 0 1 1 0 0 0 0 0))
(defconst *rtt-reserve* (list (* 16 *rtt-mib*) (* 512 *rtt-mib*) 2 1 0 1 1 0 100000))
(defconst *rtt-conn-budget* (list (* 4 *rtt-mib*) 0 1 1 10 0 0 1 10000))
(defconst *rtt-read* (list 65536 0 0 0 1 0 0 0 1000))
(defconst *rtt-dw* (list 0 4096 0 0 0 1 0 0 0))

;; The root: eight slots, the reserve a sub-bank of two slots at slot 1.
(defconst *rtt-t0* (cadr (fn-rt-install *rtt-budget* *rtt-baseline* *rtt-reserve* 8 2)))
(assert! (equal (car (fn-rt-install *rtt-budget* *rtt-baseline* *rtt-reserve* 8 2)) :installed))
(assert! (fn-rt-okp *rtt-t0*))
(assert! (equal (fn-rv-budget (fn-rt-sub 1 *rtt-t0*)) *rtt-reserve*))
(assert! (equal (fn-rt-sub 0 *rtt-t0*) nil))
(assert! (equal (len (fn-rt-subs *rtt-t0*)) 8))

;; A connection opened on the root: slot 2, token 1, four slots of its own.
(defconst *rtt-open* (fn-rt-step *rtt-t0* (list :root :open 2 *rtt-conn-budget* 4)))
(defconst *rtt-t1* (cadr *rtt-open*))
(assert! (equal (car *rtt-open*) :opened))
(assert! (equal (caddr *rtt-open*) 1))
(assert! (fn-rt-okp *rtt-t1*))
(assert! (equal (fn-rv-budget (fn-rt-sub 2 *rtt-t1*)) *rtt-conn-budget*))
(assert! (equal (fn-rv-slot-count (fn-rt-sub 2 *rtt-t1*)) 4))
(assert! (equal (fn-rv-row 2 (fn-rt-root *rtt-t1*)) (list* 2 1 *rtt-conn-budget*)))

;; A read drawn inside the connection (owner (2 . 1)): the root unchanged.
(defconst *rtt-draw* (fn-rt-step *rtt-t1* (list (cons 2 1) :draw 0 *rtt-read*)))
(defconst *rtt-t2* (cadr *rtt-draw*))
(assert! (equal (car *rtt-draw*) :drawn))
(assert! (equal (caddr *rtt-draw*) 1))
(assert! (fn-rt-okp *rtt-t2*))
(assert! (equal (fn-rt-root *rtt-t2*) (fn-rt-root *rtt-t1*)))
(assert! (equal (fn-rv-drawn (fn-rt-sub 2 *rtt-t2*)) *rtt-read*))
;; Addressed to the wrong token, or to a drawn slot, or nested: refused by
;; name, the tree itself.
(assert! (equal (identity (fn-rt-step *rtt-t2* (list (cons 2 2) :draw 1 *rtt-read*)))
                (list :stale *rtt-t2*)))
(assert! (equal (identity (fn-rt-step *rtt-t2* (list (cons 0 1) :draw 1 *rtt-read*)))
                (list :stale *rtt-t2*)))
(assert! (equal (identity (fn-rt-step *rtt-t2* (list (cons 2 1) :open 1 *rtt-read* 2)))
                (list :no-nested-sub-banks *rtt-t2*)))
(assert! (equal (identity (fn-rt-step *rtt-t2* (list 7 :draw 1 *rtt-read*)))
                (list :unknown-owner *rtt-t2*)))
;; Its settle, and the replay.
(defconst *rtt-t3* (cadr (fn-rt-step *rtt-t2* (list (cons 2 1) :settle 0 1))))
(assert! (equal (car (fn-rt-step *rtt-t2* (list (cons 2 1) :settle 0 1))) :settled))
(assert! (fn-rt-okp *rtt-t3*))
(assert! (equal (identity (fn-rt-step *rtt-t3* (list (cons 2 1) :settle 0 1)))
                (list :stale *rtt-t3*)))
;; The reserve grown by the root (dW+): the sub-bank's budget grows with
;; the row; a draw inside the reserve under its token.
(defconst *rtt-t4* (cadr (fn-rt-step *rtt-t3* (list :root :grow 1 1 *rtt-dw*))))
(assert! (equal (car (fn-rt-step *rtt-t3* (list :root :grow 1 1 *rtt-dw*))) :grown))
(assert! (fn-rt-okp *rtt-t4*))
(assert! (equal (fn-rv-budget (fn-rt-sub 1 *rtt-t4*)) (fn-rv-plus *rtt-reserve* *rtt-dw*)))
(assert! (equal (car (fn-rt-step *rtt-t4* (list (cons 1 1) :draw 0 *rtt-dw*))) :drawn))

;; The connection destroyed by the root with a read outstanding: what it
;; spent is read from the sub-bank; the root gets back the rest.
(defconst *rtt-t5* (cadr (fn-rt-step *rtt-t4* (list (cons 2 1) :draw 1 *rtt-read*))))
(assert! (equal (fn-rv-drawn (fn-rt-sub 2 *rtt-t5*)) (list 65536 0 0 0 2 0 0 0 2000)))
(defconst *rtt-destroy* (fn-rt-step *rtt-t5* (list :root :destroy 2 1)))
(defconst *rtt-t6* (cadr *rtt-destroy*))
(assert! (equal (car *rtt-destroy*) :destroyed))
(assert! (fn-rt-okp *rtt-t6*))
(assert! (equal (fn-rt-sub 2 *rtt-t6*) nil))
(assert! (equal (fn-rv-slack (fn-rt-root *rtt-t6*))
                (fn-rv-plus (fn-rv-slack (fn-rt-root *rtt-t5*))
                            (fn-rv-monus *rtt-conn-budget* (list 0 0 0 0 2 0 0 0 2000)))))
;; Revoked: the outstanding read's completion, a new draw, anything
;; addressed to the destroyed token is :stale; the slot re-opened under
;; token 2 answers only to token 2.
(assert! (equal (identity (fn-rt-step *rtt-t6* (list (cons 2 1) :settle 1 1)))
                (list :stale *rtt-t6*)))
(assert! (equal (identity (fn-rt-step *rtt-t6* (list (cons 2 1) :draw 2 *rtt-read*)))
                (list :stale *rtt-t6*)))
(defconst *rtt-t7* (cadr (fn-rt-step *rtt-t6* (list :root :open 2 *rtt-conn-budget* 4))))
(assert! (equal (caddr (fn-rt-step *rtt-t6* (list :root :open 2 *rtt-conn-budget* 4))) 2))
(assert! (fn-rt-okp *rtt-t7*))
(assert! (equal (identity (fn-rt-step *rtt-t7* (list (cons 2 1) :settle 1 1)))
                (list :stale *rtt-t7*)))
(assert! (equal (identity (fn-rt-step *rtt-t7* (list (cons 2 1) :draw 0 *rtt-read*)))
                (list :stale *rtt-t7*)))
(assert! (equal (car (fn-rt-step *rtt-t7* (list (cons 2 2) :draw 0 *rtt-read*))) :drawn))
;; A destroy replayed (no sub-bank behind the idle slot: the spent of none
;; is no vector, so the bank's destroy refuses it :invalid-destroy -- one
;; word for every dead token is NEXT), or with the wrong token: refused,
;; the tree itself.
(assert! (equal (identity (fn-rt-step *rtt-t6* (list :root :destroy 2 1)))
                (list :invalid-destroy *rtt-t6*)))
(assert! (equal (identity (fn-rt-step *rtt-t7* (list :root :destroy 2 1))) (list :stale *rtt-t7*)))
;; A run: refusals leave the tree; an admitted run keeps the invariant.
(defconst *rtt-refused-run*
  (list (list (cons 2 1) :settle 1 1) (list :root :destroy 2 1) (list (cons 1 2) :draw 0 *rtt-dw*)
        (list :root :draw 0 *rtt-read*) (list (cons 2 2) :open 1 *rtt-read* 2) (list 7 :draw 1 nil)))
(assert! (equal (car (fn-rt-run *rtt-t7* *rtt-refused-run*))
                '(:stale :stale :stale :slot-busy :no-nested-sub-banks :unknown-owner)))
(assert! (equal (cadr (fn-rt-run *rtt-t7* *rtt-refused-run*)) *rtt-t7*))
(defconst *rtt-admitted-run*
  (list (list (cons 2 2) :draw 0 *rtt-read*) (list (cons 2 2) :settle 0 1)
        (list :root :open 3 *rtt-conn-budget* 2) (list :root :destroy 3 1)))
(assert! (equal (car (fn-rt-run *rtt-t7* *rtt-admitted-run*)) '(:drawn :settled :opened :destroyed)))
(assert! (fn-rt-okp (cadr (fn-rt-run *rtt-t7* *rtt-admitted-run*))))

;; -----------------------------------------------------------------------------
;; The keystones with their teeth.

;; Trees no step builds: a sub-bank row with no sub-bank behind it; a
;; sub-bank that spent past its budget.
(defconst *rtt-corrupt-missing* (fn-rt-make (fn-rt-root *rtt-t1*) (fn-rt-subs *rtt-t0*)))
(defconst *rtt-corrupt-overspent*
  (fn-rt-make (fn-rt-root *rtt-t1*)
              (update-nth 2 (fn-rv-make *rtt-conn-budget* (list 0 0 0 0 11 0 0 0 0) (fn-rv-idle-rows 4))
                          (fn-rt-subs *rtt-t1*))))
(assert! (and (not (fn-rt-okp *rtt-corrupt-missing*)) (not (fn-rt-okp *rtt-corrupt-overspent*))))

(defkeystone rtt-step-keeps-okp
  (implies (fn-rt-okp tree)
           (fn-rt-okp (cadr (fn-rt-step tree op))))
  :id "PRF-1209"
  :subject fn-rt-step
  :mutations (:deferred "no false neighbour named yet")
  :restates fn-rt-step-keeps-okp
  :hyps (okp)
  :witness ((tree *rtt-t1*) (op (list (cons 2 1) :draw 0 *rtt-read*)))
  :breaks ((okp ((tree *rtt-corrupt-missing*) (op (list :root :settle 0 1)))
                :logical "a sub-bank row with no sub-bank behind it; no step builds it"))
  :hints (("Goal" :by fn-rt-step-keeps-okp)))

(defkeystone rtt-run-keeps-okp
  (implies (fn-rt-okp tree)
           (fn-rt-okp (cadr (fn-rt-run tree ops))))
  :id "PRF-1209"
  :subject fn-rt-run
  :mutations (:deferred "no false neighbour named yet")
  :restates fn-rt-run-keeps-okp
  :hyps (okp)
  :witness ((tree *rtt-t7*) (ops *rtt-admitted-run*))
  :breaks ((okp ((tree *rtt-corrupt-missing*) (ops (list (list :root :settle 0 1))))
                :logical "a sub-bank row with no sub-bank behind it; no step builds it"))
  :hints (("Goal" :by fn-rt-run-keeps-okp)))

(defkeystone rtt-step-refused-keeps-the-tree
  (implies (not (fn-rv-admittedp (car (fn-rt-step tree op))))
           (equal (cadr (fn-rt-step tree op)) tree))
  :id "PRF-1209"
  :subject fn-rt-step
  :mutations (:deferred "no false neighbour named yet")
  :restates fn-rt-step-refused-keeps-the-tree
  :hyps (refused)
  :witness ((tree *rtt-t6*) (op (list (cons 2 1) :settle 1 1)))
  :breaks ((refused ((tree *rtt-t6*) (op (list :root :open 2 *rtt-conn-budget* 4)))))
  :hints (("Goal" :by fn-rt-step-refused-keeps-the-tree)))

(defkeystone rtt-sub-bank-steps-keep-the-root
  (equal (fn-rt-root (cadr (fn-rt-step tree (cons (cons slot gen) step))))
         (fn-rt-root tree))
  :id "PRF-1209"
  :subject fn-rt-step
  :restates fn-rt-sub-bank-steps-keep-the-root
  :witness ((tree *rtt-t1*) (slot 2) (gen 1) (step (list :draw 0 *rtt-read*)))
  :mutations ((a-root-step-keeps-the-root
               (:conclusion
                (equal (fn-rt-root (cadr (fn-rt-step tree (cons :root step))))
                       (fn-rt-root tree)))
               ((tree *rtt-t1*) (slot 2) (gen 1) (step (list :open 3 *rtt-conn-budget* 2)))
               :fault "a root step claimed to keep the root"))
  :hints (("Goal" :by fn-rt-sub-bank-steps-keep-the-root)))

(defkeystone rtt-destroy-revokes-the-sub-bank
  (implies (equal (car (fn-rt-step tree (list :root :destroy slot gen))) :destroyed)
           (let ((later (cadr (fn-rt-run (cadr (fn-rt-step tree (list :root :destroy slot gen)))
                                         ops))))
             (and (equal (car (fn-rt-step later (cons (cons slot gen) step))) :stale)
                  (equal (cadr (fn-rt-step later (cons (cons slot gen) step))) later))))
  :id "PRF-1209"
  :subject fn-rt-step
  :mutations (:deferred "no false neighbour named yet")
  :restates fn-rt-destroy-revokes-the-sub-bank
  :hyps (destroyed)
  :witness ((tree *rtt-t5*) (slot 2) (gen 1)
            (ops (list (list :root :open 2 *rtt-conn-budget* 4) (list (cons 2 2) :draw 0 *rtt-read*)))
            (step (list :settle 1 1)))
  :breaks ((destroyed ((tree *rtt-corrupt-overspent*) (slot 2) (gen 1) (ops nil)
                       (step (list :draw 1 *rtt-read*)))
                      :logical "a sub-bank that spent past its budget refuses its destroy (:sub-bank-overspent) and stays addressable; no step builds it"))
  :hints (("Goal" :by fn-rt-destroy-revokes-the-sub-bank)))
