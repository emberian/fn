(in-package "ACL2")
(include-book "../../books/owner-identity-prepare")
(include-book "store-identity-reserve-tests")

(defconst *idrp-t-owner*
 (fn-ocfg-make
  (fn-own-make *idr-reserved* nil nil 0 1 nil nil nil nil nil nil nil nil nil nil)
  (fn-cfg-initial) nil nil))

(defun idrp-t-eval-in (oc event grant fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (word next remaining installp)
    (fn-idrp-prepare-retention oc event grant fn-arena)
    (mv (list word next remaining installp
              (fn-ocfg-step oc (list :store (list :prepare-retention event)) fn-arena))
        fn-arena)))
(defun idrp-t-eval (oc event grant)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena) (idrp-t-eval-in oc event grant fn-arena) result)))

(defconst *idrp-t-good* (idrp-t-eval *idrp-t-owner* *idr-release-record* *idr-grant*))
; Reachable positive, complete output/effect conclusion of the literal theorem.
(assert-event
 (and (fn-sn-statep (fn-sbud-oc-store *idrp-t-owner*))
      (fn-idr-grant-boundp (fn-sbud-oc-store *idrp-t-owner*) *idr-release-record* *idr-grant*)
      (null (nth 2 *idrp-t-good*))
      (equal (nth 3 *idrp-t-good*) t)
      (equal (nth 1 *idrp-t-good*) (nth 4 *idrp-t-good*))
      (not (equal (fn-sbud-oc-store (nth 1 *idrp-t-good*))
                  (fn-sbud-oc-store *idrp-t-owner*)))
      (equal (nth 0 *idrp-t-good*) :prepared)))

(defconst *idrp-t-denied* (idrp-t-eval *idrp-t-owner* *idr-release-record* nil))
; Exhausted grant: no second prepare and no installer, even in reserved phase.
(assert-event
 (and (not (fn-idr-grant-boundp (fn-sbud-oc-store *idrp-t-owner*) *idr-release-record* nil))
      (null (nth 2 *idrp-t-denied*)) (null (nth 3 *idrp-t-denied*))
      (equal (nth 1 *idrp-t-denied*) *idrp-t-owner*)
      (equal (nth 0 *idrp-t-denied*) :refused)))

(defconst *idrp-t-mutated* (idrp-t-eval *idrp-t-owner* *idr-record* *idr-grant*))
; Mutation: another event cannot steal the release grant.
(assert-event
 (and (not (fn-idr-grant-boundp (fn-sbud-oc-store *idrp-t-owner*) *idr-record* *idr-grant*))
      (null (nth 2 *idrp-t-mutated*)) (null (nth 3 *idrp-t-mutated*))
      (equal (nth 1 *idrp-t-mutated*) *idrp-t-owner*)
      (equal (nth 0 *idrp-t-mutated*) :refused)))
