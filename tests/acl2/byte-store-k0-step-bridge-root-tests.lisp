; Witnesses and teeth for lane k0-rest (PKT-080): the coverage generic over the
; root name (fn-bs-k0s-root-rename-pendingp) at the state checkpoint's and the
; profile's pending rename, the two programs' cuts by the keystone
; (fn-bs-k0-state-checkpoint-cuts-relation-by-step,
; fn-bs-k0-profile-cuts-relation-by-step) and every step at their pairs with
; any outcome.  Witness: the second publication's entry pair (bskc-rb,
; bskc-rk), related, outside the recovery window, :root and :transactions
; quiet; the checkpoint octets arbitrary, the profile's the initial config.
(in-package "ACL2")
(include-book "../../books/byte-store-k0-step-bridge-root")
(include-book "byte-store-k0-cuts-tests")
(include-book "std/testing/must-fail" :dir :system)

(defun bskr-cuts-ok (run ks)
  (and (fn-bs-store-relation (car (nth 1 run)) ks)
       (fn-bs-store-relation (car (nth 3 run)) ks)
       (fn-bs-store-relation (car (nth 5 run)) ks)
       (fn-bs-k0s-root-rename-pendingp (car (nth 7 run)) ks)
       (fn-bs-store-relation (car (nth 9 run)) ks)
       (equal (cdr (nth 1 run)) ks) (equal (cdr (nth 3 run)) ks) (equal (cdr (nth 5 run)) ks)
       (equal (cdr (nth 7 run)) ks) (equal (cdr (nth 9 run)) ks)))
(defun bskr-scp (bs ks stage octets)
  (bskr-cuts-ok (fn-bs-run bs ks (fn-bs-scp-program stage octets) nil nil nil) ks))
(defun bskr-profile (bs ks stage octets)
  (bskr-cuts-ok (fn-bs-run bs ks (fn-bs-profile-program stage octets) nil nil nil) ks))
(defconst *bskr-ck* '(70 78 83 67 1 2 3))
(defun bskr-cfg () (fn-bs-initial-config-octets))

; Witnesses: every hypothesis holds and every cut is as claimed.  The
; replaced cut is covered and not related (the relation's pending shape names
; only the frontier's root entry), and its two resolutions differ.
(assert-event (bskc-stage-hyps (bskc-rb) (bskc-rk) ".stage-ck-1" *bskr-ck*))
(assert-event (bskr-scp (bskc-rb) (bskc-rk) ".stage-ck-1" *bskr-ck*))
(assert-event (fn-bs-config-okp (bskr-cfg)))
(assert-event (bskc-stage-hyps (bskc-rb) (bskc-rk) ".stage-profile-1" (bskr-cfg)))
(assert-event (bskr-profile (bskc-rb) (bskc-rk) ".stage-profile-1" (bskr-cfg)))
(defun bskr-scp-b4 ()
  (car (nth 7 (fn-bs-run (bskc-rb) (bskc-rk) (fn-bs-scp-program ".stage-ck-1" *bskr-ck*) nil nil nil))))
(defun bskr-profile-b4 ()
  (car (nth 7 (fn-bs-run (bskc-rb) (bskc-rk) (fn-bs-profile-program ".stage-profile-1" (bskr-cfg)) nil nil nil))))
(assert-event (not (fn-bs-store-relation (bskr-scp-b4) (bskc-rk))))
(assert-event (equal (fn-bs-k0s-root-name (bskr-scp-b4)) *fn-bs-state-checkpoint-name*))
(assert-event (not (equal (fn-bs-root-rename-dropped (bskr-scp-b4)) (fn-bs-k0s-root-rename-landed (bskr-scp-b4)))))
(assert-event (not (fn-bs-store-relation (bskr-profile-b4) (bskc-rk))))
(assert-event (equal (fn-bs-k0s-root-name (bskr-profile-b4)) *fn-bs-config-name*))
; The landed profile resolution names the new config inode.
(assert-event (equal (fn-bs-durable-entry (fn-bs-k0s-root-rename-landed (bskr-profile-b4)) :root *fn-bs-config-name*)
                     (fn-bs-next-ino (bskc-rb))))
; The general step's arms at the new pairs: the rename onto each name, and the
; root barrier over each pending rename with :ok and with an EIO that drops it.
(assert-event (bsks-ok (bskr-scp-b4) (bskc-rk) '(:fsync-dir :root) :ok))
(assert-event (bsks-ok (bskr-scp-b4) (bskc-rk) '(:fsync-dir :root) '(:eio :drop)))
(assert-event (bsks-ok (bskr-profile-b4) (bskc-rk) '(:fsync-dir :root) '(:eio :drop)))

; Teeth, one per hypothesis of the cuts theorems.
; The relation: the initial image under the same kernel.
(must-fail (assert-event (bskr-scp (bsk5-initial) (bskc-rk) ".stage-ck-1" *bskr-ck*)))
(must-fail (assert-event (bskr-profile (bsk5-initial) (bskc-rk) ".stage-profile-1" (bskr-cfg))))
; A name for the stage: 7 is not one.
(must-fail (assert-event (bskr-scp (bskc-rb) (bskc-rk) 7 *bskr-ck*)))
(must-fail (assert-event (bskr-profile (bskc-rb) (bskc-rk) 7 (bskr-cfg))))
; The stage absent: occupied by inode 0 (bskc-occupied, the cuts tests').
(assert-event (fn-bs-lookup (bskc-occupied) :staging ".stage-k5-2"))
(must-fail (assert-event (bskr-scp (bskc-occupied) (bskc-rk) ".stage-k5-2" *bskr-ck*)))
(must-fail (assert-event (bskr-profile (bskc-occupied) (bskc-rk) ".stage-k5-2" (bskr-cfg))))
; Typed octets: (300).
(must-fail (assert-event (bskr-scp (bskc-rb) (bskc-rk) ".stage-ck-1" '(300))))
; :root quiet: the frontier run's attempted pair 11 (related, the frontier
; rename pending): the checkpoint's rename joins a second root entry, and the
; replaced cut is neither related nor covered.
(assert-event (fn-bs-store-relation (car (bskc-f 11)) (cdr (bskc-f 11))))
(assert-event (not (fn-bs-lookup (car (bskc-f 11)) :staging ".stage-ck-1")))
(must-fail (assert-event (bskr-scp (car (bskc-f 11)) (cdr (bskc-f 11)) ".stage-ck-1" *bskr-ck*)))
; The configuration check (profile only): octets the check refuses.  The
; landed resolution's config.json fails it, so the replaced cut is not
; covered and the durable cut not related.
(assert-event (not (fn-bs-config-okp *bskr-ck*)))
(must-fail (assert-event (bskr-profile (bskc-rb) (bskc-rk) ".stage-profile-1" *bskr-ck*)))
; No must-fail: :transactions quiet and the recovery-window guard are the
; keystone's step-input guards (stage lemma, lane k0-cuts); the conclusion is
; not shown to need them.
