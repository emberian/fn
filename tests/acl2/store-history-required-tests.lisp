; Witnesses and teeth for books/store-history-required.
(in-package "ACL2")
(include-book "../../books/store-history-required")
(include-book "std/testing/must-fail" :dir :system)

; The fixtures that hold a marker frame are zero-ary functions, not
; constants: a defconst is evaluated without the SHA-256 attachment.
; Profiles: the development preset (format 8, `unmarked') and the same with
; the requirement; the operator's request `--history-marker required' over
; the store's own profile.
(defconst *hrt-unmarked* *fn-bs-profile-development*)
(defconst *hrt-required* (fn-bs-profile-put 14 1 *fn-bs-profile-development*))
(defconst *hrt-migrate* '(:current ((14 . 1))))
(assert-event (fn-bs-profile-validp *hrt-unmarked*))
(assert-event (fn-bs-profile-validp *hrt-required*))
(assert-event (not (fn-bs-profile-marker-requiredp *hrt-unmarked*)))
(assert-event (fn-bs-profile-marker-requiredp *hrt-required*))
; A format-7 store runs `unmarked'.
(assert-event (not (fn-bs-profile-marker-requiredp
                    *fn-bs-meta-format-7-development-values*)))

; The decisions.
(assert-event (equal (fn-hmr-open-verdict *hrt-unmarked* '(:absent) 3)
                     '(:admitted :unmarked)))
(assert-event (equal (fn-hmr-open-verdict *hrt-required* '(:absent) 3)
                     '(:refused :marker-missing)))
(assert-event (equal (fn-hmr-open-verdict *hrt-required*
                                          (list :present (fn-hm-after-commit 2)) 2)
                     '(:refused :history-short-of-marker 3)))
(assert-event (equal (fn-hmr-open-verdict *hrt-required*
                                          (list :present (fn-hm-after-commit 2)) 4)
                     '(:admitted :marked 3)))
; The catch-up: nothing when the marker counts the history, the count's frame
; when it is behind or absent (count 0 included), nothing for a refusal.
(assert-event (equal (fn-hmr-catch-up *hrt-unmarked* (list :present (fn-hm-after-commit 2)) 3)
                     nil))
(assert-event (equal (fn-hmr-catch-up *hrt-unmarked* (list :present (fn-hm-after-commit 2)) 4)
                     (fn-hm-after-commit 3)))
(assert-event (equal (fn-hm-decode (fn-hmr-catch-up *hrt-unmarked* '(:absent) 0)) 0))
(assert-event (equal (fn-hmr-catch-up *hrt-required* '(:absent) 4) nil))
(assert-event (equal (fn-hmr-catch-up *hrt-unmarked* (list :present (fn-hm-after-commit 5)) 4)
                     nil))
; The upgrade: `required' over a covering marker, refused over a marker
; behind the history or none; never undone.
(assert-event (equal (car (fn-hmr-upgrade-verdict *hrt-unmarked* *hrt-migrate*
                                                  (list :present (fn-hm-after-commit 2)) 3))
                     :upgrade))
(assert-event (equal (fn-bs-config-decode
                      (cadr (fn-hmr-upgrade-verdict *hrt-unmarked* *hrt-migrate*
                                                    (list :present (fn-hm-after-commit 2)) 3)))
                     *hrt-required*))
(assert-event (equal (fn-hmr-upgrade-verdict *hrt-unmarked* *hrt-migrate*
                                             (list :present (fn-hm-after-commit 1)) 3)
                     '(:refused :history-marker-not-covering)))
(assert-event (equal (fn-hmr-upgrade-verdict *hrt-unmarked* *hrt-migrate* '(:absent) 3)
                     '(:refused :history-marker-not-covering)))
(assert-event (equal (fn-hmr-upgrade-verdict *hrt-required* '(:current ((14 . 0)))
                                             (list :present (fn-hm-after-commit 2)) 3)
                     '(:refused :not-an-upgrade "history-marker")))
; The 7-to-8 step with the requirement, in one verdict.
(assert-event (equal (car (fn-hmr-upgrade-verdict *fn-bs-meta-format-7-development-values*
                                                  *hrt-migrate*
                                                  (list :present (fn-hm-after-commit 2)) 3))
                     :upgrade))
; `init' never writes it.
(assert-event (equal (fn-bs-profile-init-verdict '(:development ((14 . 1))))
                     '(:refused :history-marker-required-before-a-marker)))
(assert-event (equal (fn-bs-profile-invalid-reason (fn-bs-profile-put 14 2 *hrt-unmarked*))
                     :history-marker-not-a-word))

; -----------------------------------------------------------------------------
; The reachable history of D31 case 2, from a fresh `unmarked' store: the
; first open writes the marker (count 0); a commit is answered (240); the
; next commit's record is durable and the process dies at `marker-created'
; (before its marker); the next open finds the record and catches the marker
; up; the client's retry resolves as already stored (record 1) and nothing
; else commits.  Then the newest file disappears: the open is refused.
(defconst *hrt-st0* (fn-hmr-state 0 '(:absent) 0 *hrt-unmarked* nil))
(defconst *hrt-retry*
  '((:open :marker-durable nil) (:commit :marker-durable nil)
    (:commit :marker-created nil) (:open :marker-durable nil) (:resolve 1)))
(defun hrt-end () (fn-hmr-run *hrt-retry* *hrt-st0*))
(assert-event (fn-hmr-invp *hrt-st0*))
(assert-event (equal (fn-hmr-count (hrt-end)) 2))
(assert-event (equal (nth 2 (hrt-end)) 2))
(assert-event (equal (fn-hmr-marker-count (nth 1 (hrt-end))) 2))
(assert-event (nth 4 (hrt-end)))
; Before the catch-up the marker was behind the durable record.
(assert-event (equal (fn-hmr-marker-count (nth 1 (fn-hmr-run (take 3 *hrt-retry*) *hrt-st0*))) 1))
; The loss of the newest file, at the next open.
(assert-event (equal (fn-hmr-open-verdict (nth 3 (hrt-end)) (nth 1 (hrt-end)) 1)
                     '(:refused :history-short-of-marker 2)))
; The catch-up crashed before its rename, then completed at the next open.
(defconst *hrt-retry-crashed*
  '((:open :marker-durable nil) (:commit :marker-durable nil)
    (:commit :marker-created nil) (:open :marker-written nil)
    (:open :marker-replaced nil) (:open :marker-durable t) (:resolve 1)))
(assert-event (equal (fn-hmr-run *hrt-retry-crashed* *hrt-st0*) (hrt-end)))
; The resolution of a crashed catch-up is not answered: no process is live.
(assert-event (equal (nth 2 (fn-hmr-run (take 5 *hrt-retry-crashed*) *hrt-st0*))
                     1))
(assert-event (equal (fn-hmr-run '((:resolve 1)) (fn-hmr-run (take 5 *hrt-retry-crashed*) *hrt-st0*))
                     (fn-hmr-run (take 5 *hrt-retry-crashed*) *hrt-st0*)))

; The migration, reachable from the end above: the store at rest opens
; (nothing to catch up) and the upgrade writes `required'; then the marker's
; deletion is damage.
(defun hrt-rest () (fn-hmr-run '((:uncertain nil)) (hrt-end)))
(defun hrt-migrated ()
  (fn-hmr-run '((:open :marker-durable nil) (:migrate (:current ((14 . 1))) t)) (hrt-rest)))
(assert-event (not (nth 4 (hrt-rest))))
(assert-event (equal (nth 3 (hrt-migrated)) *hrt-required*))
(assert-event (fn-hmr-invp (hrt-migrated)))
(assert-event (equal (fn-hmr-open-verdict (nth 3 (hrt-migrated)) '(:absent) 2)
                     '(:refused :marker-missing)))

; A legacy store whose marker is behind (as the deployed node's could be
; after a crash): the upgrade's open writes the marker first, then the
; profile.  Crashed in the profile program with the old profile kept, the
; store is `unmarked' with the covering marker.
(defun hrt-legacy () (fn-hmr-state 3 (list :present (fn-hm-after-commit 1)) 2 *hrt-unmarked* nil))
(assert-event (fn-hmr-invp (hrt-legacy)))
(assert-event (equal (fn-hmr-run '((:open :marker-durable nil) (:migrate (:current ((14 . 1))) nil))
                                 (hrt-legacy))
                     (fn-hmr-state 3 (list :present (fn-hm-after-commit 2)) 2 *hrt-unmarked* nil)))

; -----------------------------------------------------------------------------
; Teeth.  Per keystone: the positive witness asserts every hypothesis and the
; conclusion; each hypothesis-removal witness asserts the retained
; hypotheses, the failure of the removed one, and the failure of the
; conclusion.

; Keystone 1, fn-hmr-step-preserves-the-invariant (and its run form).
; Positive: every step of the reachable retry history.
(defun hrt-k1-holds (op st)
  (and (fn-hmr-invp st) (fn-hmr-invp (fn-hmr-step op st))))
(assert-event (hrt-k1-holds '(:resolve 1) (fn-hmr-run (take 4 *hrt-retry*) *hrt-st0*)))
(assert-event (hrt-k1-holds '(:commit :marker-created nil) (fn-hmr-run (take 2 *hrt-retry*) *hrt-st0*)))
(assert-event (fn-hmr-invp (fn-hmr-run *hrt-retry-crashed* *hrt-st0*)))
; Removal of (fn-hmr-invp st), a corrupted-state witness: a process live over
; a marker behind the durable history -- an open that skipped the catch-up
; -- answers the retry, and the answer is above the marker.
(defun hrt-no-catch-up ()
  (fn-hmr-state 2 (list :present (fn-hm-after-commit 0)) 1 *hrt-unmarked* t))
(assert-event (not (fn-hmr-invp (hrt-no-catch-up))))
(assert-event (not (fn-hmr-invp (fn-hmr-step '(:resolve 1) (hrt-no-catch-up)))))
(assert-event (not (fn-hmr-invp (fn-hmr-run '((:resolve 1)) (hrt-no-catch-up)))))

; Keystone 2, fn-hmr-open-refuses-below-every-answered-record.
(defun hrt-k2-hyps (ops st k)
  (and (fn-hmr-invp st) (natp k) (< k (nfix (nth 2 (fn-hmr-run ops st))))))
(defun hrt-k2-concl (ops st k)
  (let ((end (fn-hmr-run ops st)))
    (equal (fn-hmr-open-verdict (nth 3 end) (nth 1 end) k)
           (list :refused :history-short-of-marker
                 (fn-hmr-marker-count (nth 1 end))))))
(assert-event (and (hrt-k2-hyps *hrt-retry* *hrt-st0* 1)
                   (hrt-k2-concl *hrt-retry* *hrt-st0* 1)))
(assert-event (and (hrt-k2-hyps *hrt-retry* *hrt-st0* 0)
                   (hrt-k2-concl *hrt-retry* *hrt-st0* 0)))
; Removal of the invariant (corrupted state): the retry answered without the
; catch-up, the newest file then lost, is admitted.
(assert-event (and (not (fn-hmr-invp (hrt-no-catch-up)))
                   (natp 1) (< 1 (nfix (nth 2 (fn-hmr-run '((:resolve 1)) (hrt-no-catch-up)))))))
(must-fail (assert-event (hrt-k2-concl '((:resolve 1)) (hrt-no-catch-up) 1)))
(assert-event (equal (fn-hmr-open-verdict *hrt-unmarked* (list :present (fn-hm-after-commit 0)) 1)
                     '(:admitted :marked 1)))
; Removal of (natp k).
(assert-event (and (fn-hmr-invp *hrt-st0*) (not (natp -1))
                   (< -1 (nfix (nth 2 (hrt-end))))))
(must-fail (assert-event (hrt-k2-concl *hrt-retry* *hrt-st0* -1)))
; Removal of (< k A): the whole history is there.
(assert-event (and (fn-hmr-invp *hrt-st0*) (natp 2) (not (< 2 (nfix (nth 2 (hrt-end)))))))
(must-fail (assert-event (hrt-k2-concl *hrt-retry* *hrt-st0* 2)))

; Keystone 3, fn-hmr-required-store-never-admits-an-absent-marker.
(defun hrt-k3-concl (ops st k)
  (equal (fn-hmr-open-verdict (nth 3 (fn-hmr-run ops st)) '(:absent) k)
         (list :refused :marker-missing)))
(assert-event (and (fn-bs-profile-marker-requiredp (nth 3 (hrt-migrated))) (natp 2)
                   (hrt-k3-concl *hrt-retry* (hrt-migrated) 2)))
; Removal of the requirement: an `unmarked' store admits the absence.
(assert-event (and (not (fn-bs-profile-marker-requiredp (nth 3 (hrt-end)))) (natp 2)))
(must-fail (assert-event (hrt-k3-concl nil (hrt-end) 2)))
; Removal of (natp k).
(assert-event (and (fn-bs-profile-marker-requiredp (nth 3 (hrt-migrated))) (not (natp -1))))
(must-fail (assert-event (hrt-k3-concl nil (hrt-migrated) -1)))

; Keystone 4, fn-hmr-requirement-follows-a-covering-marker.
(defun hrt-live-covered () (fn-hmr-run '((:open :marker-durable nil)) (hrt-rest)))
(defun hrt-k4-concl (op st)
  (and (equal (car op) :migrate) (nth 4 st)
       (fn-hmr-coveringp (nth 1 st) (fn-hmr-count st))
       (equal (nth 1 (fn-hmr-step op st)) (nth 1 st))))
(assert-event (and (not (fn-bs-profile-marker-requiredp (nth 3 (hrt-live-covered))))
                   (fn-bs-profile-marker-requiredp
                    (nth 3 (fn-hmr-step (list :migrate *hrt-migrate* t) (hrt-live-covered))))
                   (hrt-k4-concl (list :migrate *hrt-migrate* t) (hrt-live-covered))))
; Removal of "unmarked before": a required store stays required over any
; step, here an answered retry.
(defun hrt-required-live () (fn-hmr-run '((:open :marker-durable nil)) (hrt-migrated)))
(assert-event (and (fn-bs-profile-marker-requiredp (nth 3 (hrt-required-live)))
                   (fn-bs-profile-marker-requiredp
                    (nth 3 (fn-hmr-step '(:resolve 0) (hrt-required-live))))))
(must-fail (assert-event (hrt-k4-concl '(:resolve 0) (hrt-required-live))))
; Removal of "required after": a burn.
(assert-event (and (not (fn-bs-profile-marker-requiredp (nth 3 (hrt-live-covered))))
                   (not (fn-bs-profile-marker-requiredp
                         (nth 3 (fn-hmr-step '(:burn) (hrt-live-covered)))))))
(must-fail (assert-event (hrt-k4-concl '(:burn) (hrt-live-covered))))
; The gate itself: a live process over a marker behind the history (a
; corrupted state) cannot migrate.
(assert-event (not (fn-bs-profile-marker-requiredp
                    (nth 3 (fn-hmr-step (list :migrate *hrt-migrate* t) (hrt-no-catch-up))))))

; Keystone 5, fn-hmr-legacy-store-migrates-by-the-two-step.
(defun hrt-k5-concl (op1 op2 st)
  (let ((mid (fn-hmr-step op1 st)))
    (and (equal (car op1) :open) (equal (car op2) :migrate)
         (fn-hmr-coveringp (nth 1 mid) (fn-hmr-count mid))
         (equal (nth 1 (fn-hmr-step op2 mid)) (nth 1 mid)))))
(defconst *hrt-open* '(:open :marker-durable nil))
(defconst *hrt-mig* (list :migrate *hrt-migrate* t))
(assert-event (and (not (nth 4 (hrt-legacy)))
                   (not (fn-bs-profile-marker-requiredp (nth 3 (hrt-legacy))))
                   (fn-bs-profile-marker-requiredp
                    (nth 3 (fn-hmr-step *hrt-mig* (fn-hmr-step *hrt-open* (hrt-legacy)))))
                   (hrt-k5-concl *hrt-open* *hrt-mig* (hrt-legacy))))
; Removal of "at rest": a live process migrates after answering a retry.
(assert-event (and (nth 4 (hrt-live-covered))
                   (not (fn-bs-profile-marker-requiredp (nth 3 (hrt-live-covered))))
                   (fn-bs-profile-marker-requiredp
                    (nth 3 (fn-hmr-step *hrt-mig* (fn-hmr-step '(:resolve 0) (hrt-live-covered)))))))
(must-fail (assert-event (hrt-k5-concl '(:resolve 0) *hrt-mig* (hrt-live-covered))))
; Removal of "unmarked": a required store at rest, two burns.
(assert-event (and (not (nth 4 (hrt-migrated)))
                   (fn-bs-profile-marker-requiredp (nth 3 (hrt-migrated)))
                   (fn-bs-profile-marker-requiredp
                    (nth 3 (fn-hmr-step '(:burn) (fn-hmr-step '(:burn) (hrt-migrated)))))))
(must-fail (assert-event (hrt-k5-concl '(:burn) '(:burn) (hrt-migrated))))
; Removal of "required after": the open alone, then a burn.
(assert-event (and (not (nth 4 (hrt-legacy)))
                   (not (fn-bs-profile-marker-requiredp (nth 3 (hrt-legacy))))
                   (not (fn-bs-profile-marker-requiredp
                         (nth 3 (fn-hmr-step '(:burn) (fn-hmr-step *hrt-open* (hrt-legacy))))))))
(must-fail (assert-event (hrt-k5-concl *hrt-open* '(:burn) (hrt-legacy))))
