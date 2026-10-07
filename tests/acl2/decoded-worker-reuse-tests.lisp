; PRF-1298: actual acquisition/return/retirement/reassignment, no invented
; completion token. Corrupted carry mutations are labelled separately.
(in-package "ACL2")
(include-book "../../books/decoded-worker-job")
(include-book "../../books/defkeystone")

(defun-nx fn-dwrt-running ()
  (let* ((ledger (mv-nth 1 (fn-prl-register
                           (fn-prl-make '(200000 0 2 1 20)) 7 '(64 0 1 0 0))))
         (admitted (fn-pwz-admit ledger '(7 100 320 120 40 200 99 250 0)
                                 '(86928 0 0 1 1)))
         (token (nth 1 admitted))
         (acquired (fn-pwx-acquire (nth 2 admitted) (fn-pxe-new 0) token))
         (carry (mv-nth 1 (fn-dwa-assign (nth 2 acquired) (nth 1 acquired)
                                        token token 47 (create-fn-pww-carry)))))
    (list (nth 2 acquired) (nth 1 acquired) token carry)))
(defun-nx fn-dwrt-returned (cancelp)
  (let* ((r (fn-dwrt-running))
         (cancel (if cancelp (fn-pwx-cancel (nth 0 r) (nth 1 r) (nth 2 r))
                   (list :unchanged (nth 1 r) (nth 0 r))))
         (returned (fn-pwx-return (nth 2 cancel) (nth 1 cancel) (nth 2 r))))
    (list (nth 2 returned) (nth 1 returned) (nth 2 r) (nth 3 r))))
(defun-nx fn-dwrt-retired (cancelp)
  (let ((r (fn-dwrt-returned cancelp)))
    (fn-dwa-retire (nth 0 r) (nth 1 r) (nth 2 r) (nth 3 r))))

(defthm fn-dwrt-returned-positive
 (let* ((r (fn-dwrt-returned nil)) (retired (fn-dwrt-retired nil)))
  (and (fn-pwx-boundp (nth 0 r) (nth 1 r) (nth 2 r) :returned)
       (equal (car retired) :reusable)
       (equal (cadr retired) (create-fn-pww-carry))
       (equal (fn-dwa-retire (nth 0 r) (nth 1 r) (nth 2 r) (cadr retired))
              (list :decoded-retirement-unavailable (cadr retired)))))
 :rule-classes nil)
(defthm fn-dwrt-cancelled-positive
 (let ((r (fn-dwrt-returned t)))
  (and (fn-pwx-boundp (nth 0 r) (nth 1 r) (nth 2 r) :cancelled-returned)
       (equal (car (fn-dwrt-retired t)) :reusable)))
 :rule-classes nil)
; Physical running state does not authorize recycling.
(defthm fn-dwrt-running-refusal
 (let ((r (fn-dwrt-running)))
  (and (fn-pwx-boundp (nth 0 r) (nth 1 r) (nth 2 r) :running)
       (equal (fn-dwa-retire (nth 0 r) (nth 1 r) (nth 2 r) (nth 3 r))
              (list :decoded-retirement-unavailable (nth 3 r)))))
 :rule-classes nil)
; MUTATION: pending read, torn intermediate phase, and wrong token all refuse.
(defthm fn-dwrt-corrupted-carry-refusal
 (let* ((r (fn-dwrt-returned nil)) (c (nth 3 r)))
  (and
   (equal (car (fn-dwa-retire (nth 0 r) (nth 1 r) (nth 2 r)
                 (update-fn-pww-pending-action '(:read) c))) :decoded-retirement-unavailable)
   (equal (car (fn-dwa-retire (nth 0 r) (nth 1 r) (nth 2 r)
                 (update-fn-pww-phase :codec-acting c))) :decoded-retirement-unavailable)
   (equal (car (fn-dwa-retire (nth 0 r) (nth 1 r) nil c)) :decoded-retirement-unavailable)))
 :rule-classes nil)
; Release the previous token, acquire its successor, and assign the SAME carry.
(defthm fn-dwrt-reassignment
 (let* ((r (fn-dwrt-returned nil))
        (carry (cadr (fn-dwrt-retired nil)))
        (release (fn-pwx-release (nth 0 r) (nth 1 r) (nth 2 r)))
        (admit (fn-pwz-admit (nth 2 release) '(7 100 320 120 40 200 99 250 0)
                             '(86928 0 0 1 1)))
        (token (nth 1 admit))
        (acquire (fn-pwx-acquire (nth 2 admit) (nth 1 release) token))
        (assign (fn-dwa-assign (nth 2 acquire) (nth 1 acquire) token token 48 carry)))
   (and (equal (car release) :released)
        (equal (car acquire) :assigned)
        (not (equal token (nth 2 r)))
        (equal (car assign) :decoded-assigned)
        (equal (fn-pww-token (cadr assign)) token)
        (equal (fn-pww-source-incarnation (cadr assign)) 48)
        (null (fn-pww-controller (cadr assign)))))
 :rule-classes nil)

; fn-dwa-retirement-revokes-prior-authority and fn-dwa-refused-retirement-
; preserves-carry (TEETH CONTRACT v1).  Both claims are over mv-nth of
; fn-dwa-retire, so the witnesses are ground theorems (lemma debt,
; TEETH-OWED-MV-CLAIM); the antecedent stays inside the implication, so the
; mutations drop it at the other state or break one conclusion.
(defthm dwat-revokes-witness
  (implies (equal (mv-nth 0 (fn-dwa-retire (nth 0 (fn-dwrt-returned nil)) (nth 1 (fn-dwrt-returned nil)) (nth 2 (fn-dwrt-returned nil)) (nth 3 (fn-dwrt-returned nil)))) :reusable)
           (let ((next (mv-nth 1 (fn-dwa-retire (nth 0 (fn-dwrt-returned nil)) (nth 1 (fn-dwrt-returned nil)) (nth 2 (fn-dwrt-returned nil)) (nth 3 (fn-dwrt-returned nil))))))
             (and (equal (fn-pww-token next) nil)
                  (equal (fn-pww-root next) nil)
                  (equal (fn-pww-source-incarnation next) nil)
                  (equal (fn-pww-controller next) nil)
                  (equal (fn-pww-pending-action next) nil)
                  (equal (fn-pww-storage-receipt next) nil)
                  (equal (fn-pww-borrow-phase next) :none)
                  (equal (fn-pww-phase next) :uninstalled))))
  :rule-classes nil)

(defthm dwat-revokes-mut1
  (and (implies (equal (mv-nth 0 (fn-dwa-retire (nth 0 (fn-dwrt-returned nil)) (nth 1 (fn-dwrt-returned nil)) (nth 2 (fn-dwrt-returned nil)) (nth 3 (fn-dwrt-returned nil)))) :reusable)
           (let ((next (mv-nth 1 (fn-dwa-retire (nth 0 (fn-dwrt-returned nil)) (nth 1 (fn-dwrt-returned nil)) (nth 2 (fn-dwrt-returned nil)) (nth 3 (fn-dwrt-returned nil))))))
             (and (equal (fn-pww-token next) nil)
                  (equal (fn-pww-root next) nil)
                  (equal (fn-pww-source-incarnation next) nil)
                  (equal (fn-pww-controller next) nil)
                  (equal (fn-pww-pending-action next) nil)
                  (equal (fn-pww-storage-receipt next) nil)
                  (equal (fn-pww-borrow-phase next) :none)
                  (equal (fn-pww-phase next) :uninstalled))))
       (not (implies (equal (mv-nth 0 (fn-dwa-retire (nth 0 (fn-dwrt-returned nil)) (nth 1 (fn-dwrt-returned nil)) (nth 2 (fn-dwrt-returned nil)) (nth 3 (fn-dwrt-returned nil)))) :reusable)
           (equal (fn-pww-token (mv-nth 1 (fn-dwa-retire (nth 0 (fn-dwrt-returned nil)) (nth 1 (fn-dwrt-returned nil)) (nth 2 (fn-dwrt-returned nil)) (nth 3 (fn-dwrt-returned nil))))) (nth 2 (fn-dwrt-returned nil))))))
  :rule-classes nil)

(defthm dwat-revokes-mut2
  (and (implies (equal (mv-nth 0 (fn-dwa-retire (nth 0 (fn-dwrt-running)) (nth 1 (fn-dwrt-running)) (nth 2 (fn-dwrt-running)) (nth 3 (fn-dwrt-running)))) :reusable)
           (let ((next (mv-nth 1 (fn-dwa-retire (nth 0 (fn-dwrt-running)) (nth 1 (fn-dwrt-running)) (nth 2 (fn-dwrt-running)) (nth 3 (fn-dwrt-running))))))
             (and (equal (fn-pww-token next) nil)
                  (equal (fn-pww-root next) nil)
                  (equal (fn-pww-source-incarnation next) nil)
                  (equal (fn-pww-controller next) nil)
                  (equal (fn-pww-pending-action next) nil)
                  (equal (fn-pww-storage-receipt next) nil)
                  (equal (fn-pww-borrow-phase next) :none)
                  (equal (fn-pww-phase next) :uninstalled))))
       (not (implies t (let ((next (mv-nth 1 (fn-dwa-retire (nth 0 (fn-dwrt-running)) (nth 1 (fn-dwrt-running)) (nth 2 (fn-dwrt-running)) (nth 3 (fn-dwrt-running))))))
             (and (equal (fn-pww-token next) nil)
                  (equal (fn-pww-root next) nil)
                  (equal (fn-pww-source-incarnation next) nil)
                  (equal (fn-pww-controller next) nil)
                  (equal (fn-pww-pending-action next) nil)
                  (equal (fn-pww-storage-receipt next) nil)
                  (equal (fn-pww-borrow-phase next) :none)
                  (equal (fn-pww-phase next) :uninstalled))))))
  :rule-classes nil)

(defthm dwat-revokes-mut3
  (and (implies (equal (mv-nth 0 (fn-dwa-retire (nth 0 (fn-dwrt-returned nil)) (nth 1 (fn-dwrt-returned nil)) (nth 2 (fn-dwrt-returned nil)) (nth 3 (fn-dwrt-returned nil)))) :reusable)
           (let ((next (mv-nth 1 (fn-dwa-retire (nth 0 (fn-dwrt-returned nil)) (nth 1 (fn-dwrt-returned nil)) (nth 2 (fn-dwrt-returned nil)) (nth 3 (fn-dwrt-returned nil))))))
             (and (equal (fn-pww-token next) nil)
                  (equal (fn-pww-root next) nil)
                  (equal (fn-pww-source-incarnation next) nil)
                  (equal (fn-pww-controller next) nil)
                  (equal (fn-pww-pending-action next) nil)
                  (equal (fn-pww-storage-receipt next) nil)
                  (equal (fn-pww-borrow-phase next) :none)
                  (equal (fn-pww-phase next) :uninstalled))))
       (not (implies (equal (mv-nth 0 (fn-dwa-retire (nth 0 (fn-dwrt-returned nil)) (nth 1 (fn-dwrt-returned nil)) (nth 2 (fn-dwrt-returned nil)) (nth 3 (fn-dwrt-returned nil)))) :reusable)
           (let ((next (mv-nth 1 (fn-dwa-retire (nth 0 (fn-dwrt-returned nil)) (nth 1 (fn-dwrt-returned nil)) (nth 2 (fn-dwrt-returned nil)) (nth 3 (fn-dwrt-returned nil))))))
             (equal (fn-pww-phase next) :assigned)))))
  :rule-classes nil)

(defteeth fn-dwa-retirement-revokes-prior-authority
  :claim (() (implies (equal (mv-nth 0 (fn-dwa-retire ledger worker token carry)) :reusable)
           (let ((next (mv-nth 1 (fn-dwa-retire ledger worker token carry))))
             (and (equal (fn-pww-token next) nil)
                  (equal (fn-pww-root next) nil)
                  (equal (fn-pww-source-incarnation next) nil)
                  (equal (fn-pww-controller next) nil)
                  (equal (fn-pww-pending-action next) nil)
                  (equal (fn-pww-storage-receipt next) nil)
                  (equal (fn-pww-borrow-phase next) :none)
                  (equal (fn-pww-phase next) :uninstalled)))))
  :subject fn-dwa-retire
  :witness-lemma dwat-revokes-witness
  :witness ((ledger (nth 0 (fn-dwrt-returned nil))) (worker (nth 1 (fn-dwrt-returned nil))) (token (nth 2 (fn-dwrt-returned nil))) (carry (nth 3 (fn-dwrt-returned nil))))
  :mutations ((token-kept
               (:conclusion (implies (equal (mv-nth 0 (fn-dwa-retire ledger worker token carry)) :reusable)
           (equal (fn-pww-token (mv-nth 1 (fn-dwa-retire ledger worker token carry))) token)))
               ((ledger (nth 0 (fn-dwrt-returned nil))) (worker (nth 1 (fn-dwrt-returned nil))) (token (nth 2 (fn-dwrt-returned nil))) (carry (nth 3 (fn-dwrt-returned nil))))
               :fault "a retirement that leaves the retired token in the carry"
               :lemma dwat-revokes-mut1)
              (no-reusable-hypothesis
               (:conclusion (implies t (let ((next (mv-nth 1 (fn-dwa-retire ledger worker token carry))))
             (and (equal (fn-pww-token next) nil)
                  (equal (fn-pww-root next) nil)
                  (equal (fn-pww-source-incarnation next) nil)
                  (equal (fn-pww-controller next) nil)
                  (equal (fn-pww-pending-action next) nil)
                  (equal (fn-pww-storage-receipt next) nil)
                  (equal (fn-pww-borrow-phase next) :none)
                  (equal (fn-pww-phase next) :uninstalled)))))
               ((ledger (nth 0 (fn-dwrt-running))) (worker (nth 1 (fn-dwrt-running))) (token (nth 2 (fn-dwrt-running))) (carry (nth 3 (fn-dwrt-running))))
               :fault "a statement that wipes the carry even when the retirement is refused"
               :lemma dwat-revokes-mut2)
              (phase-left-assigned
               (:conclusion (implies (equal (mv-nth 0 (fn-dwa-retire ledger worker token carry)) :reusable)
           (let ((next (mv-nth 1 (fn-dwa-retire ledger worker token carry))))
             (equal (fn-pww-phase next) :assigned))))
               ((ledger (nth 0 (fn-dwrt-returned nil))) (worker (nth 1 (fn-dwrt-returned nil))) (token (nth 2 (fn-dwrt-returned nil))) (carry (nth 3 (fn-dwrt-returned nil))))
               :fault "a retirement that leaves the carry assigned"
               :lemma dwat-revokes-mut3)))

(defthm dwat-refused-witness
  (implies (not (equal (mv-nth 0 (fn-dwa-retire (nth 0 (fn-dwrt-running)) (nth 1 (fn-dwrt-running)) (nth 2 (fn-dwrt-running)) (nth 3 (fn-dwrt-running)))) :reusable))
           (equal (mv-nth 1 (fn-dwa-retire (nth 0 (fn-dwrt-running)) (nth 1 (fn-dwrt-running)) (nth 2 (fn-dwrt-running)) (nth 3 (fn-dwrt-running)))) (nth 3 (fn-dwrt-running))))
  :rule-classes nil)

(defthm dwat-refused-mut1
  (and (implies (not (equal (mv-nth 0 (fn-dwa-retire (nth 0 (fn-dwrt-running)) (nth 1 (fn-dwrt-running)) (nth 2 (fn-dwrt-running)) (nth 3 (fn-dwrt-running)))) :reusable))
           (equal (mv-nth 1 (fn-dwa-retire (nth 0 (fn-dwrt-running)) (nth 1 (fn-dwrt-running)) (nth 2 (fn-dwrt-running)) (nth 3 (fn-dwrt-running)))) (nth 3 (fn-dwrt-running))))
       (not (implies (not (equal (mv-nth 0 (fn-dwa-retire (nth 0 (fn-dwrt-running)) (nth 1 (fn-dwrt-running)) (nth 2 (fn-dwrt-running)) (nth 3 (fn-dwrt-running)))) :reusable))
           (equal (mv-nth 1 (fn-dwa-retire (nth 0 (fn-dwrt-running)) (nth 1 (fn-dwrt-running)) (nth 2 (fn-dwrt-running)) (nth 3 (fn-dwrt-running)))) (create-fn-pww-carry)))))
  :rule-classes nil)

(defthm dwat-refused-mut2
  (and (implies (not (equal (mv-nth 0 (fn-dwa-retire (nth 0 (fn-dwrt-returned nil)) (nth 1 (fn-dwrt-returned nil)) (nth 2 (fn-dwrt-returned nil)) (nth 3 (fn-dwrt-returned nil)))) :reusable))
           (equal (mv-nth 1 (fn-dwa-retire (nth 0 (fn-dwrt-returned nil)) (nth 1 (fn-dwrt-returned nil)) (nth 2 (fn-dwrt-returned nil)) (nth 3 (fn-dwrt-returned nil)))) (nth 3 (fn-dwrt-returned nil))))
       (not (implies t (equal (mv-nth 1 (fn-dwa-retire (nth 0 (fn-dwrt-returned nil)) (nth 1 (fn-dwrt-returned nil)) (nth 2 (fn-dwrt-returned nil)) (nth 3 (fn-dwrt-returned nil)))) (nth 3 (fn-dwrt-returned nil))))))
  :rule-classes nil)

(defteeth fn-dwa-refused-retirement-preserves-carry
  :claim (() (implies (not (equal (mv-nth 0 (fn-dwa-retire ledger worker token carry)) :reusable))
           (equal (mv-nth 1 (fn-dwa-retire ledger worker token carry)) carry)))
  :subject fn-dwa-retire
  :witness-lemma dwat-refused-witness
  :witness ((ledger (nth 0 (fn-dwrt-running))) (worker (nth 1 (fn-dwrt-running))) (token (nth 2 (fn-dwrt-running))) (carry (nth 3 (fn-dwrt-running))))
  :mutations ((refusal-wipes-the-carry
               (:conclusion (implies (not (equal (mv-nth 0 (fn-dwa-retire ledger worker token carry)) :reusable))
           (equal (mv-nth 1 (fn-dwa-retire ledger worker token carry)) (create-fn-pww-carry))))
               ((ledger (nth 0 (fn-dwrt-running))) (worker (nth 1 (fn-dwrt-running))) (token (nth 2 (fn-dwrt-running))) (carry (nth 3 (fn-dwrt-running))))
               :fault "a refused retirement that wipes the carry anyway"
               :lemma dwat-refused-mut1)
              (no-refusal-hypothesis
               (:conclusion (implies t (equal (mv-nth 1 (fn-dwa-retire ledger worker token carry)) carry)))
               ((ledger (nth 0 (fn-dwrt-returned nil))) (worker (nth 1 (fn-dwrt-returned nil))) (token (nth 2 (fn-dwrt-returned nil))) (carry (nth 3 (fn-dwrt-returned nil))))
               :fault "a statement that the carry is unchanged even when the retirement succeeded"
               :lemma dwat-refused-mut2)))

; fn-dwj-retirement-preserves-private-backing (TEETH CONTRACT v1).  The job is
; a ground value: the fixture's returned carry in a fresh job
; (update-fn-dwj-carry over create-fn-decoded-job), so its private backing is
; the stobj's initial one.  The witnesses are ground theorems written with
; the claim's let over NEXT and the free JOB.  The mutation is a retirement
; that leaves the carry as well: false, because the retirement wipes it.
(defthm dwjt-backing-witness
  (let ((next (mv-nth 1 (fn-dwj-retire (nth 0 (fn-dwrt-returned nil)) (nth 1 (fn-dwrt-returned nil)) (nth 2 (fn-dwrt-returned nil)) (update-fn-dwj-carry (nth 3 (fn-dwrt-returned nil)) (create-fn-decoded-job))))) (job (update-fn-dwj-carry (nth 3 (fn-dwrt-returned nil)) (create-fn-decoded-job))))
    (and (equal (fn-dwj-input next) (fn-dwj-input job))
         (equal (fn-dwj-hash next) (fn-dwj-hash job))
         (equal (fn-dwj-zin next) (fn-dwj-zin job))
         (equal (fn-dwj-win next) (fn-dwj-win job))
         (equal (fn-dwj-tab next) (fn-dwj-tab job))
         (equal (fn-dwj-out next) (fn-dwj-out job))
         (equal (fn-dwj-window next) (fn-dwj-window job))))
  :rule-classes nil)

(defthm dwjt-backing-mut1
  (and (let ((next (mv-nth 1 (fn-dwj-retire (nth 0 (fn-dwrt-returned nil)) (nth 1 (fn-dwrt-returned nil)) (nth 2 (fn-dwrt-returned nil)) (update-fn-dwj-carry (nth 3 (fn-dwrt-returned nil)) (create-fn-decoded-job))))) (job (update-fn-dwj-carry (nth 3 (fn-dwrt-returned nil)) (create-fn-decoded-job))))
    (and (equal (fn-dwj-input next) (fn-dwj-input job))
         (equal (fn-dwj-hash next) (fn-dwj-hash job))
         (equal (fn-dwj-zin next) (fn-dwj-zin job))
         (equal (fn-dwj-win next) (fn-dwj-win job))
         (equal (fn-dwj-tab next) (fn-dwj-tab job))
         (equal (fn-dwj-out next) (fn-dwj-out job))
         (equal (fn-dwj-window next) (fn-dwj-window job))))
       (not (let ((next (mv-nth 1 (fn-dwj-retire (nth 0 (fn-dwrt-returned nil)) (nth 1 (fn-dwrt-returned nil)) (nth 2 (fn-dwrt-returned nil)) (update-fn-dwj-carry (nth 3 (fn-dwrt-returned nil)) (create-fn-decoded-job))))) (job (update-fn-dwj-carry (nth 3 (fn-dwrt-returned nil)) (create-fn-decoded-job))))
    (and (and (equal (fn-dwj-input next) (fn-dwj-input job))
         (equal (fn-dwj-hash next) (fn-dwj-hash job))
         (equal (fn-dwj-zin next) (fn-dwj-zin job))
         (equal (fn-dwj-win next) (fn-dwj-win job))
         (equal (fn-dwj-tab next) (fn-dwj-tab job))
         (equal (fn-dwj-out next) (fn-dwj-out job))
         (equal (fn-dwj-window next) (fn-dwj-window job))) (equal (fn-dwj-carry next) (fn-dwj-carry job))))))
  :rule-classes nil)

(defteeth fn-dwj-retirement-preserves-private-backing
  :claim (() (let ((next (mv-nth 1 (fn-dwj-retire ledger worker token job))))
    (and (equal (fn-dwj-input next) (fn-dwj-input job))
         (equal (fn-dwj-hash next) (fn-dwj-hash job))
         (equal (fn-dwj-zin next) (fn-dwj-zin job))
         (equal (fn-dwj-win next) (fn-dwj-win job))
         (equal (fn-dwj-tab next) (fn-dwj-tab job))
         (equal (fn-dwj-out next) (fn-dwj-out job))
         (equal (fn-dwj-window next) (fn-dwj-window job)))))
  :subject fn-dwj-retire
  :witness-lemma dwjt-backing-witness
  :witness ((ledger (nth 0 (fn-dwrt-returned nil))) (worker (nth 1 (fn-dwrt-returned nil))) (token (nth 2 (fn-dwrt-returned nil))) (job (update-fn-dwj-carry (nth 3 (fn-dwrt-returned nil)) (create-fn-decoded-job))))
  :mutations ((carry-kept
               (:conclusion (let ((next (mv-nth 1 (fn-dwj-retire ledger worker token job))))
    (and (and (equal (fn-dwj-input next) (fn-dwj-input job))
         (equal (fn-dwj-hash next) (fn-dwj-hash job))
         (equal (fn-dwj-zin next) (fn-dwj-zin job))
         (equal (fn-dwj-win next) (fn-dwj-win job))
         (equal (fn-dwj-tab next) (fn-dwj-tab job))
         (equal (fn-dwj-out next) (fn-dwj-out job))
         (equal (fn-dwj-window next) (fn-dwj-window job))) (equal (fn-dwj-carry next) (fn-dwj-carry job)))))
               ((ledger (nth 0 (fn-dwrt-returned nil))) (worker (nth 1 (fn-dwrt-returned nil))) (token (nth 2 (fn-dwrt-returned nil))) (job (update-fn-dwj-carry (nth 3 (fn-dwrt-returned nil)) (create-fn-decoded-job))))
               :fault "a retirement claimed to leave the carry's authority in place"
               :lemma dwjt-backing-mut1)))
