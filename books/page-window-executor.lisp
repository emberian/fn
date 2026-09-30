; PRF-1128: exact window ownership on the persistent physical executor.
; Shares the idle four-field slot with page-read-executor, but retains the
; FULL typed window token. No projection drops payload offset or length.
(in-package "ACL2")
(include-book "page-window-lease")
(include-book "page-read-executor")
(include-book "decoded-window-descriptor")

(local
 (defthm fn-pwx-ledger-nth-unfolds
   (implies (natp n) (equal (fn-prl-nth n x) (nth n x)))
   :hints (("Goal" :induct (fn-prl-nth n x) :in-theory (enable fn-prl-nth nth)))))

(defun fn-pwx-tokenp (token)
  (declare (xargs :guard t))
  (and (true-listp token) (natp (nth 1 token))
       (or (and (equal (len token) 9) (equal (nth 0 token) :window)
                (fn-prw-descriptorp (cddr token)))
           (fn-pwz-tokenp token))))

(defun fn-pwx-rowp (w)
  (declare (xargs :guard t))
  (and (true-listp w) (equal (len w) 4) (natp (nth 0 w))
       (or (null (nth 1 w)) (natp (nth 1 w)))
       (if (equal (nth 2 w) :idle) (null (nth 3 w))
         (and (member-equal (nth 2 w) '(:running :returned :cancelled-running :cancelled-returned))
              (fn-pwx-tokenp (nth 3 w))
              (equal (nth 1 w) (fn-prl-nth 1 (nth 3 w))))) t))

(defun fn-pwx-boundp (ledger w token phase)
  (declare (xargs :guard t))
  (and (fn-pwx-rowp w) (fn-pwx-tokenp token)
       (equal (fn-prl-nth 2 w) phase)
       (equal (fn-prl-nth 3 w) token)
       (equal (fn-prw-phase ledger token)
              (cond ((equal phase :cancelled-running) :running)
                    ((equal phase :cancelled-returned) :returned)
                    (t phase)))
       (equal (fn-prl-nth 3 (cdr (fn-prl-binding token (fn-prl-nth 3 ledger))))
              (fn-prl-nth 0 w))))

(defun fn-pwx-acquire (ledger w token)
  (declare (xargs :guard t :guard-hints (("Goal" :in-theory (enable fn-prl-nth fn-prl-binding)))))
  (let* ((rows (fn-prl-nth 3 ledger))
         (row (cdr (fn-prl-binding token rows))))
    (if (not (and (fn-pwx-rowp w) (equal (fn-prl-nth 2 w) :idle)
                  (fn-pwx-tokenp token) (equal (fn-prw-phase ledger token) :running)
                  (null (fn-prl-nth 3 row))
                  (or (null (fn-prl-nth 1 w))
                      (< (fn-prl-nth 1 w) (fn-prl-nth 1 token)))))
        (mv :stale-job w ledger)
      (mv :assigned (list (fn-prl-nth 0 w) (fn-prl-nth 1 token) :running token)
          (fn-prl-build (fn-prl-nth 0 ledger) (fn-prl-nth 1 ledger) (fn-prl-nth 2 ledger)
            (cons (cons token (list (fn-prl-nth 0 row) :window :running (fn-prl-nth 0 w)))
                  (fn-prl-remove token rows))
            (fn-prl-nth 4 ledger))))))

; Called only after actual worker return or join. Retains every charge and
; the exact slot until the borrower drops every private/output alias.
(defun fn-pwx-return (ledger w token)
  (declare (xargs :guard t :guard-hints (("Goal" :in-theory (enable fn-prl-binding)))))
  (if (not (or (fn-pwx-boundp ledger w token :running)
               (fn-pwx-boundp ledger w token :cancelled-running))) (mv :stale-job w ledger)
    (let* ((rows (fn-prl-nth 3 ledger)) (row (cdr (fn-prl-binding token rows))))
      (mv :returned (list (fn-prl-nth 0 w) (fn-prl-nth 1 w)
                          (if (equal (fn-prl-nth 2 w) :cancelled-running)
                              :cancelled-returned :returned) token)
          (fn-prl-build (fn-prl-nth 0 ledger) (fn-prl-nth 1 ledger) (fn-prl-nth 2 ledger)
            (cons (cons token (list (fn-prl-nth 0 row) :window :returned (fn-prl-nth 0 w)))
                  (fn-prl-remove token rows))
            (fn-prl-nth 4 ledger))))))

(defun fn-pwx-release (ledger w token)
  (declare (xargs :guard t))
  (if (not (fn-pwx-boundp ledger w token :returned)) (mv :stale-job w ledger)
    (mv-let (word ledger1) (fn-prw-release ledger token)
      (if (equal word :released)
          (mv :released (list (fn-prl-nth 0 w) (fn-prl-nth 1 w) :idle nil) ledger1)
        (mv :stale-job w ledger)))))

; Cancellation revokes publication authority, but neither marks actual return
; nor frees any charge. The four-field worker is still the sole exact owner.
(defun fn-pwx-cancel (ledger w token)
  (declare (xargs :guard t))
  (cond ((fn-pwx-boundp ledger w token :running)
         (mv :cancelled (list (fn-prl-nth 0 w) (fn-prl-nth 1 w)
                             :cancelled-running token) ledger))
        ((fn-pwx-boundp ledger w token :returned)
         (mv :cancelled (list (fn-prl-nth 0 w) (fn-prl-nth 1 w)
                             :cancelled-returned token) ledger))
        ((or (fn-pwx-boundp ledger w token :cancelled-running)
             (fn-pwx-boundp ledger w token :cancelled-returned))
         (mv :cancelled w ledger))
        (t (mv :stale-job w ledger))))

(defun fn-pwx-work-permittedp (ledger w token)
  (declare (xargs :guard t))
  (fn-pwx-boundp ledger w token :running))

; Native caller has observed actual return/join and dropped retained aliases.
; Ordinary publication release remains distinct from cancelled settlement.
(defun fn-pwx-settle-cancelled (ledger w token)
  (declare (xargs :guard t))
  (if (not (fn-pwx-boundp ledger w token :cancelled-returned))
      (mv :stale-job w ledger)
    (mv-let (word ledger1) (fn-prw-release ledger token)
      (if (equal word :released)
          (mv :released (list (fn-prl-nth 0 w) (fn-prl-nth 1 w) :idle nil) ledger1)
        (mv :stale-job w ledger)))))

(defthm fn-pwx-cancel-retains-ledger
  (equal (mv-nth 2 (fn-pwx-cancel ledger w token)) ledger))

(defthm fn-pwx-cancelled-running-cannot-settle
  (implies (equal (fn-prl-nth 2 w) :cancelled-running)
           (equal (mv-list 3 (fn-pwx-settle-cancelled ledger w token))
                  (list :stale-job w ledger)))
  :hints (("Goal" :in-theory (enable fn-pwx-boundp)))
  :rule-classes nil)

(defthm fn-pwx-return-keeps-all-charges
  (equal (fn-prl-nth 1 (mv-nth 2 (fn-pwx-return ledger w token)))
         (fn-prl-nth 1 ledger))
  :hints (("Goal" :in-theory (enable fn-prl-build fn-prl-nth))))

(defthm fn-pwx-release-requires-exact-returned-window-and-slot
  (implies (equal (mv-nth 0 (fn-pwx-release ledger w token)) :released)
           (and (fn-pwx-boundp ledger w token :returned)
                (equal (mv-nth 0 (fn-prw-release ledger token)) :released)
                (equal (mv-nth 1 (fn-pwx-release ledger w token))
                       (list (fn-prl-nth 0 w) (fn-prl-nth 1 w) :idle nil))
                (equal (mv-nth 2 (fn-pwx-release ledger w token))
                       (mv-nth 1 (fn-prw-release ledger token)))))
  :rule-classes nil)

(defthm fn-pwx-other-request-cannot-return-or-release
  (implies (not (equal (fn-prl-nth 3 w) token))
           (and (equal (mv-list 3 (fn-pwx-return ledger w token)) (list :stale-job w ledger))
                (equal (mv-list 3 (fn-pwx-release ledger w token)) (list :stale-job w ledger))))
  :rule-classes nil)

(defthm fn-pwx-acquire-preserves-all-charges
  (equal (fn-prl-nth 1 (mv-nth 2 (fn-pwx-acquire ledger w token))) (fn-prl-nth 1 ledger))
  :hints (("Goal" :in-theory (enable fn-prl-build fn-prl-nth))))

(in-theory (disable fn-pwx-tokenp fn-pwx-rowp fn-pwx-boundp
                    fn-pwx-acquire fn-pwx-return fn-pwx-release))

(defthm fn-pwx-acquire-preserves-worker
  (implies (fn-pwx-rowp w)
           (fn-pwx-rowp (mv-nth 1 (fn-pwx-acquire ledger w token))))
  :hints (("Goal" :in-theory (enable fn-pwx-acquire fn-pwx-boundp fn-pwx-rowp fn-pwx-tokenp fn-prl-nth))))

(defthm fn-pwx-return-preserves-worker
  (implies (fn-pwx-rowp w)
           (fn-pwx-rowp (mv-nth 1 (fn-pwx-return ledger w token))))
  :hints (("Goal" :in-theory (enable fn-pwx-return fn-pwx-boundp fn-pwx-rowp fn-pwx-tokenp fn-prl-nth))))

(defthm fn-pwx-release-preserves-worker
  (implies (fn-pwx-rowp w)
           (fn-pwx-rowp (mv-nth 1 (fn-pwx-release ledger w token))))
  :hints (("Goal" :in-theory (enable fn-pwx-release fn-pwx-boundp fn-pwx-rowp fn-pwx-tokenp fn-prl-nth))))

(defthm fn-pwx-cancel-preserves-worker
  (implies (fn-pwx-rowp w)
           (fn-pwx-rowp (mv-nth 1 (fn-pwx-cancel ledger w token))))
  :hints (("Goal" :in-theory (enable fn-pwx-cancel fn-pwx-boundp fn-pwx-rowp fn-pwx-tokenp fn-prl-nth))))

(defthm fn-pwx-settle-cancelled-preserves-worker
  (implies (fn-pwx-rowp w)
           (fn-pwx-rowp (mv-nth 1 (fn-pwx-settle-cancelled ledger w token))))
  :hints (("Goal" :in-theory (enable fn-pwx-settle-cancelled fn-pwx-boundp fn-pwx-rowp fn-pwx-tokenp fn-prl-nth))))
