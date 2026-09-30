; INTERNAL exact shared-pool history capture custody. Not an installer.
; SOURCE comes from the actual all-event publication getter. DEMAND comes
; from the selected constructor tariff; neither is a public request field.
; One active capture serializes work admission, never caps stored history.
(in-package "ACL2")
(include-book "page-read-ledger")

(defun fn-hhc-at (n x)
 (declare (xargs :guard (natp n)))
 (if (consp x) (if (zp n) (car x) (fn-hhc-at (- n 1) (cdr x))) nil))
(defun fn-hhc-widthp (x n)
 (declare (xargs :guard (natp n)))
 (if (zp n) (null x)
  (and (consp x) (fn-hhc-widthp (cdr x) (- n 1)))))
(defun fn-hhc-tokenp (x)
 (declare (xargs :guard t))
 (and (fn-hhc-widthp x 2) (eq (fn-hhc-at 0 x) :history-capture)
      (natp (fn-hhc-at 1 x))))
; Only bounded metadata shape, never source authority or root validation.
(defun fn-hhc-sourcep (x)
 (declare (xargs :guard t))
 (and (fn-hhc-widthp x 9) (eq (fn-hhc-at 0 x) :history-source)
      (natp (fn-hhc-at 1 x)) (natp (fn-hhc-at 2 x))
      (natp (fn-hhc-at 3 x)) (natp (fn-hhc-at 5 x))
      (natp (fn-hhc-at 6 x)) (natp (fn-hhc-at 7 x))
      (<= (fn-hhc-at 7 x) (* 256 (fn-hhc-at 6 x)))
      (natp (fn-hhc-at 8 x))))
(defun fn-hhc-matches (slot token)
 (declare (xargs :guard t))
 (and (fn-hhc-widthp slot 7) (eq (fn-hhc-at 0 slot) :history-capture)
      (fn-hhc-tokenp token) (fn-hhc-tokenp (fn-hhc-at 1 slot))
      (equal (fn-hhc-at 1 token) (fn-hhc-at 1 (fn-hhc-at 1 slot)))))
(defun fn-hhc-descriptor (slot)
 (declare (xargs :guard t))
 (if (and (fn-hhc-widthp slot 7) (fn-hhc-tokenp (fn-hhc-at 1 slot))
          (fn-hhc-sourcep (fn-hhc-at 3 slot)))
  (list :history-prefix (fn-hhc-at 1 slot) (fn-hhc-at 2 slot)
        (fn-hhc-at 7 (fn-hhc-at 3 slot))
        (fn-hhc-at 1 (fn-hhc-at 3 slot))
        (fn-hhc-at 3 (fn-hhc-at 3 slot))) nil))
(defun fn-hhc-admit (ledger slot epoch source demand)
 (declare (xargs :guard t))
 (cond (slot (mv :history-source-busy nil ledger slot))
       ((not (and (natp epoch) (fn-hhc-sourcep source)
                  (fn-prs-vectorp demand)
                  (equal (fn-prl-nth 1 demand) 0)
                  (equal (fn-prl-nth 2 demand) 0)
                  (equal (fn-prl-nth 3 demand) 0)
                  (equal (fn-prl-nth 4 demand) 1)))
        (mv :invalid-history-capture nil ledger slot))
       (t
        (let ((next (fn-prl-nth 2 ledger)))
         (mv-let (word next1 charged1)
          (fn-prs-issue (fn-prl-nth 0 ledger) (fn-prl-baseline ledger)
                        '(0 0 0 0 0) (fn-prl-nth 1 ledger) next
                        (fn-prl-nth 4 (fn-prl-nth 0 ledger)) demand)
          (if (not (eq word :admitted)) (mv word nil ledger slot)
           (let* ((token (list :history-capture next))
                  (owned (list :history-capture token epoch source demand :retained nil)))
            (mv :captured (fn-hhc-descriptor owned)
                (fn-prl-build (fn-prl-nth 0 ledger) charged1 next1
                              (fn-prl-nth 3 ledger) (fn-prl-nth 4 ledger)) owned))))))))
(defun fn-hhc-recheck (slot token epoch)
 (declare (xargs :guard t))
 (if (and (fn-hhc-matches slot token) (natp epoch)
          (equal epoch (fn-hhc-at 2 slot))
          (fn-hhc-sourcep (fn-hhc-at 3 slot))
          (eq (fn-hhc-at 5 slot) :retained)) :history-source-current
  :history-source-stale))
(defun fn-hhc-read-plan (slot token epoch ordinal)
 (declare (xargs :guard t))
 (cond ((not (eq (fn-hhc-recheck slot token epoch) :history-source-current))
        '(:refused :history-source-stale))
       ((not (and (natp ordinal)
                  (< ordinal (fn-hhc-at 7 (fn-hhc-at 3 slot)))))
        '(:refused :history-ordinal))
       (t (list :read (fn-hhc-at 3 slot) ordinal))))
; Cancellation does not dispose the retained source or refund its grant.
(defun fn-hhc-cancel (slot token)
 (declare (xargs :guard t))
 (if (fn-hhc-matches slot token)
  (list :history-capture (fn-hhc-at 1 slot) (fn-hhc-at 2 slot)
        (fn-hhc-at 3 slot) (fn-hhc-at 4 slot) :cancelled (fn-hhc-at 6 slot)) slot))
; INTERNAL only: the actual scanner/reader terminal-return producer must
; establish that no borrowed row/directory/payload alias survives here.
; There is no public supplied joined/aliases-clear Boolean.
(defun fn-hhc-quiesce (slot token)
 (declare (xargs :guard t))
 (if (and (fn-hhc-matches slot token)
          (member-eq (fn-hhc-at 5 slot) '(:retained :cancelled)))
  (list :history-capture (fn-hhc-at 1 slot) (fn-hhc-at 2 slot)
        (fn-hhc-at 3 slot) (fn-hhc-at 4 slot) :quiescent nil) slot))
(local
 (defthm fn-hhc-vector-is-true-list
  (implies (fn-prs-vectorp x) (true-listp x))
  :hints (("Goal" :in-theory (enable fn-prs-vectorp fn-prs-nats-p)))))
(defun fn-hhc-release (ledger slot token)
 (declare (xargs :guard t
                 :guard-hints (("Goal" :use ((:instance fn-hhc-vector-is-true-list
                                                   (x (fn-prl-nth 1 ledger)))
                                            (:instance fn-hhc-vector-is-true-list
                                                   (x (fn-hhc-at 4 slot))))
                                       :in-theory (disable fn-prs-vectorp
                                                fn-hhc-matches fn-hhc-at fn-prl-nth)))))
 (if (not (and (fn-hhc-matches slot token)
               (eq (fn-hhc-at 5 slot) :quiescent)
               (fn-prs-vectorp (fn-prl-nth 1 ledger))
               (fn-prs-vectorp (fn-hhc-at 4 slot))
               (fn-prs-below (fn-hhc-at 4 slot) (fn-prl-nth 1 ledger))))
  (mv :history-source-held ledger slot)
  (mv :released
      (fn-prl-build (fn-prl-nth 0 ledger)
                    (fn-prs-release-reusable (fn-prl-nth 1 ledger) (fn-hhc-at 4 slot))
                    (fn-prl-nth 2 ledger) (fn-prl-nth 3 ledger) (fn-prl-nth 4 ledger)) nil)))
(defun fn-hhc-reset-status (slot)
 (declare (xargs :guard t))
 (if slot :history-source-held :history-reset-clear))

(defthm fn-hhc-capture-owns-exact-prefix-and-shared-identity
 (implies (eq (mv-nth 0 (fn-hhc-admit ledger slot epoch source demand)) :captured)
  (and (equal (mv-nth 1 (fn-hhc-admit ledger slot epoch source demand))
              (list :history-prefix (list :history-capture (fn-prl-nth 2 ledger))
                    epoch (fn-hhc-at 7 source) (fn-hhc-at 1 source) (fn-hhc-at 3 source)))
       (equal (fn-hhc-at 3 (mv-nth 3 (fn-hhc-admit ledger slot epoch source demand))) source)
       (equal (fn-prl-nth 2 (mv-nth 2 (fn-hhc-admit ledger slot epoch source demand)))
              (+ 1 (fn-prl-nth 2 ledger)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hhc-admit fn-hhc-descriptor
                   fn-hhc-sourcep fn-hhc-tokenp fn-hhc-widthp fn-hhc-at
                   fn-prs-issue fn-prl-build fn-prl-nth))))
(defthm fn-hhc-read-uses-only-owned-prefix
 (implies (eq (car (fn-hhc-read-plan slot token epoch ordinal)) :read)
  (and (equal (fn-hhc-read-plan slot token epoch ordinal)
              (list :read (fn-hhc-at 3 slot) ordinal))
       (fn-hhc-matches slot token) (natp ordinal)
       (< ordinal (fn-hhc-at 7 (fn-hhc-at 3 slot)))
       (equal epoch (fn-hhc-at 2 slot))
       (eq (fn-hhc-at 5 slot) :retained)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hhc-read-plan fn-hhc-recheck))))
(defthm fn-hhc-retained-or-cancelled-blocks-reset
 (implies (fn-hhc-matches slot token)
  (and (eq (fn-hhc-reset-status slot) :history-source-held)
       (eq (fn-hhc-reset-status (fn-hhc-cancel slot token)) :history-source-held)))
 :hints (("Goal" :in-theory (enable fn-hhc-reset-status fn-hhc-cancel
                                   fn-hhc-matches fn-hhc-at fn-hhc-widthp))))
(local
 (defthm fn-hhc-nats-at
  (implies (and (fn-prs-nats-p x) (natp n) (< n (len x)))
           (natp (fn-prl-nth n x)))
  :hints (("Goal" :induct (fn-prl-nth n x)
                   :in-theory (enable fn-prs-nats-p fn-prl-nth)))))
(local
 (defthm fn-hhc-vector-identity-natural
  (implies (fn-prs-vectorp x) (natp (fn-prl-nth 4 x)))
  :hints (("Goal" :in-theory (enable fn-prs-vectorp fn-prs-nats-p fn-prl-nth)))))
(local
 (defthm fn-hhc-released-result
  (implies (equal (mv-nth 0 (fn-hhc-release ledger slot token)) :released)
   (and (fn-prs-vectorp (fn-prl-nth 1 ledger))
        (equal (fn-hhc-release ledger slot token)
         (list :released
           (fn-prl-build (fn-prl-nth 0 ledger)
              (fn-prs-release-reusable (fn-prl-nth 1 ledger) (fn-hhc-at 4 slot))
              (fn-prl-nth 2 ledger) (fn-prl-nth 3 ledger) (fn-prl-nth 4 ledger)) nil))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                              '(fn-hhc-release mv-nth))))))
(local
 (defthm fn-hhc-build-fields
  (and (equal (fn-prl-nth 1 (fn-prl-build b c n rows base)) c)
       (equal (fn-prl-nth 2 (fn-prl-build b c n rows base)) n))
  :hints (("Goal" :in-theory (enable fn-prl-build fn-prl-nth)))))
(local
 (defthm fn-hhc-ledger-nth
  (implies (natp n) (equal (fn-prl-nth n x) (nth n x)))
  :hints (("Goal" :induct (fn-prl-nth n x)
                   :in-theory (enable fn-prl-nth nth)))))
(local
 (defthm fn-hhc-release-identity-field
  (equal (fn-prl-nth 4 (fn-prs-release-reusable charged demand))
         (nfix (fn-prl-nth 4 charged)))
  :hints (("Goal" :in-theory (enable fn-prl-nth fn-prs-release-reusable nth)))))
(defthm fn-hhc-release-preserves-spent-identity-and-clears-custody
 (implies (eq (mv-nth 0 (fn-hhc-release ledger slot token)) :released)
  (and (equal (mv-nth 2 (fn-hhc-release ledger slot token)) nil)
       (equal (fn-prl-nth 2 (mv-nth 1 (fn-hhc-release ledger slot token)))
              (fn-prl-nth 2 ledger))
       (equal (fn-prl-nth 4 (fn-prl-nth 1 (mv-nth 1 (fn-hhc-release ledger slot token))))
              (fn-prl-nth 4 (fn-prl-nth 1 ledger)))))
 :rule-classes nil
 :hints (("Goal"
          :use ((:instance fn-hhc-released-result)
                (:instance fn-hhc-vector-identity-natural (x (fn-prl-nth 1 ledger))))
          :in-theory (union-theories (theory 'minimal-theory)
                        '(mv-nth fn-hhc-build-fields
                          fn-hhc-release-identity-field nfix natp)))))

(defthm fn-hhc-refused-release-keeps-custody-and-charge
 (implies (not (eq (mv-nth 0 (fn-hhc-release ledger slot token)) :released))
  (and (equal (mv-nth 1 (fn-hhc-release ledger slot token)) ledger)
       (equal (mv-nth 2 (fn-hhc-release ledger slot token)) slot)))
 :hints (("Goal" :in-theory (enable fn-hhc-release))))
(in-theory (disable fn-hhc-admit fn-hhc-recheck fn-hhc-read-plan fn-hhc-cancel
                    fn-hhc-quiesce fn-hhc-release fn-hhc-reset-status))
