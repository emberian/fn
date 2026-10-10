; fn: the owner admits an article by the memory equation (K-ADMIT; Builder M,
; memory landing 3+4, 2026-10-09).
;
; An article is admitted exactly when three resources admit it, and the
; refusal word names the first that refuses:
;   transactions T  (books/store-capacity-vector.lisp, :unaffordable)
;   history H       (payload octets since landing 3+4, :history-exhausted)
;   memory          the memory gate at the launch's LIMIT over the carried
;                   totals plus the held row the article becomes
;                   (books/memory-model.lisp fn-mm-gate-p; :memory)
; The owner (host/owner-host.lisp fn-owner-prepare-buffer) carries TOT
; (books/history-totals-carried.lisp, K-TOTALS) and builds ROW with
; fn-apc-intern-row-at before the prepare, so the memory term charges the
; row exactly, not a worst case.  The prepare is handed budget 0 when the
; memory gate refuses, so it answers :unaffordable and the word names the
; memory.  A store the gate admitted reopens within LIMIT (K3,
; fn-mm-gate-p's reopen conjunct).
;
; KEYSTONES (K-ADMIT)
;   fn-adm-article-budget-admits-exactly-the-three
;   fn-adm-article-word-under-the-budget-names-the-resource
;   fn-adm-admitted-row-keeps-the-gate

(in-package "ACL2")
(include-book "store-capacity-vector")
(include-book "memory-model")
(include-book "history-totals-carried")

(local (in-theory (disable (tau-system))))

(defun fn-adm-residency (tot)
  (declare (xargs :guard t))
  (if (fn-mm-tot-p tot) (if (fn-mm-tot-paged-p tot) :paged :resident) :resident))

; The totals after ROW commits.
(defun fn-adm-after (tot row)
  (declare (xargs :guard t :verify-guards nil))
  (fn-mm-tot-plus tot (fn-ct-row-tot row (fn-adm-residency tot))))

(defun fn-adm-memory-admitp (profile img cfg limit tot row)
  (declare (xargs :guard t :verify-guards nil))
  (fn-mm-gate-p profile img cfg limit (fn-adm-after tot row)))

; The budget the served prepare is handed.
(defun fn-adm-article-budget (profile img cfg limit used bytes-used record debt tot row)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-adm-memory-admitp profile img cfg limit tot row)
      (fn-cvec-article-budget-for profile used bytes-used record debt)
    0))

; The word the host reports: T, then H, then the memory.
(defun fn-adm-article-word (word profile img cfg limit used bytes-used record debt tot row)
  (declare (xargs :guard t :verify-guards nil))
  (let ((w (fn-cvec-article-refusal-word word profile used bytes-used record debt)))
    (if (and (equal w :unaffordable)
             (fn-cvec-article-transactions-admitp profile used debt)
             (fn-cvec-article-history-admitp
              profile bytes-used
              (fn-sbud-article-gate-figure (len (fn-record-payload record))
                                           (len (fn-record-groups record)))
              debt)
             (not (fn-adm-memory-admitp profile img cfg limit tot row)))
        :memory
      w)))

; KEYSTONE K-ADMIT (1): the budget admits one more record exactly when the
; transactions, the history and the memory admit it.
(defthm fn-adm-article-budget-admits-exactly-the-three
  (iff (fn-sbud-admitp (fn-adm-article-budget profile img cfg limit used bytes-used
                                              record debt tot row)
                       used)
       (and (fn-cvec-article-transactions-admitp profile used debt)
            (fn-cvec-article-history-admitp
             profile bytes-used
             (fn-sbud-article-gate-figure (len (fn-record-payload record))
                                          (len (fn-record-groups record)))
             debt)
            (fn-adm-memory-admitp profile img cfg limit tot row)))
  :hints (("Goal" :use ((:instance fn-cvec-article-budget-for-admits-exactly-both-sides))
           :in-theory (e/d (fn-adm-article-budget fn-sbud-admitp)
                           (fn-adm-memory-admitp fn-cvec-article-budget-for
                            fn-cvec-article-transactions-admitp fn-cvec-article-history-admitp
                            fn-sbud-article-gate-figure fn-cvec-article-budget-for-admits-exactly-both-sides)))))

; KEYSTONE K-ADMIT (2): under the budget the host handed, a refusal names
; the first resource that refused.
(defthm fn-adm-article-word-under-the-budget-names-the-resource
  (let* ((tx (fn-cvec-article-transactions-admitp profile used debt))
         (hx (fn-cvec-article-history-admitp
              profile bytes-used
              (fn-sbud-article-gate-figure (len (fn-record-payload record))
                                           (len (fn-record-groups record)))
              debt))
         (mx (fn-adm-memory-admitp profile img cfg limit tot row))
         (w (fn-adm-article-word :unaffordable profile img cfg limit used bytes-used
                                 record debt tot row)))
    (implies (not (fn-sbud-admitp (fn-adm-article-budget profile img cfg limit used
                                                         bytes-used record debt tot row)
                                  used))
             (and (member-equal w '(:unaffordable :history-exhausted :memory))
                  (iff (equal w :unaffordable) (not tx))
                  (iff (equal w :history-exhausted) (and tx (not hx)))
                  (iff (equal w :memory) (and tx hx (not mx))))))
  :hints (("Goal" :use ((:instance fn-adm-article-budget-admits-exactly-the-three)
                        (:instance fn-cvec-article-budget-for-admits-exactly-both-sides)
                        (:instance fn-cvec-article-refusal-word-under-the-budget-names-the-resource))
           :in-theory (e/d (fn-adm-article-word fn-cvec-article-refusal-word)
                           (fn-adm-article-budget fn-adm-memory-admitp fn-cvec-article-budget-for
                            fn-cvec-article-transactions-admitp fn-cvec-article-history-admitp
                            fn-sbud-article-gate-figure fn-sbud-admitp
                            fn-adm-article-budget-admits-exactly-the-three
                            fn-cvec-article-budget-for-admits-exactly-both-sides
                            fn-cvec-article-refusal-word-under-the-budget-names-the-resource)))))

; A word other than :unaffordable passes through.
(defthm fn-adm-article-word-passes-other-words
  (implies (not (equal word :unaffordable))
           (equal (fn-adm-article-word word profile img cfg limit used bytes-used
                                       record debt tot row)
                  word))
  :hints (("Goal" :in-theory (enable fn-adm-article-word fn-cvec-article-refusal-word))))

; KEYSTONE K-ADMIT (3): a row the budget admitted leaves the totals within
; the gate: the store it commits serves within LIMIT (K1) and reopens
; within it (K3).
(defthm fn-adm-admitted-row-keeps-the-gate
  (implies (fn-sbud-admitp (fn-adm-article-budget profile img cfg limit used bytes-used
                                                  record debt tot row)
                           used)
           (and (<= (fn-mm-sum profile img cfg (fn-adm-after tot row)) limit)
                (<= (fn-mm-reopen-need profile img cfg (fn-adm-after tot row)) limit)))
  :hints (("Goal" :use ((:instance fn-adm-article-budget-admits-exactly-the-three))
           :in-theory (e/d (fn-adm-memory-admitp fn-mm-gate-p)
                           (fn-adm-article-budget fn-adm-article-budget-admits-exactly-the-three fn-mm-sum fn-mm-reopen-need fn-adm-after fn-mm-tot-plus
                            fn-cvec-article-transactions-admitp fn-cvec-article-history-admitp
                            fn-sbud-article-gate-figure fn-sbud-admitp)))))
