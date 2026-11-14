; Bounded reads of the immutable original stream identities of an article.
; Expand fn2-article-membership-events after fn2-auth-read-events, before CNS.
(in-package "ACL2")
(include-book "ordered")
(include-book "arms")
(fn2-book-layer :e)

(defun fn2-article-membership-position-code (ordinal count step)
  (declare (xargs :guard t))
  (cond ((not (and (unsigned-byte-p 60 ordinal) (unsigned-byte-p 60 count)
                   (member-equal step '(0 1)))) :fault)
        ((< ordinal count) :read)
        ((and (equal ordinal count) (equal step 0)) :end)
        (t :fault)))

; The callback return contract and machine-cost declaration belong to this
; shared operation, not to a handwritten CNS copy of the storage lookup.
(defcost fn2-article-membership-count-step :answers (:ok :more :absent :fault) :bytes 4096
 :doc "One exact article metadata lookup step; returns code, persisted membership count, next-step. Step0 starts a lookup; step1 resumes the same article on the owned read row. Missing article is absent.")
(defcost fn2-article-membership-step :answers (:ok :more :end :fault) :bytes 4096
 :doc "One exact original-stream membership step; returns code, next ordinal, stream, next-step. Missing ordinal below persisted count is fault. Successful resumed lookup checks both returned key fields. The stored count is never clamped to a current admission profile.")

(defmacro fn2-article-membership-events ()
 '(progn
    ; COUNT-P selects metadata versus membership. The returned keys, not just
    ; the read-row SID, bind a continuation to the supplied article/ordinal.
    (defun fn2-article-membership-read-step (count-p article ordinal step x budget fn2-core)
      (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
      (b* (((unless (and (unsigned-byte-p 60 article) (unsigned-byte-p 60 ordinal)
                        (member-equal step '(0 1))))
            (mv :fault 0 0 fn2-core))
           (sid (if count-p *fn2-article-sid* *fn2-article-membership-sid*))
           ((mv & fn2-core) (if (equal step 0) (fn2-read-release x fn2-core) (mv :ok fn2-core)))
           ((mv k0 fn2-core)
            (if (equal step 0)
                (fn2-read-key x :lo (if count-p *fn2-article-entry-field-article*
                                     *fn2-article-membership-entry-field-article*) article fn2-core)
              (mv :ok fn2-core)))
           ((mv k1 fn2-core)
            (if (and (equal step 0) (not count-p))
                (fn2-read-key x :lo *fn2-article-membership-entry-field-ordinal* ordinal fn2-core)
              (mv :ok fn2-core)))
           ((unless (and (eq k0 :ok) (eq k1 :ok)))
            (mv-let (& fn2-core) (fn2-read-release x fn2-core) (mv :fault 0 0 fn2-core)))
           ((mv code fn2-core) (fn2-auth-lookup-step x sid budget fn2-core))
           ((when (eq code :more)) (mv :more 0 1 fn2-core))
           ((unless (eq code :ok)) (mv (if (eq code :absent) :absent :fault) 0 0 fn2-core))
           ((mv vc key ord value fn2-core)
            (fn2-auth-take-values x
              (if count-p *fn2-article-entry-field-article* *fn2-article-membership-entry-field-article*)
              (if count-p nil *fn2-article-membership-entry-field-ordinal*)
              (if count-p *fn2-article-entry-field-membership-count* *fn2-article-membership-entry-field-stream*)
              fn2-core)))
        (if (and (eq vc :ok) (equal key article) (or count-p (equal ord ordinal))
                 (unsigned-byte-p 60 value))
            (mv :ok value 0 fn2-core)
          (mv :fault 0 0 fn2-core))))
    (fn2-core-preserves fn2-article-membership-read-step
      (count-p article ordinal step x budget fn2-core) :position 3 :rows nil)
    (defthm fn2-article-membership-read-step-natps
      (and (natp (mv-nth 1 (fn2-article-membership-read-step count-p article ordinal step x budget fn2-core)))
           (natp (mv-nth 2 (fn2-article-membership-read-step count-p article ordinal step x budget fn2-core))))
      :rule-classes :rewrite)
    (defthm fn2-article-membership-read-step-value-width
      (unsigned-byte-p 60 (mv-nth 1 (fn2-article-membership-read-step count-p article ordinal step x budget fn2-core))))
    (defthm fn2-article-membership-read-step-phase-width
      (unsigned-byte-p 8 (mv-nth 2 (fn2-article-membership-read-step count-p article ordinal step x budget fn2-core))))
    (in-theory (disable fn2-article-membership-read-step))
    (defun fn2-article-membership-count-step (article step x budget fn2-core)
      (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
      (fn2-article-membership-read-step t article 0 step x budget fn2-core))
    (fn2-core-preserves fn2-article-membership-count-step
      (article step x budget fn2-core) :position 3 :rows nil)
    (defthm fn2-article-membership-count-step-widths
      (and (unsigned-byte-p 60 (mv-nth 1 (fn2-article-membership-count-step article step x budget fn2-core)))
           (unsigned-byte-p 8 (mv-nth 2 (fn2-article-membership-count-step article step x budget fn2-core)))))
    (in-theory (disable fn2-article-membership-count-step))
    (defun fn2-article-membership-step (article ordinal count step x budget fn2-core)
      (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
      (let ((position-code (fn2-article-membership-position-code ordinal count step)))
        (if (or (not (unsigned-byte-p 60 article)) (not (eq position-code :read)))
            (mv (if (unsigned-byte-p 60 article) position-code :fault)
                (if (eq position-code :end) (nfix ordinal) 0) 0 0 fn2-core)
          (mv-let (code stream next-step fn2-core)
            (fn2-article-membership-read-step nil article ordinal step x budget fn2-core)
            (mv (if (member-eq code '(:ok :more)) code :fault)
                (if (eq code :ok) (+ 1 ordinal) ordinal)
                stream next-step fn2-core)))))
    (fn2-core-preserves fn2-article-membership-step
      (article ordinal count step x budget fn2-core) :position 4 :rows nil)
    (defthm fn2-article-membership-step-widths
      (and (unsigned-byte-p 60 (mv-nth 1 (fn2-article-membership-step article ordinal count step x budget fn2-core)))
           (unsigned-byte-p 60 (mv-nth 2 (fn2-article-membership-step article ordinal count step x budget fn2-core)))
           (unsigned-byte-p 8 (mv-nth 3 (fn2-article-membership-step article ordinal count step x budget fn2-core)))))
    (in-theory (disable fn2-article-membership-step))))
