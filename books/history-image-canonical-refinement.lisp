; Actual HPI canonical phase composition; proof-only carried state.
; Work in progress: no whole-writer completion claim.
(in-package "ACL2")
(include-book "history-image-private-trace")
(include-book "history-image-writer-refinement")

(defun fn-hpic-meta-field (i c)
 (declare (xargs :guard t :verify-guards nil))
 (fn-omk-at i (fn-omk-at 19 c)))

(defun fn-hpic-directory-model (c digests)
 (declare (xargs :guard t :verify-guards nil))
 (pgs-encode-run (fn-hpm-model-entries digests (fn-hpic-meta-field 5 c))
                 (nfix (fn-omk-at 3 (fn-omk-at 1 (fn-omk-at 6 c))))))

(defun fn-hpic-cached-digest-agreesp (c digests)
 (declare (xargs :guard t :verify-guards nil))
 (let ((cache (fn-omk-at 21 c)) (ordinal (fn-hpic-meta-field 1 c)))
  (implies (and (fn-omk-widthp cache 3) (eq (fn-omk-at 0 cache) :digest)
                (equal (fn-omk-at 1 cache) ordinal)
                (unsigned-byte-p 256 (fn-omk-at 2 cache))
                (< ordinal (len digests)))
   (equal (fn-omk-at 2 cache) (nth ordinal digests)))))

; The full directory run may cross a physical page in the middle of an
; entry. Its canonical position is global; it is never reset to page-local
; ordinal/component. Correct spool values are conditional on the private
; byte observation/actual digest relation, not inferred from a cached word.
(defun fn-hpic-directory-invariantp (c digests fn-hpb)
 (declare (xargs :stobjs fn-hpb :verify-guards nil))
 (let* ((layout (fn-omk-at 1 (fn-omk-at 6 c)))
        (m (nfix (fn-omk-at 3 layout)))
        (ordinal (fn-hpic-meta-field 1 c)) (component (fn-hpic-meta-field 2 c))
        (remaining (fn-hpic-meta-field 3 c)) (base (fn-hpic-meta-field 5 c))
        (page (fn-hpic-meta-field 6 c)) (position (+ (* 6 ordinal) component)))
  (and (fn-omk-widthp c 25) (equal (fn-omk-at 0 c) :metadata)
       (equal (fn-hpic-meta-field 0 c) :directory)
       (natp ordinal) (natp component) (< component 6)
       (natp remaining) (natp base) (natp page) (< page m)
       (equal base (nfix (fn-omk-at 5 layout)))
       (equal (fn-hpic-meta-field 4 c) (len digests))
       (equal (len digests) (nfix (fn-omk-at 2 layout)))
       (<= (* 6 (len digests)) (* 2048 m))
       (natp (fn-hpb-used fn-hpb)) (<= (fn-hpb-used fn-hpb) 2048)
       (equal position (+ (* 2048 page) (fn-hpb-used fn-hpb)))
       (equal (+ remaining position) (* 2048 m))
       (fn-hpic-cached-digest-agreesp c digests)
       (equal (fn-hpb-prefix fn-hpb)
              (take (fn-hpb-used fn-hpb)
                    (nthcdr (* 2048 page) (fn-hpic-directory-model c digests)))))))

(local (defthm fn-hpic-take-next
 (implies (natp n)
  (equal (take (+ 1 n) xs) (append (take n xs) (list (nth n xs)))))
 :hints (("Goal" :induct (take n xs) :in-theory (enable take nth)))))

(defun fn-hpic-current-cachep (c)
 (declare (xargs :guard t :verify-guards nil))
 (let ((cache (fn-omk-at 21 c)))
  (and (fn-omk-widthp cache 3) (eq (fn-omk-at 0 cache) :digest)
       (equal (fn-omk-at 1 cache) (fn-hpic-meta-field 1 c))
       (unsigned-byte-p 256 (fn-omk-at 2 cache)))))

(local (defthm fn-hpic-mv-zero-unfolds
 (equal (mv-nth 0 x) (car x))
 :hints (("Goal" :in-theory (enable mv-nth)))))

(local (defthm fn-hpic-issued-page-is-not-continue-unfolds
 (not (equal (car (fn-hpi-await-page region logical physical buffer resume c)) :continue))
 :hints (("Goal" :in-theory (e/d (fn-hpi-await-page) (fn-hpi-set fn-hpi-set-is-update-by-definition fn-hpi-write-effect fn-omk-at))))))
(local (defthm fn-hpic-issued-io-is-not-continue-unfolds
 (not (equal (car (fn-hpi-issue-io tag kind ordinal offset length bytes wait c)) :continue))
 :hints (("Goal" :in-theory (e/d (fn-hpi-issue-io) (fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at))))))

(local (defthm fn-hpic-metadata-continue-is-stored-unfolds
 (let* ((meta (fn-omk-at 19 c))
        (digest (if (fn-hpic-current-cachep c) (fn-omk-at 2 (fn-omk-at 21 c)) 0))
        (step (fn-hpm-tick (fn-omk-at 1 meta) (fn-omk-at 2 meta) (fn-omk-at 3 meta)
                          (fn-omk-at 4 meta) (fn-omk-at 5 meta) digest fn-hpb)))
  (implies (equal (car (fn-hpi-metadata-step c fn-hpb)) :continue)
   (and (equal (car step) :stored)
        (equal (mv-nth 3 (fn-hpi-metadata-step c fn-hpb)) (mv-nth 4 step))
        (implies (< (fn-omk-at 1 meta) (fn-omk-at 4 meta)) (fn-hpic-current-cachep c)))))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-hpi-metadata-step fn-hpic-current-cachep fn-hpic-meta-field)
    (mv-nth fn-omk-at fn-hpi-set fn-hpi-set-is-update-by-definition fn-hpi-issue-io fn-hpi-await-page
     fn-hpb-ready fn-hpb-used fn-hpb-prefix fn-hpm-tick fn-hpm-tick-nonstored-unchanged))))
 :rule-classes nil))

(local (defthm fn-hpic-stored-active-address-unfolds
 (implies (and (natp base) (natp ordinal) (< ordinal entries)
               (equal (car (fn-hpm-tick ordinal component remaining entries base digest fn-hpb)) :stored))
  (unsigned-byte-p 64 (+ base ordinal)))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-hpm-tick) (mv-nth fn-hpb-put fn-hpm-word fn-hpb-ready fn-hpb-used))))))

(local (defthm fn-hpic-stored-step-has-word-room-unfolds
 (implies (equal (car (fn-hpm-tick ordinal component remaining entries base digest fn-hpb)) :stored)
  (and (posp remaining) (< (fn-hpb-used fn-hpb) 2048)))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-hpm-tick) (mv-nth fn-hpb-put fn-hpm-word fn-hpb-ready fn-hpb-used))))))

(local (defthm fn-hpic-cached-value-is-canonical-unfolds
 (implies (and (fn-hpic-cached-digest-agreesp c digests) (fn-hpic-current-cachep c)
               (< (fn-hpic-meta-field 1 c) (len digests)))
  (equal (fn-omk-at 2 (fn-omk-at 21 c)) (nth (fn-hpic-meta-field 1 c) digests)))
 :hints (("Goal" :in-theory (e/d (fn-hpic-cached-digest-agreesp fn-hpic-current-cachep)
                                (fn-hpic-meta-field fn-omk-at unsigned-byte-p))))))

; The actual metadata controller, not its scalar emitter alone, appends the
; canonical global directory word when its returned status is :continue.
(defthm fn-hpi-metadata-step-appends-current-directory-word
 (implies (and (fn-hpic-directory-invariantp c digests fn-hpb)
               (equal (mv-nth 0 (fn-hpi-metadata-step c fn-hpb)) :continue))
  (equal (fn-hpb-prefix (mv-nth 3 (fn-hpi-metadata-step c fn-hpb)))
         (append (fn-hpb-prefix fn-hpb)
                 (list (nth (+ (* 6 (fn-hpic-meta-field 1 c)) (fn-hpic-meta-field 2 c))
                            (fn-hpic-directory-model c digests))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :cases ((< (fn-hpic-meta-field 1 c) (len digests)))
  :use (fn-hpic-metadata-continue-is-stored-unfolds
        (:instance fn-hpic-stored-step-has-word-room-unfolds
          (ordinal (fn-hpic-meta-field 1 c)) (component (fn-hpic-meta-field 2 c))
          (remaining (fn-hpic-meta-field 3 c)) (entries (fn-hpic-meta-field 4 c))
          (base (fn-hpic-meta-field 5 c))
          (digest (if (fn-hpic-current-cachep c) (fn-omk-at 2 (fn-omk-at 21 c)) 0)))
        (:instance fn-hpic-stored-active-address-unfolds
          (ordinal (fn-hpic-meta-field 1 c)) (component (fn-hpic-meta-field 2 c))
          (remaining (fn-hpic-meta-field 3 c)) (entries (fn-hpic-meta-field 4 c))
          (base (fn-hpic-meta-field 5 c))
          (digest (if (fn-hpic-current-cachep c) (fn-omk-at 2 (fn-omk-at 21 c)) 0)))
        (:instance fn-hpm-tick-refines-directory-effect
          (ordinal (fn-hpic-meta-field 1 c)) (component (fn-hpic-meta-field 2 c))
          (remaining (fn-hpic-meta-field 3 c)) (entries (fn-hpic-meta-field 4 c))
          (base (fn-hpic-meta-field 5 c)) (digest (if (fn-hpic-current-cachep c) (fn-omk-at 2 (fn-omk-at 21 c)) 0))
          (m (nfix (fn-omk-at 3 (fn-omk-at 1 (fn-omk-at 6 c))))))
        (:instance fn-hpm-tick-refines-emission-effect
          (ordinal (fn-hpic-meta-field 1 c)) (component (fn-hpic-meta-field 2 c))
          (remaining (fn-hpic-meta-field 3 c)) (entries (fn-hpic-meta-field 4 c))
          (base (fn-hpic-meta-field 5 c))
          (digest (if (fn-hpic-current-cachep c) (fn-omk-at 2 (fn-omk-at 21 c)) 0)))
        (:instance fn-hpm-directory-padding-is-zero
          (i (+ (* 6 (fn-hpic-meta-field 1 c)) (fn-hpic-meta-field 2 c)))
          (base (fn-hpic-meta-field 5 c))
          (m (nfix (fn-omk-at 3 (fn-omk-at 1 (fn-omk-at 6 c)))))))
  :in-theory (e/d (fn-hpic-directory-invariantp
                   fn-hpic-meta-field fn-hpic-directory-model)
    (mv-nth fn-omk-at fn-hpi-set fn-hpi-set-is-update-by-definition fn-hpi-metadata-step fn-hpi-issue-io fn-hpi-await-page fn-hpb-ready fn-hpb-used fn-hpb-prefix
     take nth nthcdr fn-hpic-take-next unsigned-byte-p
     fn-hpic-cached-digest-agreesp fn-hpic-current-cachep
     fn-hpm-tick fn-hpm-tick-nonstored-unchanged fn-hpm-word pgs-encode-run fn-hpm-model-entries)))))

(local (defthm fn-hpic-tick-metadata-prefix-and-frame-unfolds
 (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-omk-widthp c 25) (equal (fn-omk-at 0 c) :metadata)
                (equal (car r) :continue))
   (and (equal (mv-nth 2 r) (mv-nth 2 (fn-hpi-metadata-step c fn-hpb)))
        (equal (mv-nth 8 r) (mv-nth 3 (fn-hpi-metadata-step c fn-hpb)))
        (equal (fn-hpb-prefix (mv-nth 8 r))
               (fn-hpb-prefix (mv-nth 3 (fn-hpi-metadata-step c fn-hpb))))
        (equal (mv-nth 3 r) ledger)
        (equal (mv-nth 4 r) fn-hpq0) (equal (mv-nth 5 r) fn-hpq1)
        (equal (mv-nth 6 r) fn-hpq2) (equal (mv-nth 7 r) fn-hpq3)
        (equal (mv-nth 9 r) pgs-digest-state)
        (equal (car (fn-hpi-metadata-step c fn-hpb)) :continue))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-hpi-tick fn-hpi-stream-step)
    (fn-hpi-metadata-step fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at
     fn-hpi-grant-matchesp fn-hpb-prefix mv-nth fn-hpi-digest-begin fn-hpi-digest-validp
     fn-hpi-io-matchp fn-hpi-octets-p pgs-dcb-read-demand pgs-dcb-step
     fn-hpi-issue-io fn-hpi-after-spool pgs-dcb-result-octets fn-hpir-root))))))

; Direct actual host-called subject. Only the carried canonical phase
; invariant and returned continuation status are retained premises: a
; separate caller-asserted live receipt is unnecessary because this path
; is gated by the actual fn-hpi-tick authority check.
(defthm fn-hpi-tick-appends-current-directory-word-and-frames-other-state
 (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-hpic-directory-invariantp c digests fn-hpb)
                (equal (car r) :continue))
   (and (equal (fn-hpb-prefix (mv-nth 8 r))
          (append (fn-hpb-prefix fn-hpb)
                  (list (nth (+ (* 6 (fn-hpic-meta-field 1 c)) (fn-hpic-meta-field 2 c))
                             (fn-hpic-directory-model c digests)))))
        (equal (mv-nth 3 r) ledger)
        (equal (mv-nth 4 r) fn-hpq0) (equal (mv-nth 5 r) fn-hpq1)
        (equal (mv-nth 6 r) fn-hpq2) (equal (mv-nth 7 r) fn-hpq3)
        (equal (mv-nth 9 r) pgs-digest-state))))
 :rule-classes nil
 :hints (("Goal" :use (fn-hpic-tick-metadata-prefix-and-frame-unfolds
                       fn-hpi-metadata-step-appends-current-directory-word)
  :in-theory (e/d (fn-hpic-directory-invariantp)
    (fn-hpi-tick fn-hpi-metadata-step fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at
     fn-hpb-prefix fn-hpb-used mv-nth fn-hpic-directory-model fn-hpic-meta-field
     fn-hpic-cached-digest-agreesp fn-hpi-grant-matchesp fn-hpi-stream-step take nth nthcdr)))))


(local (defthm fn-hpic-nth-nthcdr
 (implies (and (natp a) (natp n))
  (equal (nth n (nthcdr a xs)) (nth (+ a n) xs)))
 :hints (("Goal" :induct (nthcdr a xs) :in-theory (enable nth nthcdr)))))

; The concrete scratch prefix grows to exactly the next canonical prefix.
; This is still a phase law: whole directory handoff/reset and the complete
; table/data/pool/root phase invariant remain separate pending joins.
(defthm fn-hpi-tick-grows-current-directory-prefix
 (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-hpic-directory-invariantp c digests fn-hpb)
                (equal (car r) :continue))
   (equal (fn-hpb-prefix (mv-nth 8 r))
    (take (+ 1 (fn-hpb-used fn-hpb))
          (nthcdr (* 2048 (fn-hpic-meta-field 6 c)) (fn-hpic-directory-model c digests))))))
 :rule-classes nil
 :hints (("Goal" :use (fn-hpi-tick-appends-current-directory-word-and-frames-other-state
       (:instance fn-hpic-take-next (n (fn-hpb-used fn-hpb))
                  (xs (nthcdr (* 2048 (fn-hpic-meta-field 6 c)) (fn-hpic-directory-model c digests))))
       (:instance fn-hpic-nth-nthcdr (n (fn-hpb-used fn-hpb))
                  (a (* 2048 (fn-hpic-meta-field 6 c))) (xs (fn-hpic-directory-model c digests))))
  :in-theory (e/d (fn-hpic-directory-invariantp)
    (fn-hpi-tick fn-hpi-metadata-step fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at
     fn-hpb-prefix fn-hpb-used mv-nth fn-hpic-directory-model fn-hpic-meta-field
     fn-hpic-cached-digest-agreesp fn-hpi-grant-matchesp fn-hpi-stream-step take nth nthcdr
     fn-hpic-take-next fn-hpic-nth-nthcdr)))))


(local (defun fn-hpic-field-ind (j k c)
 (if (or (zp j) (zp k)) (list j k c)
  (fn-hpic-field-ind (1- j) (1- k) (if (consp c) (cdr c) nil)))))
(local (defthm fn-hpic-set-field
 (implies (and (natp k) (< k 25) (natp j) (< j 25))
  (equal (fn-omk-at j (fn-hpi-set k value c))
         (if (equal j k) value (fn-omk-at j c))))
 :hints (("Goal" :induct (fn-hpic-field-ind j k c)
  :expand ((fn-hpi-set k value c) (fn-omk-at j c)
           (fn-omk-at j (fn-hpi-set k value c))
           (:free (a d) (fn-omk-at j (cons a d))))
  :in-theory (e/d (fn-omk-at fn-hpi-set) (fn-hpi-set-is-update-by-definition))))))
(local (defthm fn-hpic-update-keeps-width
 (implies (and (natp n) (<= n 25) (natp k) (< k n) (fn-omk-widthp c n))
  (fn-omk-widthp (fn-hpi-set k value c) n))
 :hints (("Goal" :induct (fn-hpic-field-ind n k c)
  :expand ((fn-hpi-set k value c) (fn-omk-widthp c n)
           (fn-omk-widthp (fn-hpi-set k value c) n))
  :in-theory (e/d (fn-omk-widthp fn-hpi-set) (fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpic-metadata-continue-state-unfolds
 (let* ((meta (fn-omk-at 19 c))
        (step (fn-hpm-tick (fn-omk-at 1 meta) (fn-omk-at 2 meta) (fn-omk-at 3 meta)
                          (fn-omk-at 4 meta) (fn-omk-at 5 meta)
                          (if (fn-hpic-current-cachep c) (fn-omk-at 2 (fn-omk-at 21 c)) 0) fn-hpb)))
  (implies (equal (car (fn-hpi-metadata-step c fn-hpb)) :continue)
   (equal (mv-nth 2 (fn-hpi-metadata-step c fn-hpb))
          (fn-hpi-set 19 (list (fn-omk-at 0 meta) (mv-nth 1 step) (mv-nth 2 step)
                              (mv-nth 3 step) (fn-omk-at 4 meta) (fn-omk-at 5 meta)
                              (fn-omk-at 6 meta)) c))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-hpi-metadata-step fn-hpic-current-cachep fn-hpic-meta-field)
    (mv-nth fn-omk-at fn-hpi-set fn-hpi-set-is-update-by-definition fn-hpi-issue-io fn-hpi-await-page
     fn-hpb-ready fn-hpb-used fn-hpb-prefix fn-hpm-tick fn-hpm-tick-nonstored-unchanged))))))

(local (defthm fn-hpic-buffer-used-after-update-unfolds
 (equal (fn-hpb-used (update-fn-hpb-used value fn-hpb)) value)
 :hints (("Goal" :in-theory (enable fn-hpb-used update-fn-hpb-used)))))

(local (defthm fn-hpic-stored-pointer-values-unfolds
 (implies (equal (car (fn-hpm-tick ordinal component remaining entries base digest fn-hpb)) :stored)
  (and (equal (mv-nth 1 (fn-hpm-tick ordinal component remaining entries base digest fn-hpb))
              (if (equal component 5) (+ 1 ordinal) ordinal))
       (equal (mv-nth 2 (fn-hpm-tick ordinal component remaining entries base digest fn-hpb))
              (if (equal component 5) 0 (+ 1 component)))
       (equal (mv-nth 3 (fn-hpm-tick ordinal component remaining entries base digest fn-hpb))
              (1- remaining))
       (equal (fn-hpb-used (mv-nth 4 (fn-hpm-tick ordinal component remaining entries base digest fn-hpb)))
              (+ 1 (fn-hpb-used fn-hpb)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-hpm-tick fn-hpb-put)
    (mv-nth fn-hpm-tick-progress fn-hpm-tick-nonstored-unchanged fn-hpm-word fn-hpb-used
     update-fn-hpb-wi update-fn-hpb-used fn-hpb-wi))))))

(local (defthm fn-hpic-seven-fields-unfolds
 (and (equal (fn-omk-at 0 (list a b d e f g h)) a)
      (equal (fn-omk-at 1 (list a b d e f g h)) b)
      (equal (fn-omk-at 2 (list a b d e f g h)) d)
      (equal (fn-omk-at 3 (list a b d e f g h)) e)
      (equal (fn-omk-at 4 (list a b d e f g h)) f)
      (equal (fn-omk-at 5 (list a b d e f g h)) g)
      (equal (fn-omk-at 6 (list a b d e f g h)) h))
 :hints (("Goal" :in-theory (enable fn-omk-at)))))

(local (defthm fn-hpic-next-cache-agreement-unfolds
 (let* ((ordinal (fn-hpic-meta-field 1 c))
        (component (fn-hpic-meta-field 2 c))
        (next (fn-hpi-set 19
         (list (fn-hpic-meta-field 0 c)
               (if (equal component 5) (+ 1 ordinal) ordinal)
               (if (equal component 5) 0 (+ 1 component))
               remaining (fn-hpic-meta-field 4 c) (fn-hpic-meta-field 5 c)
               (fn-hpic-meta-field 6 c)) c)))
  (implies (and (natp ordinal) (fn-hpic-cached-digest-agreesp c digests)
                (implies (< ordinal (len digests)) (fn-hpic-current-cachep c)))
   (fn-hpic-cached-digest-agreesp next digests)))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-hpic-cached-digest-agreesp fn-hpic-current-cachep fn-hpic-meta-field)
   (fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at fn-omk-widthp unsigned-byte-p nth))))))

(local (defthm fn-hpic-continue-metadata-complete-state-unfolds
 (let* ((ordinal (fn-hpic-meta-field 1 c)) (component (fn-hpic-meta-field 2 c))
        (next (fn-hpi-set 19
         (list (fn-hpic-meta-field 0 c)
               (if (equal component 5) (+ 1 ordinal) ordinal)
               (if (equal component 5) 0 (+ 1 component))
               (1- (fn-hpic-meta-field 3 c)) (fn-hpic-meta-field 4 c)
               (fn-hpic-meta-field 5 c) (fn-hpic-meta-field 6 c)) c)))
  (implies (equal (car (fn-hpi-metadata-step c fn-hpb)) :continue)
   (and (equal (mv-nth 2 (fn-hpi-metadata-step c fn-hpb)) next)
        (equal (fn-hpb-used (mv-nth 3 (fn-hpi-metadata-step c fn-hpb)))
               (+ 1 (fn-hpb-used fn-hpb)))
        (posp (fn-hpic-meta-field 3 c)) (< (fn-hpb-used fn-hpb) 2048)
        (implies (< ordinal (fn-hpic-meta-field 4 c)) (fn-hpic-current-cachep c)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-hpic-metadata-continue-is-stored-unfolds
        fn-hpic-metadata-continue-state-unfolds
        (:instance fn-hpic-stored-step-has-word-room-unfolds
         (ordinal (fn-hpic-meta-field 1 c)) (component (fn-hpic-meta-field 2 c))
         (remaining (fn-hpic-meta-field 3 c)) (entries (fn-hpic-meta-field 4 c))
         (base (fn-hpic-meta-field 5 c))
         (digest (if (fn-hpic-current-cachep c) (fn-omk-at 2 (fn-omk-at 21 c)) 0)))
        (:instance fn-hpic-stored-pointer-values-unfolds
         (ordinal (fn-hpic-meta-field 1 c)) (component (fn-hpic-meta-field 2 c))
         (remaining (fn-hpic-meta-field 3 c)) (entries (fn-hpic-meta-field 4 c))
         (base (fn-hpic-meta-field 5 c))
         (digest (if (fn-hpic-current-cachep c) (fn-omk-at 2 (fn-omk-at 21 c)) 0))))
  :in-theory (e/d (fn-hpic-meta-field)
   (fn-hpic-current-cachep fn-hpi-metadata-step fn-hpi-set fn-hpi-set-is-update-by-definition
    fn-omk-at fn-hpb-used mv-nth fn-hpm-tick fn-hpic-stored-step-has-word-room-unfolds
    fn-hpm-tick-progress fn-hpm-tick-refines-emission-effect fn-hpm-tick-nonstored-unchanged))))))

(local (defthm fn-hpic-continue-state-projection-unfolds
 (implies (equal (car (fn-hpi-metadata-step c fn-hpb)) :continue)
  (equal (mv-nth 2 (fn-hpi-metadata-step c fn-hpb))
   (fn-hpi-set 19
    (list (fn-hpic-meta-field 0 c)
          (if (equal (fn-hpic-meta-field 2 c) 5) (+ 1 (fn-hpic-meta-field 1 c)) (fn-hpic-meta-field 1 c))
          (if (equal (fn-hpic-meta-field 2 c) 5) 0 (+ 1 (fn-hpic-meta-field 2 c)))
          (1- (fn-hpic-meta-field 3 c)) (fn-hpic-meta-field 4 c)
          (fn-hpic-meta-field 5 c) (fn-hpic-meta-field 6 c)) c)))
 :hints (("Goal" :use fn-hpic-continue-metadata-complete-state-unfolds
  :in-theory (disable fn-hpi-metadata-step fn-hpi-set fn-hpi-set-is-update-by-definition
                       fn-hpic-meta-field fn-omk-at fn-hpb-used mv-nth fn-hpic-current-cachep)))))
(local (defthm fn-hpic-continue-used-projection-unfolds
 (implies (equal (car (fn-hpi-metadata-step c fn-hpb)) :continue)
  (equal (fn-hpb-used (mv-nth 3 (fn-hpi-metadata-step c fn-hpb))) (+ 1 (fn-hpb-used fn-hpb))))
 :hints (("Goal" :use fn-hpic-continue-metadata-complete-state-unfolds
  :in-theory (disable fn-hpi-metadata-step fn-hpi-set fn-hpi-set-is-update-by-definition
                       fn-hpic-meta-field fn-omk-at fn-hpb-used mv-nth fn-hpic-current-cachep)))))

(local (defthm fn-hpic-metadata-continue-preserves-directory-invariant
 (implies (and (fn-hpic-directory-invariantp c digests fn-hpb)
               (equal (car (fn-hpi-metadata-step c fn-hpb)) :continue))
  (fn-hpic-directory-invariantp
   (mv-nth 2 (fn-hpi-metadata-step c fn-hpb)) digests
   (mv-nth 3 (fn-hpi-metadata-step c fn-hpb))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-hpic-continue-metadata-complete-state-unfolds
        (:instance fn-hpic-next-cache-agreement-unfolds (remaining (1- (fn-hpic-meta-field 3 c))))
        fn-hpi-metadata-step-appends-current-directory-word
        (:instance fn-hpic-take-next (n (fn-hpb-used fn-hpb))
         (xs (nthcdr (* 2048 (fn-hpic-meta-field 6 c)) (fn-hpic-directory-model c digests))))
        (:instance fn-hpic-nth-nthcdr (n (fn-hpb-used fn-hpb))
         (a (* 2048 (fn-hpic-meta-field 6 c))) (xs (fn-hpic-directory-model c digests))))
  :in-theory (e/d (fn-hpic-directory-invariantp fn-hpic-meta-field
                  fn-hpic-directory-model)
   (fn-hpic-stored-step-has-word-room-unfolds fn-hpic-stored-active-address-unfolds
    fn-hpic-cached-digest-agreesp fn-hpic-current-cachep
    fn-hpm-tick-progress fn-hpm-tick-refines-emission-effect fn-hpm-directory-padding-is-zero
    associativity-of-+ commutativity-of-+ commutativity-2-of-+
    fn-hpi-metadata-step fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at fn-omk-widthp
    mv-nth fn-hpb-prefix fn-hpb-used fn-hpm-tick fn-hpm-tick-nonstored-unchanged
    pgs-encode-run fn-hpm-model-entries take nth nthcdr unsigned-byte-p
    fn-hpic-take-next fn-hpic-nth-nthcdr))))))

; Continuing the actual funded host-called controller preserves the whole
; carried directory phase state, including its concrete scratch prefix.
(defthm fn-hpi-tick-preserves-current-directory-invariant
 (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-hpic-directory-invariantp c digests fn-hpb)
                (equal (car r) :continue))
   (fn-hpic-directory-invariantp (mv-nth 2 r) digests (mv-nth 8 r))))
 :rule-classes nil
 :hints (("Goal" :use (fn-hpic-tick-metadata-prefix-and-frame-unfolds
                       fn-hpic-metadata-continue-preserves-directory-invariant)
  :in-theory (e/d (fn-hpic-directory-invariantp)
   (fn-hpi-tick fn-hpi-metadata-step fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at
    fn-hpb-prefix fn-hpb-used mv-nth fn-hpic-directory-model fn-hpic-meta-field
    fn-hpic-cached-digest-agreesp fn-hpi-grant-matchesp fn-hpi-stream-step take nth nthcdr)))))

(local (defthm fn-hpic-issued-io-is-not-write-unfolds
 (not (equal (car (fn-hpi-issue-io tag kind ordinal offset length bytes wait c)) :write))
 :hints (("Goal" :in-theory (e/d (fn-hpi-issue-io)
  (fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at))))))

(local (defthm fn-hpic-metadata-directory-write-unfolds
 (let ((r (fn-hpi-metadata-step c fn-hpb)))
  (implies (and (equal (fn-hpic-meta-field 0 c) :directory)
                (equal (car r) :write))
   (and (equal (fn-hpb-used fn-hpb) 2048)
        (equal (mv-nth 3 r) fn-hpb)
        (equal (mv-nth 1 r)
         (fn-hpi-write-effect (fn-omk-at 1 c) (fn-omk-at 3 c)
           (nfix (fn-omk-at 4 c)) :directory (fn-hpic-meta-field 6 c)
           (+ 1 (fn-hpic-meta-field 6 c)) (nfix (fn-omk-at 4 (fn-omk-at 16 c)))))
        (equal (fn-omk-at 0 (mv-nth 2 r)) :wait-write)
        (equal (fn-hpic-meta-field 6 (mv-nth 2 r)) (+ 1 (fn-hpic-meta-field 6 c)))
        (equal (fn-hpic-meta-field 1 (mv-nth 2 r)) (fn-hpic-meta-field 1 c))
        (equal (fn-hpic-meta-field 2 (mv-nth 2 r)) (fn-hpic-meta-field 2 c))
        (equal (fn-hpic-meta-field 3 (mv-nth 2 r)) (fn-hpic-meta-field 3 c))
        (equal (fn-omk-at 6 (mv-nth 2 r)) (fn-omk-at 6 c)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-hpi-metadata-step fn-hpi-await-page fn-hpic-meta-field fn-hpb-ready)
   (fn-hpi-write-effect fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at mv-nth
    fn-hpb-used fn-hpm-tick fn-hpm-tick-progress fn-hpm-tick-nonstored-unchanged
    fn-hpi-issue-io fn-hpb-prefix))))))

(local (defthm fn-hpic-tick-metadata-write-and-frame-unfolds
 (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-omk-widthp c 25) (equal (fn-omk-at 0 c) :metadata)
                (equal (car r) :write))
   (and (equal (mv-nth 1 r) (mv-nth 1 (fn-hpi-metadata-step c fn-hpb)))
        (equal (mv-nth 2 r) (mv-nth 2 (fn-hpi-metadata-step c fn-hpb)))
        (equal (mv-nth 8 r) (mv-nth 3 (fn-hpi-metadata-step c fn-hpb)))
        (equal (mv-nth 3 r) ledger)
        (equal (mv-nth 4 r) fn-hpq0) (equal (mv-nth 5 r) fn-hpq1)
        (equal (mv-nth 6 r) fn-hpq2) (equal (mv-nth 7 r) fn-hpq3)
        (equal (mv-nth 9 r) pgs-digest-state)
        (equal (car (fn-hpi-metadata-step c fn-hpb)) :write))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-hpi-tick fn-hpi-stream-step)
   (fn-hpi-metadata-step fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at
    fn-hpi-grant-matchesp fn-hpb-prefix mv-nth fn-hpi-digest-begin fn-hpi-digest-validp
    fn-hpi-io-matchp fn-hpi-octets-p pgs-dcb-read-demand pgs-dcb-step
    fn-hpi-issue-io fn-hpi-after-spool pgs-dcb-result-octets fn-hpir-root))))))

(defthm fn-hpi-tick-hands-off-complete-canonical-directory-page
 (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-hpic-directory-invariantp c digests fn-hpb)
                (equal (car r) :write))
   (and (equal (fn-hpb-used fn-hpb) 2048)
        (equal (mv-nth 1 r)
         (fn-hpi-write-effect (fn-omk-at 1 c) (fn-omk-at 3 c)
           (nfix (fn-omk-at 4 c)) :directory (fn-hpic-meta-field 6 c)
           (+ 1 (fn-hpic-meta-field 6 c)) (nfix (fn-omk-at 4 (fn-omk-at 16 c)))))
        (equal (fn-hpb-prefix (mv-nth 8 r))
         (take 2048 (nthcdr (* 2048 (fn-hpic-meta-field 6 c)) (fn-hpic-directory-model c digests))))
        (equal (fn-omk-at 0 (mv-nth 2 r)) :wait-write)
        (equal (fn-hpic-meta-field 6 (mv-nth 2 r)) (+ 1 (fn-hpic-meta-field 6 c)))
        (equal (fn-hpic-meta-field 1 (mv-nth 2 r)) (fn-hpic-meta-field 1 c))
        (equal (fn-hpic-meta-field 2 (mv-nth 2 r)) (fn-hpic-meta-field 2 c))
        (equal (fn-hpic-meta-field 3 (mv-nth 2 r)) (fn-hpic-meta-field 3 c))
        (equal (mv-nth 3 r) ledger)
        (equal (mv-nth 4 r) fn-hpq0) (equal (mv-nth 5 r) fn-hpq1)
        (equal (mv-nth 6 r) fn-hpq2) (equal (mv-nth 7 r) fn-hpq3)
        (equal (mv-nth 8 r) fn-hpb) (equal (mv-nth 9 r) pgs-digest-state))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :use (fn-hpic-metadata-directory-write-unfolds
                              fn-hpic-tick-metadata-write-and-frame-unfolds)
  :in-theory (e/d (fn-hpic-directory-invariantp)
   (fn-hpic-take-next fn-hpic-nth-nthcdr
    fn-hpic-stored-step-has-word-room-unfolds fn-hpic-stored-active-address-unfolds
    fn-hpic-continue-state-projection-unfolds fn-hpic-continue-used-projection-unfolds
    fn-hpm-tick-progress fn-hpm-tick-refines-emission-effect fn-hpm-directory-padding-is-zero
    fn-hpi-tick fn-hpi-stream-step fn-hpi-metadata-step fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at
    fn-hpb-prefix fn-hpb-used mv-nth fn-hpic-directory-model fn-hpic-meta-field
    fn-hpic-cached-digest-agreesp fn-hpi-grant-matchesp fn-hpi-digest-begin fn-hpi-digest-validp
    fn-hpi-io-matchp fn-hpi-octets-p pgs-dcb-read-demand pgs-dcb-step
    fn-hpi-issue-io fn-hpi-after-spool pgs-dcb-result-octets fn-hpir-root take nth nthcdr)))))

(local (defthm fn-hpic-written-directory-buffer-reset-unfolds
 (let ((r (fn-hpi-written c observation fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
  (implies (and (equal (fn-omk-at 0 c) :wait-write)
                (equal (fn-omk-at 0 (fn-omk-at 17 c)) 4)
                (equal (car r) :written))
   (and (equal (fn-hpi-written-status (fn-omk-at 5 c) observation) :written)
        (equal (fn-omk-at 0 (mv-nth 1 r)) (fn-omk-at 1 (fn-omk-at 17 c)))
        (equal (fn-omk-at 19 (mv-nth 1 r)) (fn-omk-at 19 c))
        (equal (fn-omk-at 6 (mv-nth 1 r)) (fn-omk-at 6 c))
        (equal (fn-omk-at 21 (mv-nth 1 r)) (fn-omk-at 21 c))
        (equal (fn-omk-at 4 (fn-omk-at 16 (mv-nth 1 r)))
               (+ 1 (nfix (fn-omk-at 4 (fn-omk-at 16 c)))))
        (equal (fn-omk-at 5 (mv-nth 1 r)) nil)
        (equal (fn-omk-at 17 (mv-nth 1 r)) nil)
        (equal (mv-nth 2 r) fn-hpq0) (equal (mv-nth 3 r) fn-hpq1)
        (equal (mv-nth 4 r) fn-hpq2) (equal (mv-nth 5 r) fn-hpq3)
        (equal (mv-nth 6 r) (fn-hpb-begin (fn-omk-at 1 c) (fn-omk-at 2 c) fn-hpb)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-hpi-written fn-hpi-reset-buffer fn-hpi-written-status)
   (fn-hpi-written-matchp fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at
    fn-hpb-begin mv-nth))))))

(local (defthm fn-hpic-tick-written-and-frame-unfolds
 (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-omk-widthp c 25) (equal (fn-omk-at 0 c) :wait-write)
                (equal (car r) :written))
   (and (equal (mv-nth 2 r) (mv-nth 1 (fn-hpi-written c observation fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
        (equal (mv-nth 8 r) (mv-nth 6 (fn-hpi-written c observation fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
        (equal (mv-nth 4 r) (mv-nth 2 (fn-hpi-written c observation fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
        (equal (mv-nth 5 r) (mv-nth 3 (fn-hpi-written c observation fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
        (equal (mv-nth 6 r) (mv-nth 4 (fn-hpi-written c observation fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
        (equal (mv-nth 7 r) (mv-nth 5 (fn-hpi-written c observation fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
        (equal (mv-nth 3 r) ledger) (equal (mv-nth 9 r) pgs-digest-state)
        (equal (car (fn-hpi-written c observation fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)) :written))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-hpi-tick)
   (fn-hpi-written fn-hpi-grant-matchesp fn-hpi-set fn-hpi-set-is-update-by-definition
    fn-hpi-stream-step fn-hpi-buffer-step fn-hpi-supply fn-omk-at mv-nth))))))

(defun fn-hpic-scratch-ack-contextp (c)
 (declare (xargs :guard t :verify-guards nil))
 (and (fn-omk-widthp c 25) (equal (fn-omk-at 0 c) :wait-write)
      (equal (fn-omk-at 0 (fn-omk-at 17 c)) 4)))

; The definite core-matched page ACK, rather than a host success flag,
; releases the scratch prefix and advances its generation exactly once.
(defthm fn-hpi-tick-resets-directory-buffer-after-exact-written-ack
 (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-hpic-scratch-ack-contextp c)
                (equal (car r) :written))
   (and (equal (fn-hpi-written-status (fn-omk-at 5 c) observation) :written)
        (equal (fn-omk-at 0 (mv-nth 2 r)) (fn-omk-at 1 (fn-omk-at 17 c)))
        (equal (fn-omk-at 19 (mv-nth 2 r)) (fn-omk-at 19 c))
        (equal (fn-omk-at 6 (mv-nth 2 r)) (fn-omk-at 6 c))
        (equal (fn-omk-at 21 (mv-nth 2 r)) (fn-omk-at 21 c))
        (equal (fn-omk-at 4 (fn-omk-at 16 (mv-nth 2 r)))
               (+ 1 (nfix (fn-omk-at 4 (fn-omk-at 16 c)))))
        (equal (fn-omk-at 5 (mv-nth 2 r)) nil)
        (equal (fn-omk-at 17 (mv-nth 2 r)) nil)
        (equal (fn-hpb-prefix (mv-nth 8 r)) nil)
        (equal (mv-nth 8 r) (fn-hpb-begin (fn-omk-at 1 c) (fn-omk-at 2 c) fn-hpb))
        (equal (mv-nth 3 r) ledger)
        (equal (mv-nth 4 r) fn-hpq0) (equal (mv-nth 5 r) fn-hpq1)
        (equal (mv-nth 6 r) fn-hpq2) (equal (mv-nth 7 r) fn-hpq3)
        (equal (mv-nth 9 r) pgs-digest-state))))
 :rule-classes nil
 :hints (("Goal" :use (fn-hpic-written-directory-buffer-reset-unfolds fn-hpic-tick-written-and-frame-unfolds)
  :in-theory (e/d (fn-hpic-scratch-ack-contextp) (fn-hpi-tick fn-hpi-written fn-hpi-written-status fn-omk-at
   fn-hpi-set fn-hpi-set-is-update-by-definition fn-hpi-reset-buffer fn-hpb-begin
   fn-hpb-prefix mv-nth fn-hpic-take-next fn-hpic-stored-step-has-word-room-unfolds
   fn-hpic-continue-state-projection-unfolds fn-hpic-continue-used-projection-unfolds)))))

; Carried continuation after a nonfinal directory page is issued. The
; completed page is retained until its exact ACK; global position already
; names the next page. This is a proof observer, never a served revalidator.
(defun fn-hpic-directory-resume-invariantp (c digests)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((layout (fn-omk-at 1 (fn-omk-at 6 c)))
        (m (nfix (fn-omk-at 3 layout)))
        (ordinal (fn-hpic-meta-field 1 c)) (component (fn-hpic-meta-field 2 c))
        (remaining (fn-hpic-meta-field 3 c)) (base (fn-hpic-meta-field 5 c))
        (page (fn-hpic-meta-field 6 c)) (position (+ (* 6 ordinal) component)))
  (and (fn-hpic-scratch-ack-contextp c)
       (equal (fn-omk-at 1 (fn-omk-at 17 c)) :metadata)
       (equal (fn-hpic-meta-field 0 c) :directory)
       (natp ordinal) (natp component) (< component 6)
       (posp remaining) (natp base) (posp page) (< page m)
       (equal base (nfix (fn-omk-at 5 layout)))
       (equal (fn-hpic-meta-field 4 c) (len digests))
       (equal (len digests) (nfix (fn-omk-at 2 layout)))
       (<= (* 6 (len digests)) (* 2048 m))
       (equal position (* 2048 page))
       (equal (+ remaining position) (* 2048 m))
       (fn-hpic-cached-digest-agreesp c digests))))

(local (defthm fn-hpic-written-keeps-cursor-width-unfolds
 (implies (fn-omk-widthp c 25)
  (fn-omk-widthp (mv-nth 1 (fn-hpi-written c observation fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)) 25))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-hpi-written)
   (fn-hpi-written-status fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at
    fn-hpi-reset-buffer fn-hpb-begin fn-omk-widthp mv-nth
    fn-hpic-stored-step-has-word-room-unfolds fn-hpic-take-next))))))

(local (defthm fn-hpic-begin-used-is-zero-unfolds
 (equal (fn-hpb-used (fn-hpb-begin epoch lease fn-hpb)) 0)
 :hints (("Goal" :in-theory (enable fn-hpb-begin fn-hpb-used
                             update-fn-hpb-used update-fn-hpb-epoch update-fn-hpb-lease)))))

(local (defthm fn-hpic-take-zero-unfolds
 (equal (take 0 xs) nil)
 :hints (("Goal" :in-theory (enable take)))))

(local (defthm fn-hpic-written-canonical-fields-unfolds
 (let ((r (fn-hpi-written c observation fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
  (implies (and (equal (fn-omk-at 0 c) :wait-write)
                (equal (fn-omk-at 0 (fn-omk-at 17 c)) 4)
                (equal (car r) :written))
   (and (equal (fn-omk-at 19 (mv-nth 1 r)) (fn-omk-at 19 c))
        (equal (fn-omk-at 6 (mv-nth 1 r)) (fn-omk-at 6 c))
        (equal (fn-omk-at 21 (mv-nth 1 r)) (fn-omk-at 21 c))
        (equal (fn-omk-at 0 (mv-nth 1 r)) (fn-omk-at 1 (fn-omk-at 17 c))))))
 :hints (("Goal" :use fn-hpic-written-directory-buffer-reset-unfolds
  :in-theory (disable fn-hpi-written fn-omk-at mv-nth)))))

(defthm fn-hpi-tick-restores-next-canonical-directory-page-invariant
 (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-hpic-directory-resume-invariantp c digests)
                (equal (car r) :written))
   (fn-hpic-directory-invariantp (mv-nth 2 r) digests (mv-nth 8 r))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-hpi-tick-resets-directory-buffer-after-exact-written-ack
        fn-hpic-written-keeps-cursor-width-unfolds fn-hpic-tick-written-and-frame-unfolds)
  :in-theory (e/d (fn-hpic-directory-resume-invariantp fn-hpic-scratch-ack-contextp
                  fn-hpic-directory-invariantp fn-hpic-meta-field fn-hpic-directory-model
                  fn-hpic-cached-digest-agreesp)
   (fn-hpi-tick fn-hpi-written fn-hpi-written-status fn-omk-at fn-omk-widthp
    fn-hpi-set fn-hpi-set-is-update-by-definition fn-hpi-reset-buffer fn-hpb-begin
    fn-hpb-prefix fn-hpb-used mv-nth fn-hpic-take-next fn-hpic-nth-nthcdr
    fn-hpic-stored-step-has-word-room-unfolds fn-hpic-stored-active-address-unfolds
    fn-hpic-continue-state-projection-unfolds fn-hpic-continue-used-projection-unfolds
    pgs-encode-run fn-hpm-model-entries take nth nthcdr unsigned-byte-p)))))

(local (defthm fn-hpic-metadata-issued-directory-carry-unfolds
 (let ((r (fn-hpi-metadata-step c fn-hpb)))
  (implies (and (fn-omk-widthp c 25)
                (equal (fn-hpic-meta-field 0 c) :directory)
                (equal (car r) :write))
   (and (fn-omk-widthp (mv-nth 2 r) 25)
        (equal (fn-hpic-meta-field 0 (mv-nth 2 r)) :directory)
        (equal (fn-hpic-meta-field 4 (mv-nth 2 r)) (fn-hpic-meta-field 4 c))
        (equal (fn-hpic-meta-field 5 (mv-nth 2 r)) (fn-hpic-meta-field 5 c))
        (equal (fn-omk-at 21 (mv-nth 2 r)) (fn-omk-at 21 c))
        (equal (fn-omk-at 0 (fn-omk-at 17 (mv-nth 2 r))) 4)
        (equal (fn-omk-at 1 (fn-omk-at 17 (mv-nth 2 r)))
               (if (zp (fn-hpic-meta-field 3 c)) :directory-digest-start :metadata)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use fn-hpic-metadata-directory-write-unfolds
  :in-theory (e/d (fn-hpi-metadata-step fn-hpi-await-page fn-hpic-meta-field fn-hpb-ready)
   (fn-hpi-write-effect fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at mv-nth
    fn-hpb-used fn-hpb-ready fn-hpb-prefix fn-hpm-tick fn-hpm-tick-progress
    fn-hpm-tick-nonstored-unchanged fn-hpi-issue-io
    fn-hpic-stored-step-has-word-room-unfolds fn-hpic-take-next unsigned-byte-p nfix))))))

(defthm fn-hpi-tick-hands-off-next-directory-page-invariant
 (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-hpic-directory-invariantp c digests fn-hpb)
                (posp (fn-hpic-meta-field 3 c))
                (equal (car r) :write))
   (fn-hpic-directory-resume-invariantp (mv-nth 2 r) digests)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-hpic-metadata-directory-write-unfolds
        fn-hpic-metadata-issued-directory-carry-unfolds
        fn-hpic-tick-metadata-write-and-frame-unfolds)
  :in-theory (e/d (fn-hpic-directory-invariantp fn-hpic-directory-resume-invariantp
                  fn-hpic-scratch-ack-contextp fn-hpic-meta-field fn-hpic-cached-digest-agreesp)
   (fn-hpi-tick fn-hpi-metadata-step fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at
    fn-omk-widthp fn-hpb-prefix fn-hpb-used mv-nth fn-hpic-directory-model
    fn-hpic-take-next fn-hpic-nth-nthcdr fn-hpic-stored-step-has-word-room-unfolds
    fn-hpic-continue-state-projection-unfolds fn-hpic-continue-used-projection-unfolds
    pgs-encode-run fn-hpm-model-entries take nth nthcdr unsigned-byte-p)))))
