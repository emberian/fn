; Actual canonical table phase; local directory helpers stay scoped.
(in-package "ACL2")
(include-book "history-image-canonical-refinement")

(local (defthm fn-hpic-take-next
 (implies (natp n)
  (equal (take (+ 1 n) xs) (append (take n xs) (list (nth n xs)))))
 :hints (("Goal" :induct (take n xs) :in-theory (enable take nth)))))

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

(local (defthm fn-hpic-nth-nthcdr
 (implies (and (natp a) (natp n))
  (equal (nth n (nthcdr a xs)) (nth (+ a n) xs)))
 :hints (("Goal" :induct (nthcdr a xs) :in-theory (enable nth nthcdr)))))

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

(local (defthm fn-hpic-issued-io-is-not-write-unfolds
 (not (equal (car (fn-hpi-issue-io tag kind ordinal offset length bytes wait c)) :write))
 :hints (("Goal" :in-theory (e/d (fn-hpi-issue-io)
  (fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at))))))

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

(defun fn-hpic-table-start (c)
 (declare (xargs :guard t :verify-guards nil))
 (* 341 (fn-hpic-meta-field 6 c)))

(defun fn-hpic-table-digests (c digests)
 (declare (xargs :guard t :verify-guards nil))
 (take (- (fn-hpic-meta-field 4 c) (fn-hpic-table-start c))
       (nthcdr (fn-hpic-table-start c) digests)))

(defun fn-hpic-table-model (c digests)
 (declare (xargs :guard t :verify-guards nil))
 (pgs-encode-table
  (fn-hpm-model-entries (fn-hpic-table-digests c digests)
    (+ (fn-hpic-meta-field 5 c) (fn-hpic-table-start c)))))

(defun fn-hpic-table-cache-agreesp (c digests)
 (declare (xargs :guard t :verify-guards nil))
 (implies (and (fn-hpic-current-cachep c)
               (< (fn-hpic-meta-field 1 c) (fn-hpic-meta-field 4 c)))
  (equal (fn-omk-at 2 (fn-omk-at 21 c))
         (nth (fn-hpic-meta-field 1 c) digests))))

(defun fn-hpic-table-invariantp (c digests fn-hpb)
 (declare (xargs :stobjs fn-hpb :verify-guards nil))
 (let* ((layout (fn-omk-at 1 (fn-omk-at 6 c)))
        (page (fn-hpic-meta-field 6 c)) (start (fn-hpic-table-start c))
        (ordinal (fn-hpic-meta-field 1 c)) (component (fn-hpic-meta-field 2 c))
        (remaining (fn-hpic-meta-field 3 c)) (entries (fn-hpic-meta-field 4 c))
        (base (fn-hpic-meta-field 5 c)) (used (fn-hpb-used fn-hpb)))
  (and (fn-omk-widthp c 25) (equal (fn-omk-at 0 c) :metadata)
       (equal (fn-hpic-meta-field 0 c) :table)
       (natp page) (< page (nfix (fn-omk-at 2 layout)))
       (natp ordinal) (<= start ordinal) (natp component) (< component 6)
       (natp remaining) (natp base) (natp used) (<= used 2048)
       (equal base (nfix (fn-omk-at 4 layout)))
       (equal (len digests) (nfix (fn-omk-at 1 layout)))
       (<= start (len digests))
       (equal entries (min (len digests) (+ 341 start)))
       (equal (+ (* 6 (- ordinal start)) component) used)
       (equal (+ remaining used) 2048)
       (fn-hpic-table-cache-agreesp c digests)
       (equal (fn-hpb-prefix fn-hpb) (take used (fn-hpic-table-model c digests))))))

(local (defun fn-hpic-nth-take-ind (i n xs)
 (if (or (zp i) (zp n)) (list i n xs)
  (fn-hpic-nth-take-ind (1- i) (1- n) (cdr xs)))))

(local (defthm fn-hpic-nth-take-unfolds
 (implies (and (natp i) (natp n) (< i n))
  (equal (nth i (take n xs)) (nth i xs)))
 :hints (("Goal" :induct (fn-hpic-nth-take-ind i n xs) :in-theory (enable take nth)))))

(local (defthm fn-hpic-len-take-unfolds
 (implies (natp n) (equal (len (take n xs)) n))
 :hints (("Goal" :induct (take n xs) :in-theory (enable take)))))

(local (defthm fn-hpic-table-slice-current-digest-unfolds
 (implies (and (fn-hpic-table-invariantp c digests fn-hpb)
               (< (fn-hpic-meta-field 1 c) (fn-hpic-meta-field 4 c)))
  (equal (nth (- (fn-hpic-meta-field 1 c) (fn-hpic-table-start c))
              (fn-hpic-table-digests c digests))
         (nth (fn-hpic-meta-field 1 c) digests)))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-hpic-table-invariantp fn-hpic-table-digests fn-hpic-table-start)
   (fn-hpic-meta-field fn-omk-at fn-hpb-used fn-hpb-prefix take nth nthcdr
    fn-hpic-table-model fn-hpic-table-cache-agreesp fn-hpic-take-next))))))

(local (defthm fn-hpic-table-cached-value-unfolds
 (implies (and (fn-hpic-table-cache-agreesp c digests)
               (fn-hpic-current-cachep c)
               (< (fn-hpic-meta-field 1 c) (fn-hpic-meta-field 4 c)))
  (equal (fn-omk-at 2 (fn-omk-at 21 c))
         (nth (fn-hpic-meta-field 1 c) digests)))
 :hints (("Goal" :in-theory (e/d (fn-hpic-table-cache-agreesp)
             (fn-hpic-current-cachep fn-hpic-meta-field fn-omk-at nth))))))

(defthm fn-hpi-metadata-step-appends-current-table-word
 (implies (and (fn-hpic-table-invariantp c digests fn-hpb)
               (equal (car (fn-hpi-metadata-step c fn-hpb)) :continue))
  (equal (fn-hpb-prefix (mv-nth 3 (fn-hpi-metadata-step c fn-hpb)))
         (append (fn-hpb-prefix fn-hpb)
                 (list (nth (fn-hpb-used fn-hpb) (fn-hpic-table-model c digests))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :cases ((< (fn-hpic-meta-field 1 c) (fn-hpic-meta-field 4 c)))
  :use (fn-hpic-metadata-continue-is-stored-unfolds
        (:instance fn-hpic-table-slice-current-digest-unfolds)
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
        (:instance fn-hpm-word-refines-directory-run
          (base (+ (fn-hpic-meta-field 5 c) (fn-hpic-table-start c)))
          (k (- (fn-hpic-meta-field 1 c) (fn-hpic-table-start c)))
          (component (fn-hpic-meta-field 2 c)) (digests (fn-hpic-table-digests c digests)) (m 1))
        (:instance fn-hpm-tick-refines-emission-effect
          (ordinal (fn-hpic-meta-field 1 c)) (component (fn-hpic-meta-field 2 c))
          (remaining (fn-hpic-meta-field 3 c)) (entries (fn-hpic-meta-field 4 c))
          (base (fn-hpic-meta-field 5 c))
          (digest (if (fn-hpic-current-cachep c) (fn-omk-at 2 (fn-omk-at 21 c)) 0)))
        (:instance fn-hpm-directory-padding-is-zero
          (i (fn-hpb-used fn-hpb))
          (base (+ (fn-hpic-meta-field 5 c) (fn-hpic-table-start c)))
          (digests (fn-hpic-table-digests c digests)) (m 1)))
  :in-theory (e/d (fn-hpic-table-invariantp fn-hpic-table-model fn-hpic-table-digests
                  fn-hpic-table-start fn-hpic-meta-field)
   (mv-nth fn-omk-at fn-hpi-set fn-hpi-set-is-update-by-definition fn-hpi-metadata-step
    fn-hpi-issue-io fn-hpi-await-page fn-hpb-ready fn-hpb-used fn-hpb-prefix
    take nth nthcdr fn-hpic-take-next unsigned-byte-p
    fn-hpic-table-cache-agreesp fn-hpic-cached-digest-agreesp fn-hpic-current-cachep
    fn-hpm-tick fn-hpm-tick-nonstored-unchanged fn-hpm-word pgs-encode-run
    pgs-encode-table fn-hpm-model-entries
    (:executable-counterpart pgs-encode-run) (:executable-counterpart pgs-encode-table)
    (:executable-counterpart fn-hpm-model-entries))))))

(defthm fn-hpi-tick-appends-current-table-word-and-frames-other-state
 (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-hpic-table-invariantp c digests fn-hpb)
                (equal (car r) :continue))
   (and (equal (fn-hpb-prefix (mv-nth 8 r))
          (append (fn-hpb-prefix fn-hpb)
                  (list (nth (fn-hpb-used fn-hpb) (fn-hpic-table-model c digests)))))
        (equal (mv-nth 3 r) ledger)
        (equal (mv-nth 4 r) fn-hpq0) (equal (mv-nth 5 r) fn-hpq1)
        (equal (mv-nth 6 r) fn-hpq2) (equal (mv-nth 7 r) fn-hpq3)
        (equal (mv-nth 9 r) pgs-digest-state))))
 :rule-classes nil
 :hints (("Goal" :use (fn-hpic-tick-metadata-prefix-and-frame-unfolds
                       fn-hpi-metadata-step-appends-current-table-word)
  :in-theory (e/d (fn-hpic-table-invariantp)
    (fn-hpi-tick fn-hpi-metadata-step fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at
     fn-hpb-prefix fn-hpb-used mv-nth fn-hpic-table-model fn-hpic-meta-field
     fn-hpic-table-cache-agreesp fn-hpic-table-start
     fn-hpi-grant-matchesp fn-hpi-stream-step take nth nthcdr)))))

(local (defthm fn-hpic-next-table-cache-agreement-unfolds
 (let* ((ordinal (fn-hpic-meta-field 1 c)) (component (fn-hpic-meta-field 2 c))
        (next (fn-hpi-set 19
         (list (fn-hpic-meta-field 0 c)
               (if (equal component 5) (+ 1 ordinal) ordinal)
               (if (equal component 5) 0 (+ 1 component))
               remaining (fn-hpic-meta-field 4 c) (fn-hpic-meta-field 5 c)
               (fn-hpic-meta-field 6 c)) c)))
  (implies (and (natp ordinal) (fn-hpic-table-cache-agreesp c digests)
                (implies (< ordinal (fn-hpic-meta-field 4 c)) (fn-hpic-current-cachep c)))
   (fn-hpic-table-cache-agreesp next digests)))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-hpic-table-cache-agreesp fn-hpic-current-cachep fn-hpic-meta-field)
   (fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at fn-omk-widthp unsigned-byte-p nth))))))

(local (defthm fn-hpic-metadata-continue-preserves-table-invariant
 (implies (and (fn-hpic-table-invariantp c digests fn-hpb)
               (equal (car (fn-hpi-metadata-step c fn-hpb)) :continue))
  (fn-hpic-table-invariantp
   (mv-nth 2 (fn-hpi-metadata-step c fn-hpb)) digests
   (mv-nth 3 (fn-hpi-metadata-step c fn-hpb))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-hpic-continue-metadata-complete-state-unfolds
        (:instance fn-hpic-next-table-cache-agreement-unfolds (remaining (1- (fn-hpic-meta-field 3 c))))
        fn-hpi-metadata-step-appends-current-table-word
        (:instance fn-hpic-take-next (n (fn-hpb-used fn-hpb)) (xs (fn-hpic-table-model c digests))))
  :in-theory (e/d (fn-hpic-table-invariantp fn-hpic-meta-field fn-hpic-table-model
                  fn-hpic-table-digests fn-hpic-table-start)
   (fn-hpic-stored-step-has-word-room-unfolds fn-hpic-stored-active-address-unfolds
    fn-hpic-table-cache-agreesp fn-hpic-current-cachep
    fn-hpi-metadata-step fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at fn-omk-widthp
    mv-nth fn-hpb-prefix fn-hpb-used fn-hpm-tick fn-hpm-tick-nonstored-unchanged
    pgs-encode-table fn-hpm-model-entries take nth nthcdr unsigned-byte-p
    fn-hpic-take-next fn-hpic-nth-nthcdr))))))

(defthm fn-hpi-tick-preserves-current-table-invariant
 (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-hpic-table-invariantp c digests fn-hpb)
                (equal (car r) :continue))
   (fn-hpic-table-invariantp (mv-nth 2 r) digests (mv-nth 8 r))))
 :rule-classes nil
 :hints (("Goal" :use (fn-hpic-tick-metadata-prefix-and-frame-unfolds
                       fn-hpic-metadata-continue-preserves-table-invariant)
  :in-theory (e/d (fn-hpic-table-invariantp)
   (fn-hpi-tick fn-hpi-metadata-step fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at
    fn-hpb-prefix fn-hpb-used mv-nth fn-hpic-table-model fn-hpic-meta-field
    fn-hpic-table-cache-agreesp fn-hpic-table-start
    fn-hpi-grant-matchesp fn-hpi-stream-step take nth nthcdr)))))

(local (defthm fn-hpic-table-window-bound-unfolds
 (implies (fn-hpic-table-invariantp c digests fn-hpb)
  (<= (len (fn-hpic-table-digests c digests)) 341))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-hpic-table-invariantp fn-hpic-table-digests fn-hpic-table-start)
   (fn-hpic-table-cache-agreesp fn-hpic-meta-field fn-omk-at fn-hpb-used fn-hpb-prefix
    fn-hpic-table-model take nth nthcdr fn-hpic-take-next))))
 :rule-classes nil))

(local (defthm fn-hpic-table-coordinate-unfolds
 (implies (fn-hpic-table-invariantp c digests fn-hpb)
  (and (fn-omk-widthp c 25) (equal (fn-omk-at 0 c) :metadata)
       (equal (fn-hpic-meta-field 0 c) :table) (natp (fn-hpb-used fn-hpb))))
 :hints (("Goal" :in-theory (e/d (fn-hpic-table-invariantp)
     (fn-omk-widthp fn-omk-at fn-hpb-used fn-hpb-prefix fn-hpic-meta-field
      fn-hpic-table-cache-agreesp fn-hpic-table-model fn-hpic-table-start))))
 :rule-classes nil))

(local (defthm fn-hpic-table-tail-word-is-zero-unfolds
 (implies (and (fn-hpic-table-invariantp c digests fn-hpb)
               (<= 2046 (fn-hpb-used fn-hpb)) (< (fn-hpb-used fn-hpb) 2048))
  (equal (nth (fn-hpb-used fn-hpb) (fn-hpic-table-model c digests)) 0))
 :hints (("Goal" :do-not-induct t
  :use (fn-hpic-table-window-bound-unfolds fn-hpic-table-coordinate-unfolds
        (:instance fn-hpm-directory-padding-is-zero
          (i (fn-hpb-used fn-hpb))
          (base (+ (fn-hpic-meta-field 5 c) (fn-hpic-table-start c)))
          (digests (fn-hpic-table-digests c digests)) (m 1)))
  :in-theory (e/d (fn-hpic-table-model)
   (fn-hpic-table-cache-agreesp fn-hpic-current-cachep fn-hpic-meta-field fn-omk-at
    fn-hpic-table-invariantp fn-hpic-table-digests fn-hpic-table-start
    fn-hpb-used fn-hpb-prefix fn-hpic-take-next pgs-encode-table pgs-encode-run
    fn-hpm-model-entries take nth nthcdr unsigned-byte-p))))
 :rule-classes nil))

(local (defthm fn-hpic-tick-metadata-continue-has-word-room-unfolds
 (implies (and (fn-omk-widthp c 25) (equal (fn-omk-at 0 c) :metadata)
               (equal (car (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)) :continue))
  (< (fn-hpb-used fn-hpb) 2048))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-hpic-tick-metadata-prefix-and-frame-unfolds fn-hpic-continue-metadata-complete-state-unfolds)
  :in-theory (disable fn-hpi-tick fn-hpi-metadata-step fn-hpb-used fn-omk-at mv-nth
             fn-hpic-current-cachep fn-hpic-meta-field fn-hpi-set
             fn-hpic-continue-state-projection-unfolds fn-hpic-continue-used-projection-unfolds)))))

(defthm fn-hpi-tick-appends-table-tail-zero-and-preserves-invariant
 (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-hpic-table-invariantp c digests fn-hpb)
                (<= 2046 (fn-hpb-used fn-hpb))
                (equal (car r) :continue))
   (and (equal (fn-hpb-prefix (mv-nth 8 r)) (append (fn-hpb-prefix fn-hpb) (list 0)))
        (fn-hpic-table-invariantp (mv-nth 2 r) digests (mv-nth 8 r))
        (equal (mv-nth 3 r) ledger)
        (equal (mv-nth 4 r) fn-hpq0) (equal (mv-nth 5 r) fn-hpq1)
        (equal (mv-nth 6 r) fn-hpq2) (equal (mv-nth 7 r) fn-hpq3)
        (equal (mv-nth 9 r) pgs-digest-state))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-hpic-table-coordinate-unfolds fn-hpi-tick-appends-current-table-word-and-frames-other-state
        fn-hpi-tick-preserves-current-table-invariant
        fn-hpic-tick-metadata-continue-has-word-room-unfolds fn-hpic-table-tail-word-is-zero-unfolds)
  :in-theory (e/d ()
   (fn-hpi-tick fn-hpi-metadata-step fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at
    fn-hpic-meta-field fn-hpb-prefix fn-hpb-used mv-nth fn-hpic-table-cache-agreesp fn-hpic-current-cachep
    fn-hpic-table-invariantp fn-hpic-table-model fn-hpic-table-digests fn-hpic-table-start
    fn-hpic-continue-state-projection-unfolds fn-hpic-continue-used-projection-unfolds
    fn-hpic-stored-step-has-word-room-unfolds fn-hpic-stored-active-address-unfolds
    pgs-encode-table pgs-encode-run fn-hpm-model-entries take nth nthcdr fn-hpic-take-next)))))

(local (defthm fn-hpic-entry-words-length-unfolds
 (equal (len (pgs-entry-words e)) 6)
 :hints (("Goal" :in-theory (enable pgs-entry-words)))))

(local (defthm fn-hpic-model-entry-words-length-unfolds
 (equal (len (pgs-entries-words (fn-hpm-model-entries digests base))) (* 6 (len digests)))
 :hints (("Goal" :induct (fn-hpm-model-entries digests base)
                 :in-theory (enable pgs-entries-words)))))

(local (defthm fn-hpic-take-full-length-unfolds
 (implies (true-listp xs) (equal (take (len xs) xs) xs))
 :hints (("Goal" :induct (len xs) :in-theory (e/d (take) (fn-hpic-take-next))))))

(local (defthm fn-hpic-model-entries-length-unfolds
 (equal (len (fn-hpm-model-entries digests base)) (len digests))
 :hints (("Goal" :induct (fn-hpm-model-entries digests base) :in-theory (enable fn-hpm-model-entries)))))

(local (defthm fn-hpic-zero-words-length-unfolds
 (equal (len (pgs-zeros n)) (nfix n))
 :hints (("Goal" :induct (pgs-zeros n) :in-theory (enable pgs-zeros)))))

(local (defthm fn-hpic-entry-words-list-unfolds
 (true-listp (pgs-entries-words entries))
 :hints (("Goal" :induct (pgs-entries-words entries) :in-theory (enable pgs-entries-words pgs-entry-words)))))

(local (defthm fn-hpic-zero-words-list-unfolds
 (true-listp (pgs-zeros n))
 :hints (("Goal" :induct (pgs-zeros n) :in-theory (enable pgs-zeros)))))

(local (defthm fn-hpic-bounded-table-is-complete-page-unfolds
 (implies (<= (len digests) 341)
  (equal (take 2048 (pgs-encode-table (fn-hpm-model-entries digests base)))
         (pgs-encode-table (fn-hpm-model-entries digests base))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-hpic-take-full-length-unfolds
          (xs (pgs-encode-table (fn-hpm-model-entries digests base)))))
  :in-theory (e/d (pgs-encode-table pgs-encode-run)
   (take pgs-entries-words pgs-entry-words fn-hpm-model-entries pgs-zeros fn-hpic-take-next))))))

(local (defthm fn-hpic-table-model-is-complete-page-unfolds
 (implies (fn-hpic-table-invariantp c digests fn-hpb)
  (equal (take 2048 (fn-hpic-table-model c digests)) (fn-hpic-table-model c digests)))
 :hints (("Goal" :do-not-induct t
  :use (fn-hpic-table-window-bound-unfolds
        (:instance fn-hpic-bounded-table-is-complete-page-unfolds
          (digests (fn-hpic-table-digests c digests))
          (base (+ (fn-hpic-meta-field 5 c) (fn-hpic-table-start c)))))
  :in-theory (e/d (fn-hpic-table-model)
    (take pgs-entry-words pgs-entries-words fn-hpm-model-entries fn-omk-at fn-hpic-meta-field
     fn-hpb-used fn-hpb-prefix fn-hpic-take-next fn-hpic-table-cache-agreesp
     fn-hpic-table-invariantp fn-hpic-table-digests fn-hpic-table-start pgs-encode-table pgs-encode-run))))
 :rule-classes nil))

(local (defthm fn-hpic-full-table-prefix-is-model-unfolds
 (implies (and (fn-hpic-table-invariantp c digests fn-hpb)
               (equal (fn-hpb-used fn-hpb) 2048))
  (equal (fn-hpb-prefix fn-hpb) (fn-hpic-table-model c digests)))
 :rule-classes nil
 :hints (("Goal" :use fn-hpic-table-model-is-complete-page-unfolds
  :in-theory (e/d (fn-hpic-table-invariantp)
   (fn-hpb-used fn-hpb-prefix fn-hpic-table-model fn-hpic-meta-field fn-omk-at
    fn-hpic-table-cache-agreesp fn-hpic-table-start take fn-hpic-take-next)))))
)

(local (defthm fn-hpic-metadata-table-write-unfolds
 (let ((r (fn-hpi-metadata-step c fn-hpb)))
  (implies (and (equal (fn-hpic-meta-field 0 c) :table) (equal (car r) :write))
   (and (equal (fn-hpb-used fn-hpb) 2048) (equal (mv-nth 3 r) fn-hpb)
        (equal (mv-nth 1 r)
         (fn-hpi-write-effect (fn-omk-at 1 c) (fn-omk-at 3 c)
           (nfix (fn-omk-at 4 c)) :table (fn-hpic-meta-field 6 c)
           (+ (nfix (fn-omk-at 5 (fn-omk-at 1 (fn-omk-at 6 c)))) (fn-hpic-meta-field 6 c))
           (nfix (fn-omk-at 4 (fn-omk-at 16 c)))))
        (equal (fn-omk-at 0 (mv-nth 2 r)) :wait-write)
        (equal (fn-omk-at 19 (mv-nth 2 r)) (fn-omk-at 19 c))
        (equal (fn-omk-at 6 (mv-nth 2 r)) (fn-omk-at 6 c))
        (equal (fn-omk-at 0 (fn-omk-at 17 (mv-nth 2 r))) 4)
        (equal (fn-omk-at 1 (fn-omk-at 17 (mv-nth 2 r))) :table-digest-start))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-hpi-metadata-step fn-hpi-await-page fn-hpic-meta-field fn-hpb-ready)
   (fn-hpi-write-effect fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at mv-nth
    fn-hpb-used fn-hpm-tick fn-hpm-tick-progress fn-hpm-tick-nonstored-unchanged
    fn-hpi-issue-io fn-hpb-prefix fn-hpic-stored-step-has-word-room-unfolds
    unsigned-byte-p natp nfix zp zp-open))))))

(defthm fn-hpi-tick-hands-off-complete-canonical-table-page
 (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-hpic-table-invariantp c digests fn-hpb) (equal (car r) :write))
   (and (equal (fn-hpb-prefix (mv-nth 8 r)) (fn-hpic-table-model c digests))
        (equal (mv-nth 1 r)
         (fn-hpi-write-effect (fn-omk-at 1 c) (fn-omk-at 3 c)
           (nfix (fn-omk-at 4 c)) :table (fn-hpic-meta-field 6 c)
           (+ (nfix (fn-omk-at 5 (fn-omk-at 1 (fn-omk-at 6 c)))) (fn-hpic-meta-field 6 c))
           (nfix (fn-omk-at 4 (fn-omk-at 16 c)))))
        (equal (fn-omk-at 0 (mv-nth 2 r)) :wait-write)
        (equal (fn-omk-at 19 (mv-nth 2 r)) (fn-omk-at 19 c))
        (equal (fn-omk-at 6 (mv-nth 2 r)) (fn-omk-at 6 c))
        (equal (fn-omk-at 0 (fn-omk-at 17 (mv-nth 2 r))) 4)
        (equal (fn-omk-at 1 (fn-omk-at 17 (mv-nth 2 r))) :table-digest-start)
        (equal (mv-nth 3 r) ledger)
        (equal (mv-nth 4 r) fn-hpq0) (equal (mv-nth 5 r) fn-hpq1)
        (equal (mv-nth 6 r) fn-hpq2) (equal (mv-nth 7 r) fn-hpq3)
        (equal (mv-nth 8 r) fn-hpb) (equal (mv-nth 9 r) pgs-digest-state))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-hpic-table-coordinate-unfolds fn-hpic-full-table-prefix-is-model-unfolds
        fn-hpic-metadata-table-write-unfolds
        fn-hpic-tick-metadata-write-and-frame-unfolds)
  :in-theory (e/d ()
   (fn-hpi-tick fn-hpi-metadata-step fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at
    fn-hpi-write-effect fn-hpic-table-invariantp
    fn-hpb-prefix fn-hpb-used mv-nth fn-hpic-table-model fn-hpic-meta-field
    fn-hpic-table-cache-agreesp fn-hpic-table-start fn-hpic-table-digests
    fn-hpic-take-next fn-hpic-nth-nthcdr fn-hpic-stored-step-has-word-room-unfolds
    fn-hpic-continue-state-projection-unfolds fn-hpic-continue-used-projection-unfolds
    pgs-encode-table fn-hpm-model-entries take nth nthcdr unsigned-byte-p)))))

; Successful data/table digest spool settlement is the actual transition
; that establishes the next table page. This observer carries the supported
; layout coordinate and empty scratch, not a host assertion of digest truth.
(defun fn-hpic-next-table-page (c)
 (declare (xargs :guard t :verify-guards nil))
 (if (equal (fn-omk-at 0 (fn-omk-at 20 c)) :data) 0
   (+ 1 (nfix (fn-omk-at 1 (fn-omk-at 20 c))))))

(defun fn-hpic-table-spool-contextp (c digests fn-hpb)
 (declare (xargs :stobjs fn-hpb :verify-guards nil))
 (let* ((layout (fn-omk-at 1 (fn-omk-at 6 c)))
        (kind (fn-omk-at 0 (fn-omk-at 20 c)))
        (index (nfix (fn-omk-at 1 (fn-omk-at 20 c))))
        (page (fn-hpic-next-table-page c))
        (n (nfix (fn-omk-at 1 layout)))
        (nt (nfix (fn-omk-at 2 layout))))
  (and (fn-omk-widthp c 25) (equal (fn-omk-at 0 c) :wait-spool-write)
       (or (and (equal kind :data) (equal (+ 1 index) n))
           (and (equal kind :table) (< (+ 1 index) nt)))
       (equal (len digests) n) (< page nt) (<= (* 341 page) n)
       (equal (fn-hpb-used fn-hpb) 0) (equal (fn-hpb-prefix fn-hpb) nil))))

(local (defthm fn-hpic-table-start-prefix-zero-by-definition
 (equal (take 0 xs) nil)
 :hints (("Goal" :in-theory (enable take)))))

(local (defthm fn-hpic-table-meta-begin-establishes-invariant
 (implies (and (fn-omk-widthp c 25) (natp page)
               (< page (nfix (fn-omk-at 2 (fn-omk-at 1 (fn-omk-at 6 c)))))
               (<= (* 341 page) (len digests))
               (equal (len digests) (nfix (fn-omk-at 1 (fn-omk-at 1 (fn-omk-at 6 c)))))
               (equal (fn-hpb-used fn-hpb) 0) (equal (fn-hpb-prefix fn-hpb) nil))
  (fn-hpic-table-invariantp (fn-hpi-meta-begin :table page c) digests fn-hpb))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-hpi-meta-begin fn-hpic-table-invariantp fn-hpic-meta-field
                  fn-hpic-table-start fn-hpic-table-cache-agreesp)
   (fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at fn-omk-widthp
    fn-hpb-prefix fn-hpb-used fn-hpic-table-model take nth nthcdr
    fn-hpic-take-next fn-hpic-stored-step-has-word-room-unfolds))))))

(local (defthm fn-hpic-after-spool-establishes-table-invariant
 (implies (fn-hpic-table-spool-contextp c digests fn-hpb)
  (and (equal (car (fn-hpi-after-spool c pgs-digest-state)) :continue)
       (fn-hpic-table-invariantp
        (mv-nth 1 (fn-hpi-after-spool c pgs-digest-state)) digests fn-hpb)
       (equal (mv-nth 2 (fn-hpi-after-spool c pgs-digest-state)) pgs-digest-state)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-hpic-table-meta-begin-establishes-invariant
         (page (fn-hpic-next-table-page c))))
  :in-theory (e/d (fn-hpic-table-spool-contextp fn-hpic-next-table-page fn-hpi-after-spool)
   (fn-hpi-meta-begin fn-hpic-table-invariantp fn-hpi-set fn-hpi-set-is-update-by-definition
    fn-omk-at fn-omk-widthp fn-hpb-prefix fn-hpb-used fn-hpi-digest-begin mv-nth
    fn-hpic-stored-step-has-word-room-unfolds))))))

(local (defthm fn-hpic-spool-context-pending-frame-unfolds
 (implies (fn-hpic-table-spool-contextp c digests fn-hpb)
  (fn-hpic-table-spool-contextp (fn-hpi-set 5 nil c) digests fn-hpb))
 :hints (("Goal" :in-theory (e/d (fn-hpic-table-spool-contextp fn-hpic-next-table-page)
   (fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at fn-omk-widthp
    fn-hpb-prefix fn-hpb-used))))))

(local (defthm fn-hpic-matched-io-outcome-by-definition
 (implies (fn-hpi-io-matchp c observation tag width)
  (member-eq (fn-omk-at 7 observation) '(:ok :uncertain :refused)))
 :hints (("Goal" :in-theory (e/d (fn-hpi-io-matchp)
  (fn-omk-at fn-omk-widthp fn-omk-token-matchp))))))

(local (defthm fn-hpic-tick-accepted-spool-frame-unfolds
 (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-omk-widthp c 25) (equal (fn-omk-at 0 c) :wait-spool-write)
                (equal (car r) :continue))
   (and (equal (mv-nth 2 r)
          (mv-nth 1 (fn-hpi-after-spool (fn-hpi-set 5 nil c) pgs-digest-state)))
        (equal (mv-nth 9 r)
          (mv-nth 2 (fn-hpi-after-spool (fn-hpi-set 5 nil c) pgs-digest-state)))
        (equal (mv-nth 3 r) ledger) (equal (mv-nth 4 r) fn-hpq0)
        (equal (mv-nth 5 r) fn-hpq1) (equal (mv-nth 6 r) fn-hpq2)
        (equal (mv-nth 7 r) fn-hpq3) (equal (mv-nth 8 r) fn-hpb))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-hpic-matched-io-outcome-by-definition (tag :spool-written) (width 8)))
  :in-theory (e/d (fn-hpi-tick fn-hpi-stream-step)
   (fn-hpi-after-spool fn-hpi-io-matchp fn-hpi-grant-matchesp fn-omk-at fn-hpi-set
    fn-hpi-set-is-update-by-definition mv-nth fn-hpi-written fn-hpi-supply fn-hpi-buffer-step
    fn-hpi-digest-begin fn-hpi-digest-validp pgs-dcb-read-demand pgs-dcb-step
    fn-hpi-issue-io pgs-dcb-result-octets fn-hpir-root fn-hpi-octets-p))))))

(defthm fn-hpi-tick-establishes-next-canonical-table-after-spool-ack
 (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-hpic-table-spool-contextp c digests fn-hpb)
                (equal (car r) :continue))
   (and (fn-hpic-table-invariantp (mv-nth 2 r) digests (mv-nth 8 r))
        (equal (mv-nth 3 r) ledger) (equal (mv-nth 4 r) fn-hpq0)
        (equal (mv-nth 5 r) fn-hpq1) (equal (mv-nth 6 r) fn-hpq2)
        (equal (mv-nth 7 r) fn-hpq3) (equal (mv-nth 8 r) fn-hpb)
        (equal (mv-nth 9 r) pgs-digest-state))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-hpic-tick-accepted-spool-frame-unfolds
        (:instance fn-hpic-after-spool-establishes-table-invariant (c (fn-hpi-set 5 nil c))))
  :in-theory (e/d (fn-hpic-table-spool-contextp)
   (fn-hpi-tick fn-hpi-stream-step fn-hpi-after-spool fn-hpi-meta-begin
    fn-hpic-table-invariantp fn-hpic-next-table-page fn-hpi-set
    fn-hpi-set-is-update-by-definition fn-omk-at fn-omk-widthp fn-hpb-prefix
    fn-hpb-used mv-nth fn-hpic-stored-step-has-word-room-unfolds)))))

(defun fn-hpic-directory-spool-contextp (c digests fn-hpb)
 (declare (xargs :stobjs fn-hpb :verify-guards nil))
 (let* ((layout (fn-omk-at 1 (fn-omk-at 6 c)))
        (index (nfix (fn-omk-at 1 (fn-omk-at 20 c))))
        (nt (nfix (fn-omk-at 2 layout)))
        (m (nfix (fn-omk-at 3 layout))))
  (and (fn-omk-widthp c 25) (equal (fn-omk-at 0 c) :wait-spool-write)
       (equal (fn-omk-at 0 (fn-omk-at 20 c)) :table) (<= nt (+ 1 index))
       (equal (len digests) nt) (< 0 m) (<= (* 6 nt) (* 2048 m))
       (equal (fn-hpb-used fn-hpb) 0) (equal (fn-hpb-prefix fn-hpb) nil))))

(local (defthm fn-hpic-directory-meta-begin-establishes-invariant
 (implies (and (fn-omk-widthp c 25)
               (equal (len digests) (nfix (fn-omk-at 2 (fn-omk-at 1 (fn-omk-at 6 c)))))
               (< 0 (nfix (fn-omk-at 3 (fn-omk-at 1 (fn-omk-at 6 c)))))
               (<= (* 6 (len digests)) (* 2048 (nfix (fn-omk-at 3 (fn-omk-at 1 (fn-omk-at 6 c))))))
               (equal (fn-hpb-used fn-hpb) 0) (equal (fn-hpb-prefix fn-hpb) nil))
  (fn-hpic-directory-invariantp (fn-hpi-meta-begin :directory page c) digests fn-hpb))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-hpi-meta-begin fn-hpic-directory-invariantp fn-hpic-meta-field
                  fn-hpic-cached-digest-agreesp)
   (fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at fn-omk-widthp
    fn-hpb-prefix fn-hpb-used fn-hpic-directory-model take nth nthcdr
    fn-hpic-take-next fn-hpic-stored-step-has-word-room-unfolds))))))

(local (defthm fn-hpic-after-spool-establishes-directory-invariant
 (implies (fn-hpic-directory-spool-contextp c digests fn-hpb)
  (and (equal (car (fn-hpi-after-spool c pgs-digest-state)) :continue)
       (fn-hpic-directory-invariantp
        (mv-nth 1 (fn-hpi-after-spool c pgs-digest-state)) digests fn-hpb)
       (equal (mv-nth 2 (fn-hpi-after-spool c pgs-digest-state)) pgs-digest-state)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-hpic-directory-meta-begin-establishes-invariant
         (page (+ 1 (nfix (fn-omk-at 1 (fn-omk-at 20 c)))))))
  :in-theory (e/d (fn-hpic-directory-spool-contextp fn-hpi-after-spool)
   (fn-hpi-meta-begin fn-hpic-directory-invariantp fn-hpi-set fn-hpi-set-is-update-by-definition
    fn-omk-at fn-omk-widthp fn-hpb-prefix fn-hpb-used fn-hpi-digest-begin mv-nth
    fn-hpic-stored-step-has-word-room-unfolds))))))

(local (defthm fn-hpic-directory-spool-context-pending-frame-unfolds
 (implies (fn-hpic-directory-spool-contextp c digests fn-hpb)
  (fn-hpic-directory-spool-contextp (fn-hpi-set 5 nil c) digests fn-hpb))
 :hints (("Goal" :in-theory (e/d (fn-hpic-directory-spool-contextp)
   (fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at fn-omk-widthp
    fn-hpb-prefix fn-hpb-used))))))

(defthm fn-hpi-tick-establishes-canonical-directory-after-last-table-spool-ack
 (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-hpic-directory-spool-contextp c digests fn-hpb)
                (equal (car r) :continue))
   (and (fn-hpic-directory-invariantp (mv-nth 2 r) digests (mv-nth 8 r))
        (equal (mv-nth 3 r) ledger) (equal (mv-nth 4 r) fn-hpq0)
        (equal (mv-nth 5 r) fn-hpq1) (equal (mv-nth 6 r) fn-hpq2)
        (equal (mv-nth 7 r) fn-hpq3) (equal (mv-nth 8 r) fn-hpb)
        (equal (mv-nth 9 r) pgs-digest-state))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-hpic-tick-accepted-spool-frame-unfolds
        (:instance fn-hpic-after-spool-establishes-directory-invariant (c (fn-hpi-set 5 nil c))))
  :in-theory (e/d (fn-hpic-directory-spool-contextp)
   (fn-hpi-tick fn-hpi-stream-step fn-hpi-after-spool fn-hpi-meta-begin
    fn-hpic-directory-invariantp fn-hpi-set fn-hpi-set-is-update-by-definition
    fn-omk-at fn-omk-widthp fn-hpb-prefix fn-hpb-used mv-nth
    fn-hpic-stored-step-has-word-room-unfolds)))))
