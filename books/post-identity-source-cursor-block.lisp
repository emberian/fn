; Proof-only exact optional D25 agent block and its paid cursor trace.
(in-package "ACL2")
(include-book "post-identity-source-cursor-info")
(local (include-book "arithmetic/top" :dir :system))

(local (defthm fn-psc-strip-success-is-exact-drop
 (implies (and (true-listp prefix) (not (equal (fn-inj-strip prefix xs) :no)))
  (equal (fn-inj-strip prefix xs) (nthcdr (len prefix) xs)))
 :hints (("Goal" :induct (fn-inj-strip prefix xs)
  :in-theory (enable fn-inj-strip nthcdr len true-listp)))))

(local (defthm fn-psc-nthcdr-composes-offsets
 (implies (and (natp a) (natp b))
  (equal (nthcdr b (nthcdr a xs)) (nthcdr (+ a b) xs)))
 :hints (("Goal" :induct (nthcdr a xs) :in-theory (enable nthcdr)))))

(local (defthm fn-psc-info-drop-is-nthcdr
 (implies (true-listp xs) (equal (fn-inj-drop off xs) (nthcdr (nfix off) xs)))
 :hints (("Goal" :induct (fn-inj-drop off xs) :in-theory (enable fn-inj-drop nthcdr nfix true-listp)))))

(local (defthm fn-psc-block-nthcdr-at-or-past-end
 (implies (and (true-listp xs) (natp off) (<= (len xs) off))
  (equal (nthcdr off xs) nil))
 :hints (("Goal" :induct (nthcdr off xs) :in-theory (enable nthcdr len true-listp)))))

(local (defthm fn-psc-block-clamped-drop
 (implies (and (true-listp xs) (natp start) (<= start (len xs)) (natp count))
  (equal (nthcdr (min (+ start count) (len xs)) xs)
         (fn-inj-drop count (nthcdr start xs))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-block-nthcdr-at-or-past-end (off (+ start count)))
        (:instance fn-psc-block-nthcdr-at-or-past-end (off (len xs))))
  :in-theory (e/d (min) (nthcdr fn-inj-drop len))))))

(local (defthm fn-psc-block-strip-success-bound
 (implies (and (true-listp prefix) (true-listp xs)
               (not (equal (fn-inj-strip prefix xs) :no)))
  (<= (len prefix) (len xs)))
 :hints (("Goal" :induct (fn-inj-strip prefix xs)
  :in-theory (enable fn-inj-strip len true-listp)))))

(local (defthm fn-psc-block-nthcdr-length
 (implies (and (true-listp xs) (natp start) (<= start (len xs)))
  (equal (len (nthcdr start xs)) (- (len xs) start)))
 :hints (("Goal" :induct (nthcdr start xs) :in-theory (enable nthcdr len true-listp)))))

(local (defthm fn-psc-block-optional-strip-offset
 (implies (and (true-listp prefix) (true-listp xs) (natp start) (<= start (len xs)))
  (let ((end (if (equal (fn-inj-strip prefix (nthcdr start xs)) :no)
                 start (+ start (len prefix)))))
   (and (natp end) (<= end (len xs))
        (equal (nthcdr end xs) (fn-inj-strip-optional prefix (nthcdr start xs))))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-block-strip-success-bound (xs (nthcdr start xs)))
        (:instance fn-psc-strip-success-is-exact-drop (xs (nthcdr start xs)))
        (:instance fn-psc-nthcdr-composes-offsets (a start) (b (len prefix))))
  :in-theory (e/d (fn-inj-strip-optional) (fn-inj-strip nthcdr len fn-pbb-strip-at-is-inj-strip fn-pbb-strip-optional-at-is-inj-strip-optional
 fn-psc-block-strip-success-bound fn-psc-strip-success-is-exact-drop fn-psc-nthcdr-composes-offsets))))))

(local (defthm fn-psc-block-record-octets-proper
 (true-listp (fn-record-string-octets-aux chars))
 :hints (("Goal" :induct (fn-record-string-octets-aux chars)
  :in-theory (enable fn-record-string-octets-aux)))))

(local (defthm fn-psc-block-inj-append-proper
 (implies (true-listp ys) (true-listp (fn-inj-append xs ys)))
 :hints (("Goal" :induct (len xs) :in-theory (enable fn-inj-append len)))))

(local (defthm fn-psc-block-msgid-line-proper
 (true-listp (fn-inj-message-id-line (fn-record-string-octets msgid)))
 :hints (("Goal" :in-theory (enable fn-inj-message-id-line fn-record-string-octets)))))

(local (defthm fn-psc-block-reference-from-indices
 (implies (and (true-listp incoming) (natp start) (<= start (len incoming))
               (stringp msgid))
  (let* ((n (len incoming))
         (p1 (if (fn-pb-opensp *fn-inj-injection-date-field* (nthcdr start incoming))
                 (min (+ start 49) n) start))
         (idline (fn-inj-message-id-line (fn-record-string-octets msgid)))
         (p2 (if (equal (fn-inj-strip idline (nthcdr p1 incoming)) :no)
                 p1 (+ p1 (len idline))))
         (p3 (if (fn-pb-opensp *fn-inj-date-field* (nthcdr p2 incoming))
                 (min (+ p2 39) n) p2)))
   (and (natp p1) (<= p1 n) (natp p2) (<= p2 n) (natp p3) (<= p3 n)
        (equal (fn-pb-block-agent (nthcdr start incoming) (fn-record-string-octets msgid))
               (fn-pb-info-line-agent (nthcdr p3 incoming))))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-block-clamped-drop (xs incoming) (count 49))
        (:instance fn-psc-block-optional-strip-offset (xs incoming)
         (start (if (fn-pb-opensp *fn-inj-injection-date-field* (nthcdr start incoming))
                    (min (+ start 49) (len incoming)) start))
         (prefix (fn-inj-message-id-line (fn-record-string-octets msgid)))))
  :in-theory (e/d (fn-pb-block-agent min)
   (fn-pb-info-line-agent fn-pb-opensp fn-inj-strip fn-inj-strip-optional
    fn-inj-drop nthcdr len fn-psc-block-clamped-drop fn-psc-block-optional-strip-offset
    fn-pbb-strip-at-is-inj-strip fn-pbb-strip-optional-at-is-inj-strip-optional))))))

(defun fn-psc-model-block-literal-complete (pos bytes resume c incoming)
 (declare (xargs :guard t :verify-guards nil))
 (fn-psc-model-comparison-complete (fn-psc-literal pos bytes resume c) incoming nil))

(local (defthm fn-psc-block-literal-complete-frame
 (implies (and (natp pos) (true-listp bytes) (equal (fn-psc-get mode c) :agent)
               (true-listp incoming) (equal (fn-psc-get n c) (len incoming)))
  (let ((d (fn-psc-model-block-literal-complete pos bytes resume c incoming)))
   (and (equal (fn-psc-get phase d) :control) (equal (fn-psc-get resume d) resume)
        (equal (fn-psc-get base d) pos)
        (equal (if (fn-psc-get ok d) t nil)
               (not (equal (fn-inj-strip bytes (nthcdr pos incoming)) :no)))
        (implies (fn-psc-get ok d) (equal (fn-psc-get pos d) (+ pos (len bytes))))
        (equal (fn-psc-get n d) (fn-psc-get n c)) (equal (fn-psc-get mode d) :agent)
        (equal (fn-psc-get msgid d) (fn-psc-get msgid c))
        (equal (fn-psc-get skip d) (fn-psc-get skip c)))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-complete-returns-control
         (c (fn-psc-literal pos bytes resume c)) (held nil))
        (:instance fn-psc-comparison-complete-exact-flag
         (c (fn-psc-literal pos bytes resume c)) (held nil))
        (:instance fn-psc-comparison-complete-exact-position
         (c (fn-psc-literal pos bytes resume c)) (held nil))
        (:instance fn-psc-literal-comparison-is-actual-strip (held nil)))
  :in-theory (e/d (fn-psc-model-block-literal-complete fn-psc-literal fn-psc-compare
                   fn-psc-comparison-statep fn-psc-comparison-positionp fn-psc-model-source nfix)
   (fn-psc-model-comparison-complete fn-psc-comparison-complete-returns-control
    fn-psc-comparison-complete-exact-flag fn-psc-comparison-complete-exact-position
    fn-psc-literal-comparison-is-actual-strip fn-inj-strip nth nthcdr len update-nth))))))

(defun fn-psc-block-statep (c incoming)
 (declare (xargs :guard t :verify-guards nil))
 (and (equal (fn-psc-get mode c) :agent) (true-listp incoming)
      (equal (fn-psc-get n c) (len incoming)) (stringp (fn-psc-get msgid c))
      (natp (fn-psc-get skip c)) (<= (fn-psc-get skip c) (len incoming))))

(defun fn-psc-model-block-stamp (c incoming)
 (declare (xargs :guard t :verify-guards nil))
 (fn-psc-model-block-literal-complete (fn-psc-get skip c) *fn-inj-injection-date-field* :agent-stamp c incoming))

(defun fn-psc-model-block-msgid (c incoming)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((d (fn-psc-model-block-stamp c incoming))
        (p (if (fn-psc-get ok d) (min (+ (fn-psc-get skip d) 49) (fn-psc-get n d)) (fn-psc-get skip d))))
  (fn-psc-model-msgid-complete p :agent-msgid d incoming nil)))

(defun fn-psc-model-block-date (c incoming)
 (declare (xargs :guard t :verify-guards nil))
 (let ((d (fn-psc-model-block-msgid c incoming)))
  (fn-psc-model-block-literal-complete (if (fn-psc-get ok d) (fn-psc-get pos d) (fn-psc-get k d))
                                      *fn-inj-date-field* :agent-date d incoming)))

(defun fn-psc-model-block-info (c incoming)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((d (fn-psc-model-block-date c incoming))
        (p (if (fn-psc-get ok d) (min (+ (fn-psc-get base d) 39) (fn-psc-get n d)) (fn-psc-get base d))))
  (fn-psc-model-block-literal-complete p *fn-inj-injection-info-field* :agent-info-field d incoming)))

(defun fn-psc-model-block-agent-complete (c incoming)
 (declare (xargs :guard t :verify-guards nil))
 (let ((d (fn-psc-model-block-info c incoming)))
  (if (fn-psc-get ok d) (fn-psc-model-info-agent-complete d incoming) (fn-psc-step d nil))))

(local (defthm fn-psc-block-stamp-frame
 (implies (fn-psc-block-statep c incoming)
  (let* ((d (fn-psc-model-block-stamp c incoming)) (s (fn-psc-get skip c))
         (p (if (fn-pb-opensp *fn-inj-injection-date-field* (nthcdr s incoming))
                (min (+ s 49) (len incoming)) s)))
   (and (equal (fn-psc-get phase d) :control) (equal (fn-psc-get resume d) :agent-stamp)
        (equal (if (fn-psc-get ok d) t nil)
               (fn-pb-opensp *fn-inj-injection-date-field* (nthcdr s incoming)))
        (equal (fn-psc-get n d) (len incoming)) (equal (fn-psc-get mode d) :agent)
        (equal (fn-psc-get msgid d) (fn-psc-get msgid c))
        (equal (fn-psc-get skip d) s) (natp p) (<= p (len incoming))
        (equal (fn-psc-step d nil) (fn-psc-msgid-compare p :agent-msgid d)))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-block-literal-complete-frame
         (pos (fn-psc-get skip c)) (bytes *fn-inj-injection-date-field*) (resume :agent-stamp)))
  :in-theory (e/d (fn-psc-block-statep fn-psc-model-block-stamp fn-psc-step fn-psc-control min nfix fn-pb-opensp)
   (fn-psc-model-block-literal-complete fn-psc-block-literal-complete-frame fn-psc-msgid-compare
    fn-inj-strip nth nthcdr len update-nth))))))

(local (defthm fn-psc-block-record-octets-length
 (equal (len (fn-record-string-octets-aux chars)) (len chars))
 :hints (("Goal" :induct (fn-record-string-octets-aux chars) :in-theory (enable fn-record-string-octets-aux len)))))

(local (defthm fn-psc-block-inj-append-length
 (equal (len (fn-inj-append xs ys)) (+ (len xs) (len ys)))
 :hints (("Goal" :induct (len xs) :in-theory (enable fn-inj-append len)))))

(local (defthm fn-psc-block-msgid-line-length
 (implies (stringp msgid)
  (equal (len (fn-inj-message-id-line (fn-record-string-octets msgid))) (+ 14 (length msgid))))
 :hints (("Goal" :in-theory (enable fn-inj-message-id-line fn-record-string-octets length)))))

(local (defthm fn-psc-block-msgid-control-unfolds
 (implies (and (equal (fn-psc-get phase c) :control)
               (equal (fn-psc-get resume c) :agent-msgid)
               (if (fn-psc-get ok c) (natp (fn-psc-get pos c)) (natp (fn-psc-get k c))))
  (equal (fn-psc-step c byte)
         (fn-psc-literal (if (fn-psc-get ok c) (fn-psc-get pos c) (fn-psc-get k c))
                         *fn-inj-date-field* :agent-date c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-control nfix)
                                (fn-psc-literal nth len update-nth))))))

(local (defthm fn-psc-block-msgid-frame-minimal
 (implies (fn-psc-block-statep c incoming)
  (let* ((s (fn-psc-get skip c)) (text (fn-psc-get msgid c))
         (p1 (if (fn-pb-opensp *fn-inj-injection-date-field* (nthcdr s incoming))
                 (min (+ s 49) (len incoming)) s))
         (idline (fn-inj-message-id-line (fn-record-string-octets text)))
         (ok (not (equal (fn-inj-strip idline (nthcdr p1 incoming)) :no)))
         (p2 (if ok (+ p1 (len idline)) p1))
         (d (fn-psc-model-block-msgid c incoming)))
   (and (equal (fn-psc-get phase d) :control) (equal (fn-psc-get resume d) :agent-msgid)
        (equal (if (fn-psc-get ok d) t nil) ok)
        (equal (if (fn-psc-get ok d) (fn-psc-get pos d) (fn-psc-get k d)) p2)
        (equal (fn-psc-get n d) (len incoming)) (equal (fn-psc-get mode d) :agent)
        (equal (fn-psc-get msgid d) text) (natp p2) (<= p2 (len incoming))
        (equal (fn-psc-step d nil) (fn-psc-literal p2 *fn-inj-date-field* :agent-date d)))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-block-stamp-frame
        (:instance fn-psc-msgid-complete-is-current-message-id-strip
         (pos (if (fn-psc-get ok (fn-psc-model-block-stamp c incoming))
                  (min (+ (fn-psc-get skip (fn-psc-model-block-stamp c incoming)) 49)
                       (fn-psc-get n (fn-psc-model-block-stamp c incoming)))
                  (fn-psc-get skip (fn-psc-model-block-stamp c incoming))))
         (resume :agent-msgid) (c (fn-psc-model-block-stamp c incoming)) (held nil))
        (:instance fn-psc-block-optional-strip-offset (xs incoming)
         (start (if (fn-pb-opensp *fn-inj-injection-date-field* (nthcdr (fn-psc-get skip c) incoming))
                    (min (+ (fn-psc-get skip c) 49) (len incoming)) (fn-psc-get skip c)))
         (prefix (fn-inj-message-id-line (fn-record-string-octets (fn-psc-get msgid c))))))
  :in-theory (e/d (fn-psc-block-statep fn-psc-model-block-msgid fn-psc-model-source
                   nfix)
   (fn-psc-step fn-psc-control fn-psc-model-block-stamp fn-psc-model-msgid-complete fn-psc-literal fn-psc-block-stamp-frame
    fn-psc-msgid-complete-is-current-message-id-strip fn-psc-block-optional-strip-offset
    fn-pb-opensp fn-inj-strip fn-pbb-strip-at-is-inj-strip
    fn-pbb-strip-optional-at-is-inj-strip-optional fn-record-string-octets length min nth nthcdr len update-nth))))))

(local (defthm fn-psc-block-date-control-unfolds
 (implies (and (equal (fn-psc-get phase c) :control)
               (equal (fn-psc-get resume c) :agent-date)
               (natp (fn-psc-get base c)) (natp (fn-psc-get n c)))
  (equal (fn-psc-step c byte)
   (fn-psc-literal (if (fn-psc-get ok c) (min (+ (fn-psc-get base c) 39) (fn-psc-get n c)) (fn-psc-get base c))
                   *fn-inj-injection-info-field* :agent-info-field c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-control nfix) (fn-psc-literal nth len update-nth))))))

(local (defthm fn-psc-block-date-frame
 (implies (fn-psc-block-statep c incoming)
  (let* ((s (fn-psc-get skip c)) (text (fn-psc-get msgid c))
         (p1 (if (fn-pb-opensp *fn-inj-injection-date-field* (nthcdr s incoming)) (min (+ s 49) (len incoming)) s))
         (idline (fn-inj-message-id-line (fn-record-string-octets text)))
         (p2 (if (equal (fn-inj-strip idline (nthcdr p1 incoming)) :no) p1 (+ p1 (len idline))))
         (ok (fn-pb-opensp *fn-inj-date-field* (nthcdr p2 incoming)))
         (p3 (if ok (min (+ p2 39) (len incoming)) p2))
         (d (fn-psc-model-block-date c incoming)))
   (and (equal (fn-psc-get phase d) :control) (equal (fn-psc-get resume d) :agent-date)
        (equal (fn-psc-get base d) p2) (equal (if (fn-psc-get ok d) t nil) ok)
        (equal (fn-psc-get n d) (len incoming)) (equal (fn-psc-get mode d) :agent)
        (equal (fn-psc-get msgid d) text) (natp p3) (<= p3 (len incoming))
        (equal (fn-psc-step d nil) (fn-psc-literal p3 *fn-inj-injection-info-field* :agent-info-field d)))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-block-msgid-frame-minimal
        (:instance fn-psc-block-literal-complete-frame
         (pos (if (fn-psc-get ok (fn-psc-model-block-msgid c incoming))
                  (fn-psc-get pos (fn-psc-model-block-msgid c incoming))
                  (fn-psc-get k (fn-psc-model-block-msgid c incoming))))
         (bytes *fn-inj-date-field*) (resume :agent-date)
         (c (fn-psc-model-block-msgid c incoming))))
  :in-theory (e/d (fn-psc-block-statep fn-psc-model-block-date fn-pb-opensp min nfix)
   (fn-psc-step fn-psc-control fn-psc-model-block-msgid fn-psc-model-block-literal-complete
    fn-psc-literal  fn-psc-block-msgid-frame-minimal
    fn-psc-block-literal-complete-frame fn-inj-strip fn-pbb-strip-at-is-inj-strip
    fn-record-string-octets length nth nthcdr len update-nth))))))

(local (defthm fn-psc-block-info-frame
 (implies (fn-psc-block-statep c incoming)
  (let* ((before (fn-psc-model-block-date c incoming))
         (p (if (fn-psc-get ok before) (min (+ (fn-psc-get base before) 39) (len incoming)) (fn-psc-get base before)))
         (d (fn-psc-model-block-info c incoming)))
   (and (equal (fn-psc-get phase d) :control) (equal (fn-psc-get resume d) :agent-info-field)
        (equal (fn-psc-get base d) p)
        (equal (if (fn-psc-get ok d) t nil)
               (not (equal (fn-inj-strip *fn-inj-injection-info-field* (nthcdr p incoming)) :no)))
        (equal (fn-psc-get n d) (len incoming)) (equal (fn-psc-get mode d) :agent)
        (implies (fn-psc-get ok d) (fn-psc-info-agent-statep d incoming)))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-block-date-frame
        (:instance fn-psc-block-literal-complete-frame
         (pos (if (fn-psc-get ok (fn-psc-model-block-date c incoming))
                  (min (+ (fn-psc-get base (fn-psc-model-block-date c incoming)) 39)
                       (fn-psc-get n (fn-psc-model-block-date c incoming)))
                  (fn-psc-get base (fn-psc-model-block-date c incoming))))
         (bytes *fn-inj-injection-info-field*) (resume :agent-info-field)
         (c (fn-psc-model-block-date c incoming)))
        (:instance fn-psc-block-strip-success-bound (prefix *fn-inj-injection-info-field*)
         (xs (nthcdr (if (fn-psc-get ok (fn-psc-model-block-date c incoming))
                        (min (+ (fn-psc-get base (fn-psc-model-block-date c incoming)) 39) (len incoming))
                        (fn-psc-get base (fn-psc-model-block-date c incoming))) incoming))))
  :in-theory (e/d (fn-psc-block-statep fn-psc-model-block-info fn-psc-info-agent-statep)
   (fn-psc-model-block-date fn-psc-model-block-literal-complete fn-psc-block-date-frame
    fn-psc-block-literal-complete-frame fn-psc-block-strip-success-bound
    fn-psc-step fn-psc-control fn-inj-strip fn-pb-opensp fn-record-string-octets length
    fn-pbb-strip-at-is-inj-strip min nth nthcdr len update-nth))))))

(local (defthm fn-psc-strip-field-from-first-line
 (implies (and (true-listp prefix) (not (member-equal 10 prefix)) (true-listp xs))
  (equal (fn-inj-strip prefix (fn-pb-line xs))
   (if (equal (fn-inj-strip prefix xs) :no) :no
     (fn-pb-line (fn-inj-strip prefix xs)))))
 :hints (("Goal" :induct (fn-inj-strip prefix xs)
  :in-theory (enable fn-inj-strip fn-pb-line member-equal true-listp)))))

(local (defthm fn-psc-block-missing-info-is-no-agent
 (implies (and (true-listp xs)
               (equal (fn-inj-strip *fn-inj-injection-info-field* xs) :no))
  (equal (fn-pb-info-line-agent xs) nil))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-strip-field-from-first-line (prefix *fn-inj-injection-info-field*)))
  :in-theory (e/d (fn-pb-info-line-agent fn-pb-params-line-agent)
   (fn-inj-strip fn-pb-line fn-inj-injection-info-line fn-inj-take fn-inj-drop
    fn-psc-strip-field-from-first-line))))))

(local (defthm fn-psc-block-info-base-is-current-block-residual
 (implies (fn-psc-block-statep c incoming)
  (equal (fn-pb-block-agent (nthcdr (fn-psc-get skip c) incoming)
                           (fn-record-string-octets (fn-psc-get msgid c)))
         (fn-pb-info-line-agent
          (nthcdr (fn-psc-get base (fn-psc-model-block-info c incoming)) incoming))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-block-date-frame fn-psc-block-info-frame
        (:instance fn-psc-block-reference-from-indices
         (start (fn-psc-get skip c)) (msgid (fn-psc-get msgid c))))
  :in-theory (e/d (fn-psc-block-statep)
   (fn-psc-model-block-date fn-psc-model-block-info fn-psc-block-date-frame fn-psc-block-info-frame
    fn-psc-block-reference-from-indices fn-pb-block-agent fn-pb-info-line-agent
    fn-inj-strip fn-pb-opensp fn-record-string-octets length nth nthcdr len min
    fn-pbb-strip-at-is-inj-strip fn-pbb-strip-optional-at-is-inj-strip-optional))))))

(local (defthm fn-psc-block-info-failure-result
 (implies (and (equal (fn-psc-get phase c) :control)
               (equal (fn-psc-get resume c) :agent-info-field) (not (fn-psc-get ok c)))
  (and (equal (fn-psc-get phase (fn-psc-step c byte)) :done)
       (equal (fn-psc-result (fn-psc-step c byte)) :no-source)))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-control fn-psc-finish fn-psc-result)
                                (nth update-nth len))))))

(defthm fn-psc-block-agent-result-is-current-block-agent
 (implies (fn-psc-block-statep c incoming)
  (let* ((info (fn-psc-model-block-info c incoming)) (a (fn-psc-get pos info))
         (line (fn-pb-line (nthcdr a incoming))) (prefix (fn-pb-upto-semicolon line))
         (end (+ a (if (equal prefix :no) (- (len line) 2) (len prefix))))
         (agent (fn-pb-block-agent (nthcdr (fn-psc-get skip c) incoming)
                                   (fn-record-string-octets (fn-psc-get msgid c))))
         (d (fn-psc-model-block-agent-complete c incoming)))
   (and (equal (fn-psc-result d) (if agent (list :agent a end) :no-source))
        (implies agent (equal (fn-inj-take (- end a) (nthcdr a incoming)) agent)))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-block-info-frame fn-psc-block-info-base-is-current-block-residual
        (:instance fn-psc-info-agent-result-is-current-info-agent (c (fn-psc-model-block-info c incoming)))
        (:instance fn-psc-block-missing-info-is-no-agent
         (xs (nthcdr (fn-psc-get base (fn-psc-model-block-info c incoming)) incoming))))
  :in-theory (e/d (fn-psc-block-statep fn-psc-model-block-agent-complete
                    )
   (fn-psc-step fn-psc-control fn-psc-finish fn-psc-result
    fn-psc-model-block-stamp fn-psc-model-block-msgid fn-psc-model-block-date
    fn-psc-model-block-literal-complete fn-psc-block-reference-from-indices
    fn-psc-info-agent-complete-is-actual-paid-steps
    fn-psc-model-block-info fn-psc-model-info-agent-complete
    fn-psc-info-agent-result-is-current-info-agent fn-psc-info-agent-statep
    fn-psc-block-info-frame fn-psc-block-info-base-is-current-block-residual
    fn-psc-block-missing-info-is-no-agent fn-pb-block-agent fn-pb-info-line-agent
    fn-pb-line fn-inj-strip fn-pb-upto-semicolon fn-inj-take nth nthcdr len update-nth
    fn-record-string-octets fn-pbb-strip-at-is-inj-strip)))))

(local (defthm fn-psc-block-literal-preserves-layout
 (implies (equal (len c) 24) (equal (len (fn-psc-literal pos bytes resume c)) 24))
 :hints (("Goal" :in-theory (e/d (fn-psc-literal fn-psc-compare) (nth update-nth nfix len))))))

(local (defthm fn-psc-block-literal-preserves-proper-state
 (implies (true-listp c) (true-listp (fn-psc-literal pos bytes resume c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-literal fn-psc-compare) (nth update-nth nfix len))))))

(local (defthm fn-psc-block-literal-complete-state-shape
 (and (implies (equal (len c) 24)
               (equal (len (fn-psc-model-block-literal-complete pos bytes resume c incoming)) 24))
      (implies (true-listp c)
               (true-listp (fn-psc-model-block-literal-complete pos bytes resume c incoming))))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-block-literal-complete)
    (fn-psc-literal fn-psc-model-comparison-complete nth nfix len update-nth))))))

(local (defthm fn-psc-byte-run-addition
 (implies (and (natp a) (natp b))
  (equal (fn-psc-model-byte-run (+ a b) c incoming held)
         (fn-psc-model-byte-run b (fn-psc-model-byte-run a c incoming held) incoming held)))
 :hints (("Goal" :induct (fn-psc-model-byte-run a c incoming held)
          :in-theory (e/d (fn-psc-model-byte-run)
                         (nth nfix len fn-psc-step fn-psc-model-demanded-byte))))))

(local (defthm fn-psc-block-next-literal-is-paid-trace
 (implies (and (equal (fn-psc-get phase c) :control)
               (equal (fn-psc-step c nil) (fn-psc-literal pos bytes resume c)))
  (equal (fn-psc-model-block-literal-complete pos bytes resume c incoming)
         (fn-psc-model-byte-run
          (+ 1 (fn-psc-model-comparison-cost (fn-psc-literal pos bytes resume c) incoming nil)) c incoming nil)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-complete-is-actual-steps
         (c (fn-psc-literal pos bytes resume c)) (held nil))
        (:instance fn-psc-byte-run-addition (a 1)
         (b (fn-psc-model-comparison-cost (fn-psc-literal pos bytes resume c) incoming nil)) (held nil)))
  :expand ((fn-psc-model-byte-run 1 c incoming nil)
           (:free (c) (fn-psc-model-byte-run 0 c incoming nil)))
  :in-theory (e/d (fn-psc-model-block-literal-complete fn-psc-demand fn-psc-model-demanded-byte)
   (fn-psc-step fn-psc-literal fn-psc-model-byte-run fn-psc-model-comparison-cost
    fn-psc-model-comparison-complete fn-psc-comparison-complete-is-actual-steps
    fn-psc-byte-run-addition))))))

(local (defthm fn-psc-block-next-msgid-is-paid-trace
 (implies (and (equal (fn-psc-get phase c) :control)
               (equal (fn-psc-step c nil) (fn-psc-msgid-compare pos resume c))
               (true-listp c) (equal (len c) 24) (natp pos) (stringp (fn-psc-get msgid c))
               (true-listp incoming) (equal (fn-psc-get mode c) :agent)
               (equal (fn-psc-get n c) (len incoming)))
  (equal (fn-psc-model-msgid-complete pos resume c incoming nil)
         (fn-psc-model-byte-run (+ 1 (fn-psc-model-msgid-cost pos resume c incoming nil)) c incoming nil)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-msgid-complete-is-actual-paid-steps (held nil))
        (:instance fn-psc-byte-run-addition (a 1)
         (b (fn-psc-model-msgid-cost pos resume c incoming nil)) (held nil)))
  :expand ((fn-psc-model-byte-run 1 c incoming nil)
           (:free (c) (fn-psc-model-byte-run 0 c incoming nil)))
  :in-theory (e/d (fn-psc-demand fn-psc-model-demanded-byte fn-psc-model-source)
   (fn-psc-step fn-psc-msgid-compare fn-psc-model-byte-run fn-psc-model-msgid-cost
    fn-psc-model-msgid-complete fn-psc-msgid-complete-is-actual-paid-steps fn-psc-byte-run-addition
    nth len nfix))))))

(defun fn-psc-model-block-stamp-cost (c incoming)
 (declare (xargs :guard t :verify-guards nil))
 (fn-psc-model-comparison-cost (fn-psc-literal (fn-psc-get skip c) *fn-inj-injection-date-field* :agent-stamp c) incoming nil))

(defun fn-psc-model-block-msgid-cost (c incoming)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((d (fn-psc-model-block-stamp c incoming))
        (p (if (fn-psc-get ok d) (min (+ (fn-psc-get skip d) 49) (fn-psc-get n d)) (fn-psc-get skip d))))
  (+ 1 (fn-psc-model-msgid-cost p :agent-msgid d incoming nil))))

(defun fn-psc-model-block-date-cost (c incoming)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((d (fn-psc-model-block-msgid c incoming))
        (p (if (fn-psc-get ok d) (fn-psc-get pos d) (fn-psc-get k d))))
  (+ 1 (fn-psc-model-comparison-cost (fn-psc-literal p *fn-inj-date-field* :agent-date d) incoming nil))))

(defun fn-psc-model-block-info-cost (c incoming)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((d (fn-psc-model-block-date c incoming))
        (p (if (fn-psc-get ok d) (min (+ (fn-psc-get base d) 39) (fn-psc-get n d)) (fn-psc-get base d))))
  (+ 1 (fn-psc-model-comparison-cost (fn-psc-literal p *fn-inj-injection-info-field* :agent-info-field d) incoming nil))))

(defun fn-psc-model-block-finish-cost (c incoming)
 (declare (xargs :guard t :verify-guards nil))
 (let ((d (fn-psc-model-block-info c incoming)))
  (if (fn-psc-get ok d) (fn-psc-model-info-agent-cost d incoming) 1)))

(defun fn-psc-model-block-agent-cost (c incoming)
 (declare (xargs :guard t :verify-guards nil))
 (+ (fn-psc-model-block-stamp-cost c incoming) (fn-psc-model-block-msgid-cost c incoming)
    (fn-psc-model-block-date-cost c incoming) (fn-psc-model-block-info-cost c incoming)
    (fn-psc-model-block-finish-cost c incoming)))

(local (defthm fn-psc-block-stamp-is-paid-trace
 (equal (fn-psc-model-block-stamp c incoming)
        (fn-psc-model-byte-run (fn-psc-model-block-stamp-cost c incoming)
         (fn-psc-literal (fn-psc-get skip c) *fn-inj-injection-date-field* :agent-stamp c) incoming nil))
 :hints (("Goal" :use ((:instance fn-psc-comparison-complete-is-actual-steps
  (c (fn-psc-literal (fn-psc-get skip c) *fn-inj-injection-date-field* :agent-stamp c)) (held nil)))
  :in-theory (e/d (fn-psc-model-block-stamp fn-psc-model-block-stamp-cost fn-psc-model-block-literal-complete)
   (fn-psc-model-comparison-complete fn-psc-model-comparison-cost fn-psc-literal fn-psc-model-byte-run
    fn-psc-comparison-complete-is-actual-steps))))))

(local (defthm fn-psc-block-msgid-is-paid-trace
 (implies (and (fn-psc-block-statep c incoming) (true-listp c) (equal (len c) 24))
  (equal (fn-psc-model-block-msgid c incoming)
   (fn-psc-model-byte-run (fn-psc-model-block-msgid-cost c incoming) (fn-psc-model-block-stamp c incoming) incoming nil)))
 :hints (("Goal" :do-not-induct t :use (fn-psc-block-stamp-frame
  (:instance fn-psc-block-next-msgid-is-paid-trace
   (c (fn-psc-model-block-stamp c incoming)) (resume :agent-msgid)
   (pos (if (fn-psc-get ok (fn-psc-model-block-stamp c incoming))
            (min (+ (fn-psc-get skip (fn-psc-model-block-stamp c incoming)) 49) (fn-psc-get n (fn-psc-model-block-stamp c incoming)))
            (fn-psc-get skip (fn-psc-model-block-stamp c incoming))))))
  :in-theory (e/d (fn-psc-block-statep fn-psc-model-block-msgid fn-psc-model-block-msgid-cost fn-psc-model-block-stamp)
   (fn-psc-model-block-literal-complete fn-psc-block-stamp-frame fn-psc-model-msgid-complete
    fn-psc-model-msgid-cost fn-psc-model-byte-run fn-psc-msgid-compare fn-psc-step
    fn-psc-block-next-msgid-is-paid-trace nth len min nfix))))))

(local (defthm fn-psc-block-date-is-paid-trace
 (implies (fn-psc-block-statep c incoming)
  (equal (fn-psc-model-block-date c incoming)
   (fn-psc-model-byte-run (fn-psc-model-block-date-cost c incoming) (fn-psc-model-block-msgid c incoming) incoming nil)))
 :hints (("Goal" :do-not-induct t :use (fn-psc-block-msgid-frame-minimal
  (:instance fn-psc-block-next-literal-is-paid-trace
   (c (fn-psc-model-block-msgid c incoming)) (resume :agent-date) (bytes *fn-inj-date-field*)
   (pos (if (fn-psc-get ok (fn-psc-model-block-msgid c incoming)) (fn-psc-get pos (fn-psc-model-block-msgid c incoming))
            (fn-psc-get k (fn-psc-model-block-msgid c incoming))))))
  :in-theory (e/d (fn-psc-model-block-date fn-psc-model-block-date-cost)
   (fn-psc-model-block-msgid fn-psc-model-block-literal-complete fn-psc-block-msgid-frame-minimal 
    fn-psc-model-byte-run fn-psc-model-comparison-cost fn-psc-literal fn-psc-step fn-psc-block-next-literal-is-paid-trace nth len))))))

(local (defthm fn-psc-block-info-is-paid-trace-minimal
 (implies (fn-psc-block-statep c incoming)
  (equal (fn-psc-model-block-info c incoming)
   (fn-psc-model-byte-run (fn-psc-model-block-info-cost c incoming) (fn-psc-model-block-date c incoming) incoming nil)))
 :hints (("Goal" :do-not-induct t :use (fn-psc-block-date-frame
  (:instance fn-psc-block-next-literal-is-paid-trace
   (c (fn-psc-model-block-date c incoming)) (resume :agent-info-field) (bytes *fn-inj-injection-info-field*)
   (pos (if (fn-psc-get ok (fn-psc-model-block-date c incoming))
            (min (+ (fn-psc-get base (fn-psc-model-block-date c incoming)) 39) (fn-psc-get n (fn-psc-model-block-date c incoming)))
            (fn-psc-get base (fn-psc-model-block-date c incoming))))))
  :in-theory (e/d (fn-psc-model-block-info fn-psc-model-block-info-cost)
   (fn-psc-block-stamp-is-paid-trace fn-psc-block-msgid-is-paid-trace fn-psc-block-date-is-paid-trace 
    fn-psc-model-block-stamp fn-psc-model-block-msgid fn-psc-model-block-stamp-cost fn-psc-model-block-msgid-cost fn-psc-model-block-date-cost
    fn-psc-model-block-date fn-psc-model-block-literal-complete fn-psc-block-date-frame
    fn-psc-model-byte-run fn-psc-model-comparison-cost fn-psc-literal fn-psc-step fn-psc-block-next-literal-is-paid-trace nth len))))))

(local (defthm fn-psc-block-finish-is-paid-trace
 (implies (fn-psc-block-statep c incoming)
  (equal (fn-psc-model-block-agent-complete c incoming)
   (fn-psc-model-byte-run (fn-psc-model-block-finish-cost c incoming) (fn-psc-model-block-info c incoming) incoming nil)))
 :hints (("Goal" :do-not-induct t :use (fn-psc-block-info-frame
  (:instance fn-psc-info-agent-complete-is-actual-paid-steps (c (fn-psc-model-block-info c incoming))))
  :expand ((:free (c) (fn-psc-model-byte-run 1 c incoming nil)) (:free (c) (fn-psc-model-byte-run 0 c incoming nil)))
  :in-theory (e/d (fn-psc-model-block-agent-complete fn-psc-model-block-finish-cost fn-psc-demand fn-psc-model-demanded-byte)
   (fn-psc-block-stamp-is-paid-trace fn-psc-block-msgid-is-paid-trace fn-psc-block-date-is-paid-trace 
    fn-psc-model-block-stamp fn-psc-model-block-msgid fn-psc-model-block-date fn-psc-model-block-literal-complete
    fn-psc-model-block-stamp-cost fn-psc-model-block-msgid-cost fn-psc-model-block-date-cost fn-psc-model-block-info-cost
    fn-psc-step fn-psc-model-block-info fn-psc-info-agent-statep fn-psc-model-info-agent-complete fn-psc-model-info-agent-cost
    fn-psc-info-agent-complete-is-actual-paid-steps fn-psc-model-byte-run fn-psc-block-info-frame nth len))))))

(defthm fn-psc-block-agent-complete-is-actual-paid-steps
 (implies (and (fn-psc-block-statep c incoming) (true-listp c) (equal (len c) 24))
  (equal (fn-psc-model-block-agent-complete c incoming)
   (fn-psc-model-byte-run (fn-psc-model-block-agent-cost c incoming)
    (fn-psc-literal (fn-psc-get skip c) *fn-inj-injection-date-field* :agent-stamp c) incoming nil)))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-block-stamp-is-paid-trace fn-psc-block-msgid-is-paid-trace
        fn-psc-block-date-is-paid-trace fn-psc-block-info-is-paid-trace-minimal fn-psc-block-finish-is-paid-trace
        (:instance fn-psc-byte-run-addition (held nil)
         (c (fn-psc-literal (fn-psc-get skip c) *fn-inj-injection-date-field* :agent-stamp c))
         (a (fn-psc-model-block-stamp-cost c incoming))
         (b (+ (fn-psc-model-block-msgid-cost c incoming) (fn-psc-model-block-date-cost c incoming)
               (fn-psc-model-block-info-cost c incoming) (fn-psc-model-block-finish-cost c incoming))))
        (:instance fn-psc-byte-run-addition (held nil) (c (fn-psc-model-block-stamp c incoming))
         (a (fn-psc-model-block-msgid-cost c incoming))
         (b (+ (fn-psc-model-block-date-cost c incoming) (fn-psc-model-block-info-cost c incoming)
               (fn-psc-model-block-finish-cost c incoming))))
        (:instance fn-psc-byte-run-addition (held nil) (c (fn-psc-model-block-msgid c incoming))
         (a (fn-psc-model-block-date-cost c incoming))
         (b (+ (fn-psc-model-block-info-cost c incoming) (fn-psc-model-block-finish-cost c incoming))))
        (:instance fn-psc-byte-run-addition (held nil) (c (fn-psc-model-block-date c incoming))
         (a (fn-psc-model-block-info-cost c incoming)) (b (fn-psc-model-block-finish-cost c incoming))))
  :in-theory (e/d (fn-psc-model-block-agent-cost)
   (fn-psc-model-block-stamp fn-psc-model-block-msgid fn-psc-model-block-date fn-psc-model-block-info
    fn-psc-model-block-agent-complete fn-psc-model-block-literal-complete fn-psc-model-block-stamp-cost
    fn-psc-model-block-msgid-cost fn-psc-model-block-date-cost fn-psc-model-block-info-cost fn-psc-model-block-finish-cost
    fn-psc-model-byte-run fn-psc-literal fn-psc-step fn-psc-byte-run-addition
    fn-psc-block-stamp-is-paid-trace fn-psc-block-msgid-is-paid-trace fn-psc-block-date-is-paid-trace
     fn-psc-block-info-is-paid-trace-minimal fn-psc-block-finish-is-paid-trace
    nth len nfix update-nth)))))

(defthm fn-psc-block-agent-result-is-bounded
 (implies (fn-psc-block-statep c incoming)
  (fn-psc-agent-resultp (fn-psc-result (fn-psc-model-block-agent-complete c incoming)) (len incoming)))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-block-info-frame
        (:instance fn-psc-info-agent-result-is-bounded (c (fn-psc-model-block-info c incoming)))
        (:instance fn-psc-block-info-failure-result (c (fn-psc-model-block-info c incoming)) (byte nil)))
  :in-theory (e/d (fn-psc-model-block-agent-complete)
   (fn-psc-info-agent-complete-result fn-psc-block-date-frame fn-psc-block-msgid-frame-minimal fn-psc-block-stamp-frame fn-psc-block-next-literal-is-paid-trace fn-psc-block-next-msgid-is-paid-trace fn-psc-block-stamp-is-paid-trace fn-psc-block-msgid-is-paid-trace fn-psc-block-date-is-paid-trace fn-psc-block-info-is-paid-trace-minimal fn-psc-block-finish-is-paid-trace fn-psc-block-agent-complete-is-actual-paid-steps fn-psc-model-block-stamp fn-psc-model-block-msgid fn-psc-model-block-date fn-psc-model-block-literal-complete fn-psc-agent-resultp fn-psc-result fn-psc-done-result-is-stored fn-psc-step fn-psc-model-block-info
    fn-psc-model-info-agent-complete fn-psc-block-agent-complete-is-actual-paid-steps
    fn-psc-info-agent-complete-is-actual-paid-steps fn-psc-block-agent-result-is-current-block-agent
    fn-psc-info-agent-result-is-current-info-agent fn-psc-block-info-frame fn-psc-info-agent-result-is-bounded
    fn-psc-block-info-failure-result nth len)))))

(in-theory (disable fn-psc-block-statep fn-psc-model-block-agent-complete fn-psc-model-block-agent-cost fn-psc-model-block-date fn-psc-model-block-date-cost fn-psc-model-block-finish-cost fn-psc-model-block-info fn-psc-model-block-info-cost fn-psc-model-block-literal-complete fn-psc-model-block-msgid fn-psc-model-block-msgid-cost fn-psc-model-block-stamp fn-psc-model-block-stamp-cost))
