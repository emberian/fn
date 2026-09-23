; Durable boot domain for BP Bundle Age anchors.  A legacy pair
; (age . monotonic) has no epoch: it cannot be compared with a new process or
; boot counter merely because the new counter is numerically larger.  Until a
; durable domain exists, or when the saved domain differs, recovery fences the
; BP lifecycle and retains its obligations.
(in-package "ACL2")
(include-book "bp-fnbs-namespace")
(include-book "frame-trailer")
(include-book "journal-publish")

(defconst *fn-bpcd-kind* 6)
(defconst *fn-bpcd-final-name* "clock-domain.fnb")
(defconst *fn-bpcd-payload-limit* 40)
(defconst *fn-bpcd-boot-width* 36)
(defconst *fn-bpcd-observed-width* 37)

(defun fn-bpcd-final-name ()
  (declare (xargs :guard t))
  *fn-bpcd-final-name*)

(defun fn-bpcd-frame-limit ()
  (declare (xargs :guard t))
  (+ *fn-frame-header-octets* *fn-bpcd-payload-limit*
     *fn-frame-trailer-octets*))

(defun fn-bpcd-hex-octetp (x)
  (declare (xargs :guard t))
  (and (integerp x)
       (or (and (<= 48 x) (<= x 57))
           (and (<= 97 x) (<= x 102)))))

(defun fn-bpcd-boot-chars-okp (xs position)
  (declare (xargs :guard t :measure (acl2-count xs)))
  (if (atom xs)
      (null xs)
    (and (if (member-equal position '(8 13 18 23))
             (equal (car xs) 45)
           (fn-bpcd-hex-octetp (car xs)))
         (fn-bpcd-boot-chars-okp (cdr xs) (+ 1 (nfix position))))))

(defun fn-bpcd-boot-idp (xs)
  (declare (xargs :guard t))
  (and (true-listp xs)
       (equal (len xs) *fn-bpcd-boot-width*)
       (fn-bpcd-boot-chars-okp xs 0)))

(defun fn-bpcd-first (n xs)
  (declare (xargs :guard t :measure (nfix n)))
  (if (and (natp n) (< 0 n) (consp xs))
      (cons (car xs) (fn-bpcd-first (- n 1) (cdr xs)))
    nil))

(defun fn-bpcd-observed-id (observed)
  (declare (xargs :guard t))
  (let ((canonical (fn-bpcd-first *fn-bpcd-boot-width* observed)))
    (if (and (true-listp observed)
             (equal (len observed) *fn-bpcd-observed-width*)
             (equal (nth *fn-bpcd-boot-width* observed) 10)
             (fn-bpcd-boot-idp canonical))
        canonical
      nil)))

(defun fn-bpcd-frame (boot-id)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-bpcd-boot-idp boot-id))
      :bad
    (let* ((payload (fn-frame-fields-octets '(:blob) (list boot-id)))
           (protected (fn-frame-protected
                       *fn-frame-magic-bundle-store* *fn-frame-version*
                       *fn-bpcd-kind* payload)))
      (append protected (fn-frame-trailer protected)))))

(defun fn-bpcd-unframe (octets)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (and (fn-cbor-octet-listp octets)
                (<= (len octets) (fn-bpcd-frame-limit))))
      nil
    (let ((answer (fn-frame-decode
                   octets
                   (fn-frame-trailer (fn-frame-protected-prefix octets))
                   *fn-bpcd-payload-limit*)))
      (if (not (and (fn-frame-result-okp answer)
                    (equal (fn-frame-result-magic answer)
                           *fn-frame-magic-bundle-store*)
                    (equal (fn-frame-result-version answer)
                           *fn-frame-version*)
                    (equal (fn-frame-result-kind answer) *fn-bpcd-kind*)))
          nil
        (let* ((parsed (fn-frame-fields-parse
                        '(:blob) (fn-frame-result-payload answer)))
               (boot-id (fn-frame-item 0 (fn-frame-parse-value parsed))))
          (if (and (fn-frame-parse-okp parsed)
                   (fn-bpcd-boot-idp boot-id))
              boot-id
            nil))))))

(defun fn-bpcd-plan-item (index plan)
  (declare (xargs :guard t))
  (if (and (natp index) (true-listp plan))
      (nth index plan)
    nil))

; A malformed recovery plan is evidence of a conflicted namespace, never a
; reason to initialize a fresh domain marker.  Hidden stages and all final
; rows from the ACL2 mixed planner count as durable/ambiguous legacy evidence.
(defun fn-bpnf-clock-domain-legacy-evidence (plan sequence-frontier-present)
  (declare (xargs :guard t :verify-guards nil))
  (or (not (fn-bpnf-mixed-recovery-planp plan))
      sequence-frontier-present
      (consp (fn-bpcd-plan-item 1 plan))
      (consp (fn-bpcd-plan-item 2 plan))
      (consp (fn-bpcd-plan-item 3 plan))))

; The host supplies exact saved frame octets and existence, the raw 37 octets
; from Linux boot_id (including LF), and physical lock/name observations.
; It neither compares domains nor chooses whether to replay old anchors.
(defun fn-bpnf-clock-domain-plan
  (saved present observed legacy-evidence lock-owned final-absent)
  (declare (xargs :guard t :verify-guards nil))
  (let ((boot-id (fn-bpcd-observed-id observed)))
    (cond ((not boot-id) (list :fence :boot-observation))
          (present
           (let ((old (fn-bpcd-unframe saved)))
             (if (not old)
                 (list :fence :domain-frame)
               (if (equal old boot-id)
                   (list :same boot-id)
                 (list :fence :different-boot)))))
          ((not final-absent) (list :fence :name-observation))
          (legacy-evidence (list :fence :legacy-without-domain))
          ((not lock-owned) (list :fence :lock-authority))
          (t (list :initialize (fn-bpcd-frame boot-id)
                   (fn-jpub-initial t))))))

(defun fn-bpnf-clock-domain-plan-status (plan)
  (declare (xargs :guard t))
  (if (consp plan) (car plan) nil))
(defun fn-bpcd-plan-second (plan)
  (declare (xargs :guard t))
  (if (and (consp plan) (consp (cdr plan)))
      (car (cdr plan))
    nil))
(defun fn-bpcd-plan-third (plan)
  (declare (xargs :guard t))
  (if (and (consp plan) (consp (cdr plan)) (consp (cddr plan)))
      (car (cddr plan))
    nil))
(defun fn-bpnf-clock-domain-plan-frame (plan)
  (declare (xargs :guard t))
  (if (equal (fn-bpnf-clock-domain-plan-status plan) :initialize)
      (fn-bpcd-plan-second plan) nil))
(defun fn-bpnf-clock-domain-plan-publication (plan)
  (declare (xargs :guard t))
  (if (equal (fn-bpnf-clock-domain-plan-status plan) :initialize)
      (fn-bpcd-plan-third plan) nil))
(defun fn-bpnf-clock-domain-plan-boot-id (plan)
  (declare (xargs :guard t))
  (if (equal (fn-bpnf-clock-domain-plan-status plan) :same)
      (fn-bpcd-plan-second plan) nil))
(defun fn-bpnf-clock-domain-plan-reason (plan)
  (declare (xargs :guard t))
  (if (equal (fn-bpnf-clock-domain-plan-status plan) :fence)
      (fn-bpcd-plan-second plan) nil))

; The canonical Linux boot ID is a nonempty bounded frame blob.  These shape
; facts discharge the called encoder's guard and its exact read bound.
(defthm fn-bpcd-hex-is-octet
  (implies (fn-bpcd-hex-octetp x) (fn-cbor-octetp x))
  :hints (("Goal" :in-theory (enable fn-bpcd-hex-octetp fn-cbor-octetp))))

(defthm fn-bpcd-boot-chars-are-octets
  (implies (fn-bpcd-boot-chars-okp xs position)
           (fn-cbor-octet-listp xs))
  :rule-classes nil
  :hints (("Goal" :induct (fn-bpcd-boot-chars-okp xs position)
           :in-theory (enable fn-bpcd-boot-chars-okp fn-cbor-octet-listp))))

(defthm fn-bpcd-boot-id-is-octets
  (implies (fn-bpcd-boot-idp xs) (fn-cbor-octet-listp xs))
  :hints (("Goal"
           :use ((:instance fn-bpcd-boot-chars-are-octets (position 0)))
           :in-theory (enable fn-bpcd-boot-idp))))

(defthm fn-bpcd-boot-id-is-frame-blob
  (implies (fn-bpcd-boot-idp xs) (fn-frame-blobp xs))
  :hints (("Goal"
           :use ((:instance fn-cbor-at-mostp-from-length
                            (bound *fn-frame-max-blob*)))
           :in-theory (enable fn-bpcd-boot-idp fn-frame-blobp))))

(defthm fn-bpcd-boot-id-values-okp
  (implies (fn-bpcd-boot-idp boot-id)
           (fn-frame-values-okp '(:blob) (list boot-id)))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-frame-values-okp fn-frame-field-okp))))

(defthm fn-bpcd-payload-length
  (implies (fn-bpcd-boot-idp boot-id)
           (equal (len (fn-frame-fields-octets '(:blob) (list boot-id))) 40))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-frame-fields-octets fn-frame-field-octets
                              fn-frame-u32-bytes-len fn-bpcd-boot-idp))))

(defthm fn-bpcd-payload-octets
  (implies (fn-bpcd-boot-idp boot-id)
           (fn-cbor-octet-listp
            (fn-frame-fields-octets '(:blob) (list boot-id))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-frame-fields-octets-are-octets
                            (specs '(:blob)) (values (list boot-id))))
           :in-theory (enable fn-frame-values-okp fn-frame-field-okp))))

(defthm fn-bpcd-payload-is-input
  (implies (fn-bpcd-boot-idp boot-id)
           (fn-frame-inputp *fn-frame-magic-bundle-store*
                            *fn-frame-version* *fn-bpcd-kind*
                            (fn-frame-fields-octets '(:blob) (list boot-id))
                            *fn-bpcd-payload-limit*))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-frame-inputp fn-frame-magicp))))

(defthm fn-bpcd-protected-octets
  (implies (fn-bpcd-boot-idp boot-id)
           (fn-cbor-octet-listp
            (fn-frame-protected
             *fn-frame-magic-bundle-store* *fn-frame-version*
             *fn-bpcd-kind*
             (fn-frame-fields-octets '(:blob) (list boot-id)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-frame-header-octets
                            (magic *fn-frame-magic-bundle-store*)
                            (version *fn-frame-version*)
                            (kind *fn-bpcd-kind*)
                            (length (len (fn-frame-fields-octets
                                          '(:blob) (list boot-id))))))
           :in-theory (enable fn-frame-protected fn-frame-magicp))))

(defthm fn-bpcd-frame-length
  (implies (fn-bpcd-boot-idp boot-id)
           (equal (len (fn-bpcd-frame boot-id)) (fn-bpcd-frame-limit)))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-bpcd-frame fn-bpcd-frame-limit
                              fn-frame-protected fn-frame-header-octets
                              fn-frame-trailer fn-frame-len-of-append))))

(defthm fn-bpcd-frame-octets
  (implies (fn-bpcd-boot-idp boot-id)
           (fn-cbor-octet-listp (fn-bpcd-frame boot-id)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cbor-octet-listp-append
                            (xs (fn-frame-protected
                                 *fn-frame-magic-bundle-store*
                                 *fn-frame-version* *fn-bpcd-kind*
                                 (fn-frame-fields-octets
                                  '(:blob) (list boot-id))))
                            (ys (fn-frame-trailer
                                 (fn-frame-protected
                                  *fn-frame-magic-bundle-store*
                                  *fn-frame-version* *fn-bpcd-kind*
                                  (fn-frame-fields-octets
                                   '(:blob) (list boot-id)))))))
           :in-theory (enable fn-bpcd-frame fn-frame-trailer))))

; The frame the host publishes is exactly the generic sealed FNBS frame.
(defthm fn-bpcd-frame-is-seal
  (implies (fn-bpcd-boot-idp boot-id)
           (equal (fn-bpcd-frame boot-id)
                  (fn-frame-seal
                   *fn-frame-magic-bundle-store* *fn-frame-version*
                   *fn-bpcd-kind*
                   (fn-frame-fields-octets '(:blob) (list boot-id)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-frame-protected-plus-trailer-is-seal
                            (magic *fn-frame-magic-bundle-store*)
                            (version *fn-frame-version*)
                            (kind *fn-bpcd-kind*)
                            (payload (fn-frame-fields-octets
                                      '(:blob) (list boot-id)))
                            (max-payload *fn-bpcd-payload-limit*)))
           :in-theory (enable fn-bpcd-frame))))

(defthm fn-bpcd-unframe-of-frame
  (implies (fn-bpcd-boot-idp boot-id)
           (equal (fn-bpcd-unframe (fn-bpcd-frame boot-id)) boot-id))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-frame-decode-of-host-framing
                            (magic *fn-frame-magic-bundle-store*)
                            (version *fn-frame-version*)
                            (kind *fn-bpcd-kind*)
                            (payload (fn-frame-fields-octets
                                      '(:blob) (list boot-id)))
                            (max-payload *fn-bpcd-payload-limit*))
                 (:instance fn-frame-fields-parse-of-octets
                            (specs '(:blob)) (values (list boot-id)))
                 (:instance fn-bpcd-frame-octets)
                 (:instance fn-bpcd-frame-length))
           :in-theory (e/d (fn-bpcd-unframe fn-bpcd-frame
                            fn-frame-values-okp fn-frame-field-okp)
                           (fn-frame-decode fn-frame-fields-parse)))))

(verify-guards fn-bpcd-frame)
(verify-guards fn-bpcd-unframe
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-frame-decode-payload-octets
                            (digest (fn-frame-trailer
                                     (fn-frame-protected-prefix octets)))
                            (max-payload 40)))
           :in-theory (disable fn-cbor-octet-listp fn-frame-decode
                               fn-frame-fields-parse))))
(verify-guards fn-bpnf-mixed-recovery-planp)
(verify-guards fn-bpnf-clock-domain-legacy-evidence)
(verify-guards fn-bpnf-clock-domain-plan)

; The actual startup decision is the theorem subject.  :same is possible
; only when the saved canonical bytes decode and agree with this boot's
; observation.  No numerical uptime comparison occurs in this decision.
(defthm fn-bpnf-clock-domain-same-binds-durable-id
  (implies
   (equal (fn-bpnf-clock-domain-plan-status
           (fn-bpnf-clock-domain-plan
            saved present observed legacy-evidence lock-owned final-absent))
          :same)
   (and present
        (equal (fn-bpcd-unframe saved) (fn-bpcd-observed-id observed))
        (equal (fn-bpnf-clock-domain-plan-boot-id
                (fn-bpnf-clock-domain-plan
                 saved present observed legacy-evidence lock-owned
                 final-absent))
               (fn-bpcd-unframe saved))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-bpnf-clock-domain-plan
                              fn-bpnf-clock-domain-plan-status
                              fn-bpnf-clock-domain-plan-boot-id
                              fn-bpcd-plan-second))))

(defthm fn-bpnf-clock-domain-different-boot-fences
  (implies (and present
                (fn-bpcd-unframe saved)
                (fn-bpcd-observed-id observed)
                (not (equal (fn-bpcd-unframe saved)
                            (fn-bpcd-observed-id observed))))
           (equal (fn-bpnf-clock-domain-plan
                   saved present observed legacy-evidence
                   lock-owned final-absent)
                  '(:fence :different-boot)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-bpnf-clock-domain-plan))))

(defthm fn-bpnf-clock-domain-legacy-without-marker-fences
  (implies (and (not present)
                (fn-bpcd-observed-id observed)
                final-absent legacy-evidence)
           (equal (fn-bpnf-clock-domain-plan
                   saved present observed legacy-evidence
                   lock-owned final-absent)
                  '(:fence :legacy-without-domain)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-bpnf-clock-domain-plan))))
