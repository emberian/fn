; fn: the configuration namespace keeps the release's generation (PRF-138,
; STO-020; books/store-capacity-vector.lisp is the rest of the vector).
;
; The operator's content release (`retention set', books/reclaim-rule) is a
; configuration record, and the configuration namespace is bounded by the
; profile's max-config-generations (D27, PRF-102).  Without a reservation a
; store whose generations were used by other administration could never
; again authorize the release that lets it reclaim.  Here every configuration
; record other than the retention rule is authorized under one generation
; fewer, so the last generation stays the release's.
;
; Host call: host/store-node-host.lisp `fn-store-cfg-native-admin-authorize'
; (reached from host/native/admin.lisp `fnn-admin-authorize', offline and in
; the live owner's arm) hands `fn-cvec-config-generations' of the profile
; and the parsed record to `fn-native-admin-publication-authorize'.
(in-package "ACL2")
(include-book "native-admin")
(include-book "store-profile-namespace")

; The configuration generations a configuration record may use: all of them
; for the content-retention rule (`retention set', two :set-limit rows,
; books/reclaim-rule), one fewer for every other record.
(defun fn-cvec-retention-deltasp (deltas)
  (declare (xargs :guard t))
  (if (consp deltas)
      (and (consp (car deltas))
           (equal (fn-cfg-delta-kind (car deltas)) :set-limit)
           (member-equal (fn-cfg-delta-a (car deltas))
                         (list *fn-rcl-rule-slot* *fn-rcl-days-slot*))
           (fn-cvec-retention-deltasp (cdr deltas)))
    t))

(defun fn-cvec-retention-recordp (record)
  (declare (xargs :guard t))
  (and (consp (fn-cfg-record-change record))
       (fn-cvec-retention-deltasp (fn-cfg-record-change record))))

(defun fn-cvec-config-generations (profile record)
  (declare (xargs :guard t))
  (let ((g (nfix (fn-bs-profile-max-config-generations profile))))
    (if (fn-cvec-retention-recordp record)
        g
      (nfix (- g 1)))))

(local
 (defthm fn-cvec-accepted-generation-is-positive
   (let ((result (fn-native-admin-publication-authorize
                  records frontier config-records record lock-owned observed-names
                  max-generations)))
     (implies (equal (fn-native-admin-publication-status result) :accepted)
              (posp (fn-native-admin-publication-generation result))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-native-admin-publication-authorize)
                                   (fn-cnode-config-replay
                                    fn-native-admin-candidate-openp
                                    fn-native-admin-config-name
                                    fn-cfg-recordp))))))

;  KEYSTONE (the configuration namespace keeps the release's generation).  A
; configuration record other than the retention rule, authorized under
; `fn-cvec-config-generations', names a generation below the profile's
; max-config-generations, so the retention rule's record still fits after it.
(defthm fn-cvec-config-publication-keeps-the-release-generation
  (let ((result (fn-native-admin-publication-authorize
                 records frontier config-records record lock-owned observed-names
                 (fn-cvec-config-generations profile record))))
    (implies (and (equal (fn-native-admin-publication-status result) :accepted)
                  (not (fn-cvec-retention-recordp record)))
             (< (fn-native-admin-publication-generation result)
                (nfix (fn-bs-profile-max-config-generations profile)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-native-admin-publication-within-the-operator-bound
                                   (max-generations (fn-cvec-config-generations
                                                     profile record)))
                        (:instance fn-cvec-accepted-generation-is-positive
                                   (max-generations (fn-cvec-config-generations
                                                     profile record))))
           :in-theory (union-theories '(fn-cvec-config-generations nfix natp posp)
                                      (theory 'minimal-theory)))))

(in-theory (disable fn-cvec-config-generations fn-cvec-retention-recordp))

; -----------------------------------------------------------------------------
; PRF-171 (PKT-451 (C), STO-023): field 7, max-group-name-octets, is read.
;
; Before this the field had no reader: `group create' checked only the record
; codec's width (`fn-record-group-namep', 256 octets), so a profile whose
; field 7 is 100 still admitted a 256-octet name.  Every configuration record
; the host publishes, offline and through the live owner, is authorized here
; (host/store-node-host.lisp `fn-store-cfg-native-admin-authorize', from
; host/native/admin.lisp `fnn-admin-authorize'), so a record creating a group
; whose name is longer than field 7 is refused `:max-group-name-octets' by
; name before any publication.  Profile validity still requires field 7 to be
; at most the codec width (byte-store-frame `fn-bs-profile-invalid-reason',
; `:max-group-name-octets-outside-codec'), so profile validation,
; representation and format evolution agree (D27): no format changes, and a
; saved profile's field 7 now governs what it always named.  The width rising
; to the wire's 460 (RFC 3977 section 3.1) is the records-shape and
; byte-store-frame freeze, PKT-510.

; Every :create-group delta of DELTAS names a group of at most N octets.
(defun fn-cvec-group-names-within (deltas n)
  (declare (xargs :guard t))
  (if (consp deltas)
      (and (or (not (equal (fn-cfg-delta-kind (car deltas)) :create-group))
               (<= (len (fn-record-string-octets (fn-cfg-delta-a (car deltas))))
                   (nfix n)))
           (fn-cvec-group-names-within (cdr deltas) n))
    t))

; The authorization the host calls: the profile's group-name bound, then the
; publication under the profile's configuration generations.
(defun fn-cvec-native-admin-authorize
    (records frontier config-records record lock-owned observed-names profile)
  (declare (xargs :guard t))
  (if (not (fn-cvec-group-names-within
            (fn-cfg-record-change record)
            (fn-bs-profile-max-group-name-octets profile)))
      (fn-native-admin-publication-result :refused :max-group-name-octets
                                          nil nil nil)
    (fn-native-admin-publication-authorize
     records frontier config-records record lock-owned observed-names
     (fn-cvec-config-generations profile record))))

(local
 (defthm fn-cvec-publication-authorize-never-names-the-group-bound
   (not (equal (fn-native-admin-publication-reason
                (fn-native-admin-publication-authorize
                 records frontier config-records record lock-owned
                 observed-names max-generations))
               :max-group-name-octets))
   :hints (("Goal" :in-theory (e/d (fn-native-admin-publication-authorize)
                                   (fn-cnode-config-replay
                                    fn-native-admin-candidate-openp
                                    fn-native-admin-config-name
                                    fn-cfg-recordp))))))

;  KEYSTONE (field 7 governs group names).  The authorization the host calls
; refuses `:max-group-name-octets' exactly when the record creates a group
; whose name is longer than the profile's max-group-name-octets; otherwise it
; is the publication authorization it replaced, so every keystone of
; `fn-native-admin-publication-authorize' and
; `fn-cvec-config-publication-keeps-the-release-generation' carries.
(defthm fn-cvec-native-admin-authorize-refuses-exactly-past-the-group-name-bound
  (let ((result (fn-cvec-native-admin-authorize
                 records frontier config-records record lock-owned observed-names
                 profile)))
    (and (iff (equal (fn-native-admin-publication-reason result)
                     :max-group-name-octets)
              (not (fn-cvec-group-names-within
                    (fn-cfg-record-change record)
                    (fn-bs-profile-max-group-name-octets profile))))
         (implies (fn-cvec-group-names-within
                   (fn-cfg-record-change record)
                   (fn-bs-profile-max-group-name-octets profile))
                  (equal result
                         (fn-native-admin-publication-authorize
                          records frontier config-records record lock-owned
                          observed-names
                          (fn-cvec-config-generations profile record))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cvec-native-admin-authorize)
                                  (fn-native-admin-publication-reason
                                   fn-native-admin-publication-result
                                   fn-native-admin-publication-authorize
                                   fn-cvec-group-names-within
                                   fn-bs-profile-max-group-name-octets
                                   fn-cvec-config-generations)))))

;  KEYSTONE.  An accepted record creates no group whose name is longer than
; the profile's max-group-name-octets.
(defthm fn-cvec-accepted-group-names-are-within-the-profile
  (implies (equal (fn-native-admin-publication-status
                   (fn-cvec-native-admin-authorize
                    records frontier config-records record lock-owned
                    observed-names profile))
                  :accepted)
           (fn-cvec-group-names-within
            (fn-cfg-record-change record)
            (fn-bs-profile-max-group-name-octets profile)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cvec-native-admin-authorize)
                                  (fn-native-admin-publication-status
                                   fn-native-admin-publication-result
                                   fn-native-admin-publication-authorize
                                   fn-cvec-group-names-within
                                   fn-bs-profile-max-group-name-octets
                                   fn-cvec-config-generations)))))
