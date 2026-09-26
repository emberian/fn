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
           :in-theory (disable fn-native-admin-publication-authorize
                               fn-cvec-retention-recordp))))

(in-theory (disable fn-cvec-config-generations fn-cvec-retention-recordp))
