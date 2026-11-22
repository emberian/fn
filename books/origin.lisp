; Local acceptance origin. Names are assigned by the deployment authority;
; this representation does not establish global uniqueness or writer authority.
(in-package "ACL2")
(include-book "profile")
(include-book "columns")
(fn2-book-layer :b)

(defun fn2-origin-tuplep (lineage domain incarnation)
 (declare (xargs :guard t))
 (and (posp lineage) (unsigned-byte-p 60 lineage)
      (posp domain) (unsigned-byte-p 60 domain)
      (posp incarnation) (unsigned-byte-p 60 incarnation)))

(defun fn2-origin-profilep (profile)
 (declare (xargs :guard t))
 (and (fn2-origin-tuplep (fn2-profile-get :origin-lineage profile)
                        (fn2-profile-get :origin-domain profile)
                        (fn2-profile-get :origin-incarnation profile))
      (let ((revision (fn2-profile-get :history-revision profile)))
       (or (not revision) (unsigned-byte-p 60 revision)))))
(defun fn2-origin-physicalp (history history-incarnation)
 (declare (xargs :guard t))
 (and (posp history) (unsigned-byte-p 60 history)
      (posp history-incarnation) (unsigned-byte-p 60 history-incarnation)))
(defun fn2-origin-physical-profilep (profile)
 (declare (xargs :guard t))
 (fn2-origin-physicalp (fn2-profile-get :history-id profile)
                      (fn2-profile-get :history-incarnation profile)))

; At most nineteen decimal digits can represent a u60 name. Bound the input
; before traversal; never use the Lisp reader or a host arithmetic decision.
(defun fn2-origin-decimal-aux (text index value)
 (declare (xargs :measure (nfix (- (length text) (nfix index)))
  :guard (and (stringp text) (natp index) (<= index (length text))
              (natp value))))
 (if (>= (nfix index) (length text))
     (if (and (posp value) (unsigned-byte-p 60 value)) value nil)
   (let ((digit (- (char-code (char text (nfix index))) 48)))
    (if (and (<= 0 digit) (<= digit 9))
        (fn2-origin-decimal-aux text (+ 1 (nfix index)) (+ (* 10 value) digit))
      nil))))
(defun fn2-origin-decimal (text)
 (declare (xargs :guard t))
 (if (and (stringp text) (< 0 (length text)) (<= (length text) 19))
     (fn2-origin-decimal-aux text 0 0) nil))
(local (defthm fn2-origin-put-assoc-preserves-alist
 (implies (alistp profile)
          (alistp (put-assoc-equal key value profile)))
 :hints (("Goal" :induct (put-assoc-equal key value profile)))))
(defun fn2-origin-profile-from-text (profile lineage domain incarnation history history-incarnation)
 (declare (xargs :guard t
  :guard-hints (("Goal" :in-theory (disable fn2-origin-decimal put-assoc-equal)))))
 (put-assoc-equal :origin-lineage (fn2-origin-decimal lineage)
  (put-assoc-equal :origin-domain (fn2-origin-decimal domain)
   (put-assoc-equal :origin-incarnation (fn2-origin-decimal incarnation)
    (put-assoc-equal :history-id (fn2-origin-decimal history)
     (put-assoc-equal :history-incarnation (fn2-origin-decimal history-incarnation)
      (if (alistp profile) profile nil)))))))

(defun fn2-history-revision-profile-from-text (profile revision)
 (declare (xargs :guard t
  :guard-hints (("Goal" :in-theory (disable fn2-origin-decimal put-assoc-equal)))))
 (let ((profile (if (alistp profile) profile nil)))
  (if (null revision) profile
    (put-assoc-equal :history-revision (or (fn2-origin-decimal revision) :invalid) profile))))

; Immutable after construction. Boot binds the exact tuple to the persisted
; canonical genesis record before any listener or writer is released.
(defcolumns fn2-origin nil :init-name fn2-origin-empty
 :extra-fields
 ((fn2-origin-lineage :type (unsigned-byte 60) :initially 0
   :why "Configured lineage; checked against canonical persisted genesis.")
  (fn2-origin-domain :type (unsigned-byte 60) :initially 0
   :why "Configured single commit domain, distinct from a name namespace.")
  (fn2-origin-history :type (unsigned-byte 60) :initially 0
   :why "Persisted physical history identity, distinct from acceptance origin.")
  (fn2-origin-history-incarnation :type (unsigned-byte 60) :initially 0
   :why "Persisted physical history incarnation; unchanged by a clean restart.")
  (fn2-origin-history-revision :type (unsigned-byte 60) :initially 0
   :why "Genesis configuration value; zero disables sending a peer READ batch.")
  (fn2-origin-incarnation :type (unsigned-byte 60) :initially 0
   :why "Configured history incarnation, distinct from allocator writer epoch.")))
(defun fn2-origin-prepare (profile fn2-origin)
 (declare (xargs :stobjs fn2-origin :guard t))
 (let ((fn2-origin (fn2-origin-empty 0 fn2-origin)))
  (if (not (and (fn2-origin-profilep profile) (fn2-origin-physical-profilep profile))) fn2-origin
   (let* ((fn2-origin (update-fn2-origin-history (fn2-profile-get :history-id profile) fn2-origin))
          (fn2-origin (update-fn2-origin-history-incarnation (fn2-profile-get :history-incarnation profile) fn2-origin))
          (fn2-origin (update-fn2-origin-history-revision
                        (nfix (fn2-profile-get :history-revision profile)) fn2-origin))
          (fn2-origin (update-fn2-origin-lineage (fn2-profile-get :origin-lineage profile) fn2-origin))
          (fn2-origin (update-fn2-origin-domain (fn2-profile-get :origin-domain profile) fn2-origin)))
    (update-fn2-origin-incarnation (fn2-profile-get :origin-incarnation profile) fn2-origin)))))
(defthm fn2-origin-prepare-type
 (implies (fn2-originp fn2-origin) (fn2-originp (fn2-origin-prepare profile fn2-origin))))
(defthm fn2-origin-prepare-wfp
 (fn2-origin-wfp (fn2-origin-prepare profile fn2-origin)))
(in-theory (disable fn2-origin-prepare))
