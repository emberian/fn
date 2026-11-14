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
 (fn2-origin-tuplep (fn2-profile-get :origin-lineage profile)
                    (fn2-profile-get :origin-domain profile)
                    (fn2-profile-get :origin-incarnation profile)))

; At most nineteen decimal digits can represent a u60 name. Bound the input
; before traversal; never use the Lisp reader or a host arithmetic decision.
(defun fn2-origin-decimal-aux (text index value)
 (declare (xargs :measure (nfix (- (length text) index))
  :guard (and (stringp text) (natp index) (<= index (length text))
              (natp value))))
 (if (= index (length text))
     (if (and (posp value) (unsigned-byte-p 60 value)) value nil)
   (let ((digit (- (char-code (char text index)) 48)))
    (if (and (<= 0 digit) (<= digit 9))
        (fn2-origin-decimal-aux text (+ 1 index) (+ (* 10 value) digit))
      nil))))
(defun fn2-origin-decimal (text)
 (declare (xargs :guard t))
 (if (and (stringp text) (< 0 (length text)) (<= (length text) 19))
     (fn2-origin-decimal-aux text 0 0) nil))
(defun fn2-origin-profile-from-text (profile lineage domain incarnation)
 (declare (xargs :guard t))
 (put-assoc-equal :origin-lineage (fn2-origin-decimal lineage)
  (put-assoc-equal :origin-domain (fn2-origin-decimal domain)
   (put-assoc-equal :origin-incarnation (fn2-origin-decimal incarnation)
    (if (alistp profile) profile nil)))))

; Immutable after construction. Boot binds the exact tuple to the persisted
; canonical genesis record before any listener or writer is released.
(defcolumns fn2-origin nil :init-name fn2-origin-empty
 :extra-fields
 ((fn2-origin-lineage :type (unsigned-byte 60) :initially 0
   :why "Configured lineage; checked against canonical persisted genesis.")
  (fn2-origin-domain :type (unsigned-byte 60) :initially 0
   :why "Configured single commit domain, distinct from a name namespace.")
  (fn2-origin-incarnation :type (unsigned-byte 60) :initially 0
   :why "Configured history incarnation, distinct from allocator writer epoch.")))
(defun fn2-origin-prepare (profile fn2-origin)
 (declare (xargs :stobjs fn2-origin :guard t))
 (let ((fn2-origin (fn2-origin-empty 0 fn2-origin)))
  (if (not (fn2-origin-profilep profile)) fn2-origin
   (let* ((fn2-origin (update-fn2-origin-lineage (fn2-profile-get :origin-lineage profile) fn2-origin))
          (fn2-origin (update-fn2-origin-domain (fn2-profile-get :origin-domain profile) fn2-origin)))
    (update-fn2-origin-incarnation (fn2-profile-get :origin-incarnation profile) fn2-origin)))))
(defthm fn2-origin-prepare-type
 (implies (fn2-originp fn2-origin) (fn2-originp (fn2-origin-prepare profile fn2-origin))))
(defthm fn2-origin-prepare-wfp
 (fn2-origin-wfp (fn2-origin-prepare profile fn2-origin)))
(in-theory (disable fn2-origin-prepare))
