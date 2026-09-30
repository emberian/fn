; Current symbol normalization feeds the actual bounded borrowed span emitter.
; Source-library boundary only; no cold tree/host/funding completion claim.
(in-package "ACL2")
(include-book "history-record-cursor")
(include-book "history-symbol-normalize")
(local (include-book "arithmetic/top" :dir :system))

(defun fn-hrcur-ns-descriptorp (descriptor)
  (declare (xargs :guard t))
  (and (fn-hrcur-widthp descriptor 2)
       (member-equal (fn-hrcur-field 0 descriptor) '(0 4))
       (member-equal (fn-hrcur-field 1 descriptor) '(0 1 2))
       (implies (equal (fn-hrcur-field 0 descriptor) 0)
                (equal (fn-hrcur-field 1 descriptor) 0))))

(defun fn-hrcur-ns-begin (descriptor offset count capture lease)
  (declare (xargs :guard t))
  (if (and (fn-hrcur-ns-descriptorp descriptor)
           (natp offset) (< offset *fn-hrcur-u64-bound*)
           (natp count) (< count *fn-hrcur-u64-bound*)
           (< (+ offset count) *fn-hrcur-u64-bound*))
      (fn-hrcur-span-begin (fn-hrcur-field 0 descriptor)
                          (fn-hrcur-field 1 descriptor) offset
                          (if (equal (fn-hrcur-field 0 descriptor) 0) 0 count)
                          capture lease)
    (list :refused nil 0 0 capture lease 0)))

; This equality is a logical current-codec boundary, not name construction
; in an executable tick. The normalizer retains source payload as a span.
(defthm fn-hrcur-ns-symbol-wire-refines-abstract-codec
  (implies (and (member-equal pkg '(0 1 2))
                (fn-scc-octet-listp pool) (natp offset) (natp count)
                (<= (+ offset count) (len pool))
                (equal descriptor
                       (fn-hdsn-classify-name
                         pkg (coerce (fn-scc-octets-chars
                                       (take count (nthcdr offset pool))) 'string))))
           (equal (fn-hrcur-span-wire (car descriptor) (cadr descriptor)
                                     offset count pool)
                  (fn-scc-encode
                    (fn-hdc-abstract (fn-hdc-span 4 pkg offset count) pool))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hdsn-classify-matches-current-intern
                            (name (coerce (fn-scc-octets-chars
                                            (take count (nthcdr offset pool))) 'string)))
                 (:instance fn-hdsn-intern-name
                            (name (coerce (fn-scc-octets-chars
                                            (take count (nthcdr offset pool))) 'string)))
                 (:instance fn-hrcur-span-string-refines-abstract-codec))
           :in-theory
           (e/d (fn-hrcur-span-wire fn-hdc-abstract fn-hdc-span
                 fn-scc-program fn-scc-atom-octets fn-scc-octets-valuep
                 fn-scc-string-octets)
                (fn-hdsn-classify-name fn-scc-intern fn-scc-package-index
                 fn-scc-nat-octets fn-scc-chars-octets fn-scc-octets-chars
                 take nthcdr fn-midx-equal-lists-have-equal-string-coercions
                 fn-hrcur-span-string-refines-abstract-codec fn-hdsn-intern-name)))))

(defthm fn-hrcur-ns-classified-descriptorp
  (implies (and (member-equal pkg '(0 1 2)) (stringp name))
           (fn-hrcur-ns-descriptorp (fn-hdsn-classify-name pkg name)))
  :hints (("Goal" :in-theory (enable fn-hrcur-ns-descriptorp
                                    fn-hrcur-widthp fn-hrcur-field
                                    fn-hdsn-classify-name))))

(defthm fn-hrcur-ns-begin-preserves-span-invariant
  (implies (and (fn-hrcur-ns-descriptorp descriptor)
                (natp offset) (natp count)
                (< (+ offset count) *fn-hrcur-u64-bound*)
                (fn-scc-octet-listp pool) (<= (+ offset count) (len pool)))
           (and (fn-hrcur-span-invariantp
                  (fn-hrcur-ns-begin descriptor offset count capture lease) pool)
                (equal (fn-hrcur-span-rest
                         (fn-hrcur-ns-begin descriptor offset count capture lease) pool)
                       (fn-hrcur-span-wire (fn-hrcur-field 0 descriptor)
                                           (fn-hrcur-field 1 descriptor) offset
                                           (if (equal (fn-hrcur-field 0 descriptor) 0) 0 count)
                                           pool))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrcur-span-begin-refines-wire
                            (op (fn-hrcur-field 0 descriptor))
                            (pkg (fn-hrcur-field 1 descriptor))
                            (count (if (equal (fn-hrcur-field 0 descriptor) 0) 0 count))))
           :in-theory (e/d (fn-hrcur-ns-begin fn-hrcur-ns-descriptorp)
                            (fn-hrcur-span-begin fn-hrcur-span-rest
                             fn-hrcur-span-invariantp fn-hrcur-span-wire
                             fn-hrcur-span-begin-refines-wire
                             fn-hrcur-span-tick-refines-wire
                             fn-hrcur-span-supply-refines-wire)))))

(local
 (defthm fn-hrcur-ns-nil-wire-unfolds
   (equal (fn-hrcur-span-wire 0 pkg offset count pool) '(0))
   :hints (("Goal" :in-theory (enable fn-hrcur-span-wire)))))

(defthm fn-hrcur-ns-begin-refines-abstract-codec
  (implies (and (member-equal pkg '(0 1 2))
                (fn-scc-octet-listp pool) (natp offset) (natp count)
                (< (+ offset count) *fn-hrcur-u64-bound*)
                (<= (+ offset count) (len pool))
                (equal descriptor
                       (fn-hdsn-classify-name
                         pkg (coerce (fn-scc-octets-chars
                                       (take count (nthcdr offset pool))) 'string))))
           (and (fn-hrcur-span-invariantp
                  (fn-hrcur-ns-begin descriptor offset count capture lease) pool)
                (equal (fn-hrcur-span-rest
                         (fn-hrcur-ns-begin descriptor offset count capture lease) pool)
                       (fn-scc-encode
                         (fn-hdc-abstract (fn-hdc-span 4 pkg offset count) pool)))))
  :hints (("Goal" :do-not-induct t
           :expand ((:free (d) (fn-hrcur-field 0 d))
                    (:free (d) (fn-hrcur-field 1 d))
                    (:free (d) (fn-hrcur-widthp d 1))
                    (:free (d) (fn-hrcur-widthp d 2)))
           :use ((:instance fn-hrcur-ns-classified-descriptorp
                            (name (coerce (fn-scc-octets-chars
                                            (take count (nthcdr offset pool))) 'string)))
                 (:instance fn-hrcur-ns-begin-preserves-span-invariant)
                 (:instance fn-hrcur-ns-symbol-wire-refines-abstract-codec))
           :in-theory (e/d (fn-hrcur-field fn-hrcur-widthp)
                            (fn-hrcur-ns-classified-descriptorp
                             fn-hrcur-ns-begin-preserves-span-invariant
                             fn-hrcur-ns-symbol-wire-refines-abstract-codec
                             fn-hrcur-ns-begin fn-hrcur-span-wire
                             fn-hrcur-span-rest fn-hrcur-span-invariantp
                             fn-hrcur-span-tick-refines-wire
                             fn-hrcur-span-supply-refines-wire
                             fn-scc-encode fn-scc-encode-is-program
                             fn-hdc-abstract fn-hdc-span
                             fn-hdsn-classify-name)))))

(defthm fn-hrcur-ns-begin-keeps-capture-lease
  (and (equal (fn-hrcur-field 4
                (fn-hrcur-ns-begin descriptor offset count capture lease)) capture)
       (equal (fn-hrcur-field 5
                (fn-hrcur-ns-begin descriptor offset count capture lease)) lease))
  :hints (("Goal" :in-theory (enable fn-hrcur-ns-begin fn-hrcur-span-begin
                                    fn-hrcur-field))))

(in-theory (disable fn-hrcur-ns-descriptorp fn-hrcur-ns-begin))
