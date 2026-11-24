; Parse the native startup environment's group list before profile admission.
(in-package "ACL2")

; The startup environment already bounds the string. Scan its actual
; length once, copying only disjoint name spans into the profile.
(defun fn2-startup-groups-trimp (ch)
 (declare (xargs :guard t))
 (or (eql ch #\Space) (eql ch #\Tab) (eql ch #\Return)))

(defun fn2-startup-groups-emit (text start end next-id groups)
 (declare (xargs :guard (and (stringp text) (natp start) (natp end)
                             (<= start end) (<= end (length text))
                             (posp next-id) (true-listp groups))))
 (if (< start end)
     (cons (cons (subseq text start end) next-id) groups)
   groups))

(defun fn2-startup-groups-scan (text index start end next-id groups)
 (declare (xargs :measure (nfix (- (length text) (nfix index)))
                 :guard (and (stringp text) (natp index) (natp start) (natp end)
                             (<= start end) (<= end index) (<= index (length text))
                             (posp next-id) (true-listp groups))))
 ; START and END enclose the first through last non-trim characters of
 ; the current field. Equal offsets mean no name has started.
 (if (>= (nfix index) (length text))
     (reverse (fn2-startup-groups-emit text start end next-id groups))
   (let* ((ch (char text (nfix index)))
          (next (+ 1 (nfix index))))
    (cond ((or (eql ch #\,) (eql ch #\Newline))
           (fn2-startup-groups-scan text next next next
              (if (< start end) (+ 1 next-id) next-id)
              (fn2-startup-groups-emit text start end next-id groups)))
          ((fn2-startup-groups-trimp ch)
           (fn2-startup-groups-scan text next start end next-id groups))
          (t (fn2-startup-groups-scan text next (if (= start end) (nfix index) start)
                                      next next-id groups))))))

(defun fn2-startup-groups-from-text (profile text)
 (declare (xargs :guard t))
 (if (null text) profile
   (put-assoc-equal :groups
     (if (stringp text) (fn2-startup-groups-scan text 0 0 0 1 nil) :invalid)
     (if (alistp profile) profile nil))))

(defthm fn2-startup-groups-emit-alistp
 (implies (alistp groups)
          (alistp (fn2-startup-groups-emit text start end next-id groups))))

(local
 (defthm fn2-startup-groups-revappend-alistp
  (implies (and (alistp groups) (alistp acc))
           (alistp (revappend groups acc)))))

(defthm fn2-startup-groups-scan-alistp
 (implies (alistp groups)
          (alistp (fn2-startup-groups-scan text index start end next-id groups)))
 :hints (("Goal" :induct
          (fn2-startup-groups-scan text index start end next-id groups)
          :in-theory (disable fn2-startup-groups-emit fn2-startup-groups-trimp
                              char length nfix))))

(defthm fn2-startup-groups-from-text-preserves-other-key
 (implies (and (alistp profile) (not (equal key :groups)))
          (equal (assoc-equal key (fn2-startup-groups-from-text profile text))
                 (assoc-equal key profile)))
 :hints (("Goal" :in-theory (disable fn2-startup-groups-scan))))
