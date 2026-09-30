; Cold-source incremental codec components; PRF-1088 remains a planned union.
; This book extends tagged-node preparation without altering the resident API.
(in-package "ACL2")
(include-book "history-record-cursor")
; Full symbol normalizer composes at emission, independently of this NIL probe.
(local (include-book "arithmetic/top" :dir :system))

; Seven fixed fields: phase, package, original offset, original count,
; matched index, opaque capture context, opaque lease. Prefix recognition is
; only three octets, not general symbol construction or table search.
(defun fn-hrcur-nil-shapep (c)
  (declare (xargs :guard t))
  (and (fn-hrcur-widthp c 7)
       (member-eq (fn-hrcur-field 0 c) '(:check :nil :not-nil :refused))
       (member-equal (fn-hrcur-field 1 c) '(0 1 2))
       (natp (fn-hrcur-field 2 c))
       (< (fn-hrcur-field 2 c) *fn-hrcur-u64-bound*)
       (natp (fn-hrcur-field 3 c))
       (< (fn-hrcur-field 3 c) *fn-hrcur-u64-bound*)
       (natp (fn-hrcur-field 4 c)) (<= (fn-hrcur-field 4 c) 3)
       (implies (eq (fn-hrcur-field 0 c) :check)
                (and (member-equal (fn-hrcur-field 1 c) '(1 2))
                     (equal (fn-hrcur-field 3 c) 3)))))

(defun fn-hrcur-nil-begin (pkg offset count capture lease)
  (declare (xargs :guard t))
  (if (and (member-equal pkg '(0 1 2))
           (natp offset) (< offset *fn-hrcur-u64-bound*)
           (natp count) (< count *fn-hrcur-u64-bound*)
           (< (+ offset count) *fn-hrcur-u64-bound*))
      (list (if (and (member-equal pkg '(1 2)) (equal count 3))
                :check :not-nil)
            pkg offset count 0 capture lease)
    (list :refused 0 0 0 0 capture lease)))

(defun fn-hrcur-nil-tick (c)
  (declare (xargs :guard t))
  (cond ((not (fn-hrcur-nil-shapep c)) (mv '(:refused :nil-probe) c))
        ((eq (fn-hrcur-field 0 c) :nil) (mv '(:done :nil) c))
        ((eq (fn-hrcur-field 0 c) :not-nil) (mv '(:done :not-nil) c))
        ((and (eq (fn-hrcur-field 0 c) :check)
              (< (fn-hrcur-field 4 c) 3))
         (mv (list :need-byte (+ (fn-hrcur-field 2 c) (fn-hrcur-field 4 c))) c))
        (t (mv '(:refused :nil-probe) c))))

(defun fn-hrcur-nil-supply (c position byte)
  (declare (xargs :guard t))
  (let ((index (fn-hrcur-field 4 c)))
    (if (and (fn-hrcur-nil-shapep c)
             (eq (fn-hrcur-field 0 c) :check) (< index 3)
             (equal position (+ (fn-hrcur-field 2 c) index))
             (fn-scc-octetp byte))
        (let ((match (equal byte (nth index '(78 73 76)))))
          (mv :continue
              (list (if match (if (equal index 2) :nil :check) :not-nil)
                    (fn-hrcur-field 1 c) (fn-hrcur-field 2 c)
                    (fn-hrcur-field 3 c) (if match (+ 1 index) index)
                    (fn-hrcur-field 5 c) (fn-hrcur-field 6 c))))
      (mv '(:refused :nil-response) c))))

; Logical vocabulary only. The real reader authenticates one requested byte;
; no function above reads POOL or compares the opaque source/lease references.
(defun fn-hrcur-nil-model (pkg offset count pool)
  (declare (xargs :guard t :verify-guards nil))
  (and (member-equal pkg '(1 2)) (equal count 3)
       (equal (fn-hrcur-prefix 3 (fn-hrcur-tail (nfix offset) pool)) '(78 73 76)) t))

(defun fn-hrcur-nil-invariantp (c pool)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-hrcur-nil-shapep c) (fn-scc-octet-listp pool)
       (< (+ (fn-hrcur-field 2 c) (fn-hrcur-field 3 c)) *fn-hrcur-u64-bound*)
       (<= (+ (fn-hrcur-field 2 c) (fn-hrcur-field 3 c)) (len pool))
       (case (fn-hrcur-field 0 c)
         (:check
          (and (< (fn-hrcur-field 4 c) 3)
               (equal (fn-hrcur-prefix (fn-hrcur-field 4 c)
                                      (fn-hrcur-tail (fn-hrcur-field 2 c) pool))
                      (fn-hrcur-prefix (fn-hrcur-field 4 c) '(78 73 76)))))
         (:nil (fn-hrcur-nil-model (fn-hrcur-field 1 c) (fn-hrcur-field 2 c)
                                 (fn-hrcur-field 3 c) pool))
         (:not-nil (not (fn-hrcur-nil-model (fn-hrcur-field 1 c) (fn-hrcur-field 2 c)
                                          (fn-hrcur-field 3 c) pool)))
         (otherwise nil))))

(defthm fn-hrcur-nil-begin-establishes-invariant
  (implies (and (member-equal pkg '(0 1 2)) (natp offset) (natp count)
                (< (+ offset count) *fn-hrcur-u64-bound*)
                (fn-scc-octet-listp pool) (<= (+ offset count) (len pool)))
           (fn-hrcur-nil-invariantp (fn-hrcur-nil-begin pkg offset count capture lease) pool))
  :hints (("Goal" :in-theory
           (e/d (fn-hrcur-nil-begin fn-hrcur-nil-invariantp fn-hrcur-nil-shapep
                 fn-hrcur-nil-model)
                (fn-hrcur-prefix fn-hrcur-tail)))))

(defthm fn-hrcur-nil-request-does-not-move
  (equal (mv-nth 1 (fn-hrcur-nil-tick c)) c)
  :hints (("Goal" :in-theory (enable fn-hrcur-nil-tick))))

(defthm fn-hrcur-nil-supply-wrong-position-unfolds
  (implies (not (equal position (+ (fn-hrcur-field 2 c) (fn-hrcur-field 4 c))))
           (equal (fn-hrcur-nil-supply c position byte)
                  (mv '(:refused :nil-response) c)))
  :hints (("Goal" :in-theory (enable fn-hrcur-nil-supply))))

(defthm fn-hrcur-nil-tick-denotes-symbol-nullness
  (implies (fn-hrcur-nil-invariantp c pool)
           (and (fn-hrcur-nil-invariantp (mv-nth 1 (fn-hrcur-nil-tick c)) pool)
                (implies (equal (mv-nth 0 (fn-hrcur-nil-tick c)) '(:done :nil))
                         (fn-hrcur-nil-model (fn-hrcur-field 1 c) (fn-hrcur-field 2 c)
                                            (fn-hrcur-field 3 c) pool))
                (implies (equal (mv-nth 0 (fn-hrcur-nil-tick c)) '(:done :not-nil))
                         (not (fn-hrcur-nil-model (fn-hrcur-field 1 c) (fn-hrcur-field 2 c)
                                                 (fn-hrcur-field 3 c) pool)))))
  :hints (("Goal" :in-theory
           (e/d (fn-hrcur-nil-tick fn-hrcur-nil-invariantp fn-hrcur-nil-shapep)
                (fn-hrcur-nil-model)))))

(local
 (defthm fn-hrcur-nil-prefix-by-index
   (implies (and (natp offset) (member-equal index '(0 1 2 3)))
            (equal (fn-hrcur-prefix index (fn-hrcur-tail offset pool))
                   (case index
                     (0 nil)
                     (1 (list (nth offset pool)))
                     (2 (list (nth offset pool) (nth (+ 1 offset) pool)))
                     (otherwise (list (nth offset pool) (nth (+ 1 offset) pool)
                                      (nth (+ 2 offset) pool))))))
   :hints (("Goal" :induct (fn-hrcur-tail offset pool)
            :expand ((:free (xs) (fn-hrcur-prefix 0 xs))
                     (:free (xs) (fn-hrcur-prefix 1 xs))
                     (:free (xs) (fn-hrcur-prefix 2 xs))
                     (:free (xs) (fn-hrcur-prefix 3 xs)))
            :in-theory (e/d (fn-hrcur-tail fn-hrcur-prefix nth)
                            (fn-hrcur-tail-is-nthcdr fn-hrcur-prefix-is-take
                             nthcdr take))))))

(local
 (defthm fn-hrcur-nil-pool-byte
   (implies (and (fn-scc-octet-listp pool) (natp position)
                 (< position (len pool)))
            (fn-scc-octetp (nth position pool)))
   :hints (("Goal" :induct (nth position pool)
            :in-theory (enable nth fn-scc-octet-listp fn-scc-octetp)))))

(defthm fn-hrcur-nil-supply-preserves-invariant
  (implies (and (fn-hrcur-nil-invariantp c pool)
                (eq (fn-hrcur-field 0 c) :check)
                (equal position (+ (fn-hrcur-field 2 c) (fn-hrcur-field 4 c)))
                (equal byte (nth position pool)))
           (and (equal (mv-nth 0 (fn-hrcur-nil-supply c position byte)) :continue)
                (fn-hrcur-nil-invariantp
                  (mv-nth 1 (fn-hrcur-nil-supply c position byte)) pool)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrcur-nil-pool-byte (position (fn-hrcur-field 2 c)))
                 (:instance fn-hrcur-nil-pool-byte (position (+ 1 (fn-hrcur-field 2 c))))
                 (:instance fn-hrcur-nil-pool-byte (position (+ 2 (fn-hrcur-field 2 c)))))
           :cases ((equal (fn-hrcur-field 4 c) 0)
                   (equal (fn-hrcur-field 4 c) 1)
                   (equal (fn-hrcur-field 4 c) 2))
           :in-theory
           (e/d (fn-hrcur-nil-invariantp fn-hrcur-nil-shapep
                 fn-hrcur-nil-supply fn-hrcur-nil-model natp)
                (fn-hrcur-prefix fn-hrcur-tail nth
                 fn-hrcur-prefix-is-take fn-hrcur-tail-is-nthcdr
                 fn-hrcur-nil-pool-byte fn-scc-octetp)))))

(local
 (defthm fn-hrcur-nil-intern-name-by-definition
   (implies (and (member-equal pkg '(0 1 2)) (stringp name))
            (equal (symbol-name (fn-scc-intern pkg name)) name))
   :hints (("Goal" :in-theory (enable fn-scc-intern)))))

(local
 (defthm fn-hrcur-nil-intern-null-by-definition
   (implies (and (member-equal pkg '(0 1 2)) (stringp name))
            (equal (equal (fn-scc-intern pkg name) nil)
                   (and (member-equal pkg '(1 2)) (equal name "NIL") t)))
   :hints (("Goal" :use fn-hrcur-nil-intern-name-by-definition
            :cases ((equal name "NIL"))
            :in-theory (enable fn-scc-intern)))))

(local
 (defthm fn-hrcur-nil-octets-chars-roundtrip
   (implies (fn-scc-octet-listp bytes)
            (equal (fn-scc-chars-octets (fn-scc-octets-chars bytes)) bytes))
   :hints (("Goal" :induct (fn-scc-octet-listp bytes)
            :in-theory (enable fn-scc-octet-listp fn-scc-octetp
                               fn-scc-chars-octets fn-scc-octets-chars)))))

(local
 (defthm fn-hrcur-nil-bytes-name
   (implies (fn-scc-octet-listp bytes)
            (equal (equal (coerce (fn-scc-octets-chars bytes) 'string) "NIL")
                   (equal bytes '(78 73 76))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance coerce-inverse-1 (x (fn-scc-octets-chars bytes)))
                  (:instance fn-hrcur-nil-octets-chars-roundtrip)
                  (:instance fn-scc-octets-chars-character-listp (xs bytes)))
            :in-theory (e/d (fn-scc-chars-octets)
                            (fn-scc-octets-chars fn-scc-octet-listp
                             fn-hrcur-nil-octets-chars-roundtrip coerce-inverse-1
                             fn-scc-octets-chars-character-listp
                             fn-midx-equal-lists-have-equal-string-coercions))))))

(local
 (defthm fn-hrcur-nil-prefix-length
   (equal (len (fn-hrcur-prefix count xs)) (nfix count))
   :hints (("Goal" :induct (fn-hrcur-prefix count xs)
            :in-theory (e/d (fn-hrcur-prefix len)
                            (fn-hrcur-prefix-is-take))))))

(local
 (defthm fn-hrcur-nil-tail-length
   (implies (and (natp offset) (<= offset (len pool)))
            (equal (len (fn-hrcur-tail offset pool)) (- (len pool) offset)))
   :hints (("Goal" :induct (fn-hrcur-tail offset pool)
            :in-theory (e/d (fn-hrcur-tail len)
                            (fn-hrcur-tail-is-nthcdr))))))

(local
 (defthm fn-hrcur-nil-slice-octets
   (implies (and (fn-scc-octet-listp pool) (natp offset) (natp count)
                 (<= (+ offset count) (len pool)))
            (fn-scc-octet-listp (fn-hrcur-prefix count (fn-hrcur-tail offset pool))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-scc-octet-listp-facts (x pool) (n offset))
                  (:instance fn-scc-octet-listp-take
                             (x (nthcdr offset pool)) (n count))
                  (:instance fn-hrcur-nil-tail-length))
            :in-theory (e/d (fn-hrcur-tail-is-nthcdr fn-hrcur-prefix-is-take)
                            (nthcdr take fn-scc-octet-listp-facts
                             fn-scc-octet-listp-take fn-scc-octet-listp))))))

(defthm fn-hrcur-nil-model-refines-decoded-symbol
  (implies (and (member-equal pkg '(0 1 2)) (fn-scc-octet-listp pool)
                (natp offset) (natp count) (<= (+ offset count) (len pool)))
           (equal (fn-hrcur-nil-model pkg offset count pool)
                  (equal (fn-hdc-abstract (fn-hdc-span 4 pkg offset count) pool) nil)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrcur-nil-slice-octets)
                 (:instance fn-hrcur-nil-intern-null-by-definition
                            (name (coerce (fn-scc-octets-chars
                                            (fn-hrcur-prefix count
                                              (fn-hrcur-tail offset pool))) 'string)))
                 (:instance fn-hrcur-nil-bytes-name
                            (bytes (fn-hrcur-prefix count (fn-hrcur-tail offset pool))))
                 (:instance fn-hrcur-nil-prefix-length
                            (xs (fn-hrcur-tail offset pool))))
           :in-theory
           (e/d (fn-hrcur-nil-model fn-hdc-span fn-hdc-abstract)
                (fn-scc-intern fn-scc-octets-chars fn-hrcur-prefix fn-hrcur-tail
                 fn-hrcur-nil-intern-null-by-definition fn-hrcur-nil-bytes-name
                 fn-hrcur-nil-prefix-length fn-hrcur-nil-slice-octets
                 fn-midx-equal-lists-have-equal-string-coercions)))))

(defun fn-hrcur-nil-work (c)
  (declare (xargs :guard t :verify-guards nil))
  (if (eq (fn-hrcur-field 0 c) :check)
      (nfix (- 3 (nfix (fn-hrcur-field 4 c)))) 0))

(defthm fn-hrcur-nil-supply-progress
  (implies (and (fn-hrcur-nil-shapep c) (eq (fn-hrcur-field 0 c) :check)
                (< (fn-hrcur-field 4 c) 3)
                (equal position (+ (fn-hrcur-field 2 c) (fn-hrcur-field 4 c)))
                (fn-scc-octetp byte))
           (< (fn-hrcur-nil-work (mv-nth 1 (fn-hrcur-nil-supply c position byte)))
              (fn-hrcur-nil-work c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-hrcur-nil-work fn-hrcur-nil-supply
                              fn-hrcur-nil-shapep natp))))

(defthm fn-hrcur-nil-keeps-capture-lease
  (and (equal (fn-hrcur-field 5 (mv-nth 1 (fn-hrcur-nil-tick c)))
              (fn-hrcur-field 5 c))
       (equal (fn-hrcur-field 6 (mv-nth 1 (fn-hrcur-nil-tick c)))
              (fn-hrcur-field 6 c))
       (equal (fn-hrcur-field 5 (mv-nth 1 (fn-hrcur-nil-supply c position byte)))
              (fn-hrcur-field 5 c))
       (equal (fn-hrcur-field 6 (mv-nth 1 (fn-hrcur-nil-supply c position byte)))
              (fn-hrcur-field 6 c)))
  :hints (("Goal" :in-theory (enable fn-hrcur-nil-tick fn-hrcur-nil-supply))))

(in-theory (disable fn-hrcur-nil-shapep fn-hrcur-nil-begin fn-hrcur-nil-tick
                    fn-hrcur-nil-supply fn-hrcur-nil-model fn-hrcur-nil-invariantp
                    fn-hrcur-nil-work))
