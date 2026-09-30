; Bounded cold-reopen header decision. The caller's registered job owns the
; descriptor/source incarnation. Runtime/profile admission precedes begin.
; This boundary never grants digest authority or produces recovered CURRENT.
(in-package "ACL2")
(include-book "bp-node-checkpoint-reader")
(include-book "bp-node-checkpoint-job")
(set-verify-guards-eagerness 2)

; tag/status/token/epoch/depth/frame-bound/file-length/offset/payload-count/reason.
(defun fn-bpfr-make (status token epoch depth bound length offset count reason)
 (declare (xargs :guard t))
 (list :bp-checkpoint-frame-reader status token epoch depth bound length offset count reason))
(defun fn-bpfr-begin (token epoch depth bound observed-length)
 (declare (xargs :guard t))
 (fn-bpfr-make
  (if (and (natp bound) (natp observed-length) (<= 46 observed-length)
            (<= observed-length bound)) :header :refused)
  token epoch depth bound observed-length 0 0 :file-length))
(defun fn-bpfr-header-step (job byte)
 (declare (xargs :guard (fn-cbor-octetp byte)))
 (let* ((offset (fn-bpn-nth 7 job)) (count (fn-bpn-nth 8 job))
        (next-count (if (and (natp count) (natp offset) (<= 6 offset))
                         (+ (* 256 count) byte) count))
        (next-offset (if (natp offset) (+ 1 offset) offset))
        (valid (and (equal (fn-bpn-nth 1 job) :header)
                    (natp offset) (< offset 14) (natp count)
                    (or (<= 6 offset) (equal byte (nth offset *fn-bpnr-head*)))))
        (complete (equal next-offset 14))
        (length-ok (and (posp next-count) (<= next-count *fn-bpc-max-uint*)
                        (natp (fn-bpn-nth 5 job))
                        (equal (fn-bpn-nth 6 job) (+ 46 next-count))
                        (<= (+ 46 next-count) (fn-bpn-nth 5 job)))))
  (if (not (equal (fn-bpn-nth 1 job) :header)) job
   (fn-bpfr-make
    (cond ((not valid) :refused)
          ((not complete) :header)
          (length-ok :integrity-required)
          (t :refused))
    (fn-bpn-nth 2 job) (fn-bpn-nth 3 job) (fn-bpn-nth 4 job)
    (fn-bpn-nth 5 job) (fn-bpn-nth 6 job) next-offset next-count
    (cond ((not valid) :header) ((and complete (not length-ok)) :payload-length)
          (t nil))))))
(defun fn-bpfr-action (job)
 (declare (xargs :guard t))
 (case (fn-bpn-nth 1 job)
  (:header (list :read (fn-bpn-nth 7 job) 1))
  (:integrity-required (list :integrity-required (+ 14 (nfix (fn-bpn-nth 8 job)))
                            32))
  (:refused (list :refused (fn-bpn-nth 9 job)))
  (otherwise '(:uncertain))))

; One scheduling turn consumes one header byte; no list/header reversal.
(defun fn-bpfr-header-run (job octets quantum)
 (declare (xargs :guard (and (fn-cbor-octet-listp octets) (natp quantum))
                 :measure (nfix quantum)))
 (if (or (zp quantum) (not (equal (fn-bpn-nth 1 job) :header)) (not (consp octets)))
  (list job octets 0)
  (let* ((next (fn-bpfr-header-step job (car octets)))
         (answer (fn-bpfr-header-run next (cdr octets) (1- quantum))))
   (list (fn-bpn-nth 0 answer) (fn-bpn-nth 1 answer)
         (+ 1 (fn-bpn-nth 2 answer))))))

(defthm fn-bpfr-header-run-consumes-at-most-quantum
 (implies (natp quantum)
  (and (natp (fn-bpn-nth 2 (fn-bpfr-header-run job octets quantum)))
       (<= (fn-bpn-nth 2 (fn-bpfr-header-run job octets quantum)) quantum)))
 :hints (("Goal" :induct (fn-bpfr-header-run job octets quantum)
  :in-theory (e/d (fn-bpfr-header-run)
                 (fn-bpfr-header-step fn-bpfr-make))))
 :rule-classes nil)

(local (defthm fn-bpfr-fourteen-header-turns-by-definition
 (let* ((size (list b0 b1 b2 b3 b4 b5 b6 b7))
        (bytes (append *fn-bpnr-head* size)))
  (implies (and (natp bound) (natp length) (<= 46 length) (<= length bound)
                (fn-cbor-octet-listp size))
   (equal
    (fn-bpfr-header-run (fn-bpfr-begin token epoch depth bound length)
                        (append bytes input) 14)
    (list
     (fn-bpfr-header-step
      (fn-bpfr-make :header token epoch depth bound length 13
        (fn-bpc-u64-from (list 0 b0 b1 b2 b3 b4 b5 b6)) nil) b7)
     input 14))))
 :hints (("Goal" :do-not-induct t
  :expand ((:free (job octets) (fn-bpfr-header-run job octets 14))
           (:free (job octets) (fn-bpfr-header-run job octets 13))
           (:free (job octets) (fn-bpfr-header-run job octets 12))
           (:free (job octets) (fn-bpfr-header-run job octets 11))
           (:free (job octets) (fn-bpfr-header-run job octets 10))
           (:free (job octets) (fn-bpfr-header-run job octets 9))
           (:free (job octets) (fn-bpfr-header-run job octets 8))
           (:free (job octets) (fn-bpfr-header-run job octets 7))
           (:free (job octets) (fn-bpfr-header-run job octets 6))
           (:free (job octets) (fn-bpfr-header-run job octets 5))
           (:free (job octets) (fn-bpfr-header-run job octets 4))
           (:free (job octets) (fn-bpfr-header-run job octets 3))
           (:free (job octets) (fn-bpfr-header-run job octets 2))
           (:free (job octets) (fn-bpfr-header-run job octets 1))
           (:free (job octets) (fn-bpfr-header-run job octets 0)))
  :in-theory (enable fn-bpfr-header-run fn-bpfr-header-step fn-bpfr-begin
                     fn-bpfr-make fn-bpc-u64-from fn-cbor-u32-from
                     fn-cbor-octet-listp fn-cbor-octetp)))
 :rule-classes nil))


(local (defthm fn-bpfr-u64-byte-list-rebuild-by-definition
 (equal (fn-bpc-u64-bytes n)
  (list (nth 0 (fn-bpc-u64-bytes n)) (nth 1 (fn-bpc-u64-bytes n))
        (nth 2 (fn-bpc-u64-bytes n)) (nth 3 (fn-bpc-u64-bytes n))
        (nth 4 (fn-bpc-u64-bytes n)) (nth 5 (fn-bpc-u64-bytes n))
        (nth 6 (fn-bpc-u64-bytes n)) (nth 7 (fn-bpc-u64-bytes n))))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-bpc-u64-bytes fn-bpc-u32-octets binary-append nth zp car-cons cdr-cons))))
 :rule-classes nil))

(local (defthm fn-bpfr-final-u64-byte-by-definition
 (implies (fn-cbor-octet-listp (list b0 b1 b2 b3 b4 b5 b6 b7))
  (equal (+ (* 256 (fn-bpc-u64-from (list 0 b0 b1 b2 b3 b4 b5 b6))) b7)
         (fn-bpc-u64-from (list b0 b1 b2 b3 b4 b5 b6 b7))))
 :hints (("Goal" :in-theory (enable fn-bpc-u64-from fn-cbor-u32-from
                                  fn-cbor-octet-listp fn-cbor-octetp)))))


(local (defthm fn-bpfr-encoded-u64-fields-decode
 (implies (and (natp count) (<= count *fn-bpc-max-uint*))
  (equal (fn-bpc-u64-from
   (list (nth 0 (fn-bpc-u64-bytes count)) (nth 1 (fn-bpc-u64-bytes count))
         (nth 2 (fn-bpc-u64-bytes count)) (nth 3 (fn-bpc-u64-bytes count))
         (nth 4 (fn-bpc-u64-bytes count)) (nth 5 (fn-bpc-u64-bytes count))
         (nth 6 (fn-bpc-u64-bytes count)) (nth 7 (fn-bpc-u64-bytes count)))) count))
 :hints (("Goal" :use ((:instance fn-bpfr-u64-byte-list-rebuild-by-definition (n count))
                      (:instance fn-bpc-u64-from-of-u64-bytes (n count)))
                  :in-theory nil))))
(local (defthm fn-bpfr-encoded-header-refinement
 (implies (and (posp count) (<= count *fn-bpc-max-uint*)
               (natp bound) (<= (+ 46 count) bound))
  (equal
   (fn-bpfr-header-run (fn-bpfr-begin token epoch depth bound (+ 46 count))
    (append *fn-bpnr-head* (fn-bpc-u64-bytes count) input) 14)
   (list (fn-bpfr-make :integrity-required token epoch depth bound
                       (+ 46 count) 14 count nil) input 14)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-bpfr-fourteen-header-turns-by-definition
    (length (+ 46 count))
    (b0 (nth 0 (fn-bpc-u64-bytes count))) (b1 (nth 1 (fn-bpc-u64-bytes count)))
    (b2 (nth 2 (fn-bpc-u64-bytes count))) (b3 (nth 3 (fn-bpc-u64-bytes count)))
    (b4 (nth 4 (fn-bpc-u64-bytes count))) (b5 (nth 5 (fn-bpc-u64-bytes count)))
    (b6 (nth 6 (fn-bpc-u64-bytes count))) (b7 (nth 7 (fn-bpc-u64-bytes count))))
   (:instance fn-bpfr-final-u64-byte-by-definition
    (b0 (nth 0 (fn-bpc-u64-bytes count))) (b1 (nth 1 (fn-bpc-u64-bytes count)))
    (b2 (nth 2 (fn-bpc-u64-bytes count))) (b3 (nth 3 (fn-bpc-u64-bytes count)))
    (b4 (nth 4 (fn-bpc-u64-bytes count))) (b5 (nth 5 (fn-bpc-u64-bytes count)))
    (b6 (nth 6 (fn-bpc-u64-bytes count))) (b7 (nth 7 (fn-bpc-u64-bytes count))))
   (:instance fn-bpc-u64-from-is-natural
    (xs (list 0 (nth 0 (fn-bpc-u64-bytes count)) (nth 1 (fn-bpc-u64-bytes count))
       (nth 2 (fn-bpc-u64-bytes count)) (nth 3 (fn-bpc-u64-bytes count))
       (nth 4 (fn-bpc-u64-bytes count)) (nth 5 (fn-bpc-u64-bytes count))
       (nth 6 (fn-bpc-u64-bytes count)))))
   (:instance fn-bpfr-encoded-u64-fields-decode)
   (:instance fn-bpfr-u64-byte-list-rebuild-by-definition (n count))
   (:instance fn-bpc-u64-bytes-have-eight-octets (n count))
   (:instance fn-bpc-u64-from-of-u64-bytes (n count)))
  :in-theory (e/d (fn-bpfr-header-step fn-bpfr-make fn-bpn-nth fn-cbor-octet-listp fn-cbor-octetp)
   (fn-bpfr-header-run fn-bpfr-begin fn-bpc-u64-bytes fn-bpc-u64-from
    floor mod fn-bpc-u32-octets))))
 :rule-classes nil)
)

; Actual writer prefix and actual bounded reopen runner share this boundary.
(defthm fn-bpfr-checkpoint-prefix-refinement
 (implies (and (posp count) (<= count *fn-bpc-max-uint*)
               (natp bound) (<= (+ 46 count) bound))
  (equal
   (fn-bpfr-header-run (fn-bpfr-begin token epoch depth bound (+ 46 count))
                       (append (fn-bpck-prefix count) input) 14)
   (list (fn-bpfr-make :integrity-required token epoch depth bound
                       (+ 46 count) 14 count nil) input 14)))
 :hints (("Goal" :use fn-bpfr-encoded-header-refinement
  :in-theory (e/d (fn-bpck-prefix) (fn-bpfr-header-run fn-bpfr-begin
                                 fn-bpfr-make fn-bpc-u64-bytes))))
 :rule-classes nil)
