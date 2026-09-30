(in-package "ACL2")
(include-book "../../books/legacy-parser-physical-widths")

(defconst *lpw-limit* (- (expt 2 63) 33))
(defconst *lpw-descriptor* '(1 0 8 0 8 0 0))
(defconst *lpw-bytes* '(83 58 32 120 13 10 13 10))

(defthm lpw-supported-length-positive
 (and (fn-crw-supportedp *lpw-descriptor* 0)
      (natp (fn-crw-nth 4 *lpw-descriptor*))
      (<= (fn-crw-nth 4 *lpw-descriptor*) *lpw-limit*)) :rule-classes nil)
(defthm lpw-abi-positive
 (let* ((s (fn-lpc-begin 0 8 :pin)) (arena (list *lpw-bytes*))
        (out (mv-nth 0 (fn-lpc-tick s 8 arena)))
        (header (fn-lpc-at 4 out)) (body (fn-lpc-at 6 out)))
  (and (fn-crw-supportedp *lpw-descriptor* 0)
       (fn-lpw-descriptor-bound-p s *lpw-descriptor*)
       (fn-lps-scalars-p s) (fn-lpc-ready-p s arena)
       (natp (fn-lpc-at 3 out)) (<= (fn-lpc-at 3 out) *lpw-limit*)
       (natp (fn-lpc-at 1 header)) (<= (fn-lpc-at 1 header) *lpw-limit*)
       (natp (fn-lpc-at 4 header)) (<= (fn-lpc-at 4 header) *lpw-limit*)
       (natp (fn-lpc-at 5 header)) (<= (fn-lpc-at 5 header) *lpw-limit*)
       (natp (fn-lpc-at 1 body)) (<= (fn-lpc-at 1 body) *lpw-limit*)))
 :rule-classes nil)

; Logical-only source-size counterexamples: no enormous list is evaluated.
; Its constructor and executable counterpart are closed; LEN uses the theorem.
(local (defun lpw-logical-source (n)
 (declare (xargs :measure (nfix n) :verify-guards nil))
 (if (zp n) nil (cons 0 (lpw-logical-source (1- n))))))
(local (defthm lpw-logical-source-length
 (equal (len (lpw-logical-source n)) (nfix n))
 :hints (("Goal" :induct (lpw-logical-source n)))))
(local (in-theory (disable lpw-logical-source (:executable-counterpart lpw-logical-source))))

(defthm lpw-length-without-supported-descriptor
 (let ((d (list 1 0 (+ 1 *lpw-limit*) 0 (+ 1 *lpw-limit*) 0 0)))
  (and (not (fn-crw-supportedp d 0))
       (not (<= (fn-crw-nth 4 d) *lpw-limit*)))) :rule-classes nil)

; Hypothesis removal: supported; all other hypotheses affirmatively checked.
(defthm lpw-abi-without-supported
 (let* ((n (+ 1 *lpw-limit*)) (d (list 1 0 n 0 n 0 0)) (arena (list (lpw-logical-source n)))
        (s (fn-lpc-put 3 (+ 1 *lpw-limit*) (fn-lpc-begin 0 n :pin))) (out (mv-nth 0 (fn-lpc-tick s 0 arena))))
  (and (not (fn-crw-supportedp d 0))
       (fn-lpw-descriptor-bound-p s d)
       (fn-lps-scalars-p s)
       (fn-lpc-ready-p s arena)
       (not (<= (fn-lpc-at 3 out) *lpw-limit*))))
 :rule-classes nil
 :hints (("Goal" :in-theory
          (enable fn-lpw-descriptor-bound-p fn-lps-scalars-p
                  fn-lps-header-count-p fn-lps-body-count-p fn-lpc-ready-p
                  fn-lpc-cursor-bounds-p fn-lpc-header-bounds-p
                  fn-lpc-spans-bound-p fn-lpc-span-bound-p
                  fn-lpc-begin fn-lpc-header-begin fn-lpc-header-bad
                  fn-lpc-put fn-lpc-at fn-lpc-tick fn-crw-supportedp
                  fn-crw-naturals fn-crw-nth fn-arena-payload-len fn-arena-count))))

; Hypothesis removal: binding; all other hypotheses affirmatively checked.
(defthm lpw-abi-without-binding
 (let* ((n (+ 1 *lpw-limit*)) (d *lpw-descriptor*) (arena (list (lpw-logical-source n)))
        (s (fn-lpc-put 3 (+ 1 *lpw-limit*) (fn-lpc-begin 0 n :pin))) (out (mv-nth 0 (fn-lpc-tick s 0 arena))))
  (and (fn-crw-supportedp d 0)
       (not (fn-lpw-descriptor-bound-p s d))
       (fn-lps-scalars-p s)
       (fn-lpc-ready-p s arena)
       (not (<= (fn-lpc-at 3 out) *lpw-limit*))))
 :rule-classes nil
 :hints (("Goal" :in-theory
          (enable fn-lpw-descriptor-bound-p fn-lps-scalars-p
                  fn-lps-header-count-p fn-lps-body-count-p fn-lpc-ready-p
                  fn-lpc-cursor-bounds-p fn-lpc-header-bounds-p
                  fn-lpc-spans-bound-p fn-lpc-span-bound-p
                  fn-lpc-begin fn-lpc-header-begin fn-lpc-header-bad
                  fn-lpc-put fn-lpc-at fn-lpc-tick fn-crw-supportedp
                  fn-crw-naturals fn-crw-nth fn-arena-payload-len fn-arena-count))))

; Hypothesis removal: scalars; all other hypotheses affirmatively checked.
(defthm lpw-abi-without-scalars
 (let* ((n 8) (d *lpw-descriptor*) (arena (list *lpw-bytes*))
        (s (fn-lpc-put 6 (list :bad (+ 1 *lpw-limit*)) (fn-lpc-begin 0 n :pin))) (out (mv-nth 0 (fn-lpc-tick s 0 arena))))
  (and (fn-crw-supportedp d 0)
       (fn-lpw-descriptor-bound-p s d)
       (not (fn-lps-scalars-p s))
       (fn-lpc-ready-p s arena)
       (not (<= (fn-lpc-at 1 (fn-lpc-at 6 out)) *lpw-limit*))))
 :rule-classes nil
 :hints (("Goal" :in-theory
          (enable fn-lpw-descriptor-bound-p fn-lps-scalars-p
                  fn-lps-header-count-p fn-lps-body-count-p fn-lpc-ready-p
                  fn-lpc-cursor-bounds-p fn-lpc-header-bounds-p
                  fn-lpc-spans-bound-p fn-lpc-span-bound-p
                  fn-lpc-begin fn-lpc-header-begin fn-lpc-header-bad
                  fn-lpc-put fn-lpc-at fn-lpc-tick fn-crw-supportedp
                  fn-crw-naturals fn-crw-nth fn-arena-payload-len fn-arena-count))))

; Hypothesis removal: ready; all other hypotheses affirmatively checked.
(defthm lpw-abi-without-ready
 (let* ((n 8) (d *lpw-descriptor*) (arena (list *lpw-bytes*))
        (s (fn-lpc-put 3 (+ 1 *lpw-limit*) (fn-lpc-begin 0 n :pin))) (out (mv-nth 0 (fn-lpc-tick s 0 arena))))
  (and (fn-crw-supportedp d 0)
       (fn-lpw-descriptor-bound-p s d)
       (fn-lps-scalars-p s)
       (not (fn-lpc-ready-p s arena))
       (not (<= (fn-lpc-at 3 out) *lpw-limit*))))
 :rule-classes nil
 :hints (("Goal" :in-theory
          (enable fn-lpw-descriptor-bound-p fn-lps-scalars-p
                  fn-lps-header-count-p fn-lps-body-count-p fn-lpc-ready-p
                  fn-lpc-cursor-bounds-p fn-lpc-header-bounds-p
                  fn-lpc-spans-bound-p fn-lpc-span-bound-p
                  fn-lpc-begin fn-lpc-header-begin fn-lpc-header-bad
                  fn-lpc-put fn-lpc-at fn-lpc-tick fn-crw-supportedp
                  fn-crw-naturals fn-crw-nth fn-arena-payload-len fn-arena-count))))

; Selected arithmetic source inventory pricing, not runtime correspondence.
; The supported endpoint can exceed positive fixnum62; the reviewed bounded
; add/sub extra-digit buffer is still32 octets before normalization.
(assert-event
 (and (> *lpw-limit* (- (expt 2 62) 1))
      (equal (fn-crw-primitive-buffer-octets *lpw-limit*) 32)))
