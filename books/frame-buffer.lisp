; frame-buffer: the frame decoded in place from the octet buffer (D27, row Q2,
; the frame-control class).
;
; The reference, `fn-frame-decode' (books/frame-fields.lisp), takes the frame
; as an octet list and answers `fn-frame-ok' with the payload as a list: every
; host call site (host/native/control.lisp reads one frame into a vector and
; converts it to a list at each of up to six decoder calls per request)
; conses the whole frame.  `fn-frb-decode' is the same decision over the
; buffer: the header's fields are read by index, the trailer is compared in
; place, and the payload is LOCATED -- the ok result carries its length, and
; the payload is the buffer's window from the header's end
; (`fn-frb-payload-is-window').  The reference's octet preflight is the
; buffer's invariant.
;
; KEYSTONE: fn-frb-decode-is-frame-decode.  The twin's result is the
; reference's, located (`fn-frb-of').  A request decoder over the buffer
; composes this with its payload grammar; the located payload is what a
; digest seam (books/frame-digest-buffer) or a CBOR reader over a window
; consumes without a list of the frame.

(in-package "ACL2")
(include-book "octets-stobj")
(include-book "frame-fields")
(include-book "octet-window")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; The located result: an ok frame with its payload replaced by its length
; (the payload's offset is the header's, a constant).

(defun fn-frb-of (r)
  (declare (xargs :guard t))
  (if (fn-frame-result-okp r)
      (fn-frame-ok (fn-frame-result-magic r) (fn-frame-result-version r)
                   (fn-frame-result-kind r)
                   (len (fn-frame-result-payload r)))
    r))

; -----------------------------------------------------------------------------
; The readers by index.  A cell of the buffer's value is an octet, so the
; reads below are naturals (the guard of the arithmetic on them).

(defthm fn-frb-cell-is-natp
  (implies (and (fn-cbor-octet-listp xs) (natp i) (< i (len xs)))
           (natp (nth i xs)))
  :hints (("Goal" :in-theory (enable fn-cbor-octet-listp nth)))
  :rule-classes ((:rewrite) (:type-prescription)))

(defun fn-frb-u32-at (j fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp j) (<= (+ 4 j) (fn-octets-len fn-octets)))
                  :guard-hints (("Goal" :in-theory (e/d (fn-oct-octets-p-is-octet-listp)
                                                        (nth))))))
  (+ (* 16777216 (fn-octets-get j fn-octets))
     (* 65536 (fn-octets-get (+ 1 j) fn-octets))
     (* 256 (fn-octets-get (+ 2 j) fn-octets))
     (fn-octets-get (+ 3 j) fn-octets)))

(defun fn-frb-magic (fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (<= *fn-frame-magic-octets* (fn-octets-len fn-octets))))
  (list (fn-octets-get 0 fn-octets) (fn-octets-get 1 fn-octets)
        (fn-octets-get 2 fn-octets) (fn-octets-get 3 fn-octets)))

; XS is exactly the buffer's suffix from J.
(defun fn-frb-suffix-equalp (j xs fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp j) (<= j (fn-octets-len fn-octets))
                              (true-listp xs))
                  :measure (len xs)))
  (if (consp xs)
      (and (< j (fn-octets-len fn-octets))
           (equal (car xs) (fn-octets-get j fn-octets))
           (fn-frb-suffix-equalp (1+ j) (cdr xs) fn-octets))
    (equal j (fn-octets-len fn-octets))))

; -----------------------------------------------------------------------------
; THE DECODER OVER THE BUFFER.  The reference's tests in the reference's
; order; its octet preflight is the buffer's invariant.

(defun fn-frb-decode (digest max-payload fn-octets)
  (declare (xargs :stobjs fn-octets :guard t :verify-guards nil))
  (let ((n (fn-octets-len fn-octets)))
    (if (not (and (natp max-payload) (<= max-payload *fn-frame-max-payload*)))
        (fn-frame-error :bound)
      (if (< (+ *fn-frame-overhead-octets* max-payload) n)
          (fn-frame-error :limit)
        (if (< n *fn-frame-header-octets*)
            (fn-frame-error :truncated)
          (let ((declared (fn-frb-u32-at 6 fn-octets)))
            (if (< max-payload declared)
                (fn-frame-error :limit)
              (if (not (equal (- n *fn-frame-header-octets*)
                              (+ declared *fn-frame-trailer-octets*)))
                  (if (< (- n *fn-frame-header-octets*)
                         (+ declared *fn-frame-trailer-octets*))
                      (fn-frame-error :truncated)
                    (fn-frame-error :length))
                (if (not (fn-frame-digestp digest))
                    (fn-frame-error :digest)
                  (if (not (fn-frb-suffix-equalp
                            (+ *fn-frame-header-octets* declared) digest fn-octets))
                      (fn-frame-error :integrity)
                    (fn-frame-ok (fn-frb-magic fn-octets)
                                 (fn-octets-get 4 fn-octets)
                                 (fn-octets-get 5 fn-octets)
                                 declared)))))))))))

; -----------------------------------------------------------------------------
; The correspondence.

(local
 (defthm fn-frb-octets-true-listp
   (implies (fn-cbor-octet-listp xs) (true-listp xs))
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))

(local
 (defthm fn-frb-at-mostp-is-len
   (equal (fn-cbor-at-mostp xs n) (<= (len xs) (nfix n)))
   :hints (("Goal" :in-theory (enable fn-cbor-at-mostp)))))

; The splitter as take and nthcdr, as one total equation (a hypothesis-free
; induction hypothesis).
(local
 (defthm fn-frb-split-is-take-nthcdr
   (equal (fn-frame-split n xs)
          (if (<= (nfix n) (len xs))
              (cons (take n xs) (nthcdr n xs))
            nil))
   :hints (("Goal" :induct (fn-frame-split n xs)
                   :in-theory (enable (:d fn-frame-split) nthcdr take)))))

(local
 (defthm fn-frb-item-is-nth
   (implies (natp n)
            (equal (fn-frame-item n xs) (nth n xs)))
   :hints (("Goal" :in-theory (enable fn-frame-item nth)))))

(local
 (defthm fn-frb-nth-of-take
   (implies (and (natp i) (natp n) (< i n))
            (equal (nth i (take n xs)) (nth i xs)))
   :hints (("Goal" :in-theory (enable nth take)))))

(local
 (defthm fn-frb-nth-of-nthcdr
   (implies (and (natp i) (natp j))
            (equal (nth i (nthcdr j xs)) (nth (+ i j) xs)))
   :hints (("Goal" :induct (nthcdr j xs) :in-theory (enable nthcdr nth)))))

(local
 (defthm fn-frb-len-of-nthcdr
   (implies (natp j)
            (equal (len (nthcdr j xs)) (nfix (- (len xs) j))))
   :hints (("Goal" :induct (nthcdr j xs) :in-theory (enable nthcdr)))))

(local
 (defthm fn-frb-nthcdr-of-nthcdr
   (implies (and (natp i) (natp j))
            (equal (nthcdr i (nthcdr j xs)) (nthcdr (+ i j) xs)))
   :hints (("Goal" :induct (nthcdr j xs) :in-theory (enable nthcdr)))))

(local
 (defthm fn-frb-take-4-is-list
   (implies (<= 4 (len xs))
            (equal (take 4 xs)
                   (list (nth 0 xs) (nth 1 xs) (nth 2 xs) (nth 3 xs))))
   :hints (("Goal" :in-theory (enable take nth)))))

(local
 (defthm fn-frb-consp-of-nthcdr
   (implies (and (natp j) (< j (len xs)))
            (consp (nthcdr j xs)))
   :hints (("Goal" :induct (nthcdr j xs) :in-theory (enable nthcdr)))))

(local
 (defthm fn-frb-car-of-nthcdr
   (implies (natp j)
            (equal (car (nthcdr j xs)) (nth j xs)))
   :hints (("Goal" :induct (nthcdr j xs) :in-theory (enable nthcdr nth)))))

(local
 (defthm fn-frb-cdr-of-nthcdr
   (implies (natp j)
            (equal (cdr (nthcdr j xs)) (nthcdr (+ 1 j) xs)))
   :hints (("Goal" :induct (nthcdr j xs) :in-theory (enable nthcdr)))))

(local
 (defthm fn-frb-nthcdr-past-end
   (implies (and (true-listp xs) (natp j) (<= (len xs) j))
            (equal (nthcdr j xs) nil))
   :hints (("Goal" :induct (nthcdr j xs) :in-theory (enable nthcdr)))))

; A list equals a cons by its car and cdr: the suffix comparison's step.
(local
 (defthm fn-frb-equal-of-cons
   (equal (equal x (cons a b))
          (and (consp x) (equal (car x) a) (equal (cdr x) b)))))

; The in-place comparison is the suffix's equality (J within the buffer:
; the guard).
(defthm fn-frb-suffix-equalp-is-suffix
  (implies (and (fn-octets-p fn-octets) (natp j) (<= j (len fn-octets))
                (true-listp xs))
           (equal (fn-frb-suffix-equalp j xs fn-octets)
                  (equal (nthcdr j fn-octets) xs)))
  :hints (("Goal" :induct (fn-frb-suffix-equalp j xs fn-octets)
                  :in-theory (enable fn-oct-octets-p-is-octet-listp))))

(local
 (defthm fn-frb-u32-at-is-u32-from
   (implies (and (fn-octets-p fn-octets) (natp j) (<= (+ 4 j) (len fn-octets)))
            (equal (fn-frb-u32-at j fn-octets)
                   (fn-cbor-u32-from (take 4 (nthcdr j fn-octets)))))
   :hints (("Goal" :in-theory (enable fn-octets-get fn-cbor-u32-from)))))

(local
 (defthm fn-frb-len-of-take
   (equal (len (take n xs)) (nfix n))
   :hints (("Goal" :in-theory (enable take)))))

(local
 (defthm fn-frb-true-listp-of-take
   (true-listp (take n xs))
   :hints (("Goal" :in-theory (enable take)))))

(local
 (defthm fn-frb-u32-from-natp
   (implies (and (natp a) (natp b) (natp c) (natp d))
            (natp (fn-cbor-u32-from (list a b c d))))
   :hints (("Goal" :in-theory (enable fn-cbor-u32-from)))
   :rule-classes ((:rewrite) (:type-prescription))))

; KEYSTONE.
(defthm fn-frb-decode-is-frame-decode
  (implies (fn-octets-p fn-octets)
           (equal (fn-frb-decode digest max-payload fn-octets)
                  (fn-frb-of (fn-frame-decode fn-octets digest max-payload))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (fn-frame-decode fn-frame-head-fields
                                   fn-oct-octets-p-is-octet-listp)
                                  (fn-cbor-u32-from fn-frame-split)))))

; The payload is the buffer's window after the header: the reference's
; payload is the window of the twin's located length (an error's payload is
; nil, the empty window).  One hypothesis, the buffer's invariant: a decode
; that is ok is one of an octet list, and under the invariant the keystone
; decides the error arms, so neither of two hypotheses would have a removal
; witness.
(defthm fn-frb-payload-is-window
  (implies (fn-octets-p fn-octets)
           (equal (fn-frame-result-payload (fn-frame-decode fn-octets digest max-payload))
                  (fn-shr-win *fn-frame-header-octets*
                              (fn-frame-result-payload
                               (fn-frb-decode digest max-payload fn-octets))
                              fn-octets)))
  :hints (("Goal" :in-theory (e/d (fn-frame-decode fn-frame-head-fields
                                   fn-shr-win fn-oct-octets-p-is-octet-listp)
                                  (fn-cbor-u32-from fn-frame-split)))))

(verify-guards fn-frb-decode
  :hints (("Goal" :in-theory (enable fn-oct-octets-p-is-octet-listp))))
