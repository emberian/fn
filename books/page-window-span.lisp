; The span borrow: one decision copies a verified range of the private window
; into a caller-owned buffer.  A copy is not an alias, so the no-escape
; property of the scalar borrow (books/page-window-read.lisp fn-pwr-byte) is
; kept; what changes is the access protocol: the consumer pays one ledger
; decision and one lock per span instead of one per octet (D27: bound work,
; never data; the representation was already arrays, the straw was not).
(in-package "ACL2")
(include-book "page-window-read")

; The caller's buffer.  Its own stobj, independent of the window's: its size
; is the longest span a caller may ask for, not a property of the window.
(defstobj fn-ew-span
  (fn-ew-span-bytes :type (array (unsigned-byte 8) (16384)) :initially 0)
  :inline t)

(defconst *fn-ew-span-capacity* 16384)

(local
 (defthm fn-pwr-span-bytesp-nth
   (implies (and (fn-ew-bytesp x) (natp i) (< i (len x)))
            (and (integerp (nth i x)) (<= 0 (nth i x)) (< (nth i x) 256)))
   :rule-classes
   ((:rewrite :corollary (implies (and (fn-ew-bytesp x) (natp i) (< i (len x)))
                                  (integerp (nth i x))))
    (:linear :corollary (implies (and (fn-ew-bytesp x) (natp i) (< i (len x)))
                                 (<= 0 (nth i x))))
    (:linear :corollary (implies (and (fn-ew-bytesp x) (natp i) (< i (len x)))
                                 (< (nth i x) 256))))))

(defun fn-pwr-span-copy (src count dst fn-ew-buffer fn-ew-span)
  (declare (xargs :stobjs (fn-ew-buffer fn-ew-span)
                  :guard (and (natp src) (natp count) (natp dst)
                              (<= (+ src count) 16384)
                              (<= (+ dst count) 16384))
                  :measure (nfix count)))
  (if (zp count) fn-ew-span
    (let ((fn-ew-span
            (update-fn-ew-span-bytesi dst (fn-ew-bytesi src fn-ew-buffer) fn-ew-span)))
      (fn-pwr-span-copy (+ 1 src) (1- count) (+ 1 dst) fn-ew-buffer fn-ew-span))))

(local
 (defthm fn-pwr-span-nth-update
   (implies (and (natp i) (natp j))
            (equal (nth i (update-nth j v xs))
                   (if (equal i j) v (nth i xs))))))

; The copy's whole effect: window octet SRC+K lands at DST+K, nothing else moves.
(defthm fn-pwr-span-copy-exact-output-and-effects
  (implies (and (natp src) (natp count) (natp dst) (natp j))
           (equal (nth j (nth 0 (fn-pwr-span-copy src count dst fn-ew-buffer fn-ew-span)))
                  (if (and (<= dst j) (< j (+ dst count)))
                      (nth (+ src (- j dst)) (nth 0 fn-ew-buffer))
                    (nth j (nth 0 fn-ew-span)))))
  :hints (("Goal" :induct (fn-pwr-span-copy src count dst fn-ew-buffer fn-ew-span)
           :in-theory (enable update-fn-ew-span-bytesi fn-ew-bytesi))))

(in-theory (disable fn-pwr-span-copy))

; Window-relative span [I, J): the octets I .. J-1 of the window the scalar
; borrow serves, copied to positions 0 .. J-I-1 of the caller's buffer.  The
; ledger, plan and publication checks are fn-pwr-byte's own, made once.
(defun fn-pwr-span (ledger worker token s i j fn-ew-buffer fn-ew-span)
  (declare (xargs :stobjs (fn-ew-buffer fn-ew-span)
                  :guard (and (true-listp s) (natp i) (natp j) (< i j))
                  :guard-hints (("Goal" :in-theory (enable fn-pwr-span-copy)))))
  (if (and (fn-pwx-boundp ledger worker token :returned)
           (fn-pwr-plan-matches-token s token)
           (fn-ewp-publication s)
           (natp (nth 5 s)) (<= (nth 5 s) 16384) (<= j (nth 5 s)))
      (let ((fn-ew-span (fn-pwr-span-copy i (- j i) 0 fn-ew-buffer fn-ew-span)))
        (mv :span fn-ew-span))
    (mv :unavailable fn-ew-span)))

(local
 (defthm fn-pwr-span-byte-facts
   (implies (equal (mv-nth 0 (fn-pwr-byte ledger worker token s i fn-ew-buffer)) :byte)
            (and (fn-pwx-boundp ledger worker token :returned)
                 (fn-pwr-plan-matches-token s token) (fn-ewp-publication s)
                 (natp i) (natp (nth 5 s)) (<= (nth 5 s) 16384) (< i (nth 5 s))
                 (equal (mv-nth 1 (fn-pwr-byte ledger worker token s i fn-ew-buffer))
                        (nth i (nth 0 fn-ew-buffer)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-pwr-byte)))))

(local
 (defthm fn-pwr-span-byte-is-byte
   (implies (and (fn-pwx-boundp ledger worker token :returned)
                 (fn-pwr-plan-matches-token s token) (fn-ewp-publication s)
                 (natp i) (natp (nth 5 s)) (<= (nth 5 s) 16384) (< i (nth 5 s)))
            (equal (fn-pwr-byte ledger worker token s i fn-ew-buffer)
                   (mv :byte (fn-ew-bytesi i fn-ew-buffer))))
   :hints (("Goal" :in-theory (enable fn-pwr-byte)))))

; KEYSTONE (a span is the scalar borrows).  When the span answers, every octet
; K of it is what the scalar borrow of I+K answers, and that borrow answers a
; byte; contrapositively a span refuses whenever the scalar refuses at ANY
; covered index.
(defthm fn-pwr-span-is-the-borrowed-bytes
  (implies (and (natp i) (natp j) (< i j) (natp k) (< k (- j i))
                (equal (mv-nth 0 (fn-pwr-span ledger worker token s i j fn-ew-buffer fn-ew-span))
                       :span))
           (and (equal (mv-nth 0 (fn-pwr-byte ledger worker token s (+ i k) fn-ew-buffer)) :byte)
                (equal (nth k (nth 0 (mv-nth 1 (fn-pwr-span ledger worker token s i j
                                                            fn-ew-buffer fn-ew-span))))
                       (mv-nth 1 (fn-pwr-byte ledger worker token s (+ i k) fn-ew-buffer)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwr-span)
           :use ((:instance fn-pwr-span-copy-exact-output-and-effects
                            (src i) (count (- j i)) (dst 0) (j k))))))

(defthm fn-pwr-span-refuses-where-the-octet-refuses
  (implies (and (natp i) (natp j) (< i j) (natp k) (< k (- j i))
                (not (equal (mv-nth 0 (fn-pwr-byte ledger worker token s (+ i k) fn-ew-buffer))
                            :byte)))
           (not (equal (mv-nth 0 (fn-pwr-span ledger worker token s i j fn-ew-buffer fn-ew-span))
                       :span)))
  :rule-classes nil
  :hints (("Goal" :use fn-pwr-span-is-the-borrowed-bytes)))

; KEYSTONE (a span answers exactly when its octets do).  The scalar borrow
; answering at both ends of [I, J) is enough (the window is one run of
; octets), and then the span answers.  A span that does not answer leaves the
; caller's buffer exactly as it was.
(defthm fn-pwr-span-answers-when-its-ends-do
  (implies (and (natp i) (natp j) (< i j)
                (equal (mv-nth 0 (fn-pwr-byte ledger worker token s i fn-ew-buffer)) :byte)
                (equal (mv-nth 0 (fn-pwr-byte ledger worker token s (- j 1) fn-ew-buffer)) :byte))
           (equal (mv-nth 0 (fn-pwr-span ledger worker token s i j fn-ew-buffer fn-ew-span))
                  :span))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwr-span)
           :use ((:instance fn-pwr-span-byte-facts (i i))
                 (:instance fn-pwr-span-byte-facts (i (- j 1)))))))

(defthm fn-pwr-span-refusal-leaves-the-buffer
  (implies (not (equal (mv-nth 0 (fn-pwr-span ledger worker token s i j fn-ew-buffer fn-ew-span))
                       :span))
           (equal (mv-nth 1 (fn-pwr-span ledger worker token s i j fn-ew-buffer fn-ew-span))
                  fn-ew-span))
  :hints (("Goal" :in-theory (enable fn-pwr-span))))

(defthm fn-pwr-span-refusal-word
  (implies (not (equal (mv-nth 0 (fn-pwr-span ledger worker token s i j fn-ew-buffer fn-ew-span))
                       :span))
           (equal (mv-nth 0 (fn-pwr-span ledger worker token s i j fn-ew-buffer fn-ew-span))
                  :unavailable))
  :hints (("Goal" :in-theory (enable fn-pwr-span))))

(in-theory (disable fn-pwr-span))

; Payload-coordinate span [I, J): the arena's coordinates, joined to the
; window exactly as fn-pwr-byte-at joins its scalar (same outcome, same
; descriptor equality, same window offset).
(defun fn-pwr-span-at (ledger worker token s file eoff elen poff plen trailer i j
                              fn-ew-buffer fn-ew-span)
  (declare (xargs :stobjs (fn-ew-buffer fn-ew-span)
                  :guard (and (true-listp s) (natp i) (natp j) (< i j))))
  (let ((outcome (fn-pwr-outcome ledger worker token s)))
    (if (not (equal outcome :ready)) (mv outcome fn-ew-span)
      (if (and (fn-pwx-tokenp token)
               (equal (list file eoff elen poff plen trailer)
                      (list (fn-prl-nth 2 token) (fn-prl-nth 3 token)
                            (fn-prl-nth 4 token) (fn-prl-nth 5 token)
                            (fn-prl-nth 6 token) (fn-prl-nth 8 token)))
               (natp i) (natp j) (natp plen) (<= j plen)
               (natp (fn-prl-nth 7 token)) (<= (fn-prl-nth 7 token) i))
          (fn-pwr-span ledger worker token s (- i (fn-prl-nth 7 token))
                       (- j (fn-prl-nth 7 token)) fn-ew-buffer fn-ew-span)
        (mv :unavailable fn-ew-span)))))

(local
 (defthm fn-pwr-span-outcome-is-never-a-byte
   (not (equal (fn-pwr-outcome ledger worker token s) :byte))
   :hints (("Goal" :in-theory (enable fn-pwr-outcome)))))

(local
 (defthm fn-pwr-span-outcome-is-never-a-span
   (not (equal (fn-pwr-outcome ledger worker token s) :span))
   :hints (("Goal" :in-theory (enable fn-pwr-outcome)))))

(local
 (defthm fn-pwr-span-at-byte-at-facts
   (implies (equal (mv-nth 0 (fn-pwr-byte-at ledger worker token s file eoff elen poff plen
                                             trailer i fn-ew-buffer))
                   :byte)
            (and (equal (fn-pwr-outcome ledger worker token s) :ready)
                 (fn-pwx-tokenp token)
                 (equal (list file eoff elen poff plen trailer)
                        (list (fn-prl-nth 2 token) (fn-prl-nth 3 token)
                              (fn-prl-nth 4 token) (fn-prl-nth 5 token)
                              (fn-prl-nth 6 token) (fn-prl-nth 8 token)))
                 (natp i) (natp plen) (< i plen)
                 (natp (fn-prl-nth 7 token)) (<= (fn-prl-nth 7 token) i)
                 (equal (fn-pwr-byte-at ledger worker token s file eoff elen poff plen
                                        trailer i fn-ew-buffer)
                        (fn-pwr-byte ledger worker token s (- i (fn-prl-nth 7 token))
                                     fn-ew-buffer))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-pwr-byte-at)))))

(local
 (defthm fn-pwr-span-at-byte-at-is-byte
   (implies (and (equal (fn-pwr-outcome ledger worker token s) :ready)
                 (fn-pwx-tokenp token)
                 (equal (list file eoff elen poff plen trailer)
                        (list (fn-prl-nth 2 token) (fn-prl-nth 3 token)
                              (fn-prl-nth 4 token) (fn-prl-nth 5 token)
                              (fn-prl-nth 6 token) (fn-prl-nth 8 token)))
                 (natp i) (natp plen) (< i plen)
                 (natp (fn-prl-nth 7 token)) (<= (fn-prl-nth 7 token) i))
            (equal (fn-pwr-byte-at ledger worker token s file eoff elen poff plen
                                   trailer i fn-ew-buffer)
                   (fn-pwr-byte ledger worker token s (- i (fn-prl-nth 7 token))
                                fn-ew-buffer)))
   :hints (("Goal" :in-theory (enable fn-pwr-byte-at)))))

(local
 (defthm fn-pwr-span-at-span-facts
   (implies (equal (mv-nth 0 (fn-pwr-span-at ledger worker token s file eoff elen poff plen
                                             trailer i j fn-ew-buffer fn-ew-span))
                   :span)
            (and (equal (fn-pwr-outcome ledger worker token s) :ready)
                 (fn-pwx-tokenp token)
                 (equal (list file eoff elen poff plen trailer)
                        (list (fn-prl-nth 2 token) (fn-prl-nth 3 token)
                              (fn-prl-nth 4 token) (fn-prl-nth 5 token)
                              (fn-prl-nth 6 token) (fn-prl-nth 8 token)))
                 (natp i) (natp j) (natp plen) (<= j plen)
                 (natp (fn-prl-nth 7 token)) (<= (fn-prl-nth 7 token) i)
                 (equal (mv-nth 0 (fn-pwr-span-at ledger worker token s file eoff elen poff plen
                                                  trailer i j fn-ew-buffer fn-ew-span))
                        (mv-nth 0 (fn-pwr-span ledger worker token s
                                               (- i (fn-prl-nth 7 token))
                                               (- j (fn-prl-nth 7 token))
                                               fn-ew-buffer fn-ew-span)))
                 (equal (mv-nth 1 (fn-pwr-span-at ledger worker token s file eoff elen poff plen
                                                  trailer i j fn-ew-buffer fn-ew-span))
                        (mv-nth 1 (fn-pwr-span ledger worker token s
                                               (- i (fn-prl-nth 7 token))
                                               (- j (fn-prl-nth 7 token))
                                               fn-ew-buffer fn-ew-span)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-pwr-span-at)))))

; KEYSTONE (a payload span is the scalar borrows, same shape as above).
(defthm fn-pwr-span-at-is-the-borrowed-bytes
  (implies (and (natp i) (natp j) (< i j) (natp k) (< k (- j i))
                (equal (mv-nth 0 (fn-pwr-span-at ledger worker token s file eoff elen poff plen
                                                 trailer i j fn-ew-buffer fn-ew-span))
                       :span))
           (and (equal (mv-nth 0 (fn-pwr-byte-at ledger worker token s file eoff elen poff plen
                                                 trailer (+ i k) fn-ew-buffer))
                       :byte)
                (equal (nth k (nth 0 (mv-nth 1 (fn-pwr-span-at ledger worker token s file eoff
                                                              elen poff plen trailer i j
                                                              fn-ew-buffer fn-ew-span))))
                       (mv-nth 1 (fn-pwr-byte-at ledger worker token s file eoff elen poff plen
                                                 trailer (+ i k) fn-ew-buffer)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-pwr-span-at-span-facts
                 (:instance fn-pwr-span-is-the-borrowed-bytes
                            (i (- i (fn-prl-nth 7 token))) (j (- j (fn-prl-nth 7 token))))
                 (:instance fn-pwr-span-at-byte-at-is-byte (i (+ i k))))
           )))

(defthm fn-pwr-span-at-refuses-where-the-octet-refuses
  (implies (and (natp i) (natp j) (< i j) (natp k) (< k (- j i))
                (not (equal (mv-nth 0 (fn-pwr-byte-at ledger worker token s file eoff elen poff
                                                      plen trailer (+ i k) fn-ew-buffer))
                            :byte)))
           (not (equal (mv-nth 0 (fn-pwr-span-at ledger worker token s file eoff elen poff plen
                                                 trailer i j fn-ew-buffer fn-ew-span))
                       :span)))
  :rule-classes nil
  :hints (("Goal" :use fn-pwr-span-at-is-the-borrowed-bytes)))

(defthm fn-pwr-span-at-answers-when-its-ends-do
  (implies (and (natp i) (natp j) (< i j)
                (equal (mv-nth 0 (fn-pwr-byte-at ledger worker token s file eoff elen poff plen
                                                 trailer i fn-ew-buffer))
                       :byte)
                (equal (mv-nth 0 (fn-pwr-byte-at ledger worker token s file eoff elen poff plen
                                                 trailer (- j 1) fn-ew-buffer))
                       :byte))
           (equal (mv-nth 0 (fn-pwr-span-at ledger worker token s file eoff elen poff plen
                                            trailer i j fn-ew-buffer fn-ew-span))
                  :span))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwr-span-at)
           :use ((:instance fn-pwr-span-at-byte-at-facts (i i))
                 (:instance fn-pwr-span-at-byte-at-facts (i (- j 1)))
                 (:instance fn-pwr-span-at-byte-at-is-byte (i i))
                 (:instance fn-pwr-span-at-byte-at-is-byte (i (- j 1)))
                 (:instance fn-pwr-span-answers-when-its-ends-do
                            (i (- i (fn-prl-nth 7 token)))
                            (j (- j (fn-prl-nth 7 token))))))))

(defthm fn-pwr-span-at-refusal-leaves-the-buffer
  (implies (not (equal (mv-nth 0 (fn-pwr-span-at ledger worker token s file eoff elen poff plen
                                                 trailer i j fn-ew-buffer fn-ew-span))
                       :span))
           (equal (mv-nth 1 (fn-pwr-span-at ledger worker token s file eoff elen poff plen
                                            trailer i j fn-ew-buffer fn-ew-span))
                  fn-ew-span))
  :hints (("Goal" :in-theory (enable fn-pwr-span-at))))

(in-theory (disable fn-pwr-span-at))
