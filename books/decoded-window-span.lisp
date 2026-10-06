; The span borrow for decoded (stored-DEFLATE) windows: the same protocol
; change as books/page-window-span.lisp.  The renderer read a compressed
; article one octet at a time, each octet two descriptor calls, a lock and a
; scalar borrow (fn-dwj-byte-at, fn-pwz-byte-at); here one ledger decision
; copies the window's octets [I, J) into the caller's own buffer (fn-ew-span,
; never an alias of the private window).  Keystones: every span octet is the
; scalar borrow of its own coordinate; a span refuses wherever the scalar
; refuses; a refusal leaves the caller's buffer as it was.
(in-package "ACL2")
(include-book "page-window-span")
(include-book "decoded-window-read")
(include-book "decoded-worker-job")

; ---- window-relative span over fn-pwz-byte -------------------------------
(defun fn-pwz-span (ledger worker token z i j fn-ew-buffer fn-ew-span)
  (declare (xargs :stobjs (fn-ew-buffer fn-ew-span)
                  :guard (and (true-listp z) (true-listp (nth 1 z))
                              (natp i) (natp j) (< i j))
                  :guard-hints (("Goal" :in-theory (enable fn-pwr-span-copy)))))
  (let ((outcome (fn-pwz-outcome ledger worker token z)))
    (if (not (eq outcome :ready)) (mv outcome fn-ew-span)
      (if (and (natp (nth 4 z)) (<= (nth 4 z) 16384) (<= j (nth 4 z)))
          (let ((fn-ew-span (fn-pwr-span-copy i (- j i) 0 fn-ew-buffer fn-ew-span)))
            (mv :span fn-ew-span))
        (mv :unavailable fn-ew-span)))))

(local
 (defthm fn-pwz-span-outcome-is-never-a-byte-or-span
   (and (not (equal (fn-pwz-outcome ledger worker token z) :byte))
        (not (equal (fn-pwz-outcome ledger worker token z) :span)))
   :hints (("Goal" :in-theory (enable fn-pwz-outcome)))))

(local
 (defthm fn-pwz-span-byte-facts
   (implies (equal (mv-nth 0 (fn-pwz-byte ledger worker token z i fn-ew-buffer)) :byte)
            (and (equal (fn-pwz-outcome ledger worker token z) :ready)
                 (natp i) (natp (nth 4 z)) (<= (nth 4 z) 16384) (< i (nth 4 z))
                 (equal (mv-nth 1 (fn-pwz-byte ledger worker token z i fn-ew-buffer))
                        (nth i (nth 0 fn-ew-buffer)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-pwz-byte fn-ew-bytesi)))))

(local
 (defthm fn-pwz-span-byte-is-byte
   (implies (and (equal (fn-pwz-outcome ledger worker token z) :ready)
                 (natp i) (natp (nth 4 z)) (<= (nth 4 z) 16384) (< i (nth 4 z)))
            (equal (fn-pwz-byte ledger worker token z i fn-ew-buffer)
                   (mv :byte (nth i (nth 0 fn-ew-buffer)))))
   :hints (("Goal" :in-theory (enable fn-pwz-byte fn-ew-bytesi)))))

(defthm fn-pwz-span-is-the-borrowed-bytes
  (implies (and (natp i) (natp j) (< i j) (natp k) (< k (- j i))
                (equal (mv-nth 0 (fn-pwz-span ledger worker token z i j fn-ew-buffer fn-ew-span))
                       :span))
           (and (equal (mv-nth 0 (fn-pwz-byte ledger worker token z (+ i k) fn-ew-buffer)) :byte)
                (equal (nth k (nth 0 (mv-nth 1 (fn-pwz-span ledger worker token z i j
                                                            fn-ew-buffer fn-ew-span))))
                       (mv-nth 1 (fn-pwz-byte ledger worker token z (+ i k) fn-ew-buffer)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwz-span)
           :use ((:instance fn-pwr-span-copy-exact-output-and-effects
                            (src i) (count (- j i)) (dst 0) (j k))))))

(defthm fn-pwz-span-refuses-where-the-octet-refuses
  (implies (and (natp i) (natp j) (< i j) (natp k) (< k (- j i))
                (not (equal (mv-nth 0 (fn-pwz-byte ledger worker token z (+ i k) fn-ew-buffer))
                            :byte)))
           (not (equal (mv-nth 0 (fn-pwz-span ledger worker token z i j fn-ew-buffer fn-ew-span))
                       :span)))
  :rule-classes nil
  :hints (("Goal" :use fn-pwz-span-is-the-borrowed-bytes)))

(defthm fn-pwz-span-answers-when-its-ends-do
  (implies (and (natp i) (natp j) (< i j)
                (equal (mv-nth 0 (fn-pwz-byte ledger worker token z i fn-ew-buffer)) :byte)
                (equal (mv-nth 0 (fn-pwz-byte ledger worker token z (- j 1) fn-ew-buffer)) :byte))
           (equal (mv-nth 0 (fn-pwz-span ledger worker token z i j fn-ew-buffer fn-ew-span))
                  :span))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwz-span)
           :use ((:instance fn-pwz-span-byte-facts (i i))
                 (:instance fn-pwz-span-byte-facts (i (- j 1)))))))

(defthm fn-pwz-span-refusal-leaves-the-buffer
  (implies (not (equal (mv-nth 0 (fn-pwz-span ledger worker token z i j fn-ew-buffer fn-ew-span))
                       :span))
           (equal (mv-nth 1 (fn-pwz-span ledger worker token z i j fn-ew-buffer fn-ew-span))
                  fn-ew-span))
  :hints (("Goal" :in-theory (enable fn-pwz-span))))

(in-theory (disable fn-pwz-span))

; ---- decoded-coordinate span over fn-pwz-byte-at -------------------------
(defun fn-pwz-span-at (ledger worker token z file eoff elen poff compressed trailer decoded
                              dict-id i j fn-ew-buffer fn-ew-span)
  (declare (xargs :stobjs (fn-ew-buffer fn-ew-span)
                  :guard (and (true-listp z) (true-listp (nth 1 z))
                              (natp i) (natp j) (< i j))))
  (let ((outcome (fn-pwz-outcome ledger worker token z)))
    (if (not (eq outcome :ready)) (mv outcome fn-ew-span)
      (if (and (equal (list file eoff elen poff compressed trailer decoded dict-id)
                      (list (fn-pwz-nth 2 token) (fn-pwz-nth 3 token) (fn-pwz-nth 4 token)
                            (fn-pwz-nth 5 token) (fn-pwz-nth 6 token) (fn-pwz-nth 8 token)
                            (fn-pwz-nth 9 token) (fn-pwz-nth 10 token)))
               (natp decoded) (<= j decoded)
               (natp (fn-pwz-nth 7 token)) (<= (fn-pwz-nth 7 token) i))
          (fn-pwz-span ledger worker token z (- i (fn-pwz-nth 7 token))
                       (- j (fn-pwz-nth 7 token)) fn-ew-buffer fn-ew-span)
        (mv :unavailable fn-ew-span)))))

(local
 (defthm fn-pwz-span-at-facts
   (implies (equal (mv-nth 0 (fn-pwz-byte-at ledger worker token z file eoff elen poff compressed
                                             trailer decoded dict-id i fn-ew-buffer))
                   :byte)
            (and (equal (fn-pwz-outcome ledger worker token z) :ready)
                 (equal (list file eoff elen poff compressed trailer decoded dict-id)
                        (list (fn-pwz-nth 2 token) (fn-pwz-nth 3 token) (fn-pwz-nth 4 token)
                              (fn-pwz-nth 5 token) (fn-pwz-nth 6 token) (fn-pwz-nth 8 token)
                              (fn-pwz-nth 9 token) (fn-pwz-nth 10 token)))
                 (natp i) (natp decoded) (< i decoded)
                 (natp (fn-pwz-nth 7 token)) (<= (fn-pwz-nth 7 token) i)
                 (equal (fn-pwz-byte-at ledger worker token z file eoff elen poff compressed
                                        trailer decoded dict-id i fn-ew-buffer)
                        (fn-pwz-byte ledger worker token z (- i (fn-pwz-nth 7 token))
                                     fn-ew-buffer))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-pwz-byte-at)))))

(local
 (defthm fn-pwz-span-at-byte-at-is-byte
   (implies (and (equal (fn-pwz-outcome ledger worker token z) :ready)
                 (equal (list file eoff elen poff compressed trailer decoded dict-id)
                        (list (fn-pwz-nth 2 token) (fn-pwz-nth 3 token) (fn-pwz-nth 4 token)
                              (fn-pwz-nth 5 token) (fn-pwz-nth 6 token) (fn-pwz-nth 8 token)
                              (fn-pwz-nth 9 token) (fn-pwz-nth 10 token)))
                 (natp i) (natp decoded) (< i decoded)
                 (natp (fn-pwz-nth 7 token)) (<= (fn-pwz-nth 7 token) i))
            (equal (fn-pwz-byte-at ledger worker token z file eoff elen poff compressed
                                   trailer decoded dict-id i fn-ew-buffer)
                   (fn-pwz-byte ledger worker token z (- i (fn-pwz-nth 7 token)) fn-ew-buffer)))
   :hints (("Goal" :in-theory (enable fn-pwz-byte-at)))))

(local
 (defthm fn-pwz-span-at-span-facts
   (implies (equal (mv-nth 0 (fn-pwz-span-at ledger worker token z file eoff elen poff compressed
                                             trailer decoded dict-id i j fn-ew-buffer fn-ew-span))
                   :span)
            (and (equal (fn-pwz-outcome ledger worker token z) :ready)
                 (equal (list file eoff elen poff compressed trailer decoded dict-id)
                        (list (fn-pwz-nth 2 token) (fn-pwz-nth 3 token) (fn-pwz-nth 4 token)
                              (fn-pwz-nth 5 token) (fn-pwz-nth 6 token) (fn-pwz-nth 8 token)
                              (fn-pwz-nth 9 token) (fn-pwz-nth 10 token)))
                 (natp decoded) (<= j decoded)
                 (natp (fn-pwz-nth 7 token)) (<= (fn-pwz-nth 7 token) i)
                 (equal (mv-nth 0 (fn-pwz-span-at ledger worker token z file eoff elen poff
                                                  compressed trailer decoded dict-id i j
                                                  fn-ew-buffer fn-ew-span))
                        (mv-nth 0 (fn-pwz-span ledger worker token z (- i (fn-pwz-nth 7 token))
                                               (- j (fn-pwz-nth 7 token)) fn-ew-buffer fn-ew-span)))
                 (equal (mv-nth 1 (fn-pwz-span-at ledger worker token z file eoff elen poff
                                                  compressed trailer decoded dict-id i j
                                                  fn-ew-buffer fn-ew-span))
                        (mv-nth 1 (fn-pwz-span ledger worker token z (- i (fn-pwz-nth 7 token))
                                               (- j (fn-pwz-nth 7 token)) fn-ew-buffer fn-ew-span)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-pwz-span-at)))))

(defthm fn-pwz-span-at-is-the-borrowed-bytes
  (implies (and (natp i) (natp j) (< i j) (natp k) (< k (- j i))
                (equal (mv-nth 0 (fn-pwz-span-at ledger worker token z file eoff elen poff
                                                 compressed trailer decoded dict-id i j
                                                 fn-ew-buffer fn-ew-span))
                       :span))
           (and (equal (mv-nth 0 (fn-pwz-byte-at ledger worker token z file eoff elen poff
                                                 compressed trailer decoded dict-id (+ i k)
                                                 fn-ew-buffer))
                       :byte)
                (equal (nth k (nth 0 (mv-nth 1 (fn-pwz-span-at ledger worker token z file eoff elen
                                                              poff compressed trailer decoded
                                                              dict-id i j fn-ew-buffer fn-ew-span))))
                       (mv-nth 1 (fn-pwz-byte-at ledger worker token z file eoff elen poff
                                                 compressed trailer decoded dict-id (+ i k)
                                                 fn-ew-buffer)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-pwz-span-at-span-facts
                 (:instance fn-pwz-span-is-the-borrowed-bytes
                            (i (- i (fn-pwz-nth 7 token))) (j (- j (fn-pwz-nth 7 token))))
                 (:instance fn-pwz-span-at-byte-at-is-byte (i (+ i k)))))))

(defthm fn-pwz-span-at-refuses-where-the-octet-refuses
  (implies (and (natp i) (natp j) (< i j) (natp k) (< k (- j i))
                (not (equal (mv-nth 0 (fn-pwz-byte-at ledger worker token z file eoff elen poff
                                                      compressed trailer decoded dict-id (+ i k)
                                                      fn-ew-buffer))
                            :byte)))
           (not (equal (mv-nth 0 (fn-pwz-span-at ledger worker token z file eoff elen poff
                                                 compressed trailer decoded dict-id i j
                                                 fn-ew-buffer fn-ew-span))
                       :span)))
  :rule-classes nil
  :hints (("Goal" :use fn-pwz-span-at-is-the-borrowed-bytes)))

(defthm fn-pwz-span-at-answers-when-its-ends-do
  (implies (and (natp i) (natp j) (< i j)
                (equal (mv-nth 0 (fn-pwz-byte-at ledger worker token z file eoff elen poff
                                                 compressed trailer decoded dict-id i fn-ew-buffer))
                       :byte)
                (equal (mv-nth 0 (fn-pwz-byte-at ledger worker token z file eoff elen poff
                                                 compressed trailer decoded dict-id (- j 1)
                                                 fn-ew-buffer))
                       :byte))
           (equal (mv-nth 0 (fn-pwz-span-at ledger worker token z file eoff elen poff compressed
                                            trailer decoded dict-id i j fn-ew-buffer fn-ew-span))
                  :span))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwz-span-at)
           :use ((:instance fn-pwz-span-at-facts (i i))
                 (:instance fn-pwz-span-at-facts (i (- j 1)))
                 (:instance fn-pwz-span-at-byte-at-is-byte (i i))
                 (:instance fn-pwz-span-at-byte-at-is-byte (i (- j 1)))
                 (:instance fn-pwz-span-answers-when-its-ends-do
                            (i (- i (fn-pwz-nth 7 token))) (j (- j (fn-pwz-nth 7 token))))))))

(defthm fn-pwz-span-at-refusal-leaves-the-buffer
  (implies (not (equal (mv-nth 0 (fn-pwz-span-at ledger worker token z file eoff elen poff
                                                 compressed trailer decoded dict-id i j
                                                 fn-ew-buffer fn-ew-span))
                       :span))
           (equal (mv-nth 1 (fn-pwz-span-at ledger worker token z file eoff elen poff compressed
                                            trailer decoded dict-id i j fn-ew-buffer fn-ew-span))
                  fn-ew-span))
  :hints (("Goal" :in-theory (enable fn-pwz-span-at))))

(in-theory (disable fn-pwz-span-at))

; ---- the job's window (fn-dwj-byte-at's join) ----------------------------
(defun fn-dwj-span-at (ledger worker token file eoff elen poff compressed trailer decoded dict-id
                              i j fn-decoded-job fn-ew-span)
  (declare (xargs :stobjs (fn-decoded-job fn-ew-span)
                  :guard (and (natp i) (natp j) (< i j)) :verify-guards nil))
  (stobj-let ((fn-pww-carry (fn-dwj-carry fn-decoded-job))
              (fn-ew-buffer (fn-dwj-window fn-decoded-job)))
    (word fn-ew-span)
    (let ((z (fn-dwa-controller fn-pww-carry)))
      (if (and (true-listp z) (true-listp (nth 1 z)))
          (fn-pwz-span-at ledger worker token z
                          file eoff elen poff compressed trailer decoded dict-id i j
                          fn-ew-buffer fn-ew-span)
        (mv :stale-decoded-worker fn-ew-span)))
    (mv word fn-ew-span)))

(verify-guards fn-dwj-span-at)

; ---- the cache's decoded span (fn-pwz-cache-byte-at's join) ---------------
(defun fn-pwz-cache-span-at (ledger token file eoff elen poff compressed trailer decoded dict-id
                                    i j fn-ew-buffer fn-ew-span)
  (declare (xargs :stobjs (fn-ew-buffer fn-ew-span)
                  :guard (and (natp i) (natp j) (< i j))
                  :guard-hints (("Goal" :in-theory (enable fn-pwr-span-copy fn-pwz-token-window-length)))))
  (if (and (fn-pwz-cachedp ledger token)
           (equal (list file eoff elen poff compressed trailer decoded dict-id)
                  (list (fn-pwz-nth 2 token) (fn-pwz-nth 3 token) (fn-pwz-nth 4 token)
                        (fn-pwz-nth 5 token) (fn-pwz-nth 6 token) (fn-pwz-nth 8 token)
                        (fn-pwz-nth 9 token) (fn-pwz-nth 10 token)))
           (natp decoded) (<= j decoded)
           (natp (fn-pwz-nth 7 token)) (<= (fn-pwz-nth 7 token) i)
           (<= (- j (fn-pwz-nth 7 token)) (fn-pwz-token-window-length token)))
      (let ((fn-ew-span (fn-pwr-span-copy (- i (fn-pwz-nth 7 token)) (- j i) 0
                                          fn-ew-buffer fn-ew-span)))
        (mv :span fn-ew-span))
    (mv :miss fn-ew-span)))

(local
 (defthm fn-pwz-span-cache-facts
   (implies (equal (mv-nth 0 (fn-pwz-cache-byte-at ledger token file eoff elen poff compressed
                                                   trailer decoded dict-id i fn-ew-buffer))
                   :byte)
            (and (fn-pwz-cachedp ledger token)
                 (equal (list file eoff elen poff compressed trailer decoded dict-id)
                        (list (fn-pwz-nth 2 token) (fn-pwz-nth 3 token) (fn-pwz-nth 4 token)
                              (fn-pwz-nth 5 token) (fn-pwz-nth 6 token) (fn-pwz-nth 8 token)
                              (fn-pwz-nth 9 token) (fn-pwz-nth 10 token)))
                 (natp i) (natp decoded) (< i decoded)
                 (natp (fn-pwz-nth 7 token)) (<= (fn-pwz-nth 7 token) i)
                 (< (- i (fn-pwz-nth 7 token)) (fn-pwz-token-window-length token))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-pwz-cache-byte-at)))))

(local
 (defthm fn-pwz-span-cache-byte-is-byte
   (implies (and (fn-pwz-cachedp ledger token)
                 (equal (list file eoff elen poff compressed trailer decoded dict-id)
                        (list (fn-pwz-nth 2 token) (fn-pwz-nth 3 token) (fn-pwz-nth 4 token)
                              (fn-pwz-nth 5 token) (fn-pwz-nth 6 token) (fn-pwz-nth 8 token)
                              (fn-pwz-nth 9 token) (fn-pwz-nth 10 token)))
                 (natp i) (natp decoded) (< i decoded)
                 (natp (fn-pwz-nth 7 token)) (<= (fn-pwz-nth 7 token) i)
                 (< (- i (fn-pwz-nth 7 token)) (fn-pwz-token-window-length token)))
            (equal (fn-pwz-cache-byte-at ledger token file eoff elen poff compressed trailer
                                         decoded dict-id i fn-ew-buffer)
                   (mv :byte (nth (- i (fn-pwz-nth 7 token)) (nth 0 fn-ew-buffer)))))
   :hints (("Goal" :in-theory (enable fn-pwz-cache-byte-at fn-ew-bytesi)))))

(defthm fn-pwz-cache-span-at-is-the-cached-bytes
  (implies (and (natp i) (natp j) (< i j) (natp k) (< k (- j i))
                (equal (mv-nth 0 (fn-pwz-cache-span-at ledger token file eoff elen poff compressed
                                                       trailer decoded dict-id i j
                                                       fn-ew-buffer fn-ew-span))
                       :span))
           (and (equal (mv-nth 0 (fn-pwz-cache-byte-at ledger token file eoff elen poff compressed
                                                       trailer decoded dict-id (+ i k)
                                                       fn-ew-buffer))
                       :byte)
                (equal (nth k (nth 0 (mv-nth 1 (fn-pwz-cache-span-at ledger token file eoff elen
                                                                    poff compressed trailer
                                                                    decoded dict-id i j
                                                                    fn-ew-buffer fn-ew-span))))
                       (mv-nth 1 (fn-pwz-cache-byte-at ledger token file eoff elen poff compressed
                                                       trailer decoded dict-id (+ i k)
                                                       fn-ew-buffer)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwz-cache-span-at)
           :use ((:instance fn-pwr-span-copy-exact-output-and-effects
                            (src (- i (fn-pwz-nth 7 token))) (count (- j i)) (dst 0) (j k))
                 (:instance fn-pwz-span-cache-byte-is-byte (i (+ i k)))))))

(defthm fn-pwz-cache-span-at-misses-where-the-octet-does
  (implies (and (natp i) (natp j) (< i j) (natp k) (< k (- j i))
                (not (equal (mv-nth 0 (fn-pwz-cache-byte-at ledger token file eoff elen poff
                                                            compressed trailer decoded dict-id
                                                            (+ i k) fn-ew-buffer))
                            :byte)))
           (not (equal (mv-nth 0 (fn-pwz-cache-span-at ledger token file eoff elen poff compressed
                                                       trailer decoded dict-id i j
                                                       fn-ew-buffer fn-ew-span))
                       :span)))
  :rule-classes nil
  :hints (("Goal" :use fn-pwz-cache-span-at-is-the-cached-bytes)))

(defthm fn-pwz-cache-span-at-answers-when-its-ends-do
  (implies (and (natp i) (natp j) (< i j)
                (equal (mv-nth 0 (fn-pwz-cache-byte-at ledger token file eoff elen poff compressed
                                                       trailer decoded dict-id i fn-ew-buffer))
                       :byte)
                (equal (mv-nth 0 (fn-pwz-cache-byte-at ledger token file eoff elen poff compressed
                                                       trailer decoded dict-id (- j 1)
                                                       fn-ew-buffer))
                       :byte))
           (equal (mv-nth 0 (fn-pwz-cache-span-at ledger token file eoff elen poff compressed
                                                  trailer decoded dict-id i j fn-ew-buffer
                                                  fn-ew-span))
                  :span))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwz-cache-span-at)
           :use ((:instance fn-pwz-span-cache-facts (i i))
                 (:instance fn-pwz-span-cache-facts (i (- j 1)))))))

(defthm fn-pwz-cache-span-at-refusal-leaves-the-buffer
  (implies (not (equal (mv-nth 0 (fn-pwz-cache-span-at ledger token file eoff elen poff compressed
                                                       trailer decoded dict-id i j fn-ew-buffer
                                                       fn-ew-span))
                       :span))
           (equal (mv-nth 1 (fn-pwz-cache-span-at ledger token file eoff elen poff compressed
                                                  trailer decoded dict-id i j fn-ew-buffer
                                                  fn-ew-span))
                  fn-ew-span))
  :hints (("Goal" :in-theory (enable fn-pwz-cache-span-at))))

(in-theory (disable fn-pwz-cache-span-at))

; KEYSTONE at the job's window: a decoded span is the job's scalar borrows
; (fn-dwj-byte-at), octet by octet, and refuses wherever they refuse.
(defthm fn-dwj-span-at-is-the-borrowed-bytes
  (implies (and (natp i) (natp j) (< i j) (natp k) (< k (- j i))
                (equal (mv-nth 0 (fn-dwj-span-at ledger worker token file eoff elen poff compressed
                                                 trailer decoded dict-id i j fn-decoded-job
                                                 fn-ew-span))
                       :span))
           (and (equal (mv-nth 0 (fn-dwj-byte-at ledger worker token file eoff elen poff compressed
                                                 trailer decoded dict-id (+ i k) fn-decoded-job))
                       :byte)
                (equal (nth k (nth 0 (mv-nth 1 (fn-dwj-span-at ledger worker token file eoff elen
                                                              poff compressed trailer decoded
                                                              dict-id i j fn-decoded-job
                                                              fn-ew-span))))
                       (mv-nth 1 (fn-dwj-byte-at ledger worker token file eoff elen poff compressed
                                                 trailer decoded dict-id (+ i k) fn-decoded-job)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-dwj-span-at fn-dwj-byte-at)
           :use ((:instance fn-pwz-span-at-is-the-borrowed-bytes
                            (z (fn-dwa-controller (nth 0 fn-decoded-job)))
                            (fn-ew-buffer (nth 7 fn-decoded-job)))))))
