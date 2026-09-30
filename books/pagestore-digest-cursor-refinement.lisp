;; Proof vocabulary only: never execute list spans or tree denotation.
(in-package "ACL2")
(include-book "pagestore-digest-cursor")
(local (include-book "arithmetic/top" :dir :system))

(defun-nx pgs-dcr-span (start end msg)
  (fn-b3-firstn (* 8 (- (nfix end) (nfix start)))
               (fn-b3-nthcdrx (* 8 (nfix start)) msg)))

(defthm pgs-dcr-span-length
  (implies (and (natp start) (natp end) (<= start end)
                (<= (* 8 end) (len msg)))
           (equal (len (pgs-dcr-span start end msg)) (* 8 (- end start))))
  :hints (("Goal" :in-theory (e/d (pgs-dcr-span) (fn-b3-firstn fn-b3-nthcdrx)))))

(defun-nx pgs-dcr-parent (leftcv rightcv)
  (fn-b3-output *fn-b3-iv* (append leftcv rightcv) 0 64 *fn-b3-parent*))

(defun-nx pgs-dcr-fold (depth out msg pgs-digest)
  (declare (xargs :stobjs pgs-digest :measure (nfix depth) :verify-guards nil))
  (if (zp depth) out
    (let* ((index (- depth 1))
           (frame (pgs-dc-framesi index pgs-digest))
           (parent
             (if (eq (fn-b3-nthx 0 frame) :left)
                 (pgs-dcr-parent (fn-b3-output-cv out)
                   (fn-b3-output-cv
                     (fn-b3-node *fn-b3-iv*
                       (pgs-dcr-span (fn-b3-nthx 1 frame) (fn-b3-nthx 2 frame) msg)
                       (fn-b3-nthx 3 frame) 0)))
               (pgs-dcr-parent (fn-b3-nthx 4 frame) (fn-b3-output-cv out)))))
      (pgs-dcr-fold index parent msg pgs-digest))))

(defun-nx pgs-dcr-current (msg pgs-digest)
  (declare (xargs :stobjs pgs-digest :verify-guards nil))
  (case (pgs-dc-mode pgs-digest)
    ((:node :split)
     (fn-b3-node *fn-b3-iv*
       (pgs-dcr-span (pgs-dc-start pgs-digest) (pgs-dc-end pgs-digest) msg)
       (pgs-dc-counter pgs-digest) 0))
    (:chunk
     (fn-b3-chunk (pgs-dc-cv pgs-digest)
       (pgs-dcr-span (pgs-dc-pos pgs-digest) (pgs-dc-end pgs-digest) msg)
       (pgs-dc-counter pgs-digest) 0
       (equal (pgs-dc-pos pgs-digest) (pgs-dc-start pgs-digest))))
    (otherwise (pgs-dc-output pgs-digest))))

(defun-nx pgs-dcr-denote (msg pgs-digest)
  (declare (xargs :stobjs pgs-digest :verify-guards nil))
  (pgs-dcr-fold (pgs-dc-depth pgs-digest)
                (pgs-dcr-current msg pgs-digest) msg pgs-digest))

(defthm pgs-dcr-node-model-base
  (implies (and (natp start) (natp end) (<= start end)
                (<= (* 8 end) (len msg)) (<= (- end start) 128))
           (equal (fn-b3-node *fn-b3-iv* (pgs-dcr-span start end msg) counter 0)
                  (fn-b3-chunk *fn-b3-iv* (pgs-dcr-span start end msg) counter 0 t)))
  :hints (("Goal" :expand ((fn-b3-node *fn-b3-iv* (pgs-dcr-span start end msg) counter 0))
                  :in-theory (disable pgs-dcr-span fn-b3-chunk))))

(defthm pgs-dcr-node-entry-keeps-current-denotation
  (implies (and (equal (pgs-dc-mode pgs-digest) :node)
                (natp (pgs-dc-start pgs-digest))
                (natp (pgs-dc-end pgs-digest))
                (<= (pgs-dc-start pgs-digest) (pgs-dc-end pgs-digest))
                (<= (* 8 (pgs-dc-end pgs-digest)) (len msg))
                (<= (- (pgs-dc-end pgs-digest) (pgs-dc-start pgs-digest)) 128))
           (equal (pgs-dcr-current msg (mv-nth 1 (pgs-dc-step nil pgs-digest)))
                  (pgs-dcr-current msg pgs-digest)))
  :hints (("Goal" :in-theory (e/d (pgs-dcr-current pgs-dc-step)
                                   (nth update-nth pgs-dcr-span fn-b3-chunk fn-b3-node))
                  :do-not-induct t)))


(defthm pgs-dcr-node-step-keeps-current-denotation
  (implies (and (equal (pgs-dc-mode pgs-digest) :node)
                (natp (pgs-dc-start pgs-digest))
                (natp (pgs-dc-end pgs-digest))
                (<= (pgs-dc-start pgs-digest) (pgs-dc-end pgs-digest))
                (<= (* 8 (pgs-dc-end pgs-digest)) (len msg)))
           (equal (pgs-dcr-current msg (mv-nth 1 (pgs-dc-step nil pgs-digest)))
                  (pgs-dcr-current msg pgs-digest)))
  :hints (("Goal" :in-theory (e/d (pgs-dcr-current pgs-dc-step)
                                   (nth update-nth pgs-dcr-span fn-b3-chunk fn-b3-node))
                  :do-not-induct t)))

(defthm pgs-dcr-fold-of-scalar-update
  (implies (and (natp k) (not (equal k *pgs-dc-framesi*)))
           (equal (pgs-dcr-fold depth out msg (update-nth k value pgs-digest))
                  (pgs-dcr-fold depth out msg pgs-digest)))
  :hints (("Goal" :induct (pgs-dcr-fold depth out msg pgs-digest)
                  :expand ((pgs-dcr-fold depth out msg (update-nth k value pgs-digest)))
                  :in-theory (e/d (pgs-dcr-fold pgs-dc-framesi)
                                   (nth update-nth pgs-dcr-parent pgs-dcr-span
                                        fn-b3-node fn-b3-chunk fn-b3-nthx fn-b3-output-cv)))))

(defthm pgs-dcr-node-step-depth-unfolds
  (implies (equal (pgs-dc-mode pgs-digest) :node)
           (equal (pgs-dc-depth (mv-nth 1 (pgs-dc-step nil pgs-digest)))
                  (pgs-dc-depth pgs-digest)))
  :hints (("Goal" :in-theory (e/d (pgs-dc-step)
                                   (nth update-nth)))))

(defthm pgs-dcr-node-step-fold-unfolds
  (implies (equal (pgs-dc-mode pgs-digest) :node)
           (equal (pgs-dcr-fold depth out msg (mv-nth 1 (pgs-dc-step nil pgs-digest)))
                  (pgs-dcr-fold depth out msg pgs-digest)))
  :hints (("Goal" :in-theory (e/d (pgs-dc-step)
                                   (nth update-nth pgs-dcr-fold)))))

(defthm pgs-dcr-node-step-preserves-denotation
  (implies (and (equal (pgs-dc-mode pgs-digest) :node)
                (natp (pgs-dc-start pgs-digest))
                (natp (pgs-dc-end pgs-digest))
                (<= (pgs-dc-start pgs-digest) (pgs-dc-end pgs-digest))
                (<= (* 8 (pgs-dc-end pgs-digest)) (len msg)))
           (equal (pgs-dcr-denote msg (mv-nth 1 (pgs-dc-step nil pgs-digest)))
                  (pgs-dcr-denote msg pgs-digest)))
  :hints (("Goal" :in-theory (e/d (pgs-dcr-denote)
                                   (pgs-dcr-current pgs-dc-step pgs-dcr-fold)))))

(local
 (defthm pgs-dcr-nthx-of-shift
   (equal (fn-b3-nthx i (if (consp words) (cdr words) nil))
          (fn-b3-nthx (+ 1 (nfix i)) words))
   :hints (("Goal" :in-theory (enable fn-b3-nthx)
                   :do-not-induct t))))

(local
 (defthm pgs-dcr-nthx-atom
   (implies (not (consp words)) (equal (fn-b3-nthx i words) 0))
   :hints (("Goal" :in-theory (enable fn-b3-nthx)))))

(local
 (defthm pgs-dcr-nthx-cdr
   (equal (fn-b3-nthx i (cdr words)) (fn-b3-nthx (+ 1 (nfix i)) words))
   :hints (("Goal" :in-theory (enable fn-b3-nthx) :do-not-induct t))))

(local
 (defthm pgs-dcr-cv8-is-pad-words
   (equal (fn-b3-cv8 cv) (pgs-dc-pad-words 8 cv))
   :hints (("Goal" :expand ((:free (words) (fn-b3-nthx 0 words)) (:free (words) (fn-b3-nthx 1 words)) (:free (words) (fn-b3-nthx 2 words)) (:free (words) (fn-b3-nthx 3 words)) (:free (words) (fn-b3-nthx 4 words)) (:free (words) (fn-b3-nthx 5 words)) (:free (words) (fn-b3-nthx 6 words)) (:free (words) (fn-b3-nthx 7 words)) (:free (words) (pgs-dc-pad-words 0 words)) (:free (words) (pgs-dc-pad-words 1 words)) (:free (words) (pgs-dc-pad-words 2 words)) (:free (words) (pgs-dc-pad-words 3 words)) (:free (words) (pgs-dc-pad-words 4 words)) (:free (words) (pgs-dc-pad-words 5 words)) (:free (words) (pgs-dc-pad-words 6 words)) (:free (words) (pgs-dc-pad-words 7 words)) (:free (words) (pgs-dc-pad-words 8 words)))
                   :in-theory (e/d (fn-b3-cv8 pgs-dc-pad-words)
                                    (fn-b3-nthx pgs-dcr-nthx-cdr pgs-dcr-nthx-of-shift))))))

(defthm pgs-dcr-cv8-of-eight-words
  (implies (and (true-listp cv) (equal (len cv) 8))
           (equal (fn-b3-cv8 cv) cv))
  :hints (("Goal" :in-theory (disable fn-b3-cv8 pgs-dc-pad-words))))

(local
 (defthm pgs-dcr-nthcdrx-of-firstn
   (equal (fn-b3-nthcdrx k (fn-b3-firstn n msg))
          (fn-b3-firstn (- (nfix n) (nfix k)) (fn-b3-nthcdrx k msg)))
   :hints (("Goal" :induct (list (fn-b3-nthcdrx k msg) (fn-b3-firstn n msg))
                   :in-theory (enable fn-b3-nthcdrx fn-b3-firstn)))))

(local
 (defthm pgs-dcr-nthcdrx-of-nthcdrx
   (equal (fn-b3-nthcdrx k (fn-b3-nthcdrx p msg))
          (fn-b3-nthcdrx (+ (nfix k) (nfix p)) msg))
   :hints (("Goal" :induct (fn-b3-nthcdrx p msg)
                   :in-theory (enable fn-b3-nthcdrx)))))

(defthm pgs-dcr-span-tail
  (implies (and (natp pos) (natp end) (<= (+ pos 8) end))
           (equal (fn-b3-nthcdrx 64 (pgs-dcr-span pos end msg))
                  (pgs-dcr-span (+ pos 8) end msg)))
  :hints (("Goal" :in-theory (e/d (pgs-dcr-span)
                                   (fn-b3-nthcdrx fn-b3-firstn)))))

(defthm pgs-dcr-chunk-model-step
  (implies (and (natp pos) (natp end) (< (+ pos 8) end)
                (<= (* 8 end) (len msg)))
           (equal (fn-b3-chunk cv (pgs-dcr-span pos end msg) counter 0 startp)
                  (fn-b3-chunk
                    (fn-b3-compress cv (fn-b3-words 16 (pgs-dcr-span pos end msg))
                                    counter 64 (if startp 1 0))
                    (pgs-dcr-span (+ pos 8) end msg) counter 0 nil)))
  :hints (("Goal" :expand ((fn-b3-chunk cv (pgs-dcr-span pos end msg) counter 0 startp))
                  :in-theory (disable pgs-dcr-span fn-b3-chunk fn-b3-compress))))

(defthm pgs-dcr-span-empty
  (equal (pgs-dcr-span pos pos msg) nil)
  :hints (("Goal" :in-theory (enable pgs-dcr-span fn-b3-firstn))))

(defthm pgs-dcr-chunk-model-last
  (implies (and (natp pos) (natp end) (<= pos end) (<= (- end pos) 8)
                (<= (* 8 end) (len msg)) (true-listp cv) (equal (len cv) 8))
           (equal (fn-b3-chunk cv (pgs-dcr-span pos end msg) counter 0 startp)
                  (fn-b3-output cv (fn-b3-words 16 (pgs-dcr-span pos end msg))
                                counter (* 8 (- end pos))
                                (logior (if startp 1 0) 2))))
  :hints (("Goal" :expand ((fn-b3-chunk cv (pgs-dcr-span pos end msg) counter 0 startp))
                  :in-theory (e/d (fn-b3-output)
                                   (pgs-dcr-span fn-b3-chunk fn-b3-compress fn-b3-cv8)))))

(local
 (defthm pgs-dcr-advanced-pos-not-start
   (implies (and (rationalp start) (rationalp pos) (<= start pos))
            (not (equal (+ 8 pos) start)))))

(defthm pgs-dcr-chunk-step-keeps-current-denotation
  (implies (and (equal (pgs-dc-mode pgs-digest) :chunk)
                (natp (pgs-dc-start pgs-digest))
                (natp (pgs-dc-pos pgs-digest))
                (natp (pgs-dc-end pgs-digest))
                (<= (pgs-dc-start pgs-digest) (pgs-dc-pos pgs-digest))
                (<= (pgs-dc-pos pgs-digest) (pgs-dc-end pgs-digest))
                (<= (* 8 (pgs-dc-end pgs-digest)) (len msg))
                (true-listp (pgs-dc-cv pgs-digest))
                (equal (len (pgs-dc-cv pgs-digest)) 8)
                (equal block (fn-b3-words 16
                              (pgs-dcr-span (pgs-dc-pos pgs-digest)
                                             (pgs-dc-end pgs-digest) msg))))
           (equal (pgs-dcr-current msg (mv-nth 1 (pgs-dc-step block pgs-digest)))
                  (pgs-dcr-current msg pgs-digest)))
  :hints (("Goal" :in-theory (e/d (pgs-dcr-current pgs-dc-step fn-b3-output-cv fn-b3-output)
                                   (nth update-nth pgs-dcr-span fn-b3-node fn-b3-chunk
                                        fn-b3-compress pgs-dc-pad-block fn-b3-cv8))
                  :expand ((fn-b3-chunk (pgs-dc-cv pgs-digest)
                            (pgs-dcr-span (pgs-dc-pos pgs-digest) (pgs-dc-end pgs-digest) msg)
                            (pgs-dc-counter pgs-digest) 0
                            (equal (pgs-dc-pos pgs-digest) (pgs-dc-start pgs-digest))))
                  :do-not-induct t)))

(defthm pgs-dcr-chunk-step-depth-unfolds
  (implies (equal (pgs-dc-mode pgs-digest) :chunk)
           (equal (pgs-dc-depth (mv-nth 1 (pgs-dc-step block pgs-digest)))
                  (pgs-dc-depth pgs-digest)))
  :hints (("Goal" :in-theory (e/d (pgs-dc-step)
                                   (nth update-nth)))))

(defthm pgs-dcr-chunk-step-fold-unfolds
  (implies (equal (pgs-dc-mode pgs-digest) :chunk)
           (equal (pgs-dcr-fold depth out msg (mv-nth 1 (pgs-dc-step block pgs-digest)))
                  (pgs-dcr-fold depth out msg pgs-digest)))
  :hints (("Goal" :in-theory (e/d (pgs-dc-step)
                                   (nth update-nth pgs-dcr-fold)))))


(defthm pgs-dcr-chunk-step-preserves-denotation
  (implies (and (equal (pgs-dc-mode pgs-digest) :chunk)
                (natp (pgs-dc-start pgs-digest))
                (natp (pgs-dc-pos pgs-digest))
                (natp (pgs-dc-end pgs-digest))
                (<= (pgs-dc-start pgs-digest) (pgs-dc-pos pgs-digest))
                (<= (pgs-dc-pos pgs-digest) (pgs-dc-end pgs-digest))
                (<= (* 8 (pgs-dc-end pgs-digest)) (len msg))
                (true-listp (pgs-dc-cv pgs-digest))
                (equal (len (pgs-dc-cv pgs-digest)) 8)
                (equal block (fn-b3-words 16
                              (pgs-dcr-span (pgs-dc-pos pgs-digest)
                                             (pgs-dc-end pgs-digest) msg))))
           (equal (pgs-dcr-denote msg (mv-nth 1 (pgs-dc-step block pgs-digest)))
                  (pgs-dcr-denote msg pgs-digest)))
  :hints (("Goal" :in-theory (e/d (pgs-dcr-denote)
                                   (pgs-dcr-current pgs-dc-step pgs-dcr-fold)))))

(defthm pgs-dcr-fold-of-frame-update-prefix
  (implies (and (natp index) (<= (nfix depth) index))
           (equal (pgs-dcr-fold depth out msg
                               (update-pgs-dc-framesi index frame pgs-digest))
                  (pgs-dcr-fold depth out msg pgs-digest)))
  :hints (("Goal" :induct (pgs-dcr-fold depth out msg pgs-digest)
                  :expand ((pgs-dcr-fold depth out msg
                               (update-pgs-dc-framesi index frame pgs-digest))
                           (pgs-dcr-fold depth out msg
                             (update-nth *pgs-dc-framesi*
                               (update-nth index frame (nth *pgs-dc-framesi* pgs-digest))
                               pgs-digest)))
                  :in-theory (e/d (pgs-dcr-fold pgs-dc-framesi update-pgs-dc-framesi)
                                   (nth update-nth pgs-dcr-parent pgs-dcr-span
                                        fn-b3-node fn-b3-nthx fn-b3-output-cv)))))

(defthm pgs-dcr-return-empty-preserves-denotation
  (implies (and (equal (pgs-dc-mode pgs-digest) :return)
                (equal (pgs-dc-depth pgs-digest) 0))
           (equal (pgs-dcr-denote msg (mv-nth 1 (pgs-dc-step nil pgs-digest)))
                  (pgs-dcr-denote msg pgs-digest)))
  :hints (("Goal" :in-theory (e/d (pgs-dcr-denote pgs-dcr-current pgs-dc-step)
                                   (nth update-nth pgs-dcr-fold)))))

(defthm pgs-dcr-root-preserves-denotation
  (implies (equal (pgs-dc-mode pgs-digest) :root)
           (equal (pgs-dcr-denote msg (mv-nth 1 (pgs-dc-step nil pgs-digest)))
                  (pgs-dcr-denote msg pgs-digest)))
  :hints (("Goal" :in-theory (e/d (pgs-dcr-denote pgs-dcr-current pgs-dc-step)
                                   (nth update-nth pgs-dcr-fold)))))

(defthm pgs-dcr-root-result-is-denotation-root
  (implies (and (equal (pgs-dc-mode pgs-digest) :root)
                (equal (pgs-dc-depth pgs-digest) 0))
           (equal (pgs-dc-result (mv-nth 1 (pgs-dc-step nil pgs-digest)))
                  (pgs-octets-be-nat
                    (fn-b3-output-root (pgs-dcr-denote msg pgs-digest)))))
  :hints (("Goal" :in-theory (e/d (pgs-dcr-denote pgs-dcr-current pgs-dc-step
                                                  pgs-dc-result pgs-dcr-fold)
                                   (nth update-nth fn-b3-output-root pgs-octets-be-nat)))))

(defthm pgs-dcr-return-right-preserves-denotation
  (implies (and (equal (pgs-dc-mode pgs-digest) :return)
                (posp (pgs-dc-depth pgs-digest))
                (<= (pgs-dc-depth pgs-digest) 64)
                (not (equal (fn-b3-nthx 0
                             (pgs-dc-framesi (- (pgs-dc-depth pgs-digest) 1) pgs-digest))
                            :left))
                (true-listp (fn-b3-nthx 4
                             (pgs-dc-framesi (- (pgs-dc-depth pgs-digest) 1) pgs-digest)))
                (equal (len (fn-b3-nthx 4
                             (pgs-dc-framesi (- (pgs-dc-depth pgs-digest) 1) pgs-digest))) 8))
           (equal (pgs-dcr-denote msg (mv-nth 1 (pgs-dc-step nil pgs-digest)))
                  (pgs-dcr-denote msg pgs-digest)))
  :hints (("Goal" :expand ((pgs-dcr-fold (pgs-dc-depth pgs-digest)
                             (pgs-dc-output pgs-digest) msg pgs-digest)
                          (pgs-dcr-fold (nth *pgs-dc-depth* pgs-digest)
                             (nth *pgs-dc-output* pgs-digest) msg pgs-digest))
                  :in-theory (e/d (pgs-dcr-denote pgs-dcr-current pgs-dc-step pgs-dcr-parent)
                                   (nth update-nth pgs-dcr-fold fn-b3-cv8 fn-b3-output
                                        fn-b3-output-cv fn-b3-node pgs-dcr-span))
                  :do-not-induct t)))

(defthm pgs-dcr-fold-of-frame-update-prefix-raw
  (implies (and (natp index) (<= (nfix depth) index))
           (equal (pgs-dcr-fold depth out msg
                     (update-nth *pgs-dc-framesi*
                       (update-nth index frame (nth *pgs-dc-framesi* pgs-digest))
                       pgs-digest))
                  (pgs-dcr-fold depth out msg pgs-digest)))
  :hints (("Goal" :use pgs-dcr-fold-of-frame-update-prefix
                  :in-theory (e/d (update-pgs-dc-framesi)
                                   (pgs-dcr-fold pgs-dcr-fold-of-frame-update-prefix)))))

(defthm pgs-dcr-span-nfix-unfolds
  (equal (pgs-dcr-span (nfix start) (nfix end) msg)
         (pgs-dcr-span start end msg))
  :hints (("Goal" :in-theory (enable pgs-dcr-span))))

(defthm pgs-dcr-return-left-preserves-denotation
  (implies (and (equal (pgs-dc-mode pgs-digest) :return)
                (posp (pgs-dc-depth pgs-digest))
                (<= (pgs-dc-depth pgs-digest) 64)
                (equal (fn-b3-nthx 0
                             (pgs-dc-framesi (- (pgs-dc-depth pgs-digest) 1) pgs-digest)) :left)
                (natp (fn-b3-nthx 3
                             (pgs-dc-framesi (- (pgs-dc-depth pgs-digest) 1) pgs-digest))))
           (equal (pgs-dcr-denote msg (mv-nth 1 (pgs-dc-step nil pgs-digest)))
                  (pgs-dcr-denote msg pgs-digest)))
  :hints (("Goal" :expand ((:free (x) (fn-b3-firstn 0 x))
                          (pgs-dcr-fold (pgs-dc-depth pgs-digest)
                             (pgs-dc-output pgs-digest) msg pgs-digest)
                          (:free (out cursor)
                            (pgs-dcr-fold (nth *pgs-dc-depth* pgs-digest) out msg cursor)))
                  :in-theory (e/d (pgs-dcr-denote pgs-dcr-current pgs-dc-step pgs-dcr-parent pgs-dcr-span)
                                   (nth update-nth pgs-dcr-fold fn-b3-cv8 fn-b3-output
                                        fn-b3-output-cv fn-b3-node fn-b3-firstn fn-b3-nthcdrx))
                  :do-not-induct t)))

(defthm pgs-dcr-split-search-preserves-denotation
  (implies (and (equal (pgs-dc-mode pgs-digest) :split)
                (posp (pgs-dc-power pgs-digest))
                (< (* 256 (pgs-dc-power pgs-digest))
                   (- (pgs-dc-end pgs-digest) (pgs-dc-start pgs-digest))))
           (equal (pgs-dcr-denote msg (mv-nth 1 (pgs-dc-step nil pgs-digest)))
                  (pgs-dcr-denote msg pgs-digest)))
  :hints (("Goal" :in-theory (e/d (pgs-dcr-denote pgs-dcr-current pgs-dc-step)
                                   (nth update-nth pgs-dcr-fold fn-b3-node pgs-dcr-span)))))

(local
 (defthm pgs-dcr-firstn-of-firstn
   (implies (and (natp k) (natp n) (<= k n))
            (equal (fn-b3-firstn k (fn-b3-firstn n msg))
                   (fn-b3-firstn k msg)))
   :hints (("Goal" :induct (list (fn-b3-firstn k msg) (fn-b3-firstn n msg))
                   :in-theory (enable fn-b3-firstn)))))

(defthm pgs-dcr-span-left
  (implies (and (natp start) (natp split) (natp end)
                (<= start split) (<= split end))
           (equal (fn-b3-firstn (* 8 (- split start)) (pgs-dcr-span start end msg))
                  (pgs-dcr-span start split msg)))
  :hints (("Goal" :in-theory (e/d (pgs-dcr-span) (fn-b3-firstn fn-b3-nthcdrx)))))

(defthm pgs-dcr-span-right
  (implies (and (natp start) (natp split) (natp end)
                (<= start split) (<= split end))
           (equal (fn-b3-nthcdrx (* 8 (- split start)) (pgs-dcr-span start end msg))
                  (pgs-dcr-span split end msg)))
  :hints (("Goal" :in-theory (e/d (pgs-dcr-span) (fn-b3-firstn fn-b3-nthcdrx)))))

(defthm pgs-dcr-node-model-split
  (implies (and (natp start) (natp end) (posp power) (natp counter)
                (< (* 128 power) (- end start))
                (<= (* 8 end) (len msg))
                (equal (fn-b3-left-chunks 1 (* 8 (- end start))) power))
           (equal (fn-b3-node *fn-b3-iv* (pgs-dcr-span start end msg) counter 0)
                  (pgs-dcr-parent
                    (fn-b3-output-cv
                      (fn-b3-node *fn-b3-iv* (pgs-dcr-span start (+ start (* 128 power)) msg) counter 0))
                    (fn-b3-output-cv
                      (fn-b3-node *fn-b3-iv* (pgs-dcr-span (+ start (* 128 power)) end msg)
                                  (+ counter power) 0)))))
  :hints (("Goal" :expand ((fn-b3-node *fn-b3-iv* (pgs-dcr-span start end msg) counter 0))
                  :use ((:instance pgs-dcr-span-left (split (+ start (* 128 power))))
                        (:instance pgs-dcr-span-right (split (+ start (* 128 power)))))
                  :in-theory (e/d (pgs-dcr-parent)
                                   (pgs-dcr-span fn-b3-node fn-b3-output-cv fn-b3-output fn-b3-left-chunks pgs-dcr-span-left
                                        pgs-dcr-span-right pgs-dcr-chunk-model-step))
                  :do-not-induct t)))

(defthm pgs-dcr-split-push-preserves-denotation
  (implies (and (equal (pgs-dc-mode pgs-digest) :split)
                (natp (pgs-dc-start pgs-digest))
                (natp (pgs-dc-end pgs-digest))
                (natp (pgs-dc-counter pgs-digest))
                (natp (pgs-dc-depth pgs-digest))
                (< (pgs-dc-depth pgs-digest) 64)
                (posp (pgs-dc-power pgs-digest))
                (< (* 128 (pgs-dc-power pgs-digest))
                   (- (pgs-dc-end pgs-digest) (pgs-dc-start pgs-digest)))
                (<= (- (pgs-dc-end pgs-digest) (pgs-dc-start pgs-digest))
                    (* 256 (pgs-dc-power pgs-digest)))
                (<= (* 8 (pgs-dc-end pgs-digest)) (len msg))
                (equal (fn-b3-left-chunks 1
                           (* 8 (- (pgs-dc-end pgs-digest) (pgs-dc-start pgs-digest))))
                       (pgs-dc-power pgs-digest)))
           (equal (pgs-dcr-denote msg (mv-nth 1 (pgs-dc-step nil pgs-digest)))
                  (pgs-dcr-denote msg pgs-digest)))
  :hints (("Goal" :expand ((:free (out cursor)
                            (pgs-dcr-fold (+ 1 (nth *pgs-dc-depth* pgs-digest)) out msg cursor)))
                  :use ((:instance pgs-dcr-node-model-split
                          (start (pgs-dc-start pgs-digest))
                          (end (pgs-dc-end pgs-digest))
                          (counter (pgs-dc-counter pgs-digest))
                          (power (pgs-dc-power pgs-digest))))
                  :in-theory (e/d (pgs-dcr-denote pgs-dcr-current pgs-dc-step pgs-dcr-parent)
                                   (nth update-nth pgs-dcr-fold fn-b3-cv8 fn-b3-output
                                        fn-b3-output-cv fn-b3-node pgs-dcr-span
                                        fn-b3-left-chunks pgs-dcr-node-model-split))
                  :do-not-induct t)))

(local
 (defthm pgs-dcr-left-chunks-search-step
   (implies (and (posp power) (natp nwords) (< (* 256 power) nwords))
            (equal (fn-b3-left-chunks (* 2 power) (* 8 nwords))
                   (fn-b3-left-chunks power (* 8 nwords))))
   :hints (("Goal" :expand ((fn-b3-left-chunks power (* 8 nwords)))
                   :in-theory (disable fn-b3-left-chunks)))))

(defthm pgs-dcr-split-search-preserves-carry
  (implies (and (equal (pgs-dc-mode pgs-digest) :split)
                (posp (pgs-dc-power pgs-digest))
                (natp (pgs-dc-start pgs-digest))
                (natp (pgs-dc-end pgs-digest))
                (< (* 256 (pgs-dc-power pgs-digest))
                   (- (pgs-dc-end pgs-digest) (pgs-dc-start pgs-digest))))
           (equal
             (fn-b3-left-chunks
               (pgs-dc-power (mv-nth 1 (pgs-dc-step nil pgs-digest)))
               (* 8 (- (pgs-dc-end pgs-digest) (pgs-dc-start pgs-digest))))
             (fn-b3-left-chunks (pgs-dc-power pgs-digest)
               (* 8 (- (pgs-dc-end pgs-digest) (pgs-dc-start pgs-digest))))))
  :hints (("Goal" :use ((:instance pgs-dcr-left-chunks-search-step
                           (power (pgs-dc-power pgs-digest))
                           (nwords (- (pgs-dc-end pgs-digest) (pgs-dc-start pgs-digest)))))
                  :in-theory (e/d (pgs-dc-step)
                                   (nth update-nth fn-b3-left-chunks
                                        pgs-dcr-left-chunks-search-step)))))

(defthm pgs-dcr-split-finished-carry-is-power
  (implies (and (posp power) (natp nwords) (<= nwords (* 256 power))
                (equal (fn-b3-left-chunks power (* 8 nwords))
                       (fn-b3-left-chunks 1 (* 8 nwords))))
           (equal (fn-b3-left-chunks 1 (* 8 nwords)) power))
  :hints (("Goal" :expand ((fn-b3-left-chunks power (* 8 nwords)))
                  :in-theory (disable fn-b3-left-chunks))))

(local
 (defthm pgs-dcr-firstn-length
   (implies (true-listp msg)
            (equal (fn-b3-firstn (len msg) msg) msg))
   :hints (("Goal" :induct (len msg) :in-theory (enable fn-b3-firstn)))))

(defthm pgs-dcr-begin-denotation-is-node
  (implies (and (natp nb) (true-listp msg) (equal (len msg) (* 64 nb)))
           (equal (pgs-dcr-denote msg (pgs-dc-begin sel base nb capture lease pgs-digest))
                  (fn-b3-node *fn-b3-iv* msg 0 0)))
  :hints (("Goal" :expand ((fn-b3-nthcdrx 0 msg))
                  :in-theory (e/d (pgs-dcr-denote pgs-dcr-current pgs-dc-begin
                                                  pgs-dcr-fold pgs-dcr-span)
                                   (nth update-nth fn-b3-node fn-b3-firstn fn-b3-nthcdrx)))))

(local
 (defthm pgs-dcr-octet-listp-true-listp
   (implies (fn-b3-octet-listp msg) (true-listp msg))
   :hints (("Goal" :induct (fn-b3-octet-listp msg)
                   :in-theory (enable fn-b3-octet-listp)))))

(defthm pgs-dcr-begin-root-is-blake3
  (implies (and (natp nb) (fn-b3-octet-listp msg) (equal (len msg) (* 64 nb)))
           (equal (pgs-octets-be-nat
                    (fn-b3-output-root
                      (pgs-dcr-denote msg (pgs-dc-begin sel base nb capture lease pgs-digest))))
                  (pgs-octets-be-nat (fn-blake3 msg))))
  :hints (("Goal" :in-theory (e/d (fn-blake3 fn-b3-hash)
                                   (pgs-dcr-denote pgs-dc-begin pgs-octets-be-nat
                                        fn-b3-output-root fn-b3-node fn-b3-fix-octets)))))

(local
 (defthm pgs-dcr-octet-listp-append
   (implies (and (fn-b3-octet-listp x) (fn-b3-octet-listp y))
            (fn-b3-octet-listp (append x y)))
   :hints (("Goal" :induct (append x y) :in-theory (enable fn-b3-octet-listp)))))

(defthm pgs-dcr-word-octets-shape
  (and (equal (len (pgs-word-le-octets word)) 8)
       (fn-b3-octet-listp (pgs-word-le-octets word)))
  :hints (("Goal" :in-theory (e/d (pgs-word-le-octets fn-b3-octet-listp) (pgs-octet)))))

(local
 (defthm pgs-dcr-len-append
   (equal (len (append x y)) (+ (len x) (len y)))
   :hints (("Goal" :induct (append x y)))))

(defthm pgs-dcr-words-octets-shape
  (and (equal (len (pgs-words-le-octets words)) (* 8 (len words)))
       (fn-b3-octet-listp (pgs-words-le-octets words)))
  :hints (("Goal" :induct (pgs-words-le-octets words)
                  :in-theory (e/d (pgs-words-le-octets)
                                   (pgs-word-le-octets fn-b3-octet-listp)))))

(local
 (defthm pgs-dcr-len-take
   (equal (len (take n words)) (nfix n))
   :hints (("Goal" :induct (take n words) :in-theory (enable take)))))

(defthm pgs-dcr-initial-root-is-existing-digest
  (implies (and (natp base) (natp nb))
    (equal
      (pgs-octets-be-nat
        (fn-b3-output-root
          (pgs-dcr-denote
            (pgs-words-le-octets (take (* 8 nb) (nthcdr base (pgs-x-arr sel pgs-mem))))
            (pgs-dc-begin sel base nb capture lease pgs-digest))))
      (mv-nth 0 (pgs-x-words-digest sel base nb pgs-mem fn-octets-pg))))
  :hints (("Goal" :in-theory (e/d (fn-blake3 fn-b3-hash) ( pgs-dcr-denote pgs-dc-begin pgs-octets-be-nat
                              fn-b3-output-root pgs-x-words-digest fn-b3-fix-octets
                              pgs-words-le-octets pgs-x-arr take nthcdr fn-blake3-of-octets)))))

;; Terminal refinement at the actual STEP boundary. The denotation equality
;; is the carried semantic obligation; no trajectory invariant is claimed here.
(defthm pgs-dcr-terminal-step-is-existing-digest
  (implies
    (and (natp base) (natp nb)
         (equal (pgs-dc-mode pgs-digest) :root)
         (equal (pgs-dc-depth pgs-digest) 0)
         (equal
           (pgs-dcr-denote
             (pgs-words-le-octets (take (* 8 nb) (nthcdr base (pgs-x-arr sel pgs-mem))))
             pgs-digest)
           (pgs-dcr-denote
             (pgs-words-le-octets (take (* 8 nb) (nthcdr base (pgs-x-arr sel pgs-mem))))
             (pgs-dc-begin sel base nb capture lease pgs-digest))))
    (equal (pgs-dc-result (mv-nth 1 (pgs-dc-step nil pgs-digest)))
           (mv-nth 0 (pgs-x-words-digest sel base nb pgs-mem fn-octets-pg))))
  :hints (("Goal"
            :use ((:instance pgs-dcr-root-result-is-denotation-root
                    (msg (pgs-words-le-octets
                           (take (* 8 nb) (nthcdr base (pgs-x-arr sel pgs-mem)))))))
            :in-theory (e/d (fn-b3-hash) ( pgs-dcr-denote pgs-dc-begin pgs-octets-be-nat
                         fn-b3-output-root pgs-x-words-digest fn-blake3 pgs-dc-result
                         pgs-dc-step pgs-words-le-octets pgs-x-arr take nthcdr
                         pgs-dcr-root-result-is-denotation-root)))))

;; Proof-only abstraction stays closed for consumers.
(in-theory (disable pgs-dcr-span pgs-dcr-parent pgs-dcr-fold
                    pgs-dcr-current pgs-dcr-denote))
