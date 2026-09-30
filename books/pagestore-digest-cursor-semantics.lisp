;; Proof-only whole-trajectory semantics. No list vocabulary runs in the host.
(in-package "ACL2")
(include-book "pagestore-digest-byte-refinement")
(include-book "pagestore-digest-block-predicate")
(include-book "pagestore-digest-byte-domain")
(include-book "pagestore-digest-cursor-counter")
(local (include-book "arithmetic-5/top" :dir :system))

(defthm pgs-dcs-word-count-rounding-window
  (implies (natp byte-total)
           (and (<= byte-total (* 8 (pgs-dcb-word-count byte-total)))
                (< (- (* 8 (pgs-dcb-word-count byte-total)) 8) byte-total)))
  :hints (("Goal" :in-theory (e/d (pgs-dcb-word-count) (ceiling))))
  :rule-classes nil)

;; A span may contain a final short word. Its byte length differs from its
;; word measure by fewer than eight bytes, even for unaligned starts.
(defthm pgs-dcs-span-length-window
  (implies (and (natp start) (natp end) (<= start end)
                (<= (* 8 start) (len msg))
                (<= end (pgs-dcb-word-count (len msg))))
           (and (<= (len (pgs-dcr-span start end msg)) (* 8 (- end start)))
                (< (- (* 8 (- end start)) 8)
                   (len (pgs-dcr-span start end msg)))))
  :hints (("Goal" :use ((:instance pgs-dcs-word-count-rounding-window
                                  (byte-total (len msg))))
                  :in-theory (e/d (pgs-dcr-span)
                                   (fn-b3-firstn fn-b3-nthcdrx pgs-dcb-word-count))))
  :rule-classes nil)

(defthm pgs-dcs-span-word-threshold
  (implies (and (natp start) (natp end) (natp threshold)
                (<= start end) (<= (* 8 start) (len msg))
                (<= end (pgs-dcb-word-count (len msg))))
           (equal (< (* 8 threshold) (len (pgs-dcr-span start end msg)))
                  (< threshold (- end start))))
  :hints (("Goal" :use pgs-dcs-span-length-window
                  :in-theory (disable pgs-dcr-span pgs-dcb-word-count)))
  :rule-classes nil)

(defthm pgs-dcs-rounded-split-test
  (implies (and (posp power) (natp nwords) (natp nbytes)
                (<= nbytes (* 8 nwords)) (< (- (* 8 nwords) 8) nbytes))
           (equal (< (* 2048 power) nbytes) (< (* 256 power) nwords))))

(defthm pgs-dcs-left-chunks-of-rounded-length
  (implies (and (posp power) (natp nwords) (natp nbytes)
                (<= nbytes (* 8 nwords)) (< (- (* 8 nwords) 8) nbytes))
           (equal (fn-b3-left-chunks power nbytes)
                  (fn-b3-left-chunks power (* 8 nwords))))
  :hints (("Goal" :induct (fn-b3-left-chunks power (* 8 nwords))
                  :in-theory (enable fn-b3-left-chunks)))
  :rule-classes nil)

(defthm pgs-dcs-span-left-chunks
  (implies (and (posp power) (natp start) (natp end)
                (<= start end) (<= (* 8 start) (len msg))
                (<= end (pgs-dcb-word-count (len msg))))
           (equal (fn-b3-left-chunks power (len (pgs-dcr-span start end msg)))
                  (fn-b3-left-chunks power (* 8 (- end start)))))
  :hints (("Goal" :use (pgs-dcs-span-length-window
                        (:instance pgs-dcs-left-chunks-of-rounded-length
                          (nwords (- end start))
                          (nbytes (len (pgs-dcr-span start end msg)))))
                  :in-theory (disable pgs-dcr-span pgs-dcb-word-count
                                      fn-b3-left-chunks))))

(defthm pgs-dcs-node-model-base
  (implies (and (natp start) (natp end) (<= start end)
                (<= (* 8 start) (len msg))
                (<= end (pgs-dcb-word-count (len msg))) (<= (- end start) 128))
           (equal (fn-b3-node *fn-b3-iv* (pgs-dcr-span start end msg) counter 0)
                  (fn-b3-chunk *fn-b3-iv* (pgs-dcr-span start end msg) counter 0 t)))
  :hints (("Goal" :use ((:instance pgs-dcs-span-word-threshold (threshold 128)))
                  :expand ((fn-b3-node *fn-b3-iv* (pgs-dcr-span start end msg) counter 0))
                  :in-theory (disable pgs-dcr-span fn-b3-chunk pgs-dcb-word-count))))

(defthm pgs-dcs-chunk-model-nonlast
  (implies (and (natp pos) (natp end) (< (+ pos 8) end)
                (<= (* 8 pos) (len msg))
                (<= end (pgs-dcb-word-count (len msg))))
           (equal (fn-b3-chunk cv (pgs-dcr-span pos end msg) counter 0 startp)
                  (fn-b3-chunk
                    (fn-b3-compress cv (fn-b3-words 16 (pgs-dcr-span pos end msg))
                                    counter 64 (if startp 1 0))
                    (pgs-dcr-span (+ pos 8) end msg) counter 0 nil)))
  :hints (("Goal" :use ((:instance pgs-dcs-span-word-threshold
                                  (start pos) (threshold 8)))
                  :expand ((fn-b3-chunk cv (pgs-dcr-span pos end msg) counter 0 startp))
                  :in-theory (disable pgs-dcr-span fn-b3-chunk fn-b3-compress
                                      pgs-dcb-word-count))))

(defthm pgs-dcs-node-model-split
  (implies (and (natp start) (natp end) (posp power) (natp counter)
                (< (* 128 power) (- end start)) (<= (* 8 start) (len msg))
                (<= end (pgs-dcb-word-count (len msg)))
                (equal (fn-b3-left-chunks 1 (* 8 (- end start))) power))
           (equal (fn-b3-node *fn-b3-iv* (pgs-dcr-span start end msg) counter 0)
                  (pgs-dcr-parent
                    (fn-b3-output-cv
                      (fn-b3-node *fn-b3-iv* (pgs-dcr-span start (+ start (* 128 power)) msg) counter 0))
                    (fn-b3-output-cv
                      (fn-b3-node *fn-b3-iv* (pgs-dcr-span (+ start (* 128 power)) end msg)
                                  (+ counter power) 0)))))
  :hints (("Goal" :expand ((fn-b3-node *fn-b3-iv* (pgs-dcr-span start end msg) counter 0))
                  :use ((:instance pgs-dcs-span-word-threshold (threshold 128))
                        (:instance pgs-dcs-span-left-chunks (power 1))
                        (:instance pgs-dcr-span-left (split (+ start (* 128 power))))
                        (:instance pgs-dcr-span-right (split (+ start (* 128 power)))))
                  :in-theory (e/d (pgs-dcr-parent)
                                   (pgs-dcr-span fn-b3-node fn-b3-output-cv fn-b3-output
                                        fn-b3-left-chunks pgs-dcr-span-left pgs-dcr-span-right
                                        pgs-dcb-word-count pgs-dcs-span-left-chunks))
                  :do-not-induct t)))


(defthm pgs-dcs-node-step-keeps-current-denotation
  (implies (and (equal (pgs-dc-mode pgs-digest-state) :node)
                (natp (pgs-dc-start pgs-digest-state))
                (natp (pgs-dc-end pgs-digest-state))
                (<= (pgs-dc-start pgs-digest-state) (pgs-dc-end pgs-digest-state))
                (<= (* 8 (pgs-dc-start pgs-digest-state)) (len msg))
                (<= (pgs-dc-end pgs-digest-state) (pgs-dcb-word-count (len msg))))
           (equal (pgs-dcr-current msg (mv-nth 1 (pgs-dc-step nil pgs-digest-state)))
                  (pgs-dcr-current msg pgs-digest-state)))
  :hints (("Goal" :in-theory (e/d (pgs-dcr-current pgs-dc-step)
                                   (nth update-nth pgs-dcr-span fn-b3-chunk fn-b3-node pgs-dcb-word-count))
                  :do-not-induct t)))

(defthm pgs-dcs-node-step-preserves-denotation
  (implies (and (equal (pgs-dc-mode pgs-digest-state) :node)
                (natp (pgs-dc-start pgs-digest-state))
                (natp (pgs-dc-end pgs-digest-state))
                (<= (pgs-dc-start pgs-digest-state) (pgs-dc-end pgs-digest-state))
                (<= (* 8 (pgs-dc-start pgs-digest-state)) (len msg))
                (<= (pgs-dc-end pgs-digest-state) (pgs-dcb-word-count (len msg))))
           (equal (pgs-dcr-denote msg (mv-nth 1 (pgs-dc-step nil pgs-digest-state)))
                  (pgs-dcr-denote msg pgs-digest-state)))
  :hints (("Goal" :in-theory (e/d (pgs-dcr-denote)
                                   (pgs-dcr-current pgs-dc-step pgs-dcr-fold)))))

(local
 (defthm pgs-dcs-advanced-pos-not-start
   (implies (and (rationalp start) (rationalp pos) (<= start pos))
            (not (equal (+ 8 pos) start)))))

(defthm pgs-dcs-chunk-nonlast-keeps-current-denotation
  (implies (and (equal (pgs-dc-mode pgs-digest-state) :chunk)
                (natp (pgs-dc-start pgs-digest-state))
                (natp (pgs-dc-pos pgs-digest-state))
                (natp (pgs-dc-end pgs-digest-state))
                (<= (pgs-dc-start pgs-digest-state) (pgs-dc-pos pgs-digest-state))
                (<= (pgs-dc-pos pgs-digest-state) (pgs-dc-end pgs-digest-state))
                (< (+ (pgs-dc-pos pgs-digest-state) 8) (pgs-dc-end pgs-digest-state))
                (<= (* 8 (pgs-dc-pos pgs-digest-state)) (len msg))
                (<= (pgs-dc-end pgs-digest-state) (pgs-dcb-word-count (len msg)))
                (true-listp (pgs-dc-cv pgs-digest-state))
                (equal (len (pgs-dc-cv pgs-digest-state)) 8)
                (equal block (fn-b3-words 16
                              (pgs-dcr-span (pgs-dc-pos pgs-digest-state)
                                             (pgs-dc-end pgs-digest-state) msg))))
           (equal (pgs-dcr-current msg (mv-nth 1 (pgs-dc-step block pgs-digest-state)))
                  (pgs-dcr-current msg pgs-digest-state)))
  :hints (("Goal" :in-theory (e/d (pgs-dcr-current pgs-dc-step fn-b3-output-cv fn-b3-output)
                                   (nth update-nth pgs-dcr-span fn-b3-node fn-b3-chunk
                                        fn-b3-compress pgs-dc-pad-block fn-b3-cv8 pgs-dcb-word-count))
                  :expand ((fn-b3-chunk (pgs-dc-cv pgs-digest-state)
                            (pgs-dcr-span (pgs-dc-pos pgs-digest-state) (pgs-dc-end pgs-digest-state) msg)
                            (pgs-dc-counter pgs-digest-state) 0
                            (equal (pgs-dc-pos pgs-digest-state) (pgs-dc-start pgs-digest-state))))
                  :do-not-induct t)))

(defthm pgs-dcs-split-push-preserves-denotation
  (implies (and (equal (pgs-dc-mode pgs-digest-state) :split)
                (natp (pgs-dc-start pgs-digest-state))
                (natp (pgs-dc-end pgs-digest-state))
                (natp (pgs-dc-counter pgs-digest-state))
                (natp (pgs-dc-depth pgs-digest-state))
                (< (pgs-dc-depth pgs-digest-state) 64)
                (posp (pgs-dc-power pgs-digest-state))
                (< (* 128 (pgs-dc-power pgs-digest-state))
                   (- (pgs-dc-end pgs-digest-state) (pgs-dc-start pgs-digest-state)))
                (<= (- (pgs-dc-end pgs-digest-state) (pgs-dc-start pgs-digest-state))
                    (* 256 (pgs-dc-power pgs-digest-state)))
                (<= (* 8 (pgs-dc-start pgs-digest-state)) (len msg))
                (<= (pgs-dc-end pgs-digest-state) (pgs-dcb-word-count (len msg)))
                (equal (fn-b3-left-chunks 1
                           (* 8 (- (pgs-dc-end pgs-digest-state) (pgs-dc-start pgs-digest-state))))
                       (pgs-dc-power pgs-digest-state)))
           (equal (pgs-dcr-denote msg (mv-nth 1 (pgs-dc-step nil pgs-digest-state)))
                  (pgs-dcr-denote msg pgs-digest-state)))
  :hints (("Goal" :expand ((:free (out cursor)
                            (pgs-dcr-fold (+ 1 (nth *pgs-dc-depth* pgs-digest-state)) out msg cursor)))
                  :use ((:instance pgs-dcs-node-model-split
                          (start (pgs-dc-start pgs-digest-state))
                          (end (pgs-dc-end pgs-digest-state))
                          (counter (pgs-dc-counter pgs-digest-state))
                          (power (pgs-dc-power pgs-digest-state))))
                  :in-theory (e/d (pgs-dcr-denote pgs-dcr-current pgs-dc-step pgs-dcr-parent)
                                   (nth update-nth pgs-dcr-fold fn-b3-cv8 fn-b3-output
                                        fn-b3-output-cv fn-b3-node pgs-dcr-span
                                        fn-b3-left-chunks pgs-dcs-node-model-split pgs-dcb-word-count))
                  :do-not-induct t)))
 
(defthm pgs-dcs-nonchunk-block-is-irrelevant
  (implies (not (equal (pgs-dc-mode pgs-digest-state) :chunk))
           (equal (pgs-dc-step block pgs-digest-state)
                  (pgs-dc-step nil pgs-digest-state)))
  :hints (("Goal" :in-theory (e/d (pgs-dc-step) (nth update-nth))))
  :rule-classes nil)

(defthm pgs-dcs-byte-step-outside-tail-is-page-step
  (implies (not (and (equal (pgs-dc-mode pgs-digest-state) :chunk)
                     (equal (pgs-dc-end pgs-digest-state) (pgs-dc-total pgs-digest-state))
                     (<= (- (pgs-dc-end pgs-digest-state) (pgs-dc-pos pgs-digest-state)) 8)))
           (equal (pgs-dcb-step byte-total block pgs-digest-state)
                  (pgs-dc-step block pgs-digest-state)))
  :hints (("Goal" :in-theory (e/d (pgs-dcb-step) (nth update-nth)))))

(defun-nx pgs-dcs-phasep (pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :verify-guards nil))
  (and (implies (member-eq (pgs-dc-mode pgs-digest-state) '(:root :done))
                (equal (pgs-dc-depth pgs-digest-state) 0))
       (implies (equal (pgs-dc-mode pgs-digest-state) :done)
                (equal (pgs-dc-answer pgs-digest-state)
                       (pgs-octets-be-nat (fn-b3-output-root (pgs-dc-output pgs-digest-state)))))
       (implies (equal (pgs-dc-mode pgs-digest-state) :split)
                (equal (fn-b3-left-chunks (pgs-dc-power pgs-digest-state)
                         (* 8 (- (pgs-dc-end pgs-digest-state) (pgs-dc-start pgs-digest-state))))
                       (fn-b3-left-chunks 1
                         (* 8 (- (pgs-dc-end pgs-digest-state) (pgs-dc-start pgs-digest-state))))))))

(defun-nx pgs-dcs-invariantp (limit byte-total msg pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :verify-guards nil))
  (and (pgs-dbd-domainp limit byte-total pgs-digest-state)
       (pgs-dcs-counterp pgs-digest-state)
       (fn-b3-octet-listp msg) (equal (len msg) byte-total)
       (pgs-dcs-phasep pgs-digest-state)
       (equal (pgs-dcr-denote msg pgs-digest-state)
              (fn-b3-node *fn-b3-iv* msg 0 0))))


(defthm pgs-dcs-chunk-nonlast-preserves-denotation
  (implies (and (equal (pgs-dc-mode pgs-digest-state) :chunk)
                (natp (pgs-dc-start pgs-digest-state))
                (natp (pgs-dc-pos pgs-digest-state)) (natp (pgs-dc-end pgs-digest-state))
                (<= (pgs-dc-start pgs-digest-state) (pgs-dc-pos pgs-digest-state))
                (< (+ (pgs-dc-pos pgs-digest-state) 8) (pgs-dc-end pgs-digest-state))
                (<= (* 8 (pgs-dc-pos pgs-digest-state)) (len msg))
                (<= (pgs-dc-end pgs-digest-state) (pgs-dcb-word-count (len msg)))
                (true-listp (pgs-dc-cv pgs-digest-state)) (equal (len (pgs-dc-cv pgs-digest-state)) 8)
                (equal block (fn-b3-words 16
                               (pgs-dcr-span (pgs-dc-pos pgs-digest-state)
                                              (pgs-dc-end pgs-digest-state) msg))))
           (equal (pgs-dcr-denote msg (mv-nth 1 (pgs-dc-step block pgs-digest-state)))
                  (pgs-dcr-denote msg pgs-digest-state)))
  :hints (("Goal" :in-theory (e/d (pgs-dcr-denote)
                                   (pgs-dcr-current pgs-dc-step pgs-dcr-fold pgs-dcb-word-count)))))

(defthm pgs-dcs-done-step-is-identity
  (implies (equal (pgs-dc-mode pgs-digest-state) :done)
           (equal (pgs-dc-step block pgs-digest-state) (list :done pgs-digest-state)))
  :hints (("Goal" :in-theory (e/d (pgs-dc-step) (nth update-nth)))))

(defthm pgs-dcs-domain-current-unfolds
  (implies (pgs-dbd-domainp limit byte-total pgs-digest-state)
           (and (natp byte-total) (natp (pgs-dc-start pgs-digest-state))
                (natp (pgs-dc-pos pgs-digest-state)) (natp (pgs-dc-end pgs-digest-state))
                (natp (pgs-dc-counter pgs-digest-state)) (natp (pgs-dc-depth pgs-digest-state))
                (<= (pgs-dc-depth pgs-digest-state) 63)
                (<= (pgs-dc-start pgs-digest-state) (pgs-dc-pos pgs-digest-state))
                (<= (pgs-dc-pos pgs-digest-state) (pgs-dc-end pgs-digest-state))
                (<= (pgs-dc-end pgs-digest-state) (pgs-dc-total pgs-digest-state))
                (equal (pgs-dc-total pgs-digest-state) (pgs-dcb-word-count byte-total))
                (<= (* 8 (pgs-dc-pos pgs-digest-state)) byte-total)
                (true-listp (pgs-dc-cv pgs-digest-state)) (equal (len (pgs-dc-cv pgs-digest-state)) 8)
                (member-eq (pgs-dc-mode pgs-digest-state) '(:node :split :chunk :return :root :done))
                (implies (member-eq (pgs-dc-mode pgs-digest-state) '(:node :split))
                         (equal (pgs-dc-pos pgs-digest-state) (pgs-dc-start pgs-digest-state)))
                (implies (equal (pgs-dc-mode pgs-digest-state) :split)
                         (and (posp (pgs-dc-power pgs-digest-state))
                              (< (pgs-dc-depth pgs-digest-state) 63)
                              (< (* 128 (pgs-dc-power pgs-digest-state))
                                 (- (pgs-dc-end pgs-digest-state) (pgs-dc-start pgs-digest-state)))))))
  :hints (("Goal" :use ((:instance pgs-dcd-powerp-bound
                          (power (pgs-dc-power pgs-digest-state))
                          (limit (- (- limit (pgs-dc-depth pgs-digest-state)) 1))))
                  :in-theory (e/d (pgs-dbd-domainp pgs-dcd-domainp)
                                   (nth update-nth pgs-dbd-framesp pgs-dcd-framesp pgs-dcd-powerp expt
                                        pgs-dcd-powerp-bound))
                  :do-not-induct t))
  :rule-classes nil)

(defthm pgs-dcs-domain-top-frame-unfolds
  (implies (and (pgs-dbd-domainp limit byte-total pgs-digest-state)
                (posp (pgs-dc-depth pgs-digest-state)))
           (let ((frame (pgs-dc-framesi (- (pgs-dc-depth pgs-digest-state) 1) pgs-digest-state)))
             (and (member-eq (fn-b3-nthx 0 frame) '(:left :right))
                  (natp (fn-b3-nthx 3 frame))
                  (implies (equal (fn-b3-nthx 0 frame) :right)
                           (and (true-listp (fn-b3-nthx 4 frame))
                                (equal (len (fn-b3-nthx 4 frame)) 8))))))
  :hints (("Goal" :use ((:instance pgs-dcd-top-frame-unfolds
                          (depth (pgs-dc-depth pgs-digest-state)) (total (pgs-dc-total pgs-digest-state))))
                  :in-theory (e/d (pgs-dbd-domainp pgs-dcd-domainp)
                                   (nth update-nth fn-b3-nthx pgs-dbd-framesp pgs-dcd-framesp
                                        pgs-dcd-powerp pgs-dcd-top-frame-unfolds expt))
                  :do-not-induct t))
  :rule-classes nil)

(defthm pgs-dcs-domain-node-preserves-denotation
  (implies (and (pgs-dbd-domainp limit byte-total pgs-digest-state)
                (equal (len msg) byte-total) (equal (pgs-dc-mode pgs-digest-state) :node))
           (equal (pgs-dcr-denote msg (mv-nth 1 (pgs-dcb-step byte-total block pgs-digest-state)))
                  (pgs-dcr-denote msg pgs-digest-state)))
  :hints (("Goal" :use (pgs-dcs-domain-current-unfolds pgs-dcs-node-step-preserves-denotation
                        pgs-dcs-nonchunk-block-is-irrelevant)
                  :in-theory (disable nth update-nth pgs-dbd-domainp pgs-dcr-denote pgs-dc-step
                                      pgs-dcb-step pgs-dcb-word-count pgs-dcs-node-step-preserves-denotation)
                  :do-not-induct t)))

(defthm pgs-dcs-domain-canonical-chunk-preserves-denotation
  (implies (and (pgs-dbd-domainp limit byte-total pgs-digest-state)
                (equal (len msg) byte-total) (equal (pgs-dc-mode pgs-digest-state) :chunk)
                (equal block (fn-b3-words 16
                               (pgs-dcr-span (pgs-dc-pos pgs-digest-state)
                                              (pgs-dc-end pgs-digest-state) msg))))
           (equal (pgs-dcr-denote msg (mv-nth 1 (pgs-dcb-step byte-total block pgs-digest-state)))
                  (pgs-dcr-denote msg pgs-digest-state)))
  :hints (("Goal" :use (pgs-dcs-domain-current-unfolds
                        pgs-dcs-chunk-nonlast-preserves-denotation
                        pgs-dcr-chunk-step-preserves-denotation
                        pgs-dbr-chunk-tail-preserves-denotation
                        (:instance pgs-dbd-word-before-end-is-byte-backed
                          (word-offset (pgs-dc-end pgs-digest-state))))
                  :in-theory (disable nth update-nth pgs-dbd-domainp pgs-dcr-denote pgs-dc-step
                                      pgs-dcb-step pgs-dcb-word-count
                                      pgs-dcs-chunk-nonlast-preserves-denotation
                                      pgs-dcr-chunk-step-preserves-denotation
                                      pgs-dbr-chunk-tail-preserves-denotation
                                      pgs-dbd-word-before-end-is-byte-backed)
                  :do-not-induct t)))

(defthm pgs-dcs-domain-split-preserves-denotation
  (implies (and (pgs-dbd-domainp limit byte-total pgs-digest-state)
                (pgs-dcs-phasep pgs-digest-state) (equal (len msg) byte-total)
                (equal (pgs-dc-mode pgs-digest-state) :split))
           (equal (pgs-dcr-denote msg (mv-nth 1 (pgs-dcb-step byte-total block pgs-digest-state)))
                  (pgs-dcr-denote msg pgs-digest-state)))
  :hints (("Goal" :use (pgs-dcs-domain-current-unfolds pgs-dcs-split-push-preserves-denotation
                        pgs-dcr-split-search-preserves-denotation pgs-dcs-nonchunk-block-is-irrelevant
                        (:instance pgs-dcr-split-finished-carry-is-power
                          (power (pgs-dc-power pgs-digest-state))
                          (nwords (- (pgs-dc-end pgs-digest-state) (pgs-dc-start pgs-digest-state)))))
                  :in-theory (e/d (pgs-dcs-phasep)
                                   (nth update-nth pgs-dbd-domainp pgs-dcr-denote pgs-dc-step
                                        pgs-dcb-step pgs-dcb-word-count fn-b3-left-chunks
                                        pgs-dcs-split-push-preserves-denotation
                                        pgs-dcr-split-search-preserves-denotation
                                        pgs-dcr-split-finished-carry-is-power))
                  :do-not-induct t)))

(defthm pgs-dcs-domain-return-preserves-denotation
  (implies (and (pgs-dbd-domainp limit byte-total pgs-digest-state)
                (equal (pgs-dc-mode pgs-digest-state) :return))
           (equal (pgs-dcr-denote msg (mv-nth 1 (pgs-dcb-step byte-total block pgs-digest-state)))
                  (pgs-dcr-denote msg pgs-digest-state)))
  :hints (("Goal" :use (pgs-dcs-domain-current-unfolds pgs-dcs-domain-top-frame-unfolds
                        pgs-dcr-return-empty-preserves-denotation pgs-dcr-return-left-preserves-denotation
                        pgs-dcr-return-right-preserves-denotation pgs-dcs-nonchunk-block-is-irrelevant)
                  :in-theory (disable nth update-nth fn-b3-nthx pgs-dbd-domainp pgs-dcr-denote
                                      pgs-dc-step pgs-dcb-step pgs-dcb-word-count
                                      pgs-dcr-return-empty-preserves-denotation
                                      pgs-dcr-return-left-preserves-denotation
                                      pgs-dcr-return-right-preserves-denotation)
                  :do-not-induct t)))

(defthm pgs-dcs-domain-terminal-preserves-denotation
  (implies (and (pgs-dcs-phasep pgs-digest-state)
                (member-eq (pgs-dc-mode pgs-digest-state) '(:root :done)))
           (equal (pgs-dcr-denote msg (mv-nth 1 (pgs-dcb-step byte-total block pgs-digest-state)))
                  (pgs-dcr-denote msg pgs-digest-state)))
  :hints (("Goal" :use (pgs-dcr-root-preserves-denotation pgs-dcs-nonchunk-block-is-irrelevant)
                  :in-theory (e/d (pgs-dcs-phasep)
                                   (nth update-nth pgs-dcr-denote pgs-dc-step pgs-dcb-step
                                        pgs-dcr-root-preserves-denotation fn-b3-left-chunks))
                  :do-not-induct t)))

(defthm pgs-dcs-canonical-byte-step-preserves-denotation
  (implies (and (pgs-dbd-domainp limit byte-total pgs-digest-state)
                (pgs-dcs-phasep pgs-digest-state) (equal (len msg) byte-total)
                (equal block (fn-b3-words 16
                               (pgs-dcr-span (pgs-dc-pos pgs-digest-state)
                                              (pgs-dc-end pgs-digest-state) msg))))
           (equal (pgs-dcr-denote msg (mv-nth 1 (pgs-dcb-step byte-total block pgs-digest-state)))
                  (pgs-dcr-denote msg pgs-digest-state)))
  :hints (("Goal" :use (pgs-dcs-domain-current-unfolds
                        pgs-dcs-domain-node-preserves-denotation
                        pgs-dcs-domain-split-preserves-denotation
                        pgs-dcs-domain-canonical-chunk-preserves-denotation
                        pgs-dcs-domain-return-preserves-denotation
                        pgs-dcs-domain-terminal-preserves-denotation)
                  :in-theory (disable nth update-nth pgs-dbd-domainp pgs-dcs-phasep
                                      pgs-dcr-denote pgs-dc-step pgs-dcb-step pgs-dcb-word-count
                                      pgs-dcs-domain-node-preserves-denotation
                                      pgs-dcs-domain-split-preserves-denotation
                                      pgs-dcs-domain-canonical-chunk-preserves-denotation
                                      pgs-dcs-domain-return-preserves-denotation
                                      pgs-dcs-domain-terminal-preserves-denotation)
                  :do-not-induct t)))

(defthm pgs-dcs-byte-step-preserves-phase
  (implies (and (pgs-dbd-domainp limit byte-total pgs-digest-state)
                (pgs-dcs-phasep pgs-digest-state))
           (pgs-dcs-phasep (mv-nth 1 (pgs-dcb-step byte-total block pgs-digest-state))))
  :hints (("Goal" :use (pgs-dcs-domain-current-unfolds pgs-dcr-split-search-preserves-carry
                        pgs-dcs-nonchunk-block-is-irrelevant)
                  :in-theory (e/d (pgs-dcs-phasep pgs-dcb-step pgs-dc-step)
                                   (nth update-nth pgs-dbd-domainp fn-b3-left-chunks
                                        pgs-dcr-split-search-preserves-carry fn-b3-output
                                        fn-b3-output-cv fn-b3-output-root pgs-octets-be-nat))
                  :do-not-induct t)))

(defthm pgs-dcs-byte-step-without-demand-block-is-irrelevant
  (implies (and (pgs-dbd-domainp limit byte-total pgs-digest-state)
                (not (pgs-dc-needs-block pgs-digest-state)))
           (equal (pgs-dcb-step byte-total block pgs-digest-state)
                  (pgs-dcb-step byte-total other-block pgs-digest-state)))
  :hints (("Goal" :use (pgs-dcs-domain-current-unfolds pgs-dbr-word-count-covers-byte-total)
                  :in-theory (e/d (pgs-dc-needs-block pgs-dcb-step pgs-dc-step)
                                   (nth update-nth pgs-dbd-domainp pgs-dcb-word-count
                                        pgs-dcs-byte-step-outside-tail-is-page-step
                                        fn-b3-output fn-b3-output-cv fn-b3-output-root pgs-octets-be-nat))
                  :do-not-induct t))
  :rule-classes nil)

(defthm pgs-dcs-byte-step-preserves-denotation
  (implies (and (pgs-dbd-domainp limit byte-total pgs-digest-state)
                (pgs-dcs-phasep pgs-digest-state) (equal (len msg) byte-total)
                (pgs-dcs-blockp block msg pgs-digest-state))
           (equal (pgs-dcr-denote msg (mv-nth 1 (pgs-dcb-step byte-total block pgs-digest-state)))
                  (pgs-dcr-denote msg pgs-digest-state)))
  :hints (("Goal" :use ((:instance pgs-dcs-canonical-byte-step-preserves-denotation
                          (block (fn-b3-words 16
                                   (pgs-dcr-span (pgs-dc-pos pgs-digest-state)
                                                  (pgs-dc-end pgs-digest-state) msg))))
                        (:instance pgs-dcs-byte-step-without-demand-block-is-irrelevant
                          (other-block (fn-b3-words 16
                                         (pgs-dcr-span (pgs-dc-pos pgs-digest-state)
                                                        (pgs-dc-end pgs-digest-state) msg)))))
                  :in-theory (e/d (pgs-dcs-blockp)
                                   (nth update-nth pgs-dbd-domainp pgs-dcs-phasep pgs-dcr-denote
                                        pgs-dc-step pgs-dcb-step pgs-dcb-word-count pgs-dc-needs-block
                                        pgs-dcs-canonical-byte-step-preserves-denotation))
                  :do-not-induct t)))

(local
 (defthm pgs-dcs-octet-listp-true-listp
   (implies (fn-b3-octet-listp msg) (true-listp msg))
   :hints (("Goal" :induct (fn-b3-octet-listp msg)
                   :in-theory (enable fn-b3-octet-listp)))))

(defthm pgs-dcs-begin-establishes-invariant
  (implies (and (natp limit) (<= limit 63)
                (fn-b3-octet-listp msg) (equal (len msg) byte-total)
                (<= (pgs-dcb-word-count byte-total) (* 128 (expt 2 limit))))
           (pgs-dcs-invariantp limit byte-total msg
             (pgs-dcb-begin sel base byte-total capture lease pgs-digest-state)))
  :hints (("Goal" :use (pgs-dbd-begin-establishes-domain pgs-dbr-byte-begin-denotation-is-node
                        pgs-dcs-byte-begin-establishes-counter)
                  :in-theory (e/d (pgs-dcs-invariantp pgs-dcs-phasep pgs-dcb-begin pgs-dc-begin)
                                   (nth update-nth pgs-dbd-domainp pgs-dcr-denote fn-b3-node
                                        fn-b3-left-chunks pgs-dcb-word-count
                                        pgs-dbd-begin-establishes-domain pgs-dbr-byte-begin-denotation-is-node
                                        pgs-dcs-byte-begin-establishes-counter))
                  :do-not-induct t)))

(defthm pgs-dcs-byte-step-preserves-invariant
  (implies (and (pgs-dcs-invariantp limit byte-total msg pgs-digest-state)
                (pgs-dcs-blockp block msg pgs-digest-state))
           (pgs-dcs-invariantp limit byte-total msg
             (mv-nth 1 (pgs-dcb-step byte-total block pgs-digest-state))))
  :hints (("Goal" :use (pgs-dbd-byte-step-preserves-domain pgs-dcs-byte-step-preserves-counter
                        pgs-dcs-byte-step-preserves-phase
                        pgs-dcs-byte-step-preserves-denotation)
                  :in-theory (e/d (pgs-dcs-invariantp)
                                   (nth update-nth pgs-dbd-domainp pgs-dcs-phasep pgs-dcs-blockp
                                        pgs-dcr-denote pgs-dcb-step fn-b3-node
                                        pgs-dbd-byte-step-preserves-domain pgs-dcs-byte-step-preserves-counter
                                        pgs-dcs-byte-step-preserves-phase
                                        pgs-dcs-byte-step-preserves-denotation))
                  :do-not-induct t)))

(defthm pgs-dcs-done-result-is-blake3
  (implies (and (pgs-dcs-invariantp limit byte-total msg pgs-digest-state)
                (equal (pgs-dc-mode pgs-digest-state) :done))
           (equal (pgs-dcb-result-octets pgs-digest-state) (fn-blake3 msg)))
  :hints (("Goal" :in-theory (e/d (pgs-dcs-invariantp pgs-dcs-phasep pgs-dcr-denote
                                                    pgs-dcr-current pgs-dcr-fold pgs-dcb-result-octets
                                                    fn-blake3 fn-b3-hash)
                                   (nth update-nth pgs-dbd-domainp fn-b3-node fn-b3-left-chunks
                                        fn-b3-output-root fn-b3-fix-octets))
                  :do-not-induct t)))

(encapsulate
 ()
 (local (include-book "std/lists/update-nth" :dir :system))
(defthm pgs-dcs-page-begin-is-byte-begin
  (implies (natp nb)
           (equal (pgs-dcb-begin sel base (* 64 nb) capture lease pgs-digest-state)
                  (pgs-dc-begin sel base nb capture lease pgs-digest-state)))
  :hints (("Goal" :in-theory (e/d (pgs-dcb-begin pgs-dc-begin pgs-dcb-word-count)
                                   (nth update-nth)))))
)

(defthm pgs-dcs-page-begin-establishes-invariant
  (implies (and (natp limit) (<= limit 63) (natp nb)
                (fn-b3-octet-listp msg) (equal (len msg) (* 64 nb))
                (<= (* 8 nb) (* 128 (expt 2 limit))))
           (pgs-dcs-invariantp limit (* 64 nb) msg
             (pgs-dc-begin sel base nb capture lease pgs-digest-state)))
  :hints (("Goal" :use ((:instance pgs-dcs-begin-establishes-invariant (byte-total (* 64 nb))))
                  :in-theory (e/d (pgs-dcb-word-count)
                                   (pgs-dcs-invariantp pgs-dcb-begin pgs-dc-begin
                                        pgs-dcs-begin-establishes-invariant)))))

(defthm pgs-dcs-invariant-implies-domain
  (implies (pgs-dcs-invariantp limit byte-total msg pgs-digest-state)
           (pgs-dbd-domainp limit byte-total pgs-digest-state))
  :hints (("Goal" :in-theory (e/d (pgs-dcs-invariantp)
                                   (pgs-dbd-domainp pgs-dcs-phasep pgs-dcr-denote fn-b3-node)))))

(defthm pgs-dcs-invariant-implies-phase
  (implies (pgs-dcs-invariantp limit byte-total msg pgs-digest-state)
           (pgs-dcs-phasep pgs-digest-state))
  :hints (("Goal" :in-theory (e/d (pgs-dcs-invariantp)
                                   (pgs-dbd-domainp pgs-dcs-phasep pgs-dcr-denote fn-b3-node)))))

(defthm pgs-dcs-page-step-preserves-invariant
  (implies (and (pgs-dcs-invariantp limit byte-total msg pgs-digest-state)
                (equal byte-total (* 8 (pgs-dc-total pgs-digest-state)))
                (pgs-dcs-blockp block msg pgs-digest-state))
           (pgs-dcs-invariantp limit byte-total msg
             (mv-nth 1 (pgs-dc-step block pgs-digest-state))))
  :hints (("Goal" :use (pgs-dcs-byte-step-preserves-invariant pgs-dcs-domain-current-unfolds
                        pgs-dbr-byte-tail-boundary-refines-page-step)
                  :in-theory (disable pgs-dcs-invariantp
                                   nth update-nth pgs-dbd-domainp pgs-dcs-phasep pgs-dcs-blockp
                                        pgs-dcr-denote pgs-dc-step pgs-dcb-step fn-b3-node
                                        pgs-dcs-byte-step-preserves-invariant
                                        pgs-dcs-byte-step-outside-tail-is-page-step
                                        pgs-dbr-byte-tail-boundary-refines-page-step))))

(defthm pgs-dcs-done-page-result-is-blake3-natural
  (implies (and (pgs-dcs-invariantp limit byte-total msg pgs-digest-state)
                (equal (pgs-dc-mode pgs-digest-state) :done))
           (equal (pgs-dc-result pgs-digest-state) (pgs-octets-be-nat (fn-blake3 msg))))
  :hints (("Goal" :use pgs-dcs-done-result-is-blake3
                  :in-theory (e/d (pgs-dcs-invariantp pgs-dcs-phasep pgs-dc-result
                                                    pgs-dcb-result-octets)
                                   (nth update-nth pgs-dbd-domainp pgs-dcr-denote fn-b3-node
                                        fn-b3-left-chunks fn-blake3 fn-b3-output-root
                                        pgs-octets-be-nat pgs-dcs-done-result-is-blake3)))))

(in-theory (disable pgs-dcs-invariantp pgs-dcs-phasep pgs-dcs-blockp))
