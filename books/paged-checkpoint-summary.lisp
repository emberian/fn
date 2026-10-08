; Stage summaries follow from the carried resident image, not a postimage premise.
(in-package "ACL2")
(include-book "paged-checkpoint-image")
(local (include-book "arithmetic/top" :dir :system))

(defthm pcksum-img-words
  (implies (pcki-img pw pgs-mem)
           (and (equal (pgs-x-words 0 16384 (len pw) pgs-mem) pw)
                (<= (+ 16384 (len pw)) (pgs-x-len 0 pgs-mem))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance pgs-x-take-of-words (s 0) (a 16384)
                            (j (len pw)) (k (* 2048 (- (pgs-v-length pgs-mem) 8))))
                 (:instance pcki-take-pw-zeros (k (len pw))
                            (z (- (* 2048 (- (pgs-v-length pgs-mem) 8)) (len pw)))))
           :in-theory (e/d (pcki-img pgs-x-len)
                        (pgs-x-words pcki-resident adt-tp-zeros
                         pgs-x-take-of-words pcki-take-pw-zeros)))))

(defthm pcksum-img-tail
  (implies (pcki-img pw pgs-mem)
           (equal (fn-pck-x-tail (len pw) pgs-mem)
                  (nthcdr (* 2048 (floor (len pw) 2048)) pw)))
  :rule-classes nil
  :hints (("Goal" :use (pcksum-img-words
                        (:instance fn-pck-x-tail-is-the-partial-page
                                   (cnt (len pw)) (words pw)))
           :in-theory (union-theories '(natp (:type-prescription len))
                                      (theory 'minimal-theory)))))

(defthm pcksum-stage-image
  (let* ((delta (fn-rows-wire-of rows fn-arena))
         (w (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows-from delta base st))))
    (implies (and (pcki-img pw pgs-mem)
                  (fn-pck-sccb-listp delta st)
                  (natp base) (< (fn-pck-plen delta base) 18446744073709551616)
                  (adt-tp-seq-lens-ok *fn-pck-row-schema* (fn-pck-rows-from delta base st))
                  (pcks-res (len pw) (+ (len pw) (len w)) pgs-mem)
                  (<= (+ (len pw) (len w)) (* 2048 (- (pgs-v-length pgs-mem) 8))))
             (let ((r (fn-pck-x-stage-rows rows (len pw) base st fn-arena fn-octets pgs-mem)))
               (and (equal (mv-nth 0 r) :ok)
                    (pcki-img (append pw w) (mv-nth 2 r))))))
  :rule-classes nil
  :hints (("Goal" :use (pcki-img-of-stage)
           :in-theory (union-theories '(pcks-wlen-is-len-words pcki-wlist-is-words
                                        pcks-treesp-of-sccb-listp)
                                      (theory 'minimal-theory)))))

(defthm fn-pck-x-stage-tail-is-the-extended-prefix
  (let* ((delta (fn-rows-wire-of rows fn-arena))
         (pw (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows prefix)))
         (w (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows-from delta base st)))
         (allw (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows (append prefix delta)))))
    (implies (and (equal cnt (len pw)) (equal base (fn-pck-plen prefix 0))
                  (fn-pck-context-agreep st (fn-pck-st-of (fn-pck-seed) prefix))
                  (pcki-img pw pgs-mem)
                  (fn-pck-sccb-listp delta st)
                  (natp base) (< (fn-pck-plen delta base) 18446744073709551616)
                  (adt-tp-seq-lens-ok *fn-pck-row-schema* (fn-pck-rows-from delta base st))
                  (pcks-res cnt (+ cnt (len w)) pgs-mem)
                  (<= (+ cnt (len w)) (* 2048 (- (pgs-v-length pgs-mem) 8))))
             (let ((r (fn-pck-x-stage-rows rows cnt base st fn-arena fn-octets pgs-mem)))
               (and (equal (mv-nth 0 r) :ok)
                    (equal (mv-nth 6 r)
                           (nthcdr (* 2048 (floor (len allw) 2048)) allw))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance pcksum-stage-image
                            (pw (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows prefix))))
                 (:instance pcksum-img-tail
                            (pw (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows (append prefix (fn-rows-wire-of rows fn-arena)))))
                            (pgs-mem (mv-nth 2 (fn-pck-x-stage-rows rows cnt base st fn-arena fn-octets pgs-mem))))
                 (:instance pcks-stage-tail-of-cursor (p cnt))
                 (:instance fn-pck-x-stage-summary-is-the-extended-prefix (p cnt))
                 (:instance fn-pck-context-rows-congruence
                            (a st) (b (fn-pck-st-of (fn-pck-seed) prefix))
                            (recs (fn-rows-wire-of rows fn-arena))))
           :in-theory (union-theories '(pck-rows-of-append adt-tp-seq-words-of-append)
                                      (theory 'minimal-theory)))))
