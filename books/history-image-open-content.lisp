; The single allocation starts the body proof with zeros and the final header.
(in-package "ACL2")
(include-book "history-image-open-proof")
(include-book "history-image-model-step")
(include-book "history-image-dirty-proof")
(local (include-book "arithmetic/top" :dir :system))

(local
 (defthm fn-his-resize-empty-zeros
  (implies (equal (len x) 0) (equal (resize-list x n 0) (adt-zeros n)))
  :hints (("Goal" :induct (adt-zeros n) :in-theory (enable resize-list adt-zeros len)))))

(defthm fn-his-grow-fresh-words
 (implies (and (posp np) (equal (pgs-w-length pgs-mem) 0) (equal (pgs-v-length pgs-mem) 0))
  (equal (nth *pgs-wi* (pgs-x-grow-image np pgs-mem)) (adt-zeros (* 2048 np))))
 :hints (("Goal" :use ((:instance fn-hp-grow-image-words (npn np)))
          :in-theory (e/d (pgs-w-length) (pgs-x-grow-image fn-hp-grow-image-words
                                        nth adt-nth-1+ adt-zeros (:e adt-zeros))))))

(defthm fn-his-image-open-words
 (implies (and (fn-hp-okp h salt)
               (equal (pgs-w-length pgs-mem) 0) (equal (pgs-v-length pgs-mem) 0)
               (equal (pgs-d-length pgs-mem) 0))
  (equal (nth *pgs-wi* (mv-nth 3 (fn-his-image-open (list (len h) (fn-hp-lens h salt)) pgs-mem)))
         (fn-hp-rep (adt-zeros (* 2048 (fn-hp-npages h salt))) 0
                     (fn-hp-hdr2 (len h) (fn-hp-lens h salt) (fn-hp-starts h salt) (fn-hp-npages h salt)))))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-his-grow-fresh-words (np (fn-hp-npages h salt)))
                (:instance fn-hp-x-mark-frame (i 0) (k (fn-hp-npages h salt))
                  (pgs-mem (fn-hp-x-put 0
                    (fn-hp-hdr2 (len h) (fn-hp-lens h salt) (fn-hp-starts h salt) (fn-hp-npages h salt))
                    (pgs-x-grow-image (fn-hp-npages h salt) pgs-mem))))
                (:instance fn-hp-grow-image-lengths (np 0) (npn (fn-hp-npages h salt)))
                (:instance fn-hp-x-put-words
                  (j 0) (ws (fn-hp-hdr2 (len h) (fn-hp-lens h salt) (fn-hp-starts h salt) (fn-hp-npages h salt)))
                  (pgs-mem (pgs-x-grow-image (fn-hp-npages h salt) pgs-mem))))
          :in-theory (e/d (fn-his-image-open)
                          (fn-his-layout fn-hp-okp fn-hp-lens fn-hp-starts fn-hp-npages
                           fn-his-canonical-lens pgs-x-grow-image fn-hp-x-put fn-hp-x-mark fn-hp-hdr2
                           fn-hp-rep adt-zeros (:e adt-zeros) floor nth adt-nth-1+ adt-nth-0)))))

(defthm fn-his-image-open-all-dirty
 (implies (and (fn-hp-okp h salt)
               (equal (pgs-w-length pgs-mem) 0) (equal (pgs-v-length pgs-mem) 0)
               (equal (pgs-d-length pgs-mem) 0))
  (fn-his-all-dirty 0 (fn-hp-npages h salt)
    (nth *pgs-di* (mv-nth 3 (fn-his-image-open (list (len h) (fn-hp-lens h salt)) pgs-mem)))))
 :hints (("Goal" :in-theory (e/d (fn-his-image-open)
                                (fn-his-layout fn-hp-okp fn-hp-lens fn-hp-starts fn-hp-npages
                                 fn-his-canonical-lens pgs-x-grow-image fn-hp-x-put fn-hp-x-mark
                                 fn-hp-hdr2 fn-his-all-dirty nth adt-nth-1+)))))
