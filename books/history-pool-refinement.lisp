; Proof-only carried residual for the actual history pool emitter.
(in-package "ACL2")
(include-book "history-pool-emitter")
(include-book "history-pages-row")
(local (include-book "arithmetic-5/top" :dir :system))

(defun fn-hper-pack (bytes)
  (declare (xargs :guard t :verify-guards nil))
  (fn-hp-pack8 (ceiling (len bytes) 8) bytes))

(defun fn-hper-pending (c partial)
  (declare (xargs :guard t :verify-guards nil))
  (fn-hper-pack (append partial (fn-hrcur-byte-rest (fn-hrcur-field 1 c)))))

(defun fn-hper-invariantp (c partial)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-hpe-invariantp c)
       (fn-scc-octet-listp partial)
       (equal (len partial) (fn-hrcur-field 2 c))
       (equal (fn-hrcur-field 3 c) (adt-unle (len partial) partial))
       (implies (equal (fn-hrcur-field 0 c) :prepared) (equal partial nil))))

; This logical update describes the seven-byte residual, never a host list.
(defun fn-hper-partial-next (c partial fn-hpb)
  (declare (xargs :stobjs fn-hpb :verify-guards nil))
  (if (or (not (fn-hpe-shapep c)) (fn-hpb-ready fn-hpb)
          (member-eq (fn-hrcur-field 0 c) '(:prepared :refused))) partial
    (if (equal (fn-hrcur-field 0 c) :finish) nil
      (mv-let (v byte next) (fn-hrcur-byte-tick (fn-hrcur-field 1 c))
        (declare (ignore next))
        (if (equal v :emit)
            (if (equal (fn-hrcur-field 2 c) 7) nil
              (append partial (list byte)))
          partial)))))

(local
 (defthm fn-hper-unle-append-exact
   (implies (true-listp prefix)
            (equal (adt-unle (len prefix) (append prefix rest))
                   (adt-unle (len prefix) prefix)))
   :hints (("Goal" :induct (len prefix) :in-theory (enable adt-unle)))))

(local
 (defthm fn-hper-nthcdr-prefix
   (implies (true-listp prefix)
            (equal (nthcdr (len prefix) (append prefix rest)) rest))
   :hints (("Goal" :induct (len prefix) :in-theory (enable nthcdr)))))

(defthm fn-hper-eight-byte-prefix
  (implies (and (true-listp prefix) (equal (len prefix) 8))
           (equal (fn-hper-pack (append prefix rest))
                  (cons (car (fn-hp-pack8 1 prefix)) (fn-hper-pack rest))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hper-unle-append-exact)
                 (:instance fn-hper-nthcdr-prefix))
           :expand ((:free (n) (fn-hp-pack8 n (append prefix rest)))
                    (fn-hp-pack8 1 prefix))
           :in-theory (e/d (fn-hper-pack) (fn-hp-pack8 adt-unle nthcdr
                      fn-hper-unle-append-exact fn-hper-nthcdr-prefix
                      adt-nthcdr-of-append-less adt-unle-append)))))

(defthm fn-hper-begin-establishes-packing-carry
  (implies (and (fn-hrcur-tree-domainp row)
                (< (len (fn-scc-encode row)) 18446744073709551616))
           (and (fn-hper-invariantp (fn-hpe-begin (list :resident row) capture lease) nil)
                (equal (fn-hper-pending (fn-hpe-begin (list :resident row) capture lease) nil)
                       (fn-hper-pack (fn-scc-encode row)))))
  :hints (("Goal" :use ((:instance fn-hpe-begin-refines-byte-total)
                        (:instance fn-hrcur-byte-begin-refines-encode))
           :in-theory (e/d (fn-hpe-begin)
                            (fn-hpe-invariantp fn-hper-pack fn-hrcur-byte-begin
                             fn-hrcur-byte-rest fn-hrcur-byte-invariantp
                             fn-hrcur-tree-domainp fn-scc-encode fn-scc-program
                             fn-scc-encode-is-program fn-hpe-begin-refines-byte-total
                             fn-hrcur-byte-begin-refines-encode)))))

(local
 (defthm fn-hper-octets-append-byte
   (implies (and (fn-scc-octet-listp partial) (fn-scc-octetp byte))
            (fn-scc-octet-listp (append partial (list byte))))
   :hints (("Goal" :in-theory (enable fn-scc-octet-listp)))))

(local
 (defthm fn-hper-carried-fields
   (implies (fn-hpe-invariantp c)
            (and (fn-hpe-shapep c)
                 (fn-hrcur-byte-invariantp (fn-hrcur-field 1 c))
                 (fn-hrcur-wordp (fn-hrcur-field 2 c) (fn-hrcur-field 3 c))
                 (natp (fn-hrcur-field 2 c)) (< (fn-hrcur-field 2 c) 8)))
   :hints (("Goal" :in-theory (enable fn-hpe-invariantp fn-hpe-shapep fn-hrcur-wordp)))))

(local
 (defthm fn-hper-octet-singleton
   (implies (fn-scc-octetp byte) (fn-scc-octet-listp (list byte)))
   :hints (("Goal" :in-theory (enable fn-scc-octet-listp)))))

 ; Phase-local proof: nonemitting child transition carries k/w and partial.
(local
 (defthm fn-hper-codec-nonemit-carry
  (implies (and (fn-hper-invariantp c partial)
                (equal (fn-hrcur-field 0 c) :codec)
                (not (fn-hpb-ready fn-hpb))
                (not (equal (mv-nth 0 (fn-hrcur-byte-tick (fn-hrcur-field 1 c))) :emit)))
           (fn-hper-invariantp (mv-nth 2 (fn-hpe-tick c fn-hpb))
                              (fn-hper-partial-next c partial fn-hpb)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hper-carried-fields)
                 (:instance fn-hpe-tick-preserves-byte-total)
                 (:instance fn-hrcur-byte-tick-preserves (c (fn-hrcur-field 1 c))))
           :in-theory (e/d (fn-hpe-tick fn-hper-invariantp fn-hper-partial-next)
                           (fn-hpe-invariantp fn-hpe-shapep fn-hper-carried-fields
                            fn-hrcur-byte-tick fn-hrcur-byte-invariantp
                            fn-hrcur-word-push fn-hrcur-word-finish fn-hpb-put
                            fn-hpe-tick-preserves-byte-total fn-hrcur-byte-tick-preserves
                            adt-unle unsigned-byte-p fn-scc-octetp))))))

(local
 (defthm fn-hper-codec-partial-carry
  (implies (and (fn-hper-invariantp c partial)
                (equal (fn-hrcur-field 0 c) :codec)
                (not (fn-hpb-ready fn-hpb))
                (< (fn-hrcur-field 2 c) 7)
                (equal (mv-nth 0 (fn-hrcur-byte-tick (fn-hrcur-field 1 c))) :emit))
           (fn-hper-invariantp (mv-nth 2 (fn-hpe-tick c fn-hpb))
                              (fn-hper-partial-next c partial fn-hpb)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hper-carried-fields)
                 (:instance fn-hpe-tick-preserves-byte-total)
                 (:instance fn-hrcur-byte-tick-preserves (c (fn-hrcur-field 1 c)))
                 (:instance fn-hrcur-word-push-refines-partial
                            (prefix partial) (k (fn-hrcur-field 2 c)) (w (fn-hrcur-field 3 c))
                            (octet (mv-nth 1 (fn-hrcur-byte-tick (fn-hrcur-field 1 c))))))
           :in-theory (e/d (fn-hpe-tick fn-hper-invariantp fn-hper-partial-next)
                           (fn-hpe-invariantp fn-hpe-shapep fn-hper-carried-fields
                            fn-hrcur-byte-tick fn-hrcur-byte-invariantp
                            fn-hrcur-word-push fn-hrcur-word-finish fn-hpb-put
                            fn-hpe-tick-preserves-byte-total fn-hrcur-byte-tick-preserves
                            fn-hrcur-word-push-refines-partial
                            adt-unle unsigned-byte-p fn-scc-octetp))))))

(local
 (defthm fn-hper-codec-eighth-carry
  (implies (and (fn-hper-invariantp c partial)
                (equal (fn-hrcur-field 0 c) :codec)
                (not (fn-hpb-ready fn-hpb))
                (equal (fn-hrcur-field 2 c) 7)
                (equal (mv-nth 0 (fn-hrcur-byte-tick (fn-hrcur-field 1 c))) :emit))
           (fn-hper-invariantp (mv-nth 2 (fn-hpe-tick c fn-hpb))
                              (fn-hper-partial-next c partial fn-hpb)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hper-carried-fields)
                 (:instance fn-hpe-tick-preserves-byte-total)
                 (:instance fn-hrcur-byte-tick-preserves (c (fn-hrcur-field 1 c)))
                 (:instance fn-hrcur-word-push-refines-pack8
                            (prefix partial) (w (fn-hrcur-field 3 c))
                            (octet (mv-nth 1 (fn-hrcur-byte-tick (fn-hrcur-field 1 c))))))
           :in-theory (e/d (fn-hpe-tick fn-hper-invariantp fn-hper-partial-next)
                           (fn-hpe-invariantp fn-hpe-shapep fn-hper-carried-fields
                            fn-hrcur-byte-tick fn-hrcur-byte-invariantp
                            fn-hrcur-word-push fn-hrcur-word-finish fn-hpb-put
                            fn-hpe-tick-preserves-byte-total fn-hrcur-byte-tick-preserves
                            fn-hrcur-word-push-refines-pack8
                            fn-hp-pack8 adt-unle unsigned-byte-p fn-scc-octetp))))))

(local
 (defthm fn-hper-finish-carry
  (implies (and (fn-hper-invariantp c partial)
                (equal (fn-hrcur-field 0 c) :finish)
                (not (fn-hpb-ready fn-hpb)))
           (fn-hper-invariantp (mv-nth 2 (fn-hpe-tick c fn-hpb))
                              (fn-hper-partial-next c partial fn-hpb)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hper-carried-fields)
                 (:instance fn-hpe-tick-preserves-byte-total))
           :in-theory (e/d (fn-hpe-tick fn-hper-invariantp fn-hper-partial-next)
                           (fn-hpe-invariantp fn-hpe-shapep fn-hper-carried-fields
                            fn-hrcur-byte-tick fn-hrcur-byte-invariantp
                            fn-hrcur-word-push fn-hrcur-word-finish fn-hpb-put
                            fn-hpe-tick-preserves-byte-total
                            fn-hp-pack8 adt-unle unsigned-byte-p fn-scc-octetp))))))


(local
 (defthm fn-hper-stationary-carry
  (implies (and (fn-hper-invariantp c partial)
                (or (fn-hpb-ready fn-hpb)
                    (equal (fn-hrcur-field 0 c) :prepared)))
           (fn-hper-invariantp (mv-nth 2 (fn-hpe-tick c fn-hpb))
                              (fn-hper-partial-next c partial fn-hpb)))
  :hints (("Goal" :use ((:instance fn-hper-carried-fields))
           :in-theory (e/d (fn-hpe-tick fn-hper-invariantp fn-hper-partial-next)
                           (fn-hpe-invariantp fn-hpe-shapep fn-hper-carried-fields
                            fn-hrcur-byte-tick fn-hrcur-word-push fn-hrcur-word-finish
                            fn-hpb-put adt-unle))))))

(local
 (defthm fn-hper-phase-range
  (implies (fn-hper-invariantp c partial)
           (and (member-eq (fn-hrcur-field 0 c) '(:codec :finish :prepared))
                (natp (fn-hrcur-field 2 c)) (< (fn-hrcur-field 2 c) 8)))
  :hints (("Goal" :use ((:instance fn-hper-carried-fields))
           :in-theory (e/d (fn-hper-invariantp fn-hpe-invariantp)
                           (fn-hpe-shapep fn-hper-carried-fields))))))

(defthm fn-hper-tick-preserves-packing-carry
  (implies (fn-hper-invariantp c partial)
           (fn-hper-invariantp (mv-nth 2 (fn-hpe-tick c fn-hpb))
                              (fn-hper-partial-next c partial fn-hpb)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hper-phase-range)
                 (:instance fn-hper-stationary-carry)
                 (:instance fn-hper-codec-nonemit-carry)
                 (:instance fn-hper-codec-partial-carry)
                 (:instance fn-hper-codec-eighth-carry)
                 (:instance fn-hper-finish-carry))
           :in-theory (disable fn-hper-invariantp fn-hper-partial-next fn-hpe-invariantp
                               fn-hpe-tick fn-hpe-shapep fn-hrcur-byte-tick
                               fn-hper-phase-range fn-hper-stationary-carry
                               fn-hper-codec-nonemit-carry fn-hper-codec-partial-carry
                               fn-hper-codec-eighth-carry fn-hper-finish-carry))))

(local
 (defthm fn-hper-emit-room
  (implies (and (fn-hpe-invariantp c)
                (equal (mv-nth 0 (fn-hrcur-byte-tick (fn-hrcur-field 1 c))) :emit))
           (and (fn-scc-octetp (mv-nth 1 (fn-hrcur-byte-tick (fn-hrcur-field 1 c))))
                (< (+ 1 (fn-hrcur-field 4 c)) 18446744073709551616)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hper-carried-fields)
                 (:instance fn-hrcur-byte-tick-preserves (c (fn-hrcur-field 1 c)))
                 (:instance fn-hrcur-byte-tick-refines-residual (c (fn-hrcur-field 1 c))))
           :in-theory (e/d (fn-hpe-invariantp fn-hpe-total fn-hpe-shapep)
                           (fn-hrcur-byte-tick fn-hrcur-byte-rest fn-hrcur-byte-invariantp
                            fn-hper-carried-fields fn-hrcur-byte-tick-preserves
                            fn-hrcur-byte-tick-refines-residual fn-hrcur-wordp))))))

(defthm fn-hper-prepared-has-no-pending
  (implies (and (fn-hper-invariantp c partial)
                (equal (fn-hrcur-field 0 c) :prepared))
           (equal (fn-hper-pending c partial) nil))
  :hints (("Goal" :in-theory (e/d (fn-hper-invariantp fn-hper-pending fn-hper-pack
                                  fn-hpe-invariantp)
                                 (fn-hrcur-byte-rest fn-hpe-shapep)))))

(local
 (defthm fn-hper-codec-nonemit-pending
  (implies (and (fn-hper-invariantp c partial)
                (equal (fn-hrcur-field 0 c) :codec)
                (not (fn-hpb-ready fn-hpb))
                (not (equal (mv-nth 0 (fn-hrcur-byte-tick (fn-hrcur-field 1 c))) :emit)))
           (and (equal (fn-hper-pending c partial)
                       (fn-hper-pending (mv-nth 2 (fn-hpe-tick c fn-hpb))
                                        (fn-hper-partial-next c partial fn-hpb)))
                (equal (mv-nth 3 (fn-hpe-tick c fn-hpb)) fn-hpb)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hper-carried-fields)
                 (:instance fn-hrcur-byte-tick-preserves (c (fn-hrcur-field 1 c)))
                 (:instance fn-hrcur-byte-tick-refines-residual (c (fn-hrcur-field 1 c))))
           :in-theory (e/d (fn-hpe-tick fn-hper-invariantp fn-hper-pending fn-hper-partial-next)
                           (fn-hpe-invariantp fn-hpe-shapep fn-hper-carried-fields
                            fn-hrcur-byte-tick fn-hrcur-byte-invariantp fn-hrcur-byte-rest
                            fn-hrcur-word-push fn-hrcur-word-finish fn-hpb-put
                            fn-hper-pack fn-hrcur-byte-tick-preserves
                            fn-hrcur-byte-tick-refines-residual adt-unle))))))

(local
 (defthm fn-hper-codec-partial-pending
  (implies (and (fn-hper-invariantp c partial)
                (equal (fn-hrcur-field 0 c) :codec)
                (not (fn-hpb-ready fn-hpb))
                (< (fn-hrcur-field 2 c) 7)
                (equal (mv-nth 0 (fn-hrcur-byte-tick (fn-hrcur-field 1 c))) :emit))
           (and (equal (fn-hper-pending c partial)
                       (fn-hper-pending (mv-nth 2 (fn-hpe-tick c fn-hpb))
                                        (fn-hper-partial-next c partial fn-hpb)))
                (equal (mv-nth 3 (fn-hpe-tick c fn-hpb)) fn-hpb)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hper-carried-fields)
                 (:instance fn-hper-emit-room)
                 (:instance fn-hrcur-byte-tick-refines-residual (c (fn-hrcur-field 1 c)))
                 (:instance fn-hrcur-word-push-refines-partial
                            (prefix partial) (k (fn-hrcur-field 2 c)) (w (fn-hrcur-field 3 c))
                            (octet (mv-nth 1 (fn-hrcur-byte-tick (fn-hrcur-field 1 c))))))
           :in-theory (e/d (fn-hpe-tick fn-hper-invariantp fn-hper-pending fn-hper-partial-next)
                           (fn-hpe-invariantp fn-hpe-shapep fn-hper-carried-fields
                            fn-hrcur-byte-tick fn-hrcur-byte-invariantp fn-hrcur-byte-rest
                            fn-hrcur-word-push fn-hrcur-word-finish fn-hpb-put
                            fn-hper-pack fn-hper-emit-room
                            fn-hrcur-word-push-refines-partial
                            fn-hrcur-byte-tick-refines-residual adt-unle unsigned-byte-p fn-scc-octetp))))))

(local
 (defthm fn-hper-scratch-room
  (implies (and (fn-hpbp fn-hpb) (not (fn-hpb-ready fn-hpb)))
           (and (natp (fn-hpb-used fn-hpb)) (< (fn-hpb-used fn-hpb) 2048)))))

(local
 (defthm fn-hper-codec-eighth-pending
  (implies (and (fn-hper-invariantp c partial) (fn-hpbp fn-hpb)
                (equal (fn-hrcur-field 0 c) :codec)
                (not (fn-hpb-ready fn-hpb))
                (equal (fn-hrcur-field 2 c) 7)
                (equal (mv-nth 0 (fn-hrcur-byte-tick (fn-hrcur-field 1 c))) :emit))
           (equal (append (fn-hpb-prefix fn-hpb) (fn-hper-pending c partial))
                  (append (fn-hpb-prefix (mv-nth 3 (fn-hpe-tick c fn-hpb)))
                          (fn-hper-pending (mv-nth 2 (fn-hpe-tick c fn-hpb))
                                           (fn-hper-partial-next c partial fn-hpb)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hper-carried-fields)
                 (:instance fn-hper-emit-room)
                 (:instance fn-hper-scratch-room)
                 (:instance fn-hrcur-byte-tick-refines-residual (c (fn-hrcur-field 1 c)))
                 (:instance fn-hper-eight-byte-prefix
                   (prefix (append partial (list (mv-nth 1 (fn-hrcur-byte-tick (fn-hrcur-field 1 c))))))
                   (rest (fn-hrcur-byte-rest (mv-nth 2 (fn-hrcur-byte-tick (fn-hrcur-field 1 c))))))
                 (:instance fn-hpe-eighth-byte-refines-pool-word (prefix partial))
                 (:instance fn-hrcur-word-push-refines-pack8
                            (prefix partial) (w (fn-hrcur-field 3 c))
                            (octet (mv-nth 1 (fn-hrcur-byte-tick (fn-hrcur-field 1 c))))))
           :in-theory (e/d (fn-hpe-tick fn-hper-invariantp fn-hper-pending fn-hper-partial-next
                            fn-scc-octet-listp)
                           (fn-hpe-invariantp fn-hpe-shapep fn-hper-carried-fields
                            fn-hrcur-byte-tick fn-hrcur-byte-invariantp fn-hrcur-byte-rest
                            fn-hrcur-word-push fn-hrcur-word-finish fn-hpb-put fn-hpb-prefix
                            fn-hper-pack fn-hper-emit-room fn-hper-scratch-room
                            fn-hper-eight-byte-prefix fn-hpe-eighth-byte-refines-pool-word
                            fn-hrcur-word-push-refines-pack8 fn-hp-pack8
                            fn-hrcur-byte-tick-refines-residual adt-unle unsigned-byte-p fn-scc-octetp))))))

(local
 (defthm fn-hper-unle-past-end
  (implies (and (natp n) (<= (len partial) n))
           (equal (adt-unle n partial) (adt-unle (len partial) partial)))
  :rule-classes nil
  :hints (("Goal" :induct (adt-unle n partial) :in-theory (enable adt-unle)))))

(local
 (defthm fn-hper-pack-partial
  (implies (and (natp k) (< k 8) (equal (len partial) k))
           (equal (fn-hper-pack partial)
                  (if (equal k 0) nil (list (adt-unle k partial)))))
  :hints (("Goal" :do-not-induct t
           :cases ((equal k 0) (equal k 1) (equal k 2) (equal k 3)
                   (equal k 4) (equal k 5) (equal k 6) (equal k 7))
           :use ((:instance fn-hper-unle-past-end (n 8)))
           :expand ((fn-hp-pack8 1 partial) (:free (b) (fn-hp-pack8 0 b)))
           :in-theory (e/d (fn-hper-pack) (adt-unle nthcdr fn-hp-pack8))))))

(local
 (defthm fn-hper-word-value-u64
  (implies (fn-hrcur-wordp k w) (unsigned-byte-p 64 w))
  :hints (("Goal" :cases ((equal k 0) (equal k 1) (equal k 2) (equal k 3)
                          (equal k 4) (equal k 5) (equal k 6) (equal k 7))
           :in-theory (enable fn-hrcur-wordp unsigned-byte-p)))))

(local
 (defthm fn-hper-finish-pending
  (implies (and (fn-hper-invariantp c partial) (fn-hpbp fn-hpb)
                (equal (fn-hrcur-field 0 c) :finish)
                (not (fn-hpb-ready fn-hpb)))
           (equal (append (fn-hpb-prefix fn-hpb) (fn-hper-pending c partial))
                  (append (fn-hpb-prefix (mv-nth 3 (fn-hpe-tick c fn-hpb)))
                          (fn-hper-pending (mv-nth 2 (fn-hpe-tick c fn-hpb))
                                           (fn-hper-partial-next c partial fn-hpb)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hper-carried-fields)
                 (:instance fn-hper-scratch-room)
                 (:instance fn-hper-pack-partial (k (fn-hrcur-field 2 c)))
                 (:instance fn-hper-word-value-u64 (k (fn-hrcur-field 2 c))
                            (w (fn-hrcur-field 3 c))))
           :in-theory (e/d (fn-hpe-tick fn-hper-invariantp fn-hper-pending fn-hper-partial-next
                            fn-hpe-invariantp fn-hrcur-word-finish)
                           (fn-hpe-shapep fn-hper-carried-fields fn-hper-scratch-room fn-hper-word-value-u64
                            fn-hrcur-byte-tick fn-hrcur-byte-invariantp fn-hrcur-byte-rest
                            fn-hrcur-word-push fn-hrcur-wordp fn-hpb-put fn-hpb-prefix
                            fn-hper-pack fn-hper-pack-partial
                            adt-unle unsigned-byte-p fn-scc-octetp))))))

(local
 (defthm fn-hper-stationary-pending
  (implies (and (fn-hper-invariantp c partial)
                (or (fn-hpb-ready fn-hpb)
                    (equal (fn-hrcur-field 0 c) :prepared)))
           (and (equal (fn-hper-pending c partial)
                       (fn-hper-pending (mv-nth 2 (fn-hpe-tick c fn-hpb))
                                        (fn-hper-partial-next c partial fn-hpb)))
                (equal (mv-nth 3 (fn-hpe-tick c fn-hpb)) fn-hpb)))
  :hints (("Goal" :use ((:instance fn-hper-carried-fields))
           :in-theory (e/d (fn-hpe-tick fn-hper-invariantp fn-hper-partial-next)
                           (fn-hpe-invariantp fn-hpe-shapep fn-hper-carried-fields
                            fn-hper-pending fn-hrcur-byte-tick fn-hrcur-word-push
                            fn-hrcur-word-finish fn-hpb-put adt-unle))))))

; Exact semantic boundary over the actual child and concrete scratch effects.
(defthm fn-hper-tick-refines-pool-residual
  (implies (and (fn-hper-invariantp c partial) (fn-hpbp fn-hpb))
           (equal (append (fn-hpb-prefix fn-hpb) (fn-hper-pending c partial))
                  (append (fn-hpb-prefix (mv-nth 3 (fn-hpe-tick c fn-hpb)))
                          (fn-hper-pending (mv-nth 2 (fn-hpe-tick c fn-hpb))
                                           (fn-hper-partial-next c partial fn-hpb)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hper-phase-range)
                 (:instance fn-hper-stationary-pending)
                 (:instance fn-hper-codec-nonemit-pending)
                 (:instance fn-hper-codec-partial-pending)
                 (:instance fn-hper-codec-eighth-pending)
                 (:instance fn-hper-finish-pending))
           :in-theory (disable fn-hper-invariantp fn-hper-partial-next fn-hper-pending
                               fn-hpe-tick fn-hpe-shapep fn-hrcur-byte-tick fn-hpbp
                               fn-hpb-prefix fn-hper-phase-range fn-hper-stationary-pending
                               fn-hper-codec-nonemit-pending fn-hper-codec-partial-pending
                               fn-hper-codec-eighth-pending fn-hper-finish-pending))))

; Reset after the outer owner has retained the completed page in its trace.
; This theorem grants no I/O completion or lease release.
(defthm fn-hper-page-reset-transfers-prefix
  (equal (append completed
                 (append (fn-hpb-prefix fn-hpb) (fn-hper-pending c partial)))
         (append (append completed (fn-hpb-prefix fn-hpb))
                 (append (fn-hpb-prefix (fn-hpb-begin epoch lease fn-hpb))
                         (fn-hper-pending c partial))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-hpb-prefix fn-hpb-begin fn-hper-pending))))

; Proof-only finite trace of actual tick/reset effects. No host collector.
(defun fn-hper-run (fuel c partial completed fn-hpb)
  (declare (xargs :stobjs fn-hpb :verify-guards nil))
  (if (zp fuel) (mv c partial completed fn-hpb)
    (if (fn-hpb-ready fn-hpb)
        (let* ((next-completed (append completed (fn-hpb-prefix fn-hpb)))
               (epoch (fn-hpb-epoch fn-hpb)) (lease (fn-hpb-lease fn-hpb))
               (fn-hpb (fn-hpb-begin epoch lease fn-hpb)))
          (fn-hper-run (1- fuel) c partial next-completed fn-hpb))
      (let ((next-partial (fn-hper-partial-next c partial fn-hpb)))
        (mv-let (verdict summary next fn-hpb) (fn-hpe-tick c fn-hpb)
          (declare (ignore verdict summary))
          (fn-hper-run (1- fuel) next next-partial completed fn-hpb))))))

(defthm fn-hper-run-preserves-carried-state
  (implies (and (fn-hper-invariantp c partial) (fn-hpbp fn-hpb))
           (and (fn-hper-invariantp (mv-nth 0 (fn-hper-run fuel c partial completed fn-hpb))
                                   (mv-nth 1 (fn-hper-run fuel c partial completed fn-hpb)))
                (fn-hpbp (mv-nth 3 (fn-hper-run fuel c partial completed fn-hpb)))))
  :hints (("Goal" :induct (fn-hper-run fuel c partial completed fn-hpb)
           :in-theory (e/d (fn-hper-run)
                           (fn-hper-invariantp fn-hper-partial-next fn-hpe-tick
                            fn-hpbp fn-hpb-begin fn-hpb-prefix)))))

(defthm fn-hper-run-refines-pool-stream
  (implies (and (fn-hper-invariantp c partial) (fn-hpbp fn-hpb))
           (equal
            (append completed (append (fn-hpb-prefix fn-hpb) (fn-hper-pending c partial)))
            (append (mv-nth 2 (fn-hper-run fuel c partial completed fn-hpb))
                    (append (fn-hpb-prefix (mv-nth 3 (fn-hper-run fuel c partial completed fn-hpb)))
                            (fn-hper-pending (mv-nth 0 (fn-hper-run fuel c partial completed fn-hpb))
                                             (mv-nth 1 (fn-hper-run fuel c partial completed fn-hpb)))))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-hper-run fuel c partial completed fn-hpb)
           :in-theory (e/d (fn-hper-run)
                           (fn-hper-invariantp fn-hper-partial-next fn-hper-pending fn-hpe-tick
                            fn-hpbp fn-hpb-begin fn-hpb-prefix)))
          ("Subgoal *1/3" :use ((:instance fn-hper-tick-refines-pool-residual)))))

(local
 (defthm fn-hper-emitter-invariant
  (implies (fn-hper-invariantp c partial) (fn-hpe-invariantp c))
  :hints (("Goal" :in-theory (enable fn-hper-invariantp)))))

(defthm fn-hper-run-preserves-byte-total
  (implies (and (fn-hper-invariantp c partial) (fn-hpbp fn-hpb))
           (equal (fn-hpe-total (mv-nth 0 (fn-hper-run fuel c partial completed fn-hpb)))
                  (fn-hpe-total c)))
  :hints (("Goal" :induct (fn-hper-run fuel c partial completed fn-hpb)
           :in-theory (e/d (fn-hper-run)
                           (fn-hper-invariantp fn-hper-partial-next fn-hpe-tick fn-hpe-invariantp fn-hpe-total
                            fn-hpbp fn-hpb-begin fn-hpb-prefix)))))

(local
 (defthm fn-hper-prepared-total-is-count
  (implies (and (fn-hper-invariantp c partial)
                (equal (fn-hrcur-field 0 c) :prepared))
           (equal (fn-hpe-total c) (fn-hrcur-field 4 c)))
  :hints (("Goal" :in-theory (e/d (fn-hper-invariantp fn-hpe-invariantp fn-hpe-shapep fn-hpe-total)
                                 (fn-hrcur-byte-rest fn-hrcur-wordp))))))

; Terminal refinement of any finite actual tick/reset trace from current codec.
; Completion/progress and the outer I/O authorization are separate obligations.
(defthm fn-hper-completed-row-is-current-codec-pool
  (let* ((initial (fn-hpe-begin (list :resident row) capture lease))
         (result (fn-hper-run fuel initial nil nil fn-hpb)))
    (implies (and (fn-hrcur-tree-domainp row)
                  (< (len (fn-scc-encode row)) 18446744073709551616)
                  (fn-hpbp fn-hpb) (equal (fn-hpb-prefix fn-hpb) nil)
                  (equal (fn-hrcur-field 0 (mv-nth 0 result)) :prepared))
             (and (equal (append (mv-nth 2 result) (fn-hpb-prefix (mv-nth 3 result)))
                         (fn-hper-pack (fn-scc-encode row)))
                  (equal (fn-hrcur-field 4 (mv-nth 0 result)) (len (fn-scc-encode row))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hper-begin-establishes-packing-carry)
                 (:instance fn-hpe-begin-refines-byte-total)
                 (:instance fn-hper-run-preserves-carried-state
                    (c (fn-hpe-begin (list :resident row) capture lease)) (partial nil) (completed nil))
                 (:instance fn-hper-run-preserves-byte-total
                    (c (fn-hpe-begin (list :resident row) capture lease)) (partial nil) (completed nil))
                 (:instance fn-hper-run-refines-pool-stream
                    (c (fn-hpe-begin (list :resident row) capture lease)) (partial nil) (completed nil)))
           :in-theory (e/d ()
                           (fn-hper-run fn-hper-pack fn-hper-pending fn-hpe-begin fn-hpe-shapep
                            fn-hper-invariantp fn-hpe-invariantp fn-hpe-total
                            fn-scc-encode-is-program fn-hper-pack-partial
                            fn-hrcur-byte-rest fn-hpb-prefix fn-hpbp fn-scc-encode
                            fn-hper-begin-establishes-packing-carry fn-hpe-begin-refines-byte-total
                            fn-hper-run-preserves-carried-state fn-hper-run-preserves-byte-total)))))
