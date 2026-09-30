; Complete tagged resident/cold residual for the actual concrete pool emitter.
; The partial is a proof-only seven-octet carry, never a host collector.
(in-package "ACL2")
(include-book "history-pool-refinement")
(include-book "history-source-byte-refinement")
(local (include-book "arithmetic-5/top" :dir :system))

(defun-nx fn-hpert-total (c pool)
  (+ (nfix (fn-hrcur-field 4 c)) (len (fn-hsrcb-rest (fn-hrcur-field 1 c) pool))))
(defun-nx fn-hpert-emitter-invariantp (c pool)
  (and (fn-hpe-shapep c)
       (member-eq (fn-hrcur-field 0 c) '(:codec :finish :prepared))
       (fn-hsrcb-invariantp (fn-hrcur-field 1 c) pool)
       (< (fn-hpert-total c pool) *fn-hrcur-u64-bound*)
       (implies (member-eq (fn-hrcur-field 0 c) '(:finish :prepared))
                (equal (fn-hsrcb-rest (fn-hrcur-field 1 c) pool) nil))))
(defun-nx fn-hpert-invariantp (c partial pool)
  (and (fn-hpert-emitter-invariantp c pool)
       (fn-scc-octet-listp partial)
       (equal (len partial) (fn-hrcur-field 2 c))
       (equal (fn-hrcur-field 3 c) (adt-unle (len partial) partial))
       (implies (equal (fn-hrcur-field 0 c) :prepared) (equal partial nil))))
(defun-nx fn-hpert-pending (c partial pool)
  (fn-hper-pack (append partial (fn-hsrcb-rest (fn-hrcur-field 1 c) pool))))
(defun fn-hpert-partial-next (c partial fn-hpb)
  (declare (xargs :stobjs fn-hpb :verify-guards nil))
  (if (or (not (fn-hpe-shapep c)) (fn-hpb-ready fn-hpb)
          (member-eq (fn-hrcur-field 0 c) '(:prepared :refused))) partial
    (if (equal (fn-hrcur-field 0 c) :finish) nil
      (mv-let (v byte next) (fn-hsrcb-tick (fn-hrcur-field 1 c))
        (declare (ignore next))
        (if (equal v :emit)
            (if (equal (fn-hrcur-field 2 c) 7) nil
              (append partial (list byte)))
          partial)))))
(defun fn-hpert-partial-supply (c partial position byte fn-hpb)
  (declare (xargs :stobjs fn-hpb :verify-guards nil))
  (if (or (not (fn-hpe-shapep c)) (fn-hpb-ready fn-hpb)
          (not (eq (fn-hrcur-field 0 c) :codec))) partial
    (mv-let (v emitted next) (fn-hsrcb-supply (fn-hrcur-field 1 c) position byte)
      (declare (ignore next))
      (if (equal v :emit)
          (if (equal (fn-hrcur-field 2 c) 7) nil
            (append partial (list emitted)))
        partial))))

(local
 (defthm fn-hpert-scalar-not-demand
   (not (eq (fn-hrcur-field 0 (mv-nth 0 (fn-hrsc-tick child))) :need-byte))
   :hints (("Goal" :in-theory (enable fn-hrsc-tick)))))
(local
 (defthm fn-hpert-cold-demand-width
   (implies (eq (fn-hrcur-field 0 (mv-nth 0 (fn-hrcur-cold-tick c))) :need-byte)
            (fn-hsrcb-demandp (mv-nth 0 (fn-hrcur-cold-tick c))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
     :use ((:instance fn-hpert-scalar-not-demand (child (fn-hrcur-field 2 c))))
     :in-theory (e/d (fn-hrcur-cold-tick fn-hrcur-cold-demand fn-hsrcb-demandp fn-hrcur-widthp)
                     (fn-hrcur-dos-tick fn-hdsn-tick fn-hrsc-tick fn-hrcur-span-tick
                      fn-hrcur-cold-symbol-childp fn-hrcur-cold-state fn-hpert-scalar-not-demand))))))

(local
 (defthm fn-hpert-child-tick-range
  (implies (fn-hsrcb-invariantp c pool)
    (or (member-eq (mv-nth 0 (fn-hsrcb-tick c)) '(:continue :emit :prepared))
        (fn-hsrcb-demandp (mv-nth 0 (fn-hsrcb-tick c)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :cases ((fn-hsrcb-coldp c))
    :use ((:instance fn-hpert-cold-demand-width (c (fn-hrcur-field 1 c)))
          (:instance fn-hrcur-cold-tick-current-codec-boundary (c (fn-hrcur-field 1 c)))
          (:instance fn-hrcur-byte-tick-preserves))
    :in-theory (e/d (fn-hsrcb-invariantp fn-hsrcb-tick fn-hsrcb-coldp fn-hsrcb-demandp
                     fn-hrcur-cold-tick-lawp fn-hrcur-widthp fn-hrcur-field)
                    (fn-hrcur-cold-tick fn-hrcur-byte-tick fn-hrcur-cold-invariantp
                     fn-hrcur-byte-invariantp fn-hrcur-cold-rest))))))

(local
 (defthm fn-hpert-finish-permitted
   (implies (fn-hrcur-wordp k w)
            (and (member-eq (mv-nth 0 (fn-hrcur-word-finish k w)) '(:emit :prepared))
                 (implies (equal (mv-nth 0 (fn-hrcur-word-finish k w)) :emit)
                          (unsigned-byte-p 64 (mv-nth 1 (fn-hrcur-word-finish k w))))))
   :hints (("Goal" :cases ((equal k 0) (equal k 1) (equal k 2) (equal k 3)
                           (equal k 4) (equal k 5) (equal k 6) (equal k 7))
            :in-theory (enable fn-hrcur-wordp fn-hrcur-word-finish)))))

(local
 (defthm fn-hpert-shape-scalars
   (implies (fn-hpe-shapep c)
            (and (unsigned-byte-p 64 (fn-hrcur-field 4 c))
                 (fn-hrcur-wordp (fn-hrcur-field 2 c) (fn-hrcur-field 3 c))))
   :hints (("Goal" :in-theory (enable fn-hpe-shapep)))))

(defthm fn-hpert-tick-preserves-byte-total
  (implies (fn-hpert-emitter-invariantp c pool)
    (and (fn-hpert-emitter-invariantp (mv-nth 2 (fn-hpe-tick c fn-hpb)) pool)
         (equal (fn-hpert-total (mv-nth 2 (fn-hpe-tick c fn-hpb)) pool) (fn-hpert-total c pool))
         (or (member-eq (mv-nth 0 (fn-hpe-tick c fn-hpb)) '(:continue :prepared :page-full))
             (fn-hsrcb-demandp (mv-nth 0 (fn-hpe-tick c fn-hpb))))
         (implies (eq (mv-nth 0 (fn-hpe-tick c fn-hpb)) :prepared)
                  (equal (mv-nth 1 (fn-hpe-tick c fn-hpb)) (fn-hpert-total c pool)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use ((:instance fn-hsrcb-tick-preserves-canonical-residual (c (fn-hrcur-field 1 c)))
          (:instance fn-hpert-child-tick-range (c (fn-hrcur-field 1 c)))
          (:instance fn-hpert-shape-scalars)
          (:instance fn-hpe-tick-keeps-shape)
          (:instance fn-hpert-finish-permitted (k (fn-hrcur-field 2 c)) (w (fn-hrcur-field 3 c)))
          (:instance fn-hrcur-word-push-preserves
            (octet (mv-nth 1 (fn-hsrcb-tick (fn-hrcur-field 1 c))))
            (k (fn-hrcur-field 2 c)) (w (fn-hrcur-field 3 c))))
    :in-theory (e/d (fn-hpert-emitter-invariantp fn-hpert-total fn-hpe-tick)
                    (fn-hsrcb-tick fn-hsrcb-rest fn-hsrcb-invariantp fn-hsrcb-demandp
                     fn-hpe-shapep fn-hpert-shape-scalars fn-scc-octetp
                     fn-hrcur-wordp fn-hpb-put fn-hrcur-word-push fn-hrcur-word-push-preserves
                     fn-hpe-tick-keeps-shape fn-hpert-finish-permitted)))))

(local
 (defthm fn-hpert-eighth-byte-refines-pool-word
  (let ((byte (mv-nth 1 (fn-hsrcb-tick (fn-hrcur-field 1 c)))))
    (implies
     (and (fn-hpe-shapep c) (equal (fn-hrcur-field 0 c) :codec)
          (natp (fn-hpb-used fn-hpb)) (< (fn-hpb-used fn-hpb) 2048)
          (equal (fn-hrcur-field 2 c) 7) (equal (len prefix) 7)
          (equal (fn-hrcur-field 3 c) (adt-unle 7 prefix))
          (equal (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c))) :emit)
          (fn-scc-octetp byte) (< (+ 1 (fn-hrcur-field 4 c)) 18446744073709551616))
     (equal (fn-hpb-prefix (mv-nth 3 (fn-hpe-tick c fn-hpb)))
            (append (fn-hpb-prefix fn-hpb)
                    (list (car (fn-hp-pack8 1 (append prefix (list byte)))))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hpert-shape-scalars)
                 (:instance fn-hrcur-word-push-refines-pack8
                   (w (fn-hrcur-field 3 c))
                   (octet (mv-nth 1 (fn-hsrcb-tick (fn-hrcur-field 1 c)))))
                 (:instance fn-hrcur-word-push-preserves (k 7) (w (fn-hrcur-field 3 c))
                   (octet (mv-nth 1 (fn-hsrcb-tick (fn-hrcur-field 1 c))))))
           :in-theory (e/d (fn-hpe-tick) (fn-hpe-shapep fn-hpert-shape-scalars fn-hsrcb-tick fn-hsrcb-tick fn-hrcur-word-push fn-hrcur-word-finish
                        fn-hpb-put fn-hpb-prefix fn-hp-pack8 adt-unle fn-hrcur-wordp
                        fn-hrcur-word-push-refines-pack8 fn-hrcur-word-push-preserves))))))

(local
 (defthm fn-hpert-octets-append-byte
   (implies (and (fn-scc-octet-listp partial) (fn-scc-octetp byte))
            (fn-scc-octet-listp (append partial (list byte))))
   :hints (("Goal" :in-theory (enable fn-scc-octet-listp)))))

(local
 (defthm fn-hpert-carried-fields
   (implies (fn-hpert-emitter-invariantp c pool)
            (and (fn-hpe-shapep c)
                 (fn-hsrcb-invariantp (fn-hrcur-field 1 c) pool)
                 (fn-hrcur-wordp (fn-hrcur-field 2 c) (fn-hrcur-field 3 c))
                 (natp (fn-hrcur-field 2 c)) (< (fn-hrcur-field 2 c) 8)))
   :hints (("Goal" :in-theory (enable fn-hpert-emitter-invariantp fn-hpe-shapep fn-hrcur-wordp)))))

(local
 (defthm fn-hpert-octet-singleton
   (implies (fn-scc-octetp byte) (fn-scc-octet-listp (list byte)))
   :hints (("Goal" :in-theory (enable fn-scc-octet-listp)))))

 ; Phase-local proof: nonemitting child transition carries k/w and partial.
(local
 (defthm fn-hpert-codec-nonemit-carry
  (implies (and (fn-hpert-invariantp c partial pool)
                (equal (fn-hrcur-field 0 c) :codec)
                (not (fn-hpb-ready fn-hpb))
                (not (equal (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c))) :emit)))
           (fn-hpert-invariantp (mv-nth 2 (fn-hpe-tick c fn-hpb))
                              (fn-hpert-partial-next c partial fn-hpb) pool))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hpert-carried-fields)
                 (:instance fn-hpert-tick-preserves-byte-total)
                 (:instance fn-hsrcb-tick-preserves-canonical-residual (c (fn-hrcur-field 1 c))))
           :in-theory (e/d (fn-hpe-tick fn-hpert-invariantp fn-hpert-partial-next)
                           (fn-hpert-emitter-invariantp fn-hpe-shapep fn-hpert-carried-fields
                            fn-hsrcb-tick fn-hsrcb-invariantp
                            fn-hrcur-word-push fn-hrcur-word-finish fn-hpb-put
                             
                            adt-unle unsigned-byte-p fn-scc-octetp ))))))

(local
 (defthm fn-hpert-codec-partial-carry
  (implies (and (fn-hpert-invariantp c partial pool)
                (equal (fn-hrcur-field 0 c) :codec)
                (not (fn-hpb-ready fn-hpb))
                (< (fn-hrcur-field 2 c) 7)
                (equal (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c))) :emit))
           (fn-hpert-invariantp (mv-nth 2 (fn-hpe-tick c fn-hpb))
                              (fn-hpert-partial-next c partial fn-hpb) pool))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hpert-carried-fields)
                 (:instance fn-hpert-tick-preserves-byte-total)
                 (:instance fn-hsrcb-tick-preserves-canonical-residual (c (fn-hrcur-field 1 c)))
                 (:instance fn-hrcur-word-push-refines-partial
                            (prefix partial) (k (fn-hrcur-field 2 c)) (w (fn-hrcur-field 3 c))
                            (octet (mv-nth 1 (fn-hsrcb-tick (fn-hrcur-field 1 c))))))
           :in-theory (e/d (fn-hpe-tick fn-hpert-invariantp fn-hpert-partial-next)
                           (fn-hpert-emitter-invariantp fn-hpe-shapep fn-hpert-carried-fields
                            fn-hsrcb-tick fn-hsrcb-invariantp
                            fn-hrcur-word-push fn-hrcur-word-finish fn-hpb-put
                             
                            fn-hrcur-word-push-refines-partial
                            adt-unle unsigned-byte-p fn-scc-octetp ))))))

(local
 (defthm fn-hpert-codec-eighth-carry
  (implies (and (fn-hpert-invariantp c partial pool)
                (equal (fn-hrcur-field 0 c) :codec)
                (not (fn-hpb-ready fn-hpb))
                (equal (fn-hrcur-field 2 c) 7)
                (equal (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c))) :emit))
           (fn-hpert-invariantp (mv-nth 2 (fn-hpe-tick c fn-hpb))
                              (fn-hpert-partial-next c partial fn-hpb) pool))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hpert-carried-fields)
                 (:instance fn-hpert-tick-preserves-byte-total)
                 (:instance fn-hsrcb-tick-preserves-canonical-residual (c (fn-hrcur-field 1 c)))
                 (:instance fn-hrcur-word-push-refines-pack8
                            (prefix partial) (w (fn-hrcur-field 3 c))
                            (octet (mv-nth 1 (fn-hsrcb-tick (fn-hrcur-field 1 c))))))
           :in-theory (e/d (fn-hpe-tick fn-hpert-invariantp fn-hpert-partial-next)
                           (fn-hpert-emitter-invariantp fn-hpe-shapep fn-hpert-carried-fields
                            fn-hsrcb-tick fn-hsrcb-invariantp
                            fn-hrcur-word-push fn-hrcur-word-finish fn-hpb-put
                             
                            fn-hrcur-word-push-refines-pack8
                            fn-hp-pack8 adt-unle unsigned-byte-p fn-scc-octetp ))))))

(local
 (defthm fn-hpert-finish-carry
  (implies (and (fn-hpert-invariantp c partial pool)
                (equal (fn-hrcur-field 0 c) :finish)
                (not (fn-hpb-ready fn-hpb)))
           (fn-hpert-invariantp (mv-nth 2 (fn-hpe-tick c fn-hpb))
                              (fn-hpert-partial-next c partial fn-hpb) pool))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hpert-carried-fields)
                 (:instance fn-hpert-tick-preserves-byte-total))
           :in-theory (e/d (fn-hpe-tick fn-hpert-invariantp fn-hpert-partial-next)
                           (fn-hpert-emitter-invariantp fn-hpe-shapep fn-hpert-carried-fields
                            fn-hsrcb-tick fn-hsrcb-invariantp
                            fn-hrcur-word-push fn-hrcur-word-finish fn-hpb-put
                            
                            fn-hp-pack8 adt-unle unsigned-byte-p fn-scc-octetp ))))))


(local
 (defthm fn-hpert-stationary-carry
  (implies (and (fn-hpert-invariantp c partial pool)
                (or (fn-hpb-ready fn-hpb)
                    (equal (fn-hrcur-field 0 c) :prepared)))
           (fn-hpert-invariantp (mv-nth 2 (fn-hpe-tick c fn-hpb))
                              (fn-hpert-partial-next c partial fn-hpb) pool))
  :hints (("Goal" :use ((:instance fn-hpert-carried-fields))
           :in-theory (e/d (fn-hpe-tick fn-hpert-invariantp fn-hpert-partial-next)
                           (fn-hpert-emitter-invariantp fn-hpe-shapep fn-hpert-carried-fields
                            fn-hsrcb-tick fn-hrcur-word-push fn-hrcur-word-finish
                            fn-hpb-put adt-unle ))))))

(local
 (defthm fn-hpert-phase-range
  (implies (fn-hpert-invariantp c partial pool)
           (and (member-eq (fn-hrcur-field 0 c) '(:codec :finish :prepared))
                (natp (fn-hrcur-field 2 c)) (< (fn-hrcur-field 2 c) 8)))
  :hints (("Goal" :use ((:instance fn-hpert-carried-fields))
           :in-theory (e/d (fn-hpert-invariantp fn-hpert-emitter-invariantp )
                           (fn-hpe-shapep fn-hpert-carried-fields))))))

(defthm fn-hpert-tick-preserves-packing-carry
  (implies (fn-hpert-invariantp c partial pool)
           (fn-hpert-invariantp (mv-nth 2 (fn-hpe-tick c fn-hpb))
                              (fn-hpert-partial-next c partial fn-hpb) pool))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hpert-phase-range)
                 (:instance fn-hpert-stationary-carry)
                 (:instance fn-hpert-codec-nonemit-carry)
                 (:instance fn-hpert-codec-partial-carry)
                 (:instance fn-hpert-codec-eighth-carry)
                 (:instance fn-hpert-finish-carry))
           :in-theory (disable fn-hpert-invariantp fn-hpert-partial-next fn-hpert-emitter-invariantp
                               fn-hpe-tick fn-hpe-shapep fn-hsrcb-tick
                               fn-hpert-phase-range fn-hpert-stationary-carry
                               fn-hpert-codec-nonemit-carry fn-hpert-codec-partial-carry
                               fn-hpert-codec-eighth-carry fn-hpert-finish-carry))))

(local
 (defthm fn-hpert-emit-room
  (implies (and (fn-hpert-emitter-invariantp c pool)
                (equal (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c))) :emit))
           (and (fn-scc-octetp (mv-nth 1 (fn-hsrcb-tick (fn-hrcur-field 1 c))))
                (< (+ 1 (fn-hrcur-field 4 c)) 18446744073709551616)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hpert-carried-fields)
                 (:instance fn-hsrcb-tick-preserves-canonical-residual (c (fn-hrcur-field 1 c)))
                 (:instance fn-hsrcb-tick-preserves-canonical-residual (c (fn-hrcur-field 1 c))))
           :in-theory (e/d (fn-hpert-emitter-invariantp fn-hpert-total fn-hpe-shapep )
                           (fn-hsrcb-tick fn-hsrcb-rest fn-hsrcb-invariantp
                            fn-hpert-carried-fields 
                             fn-hrcur-wordp))))))

(defthm fn-hpert-prepared-has-no-pending
  (implies (and (fn-hpert-invariantp c partial pool)
                (equal (fn-hrcur-field 0 c) :prepared))
           (equal (fn-hpert-pending c partial pool) nil))
  :hints (("Goal" :in-theory (e/d (fn-hpert-invariantp fn-hpert-pending fn-hper-pack
                                  fn-hpert-emitter-invariantp )
                                 (fn-hsrcb-rest fn-hpe-shapep )))))

(local
 (defthm fn-hpert-codec-nonemit-pending
  (implies (and (fn-hpert-invariantp c partial pool)
                (equal (fn-hrcur-field 0 c) :codec)
                (not (fn-hpb-ready fn-hpb))
                (not (equal (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c))) :emit)))
           (and (equal (fn-hpert-pending c partial pool)
                       (fn-hpert-pending (mv-nth 2 (fn-hpe-tick c fn-hpb))
                                        (fn-hpert-partial-next c partial fn-hpb) pool))
                (equal (mv-nth 3 (fn-hpe-tick c fn-hpb)) fn-hpb)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hpert-carried-fields)
                 (:instance fn-hsrcb-tick-preserves-canonical-residual (c (fn-hrcur-field 1 c)))
                 (:instance fn-hsrcb-tick-preserves-canonical-residual (c (fn-hrcur-field 1 c))))
           :in-theory (e/d (fn-hpe-tick fn-hpert-invariantp fn-hpert-pending fn-hpert-partial-next)
                           (fn-hpert-emitter-invariantp fn-hpe-shapep fn-hpert-carried-fields
                            fn-hsrcb-tick fn-hsrcb-invariantp fn-hsrcb-rest
                            fn-hrcur-word-push fn-hrcur-word-finish fn-hpb-put
                            fn-hper-pack 
                             adt-unle ))))))

(local
 (defthm fn-hpert-codec-partial-pending
  (implies (and (fn-hpert-invariantp c partial pool)
                (equal (fn-hrcur-field 0 c) :codec)
                (not (fn-hpb-ready fn-hpb))
                (< (fn-hrcur-field 2 c) 7)
                (equal (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c))) :emit))
           (and (equal (fn-hpert-pending c partial pool)
                       (fn-hpert-pending (mv-nth 2 (fn-hpe-tick c fn-hpb))
                                        (fn-hpert-partial-next c partial fn-hpb) pool))
                (equal (mv-nth 3 (fn-hpe-tick c fn-hpb)) fn-hpb)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hpert-carried-fields)
                 (:instance fn-hpert-emit-room)
                 (:instance fn-hsrcb-tick-preserves-canonical-residual (c (fn-hrcur-field 1 c)))
                 (:instance fn-hrcur-word-push-refines-partial
                            (prefix partial) (k (fn-hrcur-field 2 c)) (w (fn-hrcur-field 3 c))
                            (octet (mv-nth 1 (fn-hsrcb-tick (fn-hrcur-field 1 c))))))
           :in-theory (e/d (fn-hpe-tick fn-hpert-invariantp fn-hpert-pending fn-hpert-partial-next)
                           (fn-hpert-emitter-invariantp fn-hpe-shapep fn-hpert-carried-fields
                            fn-hsrcb-tick fn-hsrcb-invariantp fn-hsrcb-rest
                            fn-hrcur-word-push fn-hrcur-word-finish fn-hpb-put
                            fn-hper-pack fn-hpert-emit-room
                            fn-hrcur-word-push-refines-partial
                             adt-unle unsigned-byte-p fn-scc-octetp ))))))

(local
 (defthm fn-hpert-scratch-room
  (implies (and (fn-hpbp fn-hpb) (not (fn-hpb-ready fn-hpb)))
           (and (natp (fn-hpb-used fn-hpb)) (< (fn-hpb-used fn-hpb) 2048)))))

(local
 (defthm fn-hpert-codec-eighth-pending
  (implies (and (fn-hpert-invariantp c partial pool) (fn-hpbp fn-hpb)
                (equal (fn-hrcur-field 0 c) :codec)
                (not (fn-hpb-ready fn-hpb))
                (equal (fn-hrcur-field 2 c) 7)
                (equal (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c))) :emit))
           (equal (append (fn-hpb-prefix fn-hpb) (fn-hpert-pending c partial pool))
                  (append (fn-hpb-prefix (mv-nth 3 (fn-hpe-tick c fn-hpb)))
                          (fn-hpert-pending (mv-nth 2 (fn-hpe-tick c fn-hpb))
                                           (fn-hpert-partial-next c partial fn-hpb) pool))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hpert-carried-fields)
                 (:instance fn-hpert-emit-room)
                 (:instance fn-hpert-scratch-room)
                 (:instance fn-hsrcb-tick-preserves-canonical-residual (c (fn-hrcur-field 1 c)))
                 (:instance fn-hper-eight-byte-prefix
                   (prefix (append partial (list (mv-nth 1 (fn-hsrcb-tick (fn-hrcur-field 1 c))))))
                   (rest (fn-hsrcb-rest (mv-nth 2 (fn-hsrcb-tick (fn-hrcur-field 1 c))) pool)))
                 (:instance fn-hpert-eighth-byte-refines-pool-word (prefix partial))
                 (:instance fn-hrcur-word-push-refines-pack8
                            (prefix partial) (w (fn-hrcur-field 3 c))
                            (octet (mv-nth 1 (fn-hsrcb-tick (fn-hrcur-field 1 c))))))
           :in-theory (e/d (fn-hpe-tick fn-hpert-invariantp fn-hpert-pending fn-hpert-partial-next
                            fn-scc-octet-listp)
                           (fn-hpert-emitter-invariantp fn-hpe-shapep fn-hpert-carried-fields
                            fn-hsrcb-tick fn-hsrcb-invariantp fn-hsrcb-rest
                            fn-hrcur-word-push fn-hrcur-word-finish fn-hpb-put fn-hpb-prefix
                            fn-hper-pack fn-hpert-emit-room fn-hpert-scratch-room
                            fn-hper-eight-byte-prefix fn-hpert-eighth-byte-refines-pool-word
                            fn-hrcur-word-push-refines-pack8 fn-hp-pack8
                             adt-unle unsigned-byte-p fn-scc-octetp ))))))

(local
 (defthm fn-hpert-unle-past-end
  (implies (and (natp n) (<= (len partial) n))
           (equal (adt-unle n partial) (adt-unle (len partial) partial)))
  :rule-classes nil
  :hints (("Goal" :induct (adt-unle n partial) :in-theory (enable adt-unle)))))

(local
 (defthm fn-hpert-pack-partial
  (implies (and (natp k) (< k 8) (equal (len partial) k))
           (equal (fn-hper-pack partial)
                  (if (equal k 0) nil (list (adt-unle k partial)))))
  :hints (("Goal" :do-not-induct t
           :cases ((equal k 0) (equal k 1) (equal k 2) (equal k 3)
                   (equal k 4) (equal k 5) (equal k 6) (equal k 7))
           :use ((:instance fn-hpert-unle-past-end (n 8)))
           :expand ((fn-hp-pack8 1 partial) (:free (b) (fn-hp-pack8 0 b)))
           :in-theory (e/d (fn-hper-pack) (adt-unle nthcdr fn-hp-pack8))))))

(local
 (defthm fn-hpert-word-value-u64
  (implies (fn-hrcur-wordp k w) (unsigned-byte-p 64 w))
  :hints (("Goal" :cases ((equal k 0) (equal k 1) (equal k 2) (equal k 3)
                          (equal k 4) (equal k 5) (equal k 6) (equal k 7))
           :in-theory (enable fn-hrcur-wordp unsigned-byte-p)))))

(local
 (defthm fn-hpert-finish-pending
  (implies (and (fn-hpert-invariantp c partial pool) (fn-hpbp fn-hpb)
                (equal (fn-hrcur-field 0 c) :finish)
                (not (fn-hpb-ready fn-hpb)))
           (equal (append (fn-hpb-prefix fn-hpb) (fn-hpert-pending c partial pool))
                  (append (fn-hpb-prefix (mv-nth 3 (fn-hpe-tick c fn-hpb)))
                          (fn-hpert-pending (mv-nth 2 (fn-hpe-tick c fn-hpb))
                                           (fn-hpert-partial-next c partial fn-hpb) pool))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hpert-carried-fields)
                 (:instance fn-hpert-scratch-room)
                 (:instance fn-hpert-pack-partial (k (fn-hrcur-field 2 c)))
                 (:instance fn-hpert-word-value-u64 (k (fn-hrcur-field 2 c))
                            (w (fn-hrcur-field 3 c))))
           :in-theory (e/d (fn-hpe-tick fn-hpert-invariantp fn-hpert-pending fn-hpert-partial-next
                            fn-hpert-emitter-invariantp fn-hrcur-word-finish)
                           (fn-hpe-shapep fn-hpert-carried-fields fn-hpert-scratch-room fn-hpert-word-value-u64
                            fn-hsrcb-tick fn-hsrcb-invariantp fn-hsrcb-rest
                            fn-hrcur-word-push fn-hrcur-wordp fn-hpb-put fn-hpb-prefix
                            fn-hper-pack fn-hpert-pack-partial
                            adt-unle unsigned-byte-p fn-scc-octetp))))))

(local
 (defthm fn-hpert-stationary-pending
  (implies (and (fn-hpert-invariantp c partial pool)
                (or (fn-hpb-ready fn-hpb)
                    (equal (fn-hrcur-field 0 c) :prepared)))
           (and (equal (fn-hpert-pending c partial pool)
                       (fn-hpert-pending (mv-nth 2 (fn-hpe-tick c fn-hpb))
                                        (fn-hpert-partial-next c partial fn-hpb) pool))
                (equal (mv-nth 3 (fn-hpe-tick c fn-hpb)) fn-hpb)))
  :hints (("Goal" :use ((:instance fn-hpert-carried-fields))
           :in-theory (e/d (fn-hpe-tick fn-hpert-invariantp fn-hpert-partial-next)
                           (fn-hpert-emitter-invariantp fn-hpe-shapep fn-hpert-carried-fields
                            fn-hpert-pending fn-hsrcb-tick fn-hrcur-word-push
                            fn-hrcur-word-finish fn-hpb-put adt-unle ))))))

; Exact semantic boundary over the actual child and concrete scratch effects.
(defthm fn-hpert-tick-refines-pool-residual
  (implies (and (fn-hpert-invariantp c partial pool) (fn-hpbp fn-hpb))
           (equal (append (fn-hpb-prefix fn-hpb) (fn-hpert-pending c partial pool))
                  (append (fn-hpb-prefix (mv-nth 3 (fn-hpe-tick c fn-hpb)))
                          (fn-hpert-pending (mv-nth 2 (fn-hpe-tick c fn-hpb))
                                           (fn-hpert-partial-next c partial fn-hpb) pool))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hpert-phase-range)
                 (:instance fn-hpert-stationary-pending)
                 (:instance fn-hpert-codec-nonemit-pending)
                 (:instance fn-hpert-codec-partial-pending)
                 (:instance fn-hpert-codec-eighth-pending)
                 (:instance fn-hpert-finish-pending))
           :in-theory (disable fn-hpert-invariantp fn-hpert-partial-next fn-hpert-pending
                               fn-hpe-tick fn-hpe-shapep fn-hsrcb-tick fn-hpbp
                               fn-hpb-prefix fn-hpert-phase-range fn-hpert-stationary-pending
                               fn-hpert-codec-nonemit-pending fn-hpert-codec-partial-pending
                               fn-hpert-codec-eighth-pending fn-hpert-finish-pending))))


; Valid supply attribution is a carried physical/source relation. The current
; immutable byte is the theorem premise, never a host truth flag.
(defthm fn-hpert-supply-preserves-byte-total
  (implies (and (fn-hpert-emitter-invariantp c pool)
                (fn-hsrcb-demandp (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c))))
                (equal position (fn-hrcur-field 1 (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c)))))
                (equal byte (nth position pool)))
    (and (fn-hpert-emitter-invariantp (mv-nth 1 (fn-hpe-supply c position byte fn-hpb)) pool)
         (equal (fn-hpert-total (mv-nth 1 (fn-hpe-supply c position byte fn-hpb)) pool)
                (fn-hpert-total c pool))
         (equal (mv-nth 0 (fn-hpe-supply c position byte fn-hpb))
                (if (eq (fn-hrcur-field 0 c) :codec)
                    (if (fn-hpb-ready fn-hpb) :page-full :continue)
                  '(:refused :not-awaiting-cold-byte)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use ((:instance fn-hsrcb-supply-preserves-canonical-residual (c (fn-hrcur-field 1 c)))
          (:instance fn-hpert-shape-scalars)
          (:instance fn-hpe-supply-keeps-shape)
          (:instance fn-hrcur-word-push-preserves
            (octet (mv-nth 1 (fn-hsrcb-supply (fn-hrcur-field 1 c) position byte)))
            (k (fn-hrcur-field 2 c)) (w (fn-hrcur-field 3 c))))
    :in-theory (e/d (fn-hpert-emitter-invariantp fn-hpert-total fn-hpe-supply)
                    (fn-hsrcb-tick fn-hsrcb-supply fn-hsrcb-rest fn-hsrcb-invariantp fn-hsrcb-demandp
                     fn-hpe-shapep fn-hpert-shape-scalars fn-scc-octetp
                     fn-hrcur-wordp fn-hpb-put fn-hrcur-word-push fn-hrcur-word-push-preserves
                     fn-hpe-supply-keeps-shape)))))


(local
 (defthm fn-hperts-eighth-byte-refines-pool-word
  (let ((emitted (mv-nth 1 (fn-hsrcb-supply (fn-hrcur-field 1 c) position byte))))
    (implies
     (and (fn-hpe-shapep c) (equal (fn-hrcur-field 0 c) :codec)
          (natp (fn-hpb-used fn-hpb)) (< (fn-hpb-used fn-hpb) 2048)
          (equal (fn-hrcur-field 2 c) 7) (equal (len prefix) 7)
          (equal (fn-hrcur-field 3 c) (adt-unle 7 prefix))
          (equal (mv-nth 0 (fn-hsrcb-supply (fn-hrcur-field 1 c) position byte)) :emit)
          (fn-scc-octetp emitted) (< (+ 1 (fn-hrcur-field 4 c)) 18446744073709551616))
     (equal (fn-hpb-prefix (mv-nth 2 (fn-hpe-supply c position byte fn-hpb)))
            (append (fn-hpb-prefix fn-hpb)
                    (list (car (fn-hp-pack8 1 (append prefix (list emitted)))))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hpert-shape-scalars)
                 (:instance fn-hrcur-word-push-refines-pack8
                   (w (fn-hrcur-field 3 c))
                   (octet (mv-nth 1 (fn-hsrcb-supply (fn-hrcur-field 1 c) position byte))))
                 (:instance fn-hrcur-word-push-preserves (k 7) (w (fn-hrcur-field 3 c))
                   (octet (mv-nth 1 (fn-hsrcb-supply (fn-hrcur-field 1 c) position byte)))))
           :in-theory (e/d (fn-hpe-supply) (fn-hpe-shapep fn-hpert-shape-scalars fn-hsrcb-tick fn-hsrcb-tick fn-hrcur-word-push fn-hrcur-word-finish
                        fn-hpb-put fn-hpb-prefix fn-hp-pack8 adt-unle fn-hrcur-wordp
                        fn-hrcur-word-push-refines-pack8 fn-hrcur-word-push-preserves))))))

(local
 (defthm fn-hperts-codec-nonemit-carry
  (implies (and (fn-hsrcb-demandp (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c))))
                (equal position (fn-hrcur-field 1 (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c)))))
                (equal byte (nth position pool))
                (fn-hpert-invariantp c partial pool)
                (equal (fn-hrcur-field 0 c) :codec)
                (not (fn-hpb-ready fn-hpb))
                (not (equal (mv-nth 0 (fn-hsrcb-supply (fn-hrcur-field 1 c) position byte)) :emit)))
           (fn-hpert-invariantp (mv-nth 1 (fn-hpe-supply c position byte fn-hpb))
                              (fn-hpert-partial-supply c partial position byte fn-hpb) pool))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hpert-carried-fields)
                 (:instance fn-hpert-supply-preserves-byte-total)
                 (:instance fn-hsrcb-supply-preserves-canonical-residual (c (fn-hrcur-field 1 c))))
           :in-theory (e/d (fn-hpe-supply fn-hpert-invariantp fn-hpert-partial-supply)
                           (fn-hpert-emitter-invariantp fn-hpe-shapep fn-hpert-carried-fields
                            fn-hsrcb-supply fn-hsrcb-tick fn-hsrcb-invariantp
                            fn-hrcur-word-push fn-hrcur-word-finish fn-hpb-put
                             
                            adt-unle unsigned-byte-p fn-scc-octetp ))))))

(local
 (defthm fn-hperts-codec-partial-carry
  (implies (and (fn-hsrcb-demandp (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c))))
                (equal position (fn-hrcur-field 1 (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c)))))
                (equal byte (nth position pool))
                (fn-hpert-invariantp c partial pool)
                (equal (fn-hrcur-field 0 c) :codec)
                (not (fn-hpb-ready fn-hpb))
                (< (fn-hrcur-field 2 c) 7)
                (equal (mv-nth 0 (fn-hsrcb-supply (fn-hrcur-field 1 c) position byte)) :emit))
           (fn-hpert-invariantp (mv-nth 1 (fn-hpe-supply c position byte fn-hpb))
                              (fn-hpert-partial-supply c partial position byte fn-hpb) pool))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hpert-carried-fields)
                 (:instance fn-hpert-supply-preserves-byte-total)
                 (:instance fn-hsrcb-supply-preserves-canonical-residual (c (fn-hrcur-field 1 c)))
                 (:instance fn-hrcur-word-push-refines-partial
                            (prefix partial) (k (fn-hrcur-field 2 c)) (w (fn-hrcur-field 3 c))
                            (octet (mv-nth 1 (fn-hsrcb-supply (fn-hrcur-field 1 c) position byte)))))
           :in-theory (e/d (fn-hpe-supply fn-hpert-invariantp fn-hpert-partial-supply)
                           (fn-hpert-emitter-invariantp fn-hpe-shapep fn-hpert-carried-fields
                            fn-hsrcb-supply fn-hsrcb-tick fn-hsrcb-invariantp
                            fn-hrcur-word-push fn-hrcur-word-finish fn-hpb-put
                             
                            fn-hrcur-word-push-refines-partial
                            adt-unle unsigned-byte-p fn-scc-octetp ))))))

(local
 (defthm fn-hperts-codec-eighth-carry
  (implies (and (fn-hsrcb-demandp (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c))))
                (equal position (fn-hrcur-field 1 (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c)))))
                (equal byte (nth position pool))
                (fn-hpert-invariantp c partial pool)
                (equal (fn-hrcur-field 0 c) :codec)
                (not (fn-hpb-ready fn-hpb))
                (equal (fn-hrcur-field 2 c) 7)
                (equal (mv-nth 0 (fn-hsrcb-supply (fn-hrcur-field 1 c) position byte)) :emit))
           (fn-hpert-invariantp (mv-nth 1 (fn-hpe-supply c position byte fn-hpb))
                              (fn-hpert-partial-supply c partial position byte fn-hpb) pool))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hpert-carried-fields)
                 (:instance fn-hpert-supply-preserves-byte-total)
                 (:instance fn-hsrcb-supply-preserves-canonical-residual (c (fn-hrcur-field 1 c)))
                 (:instance fn-hrcur-word-push-refines-pack8
                            (prefix partial) (w (fn-hrcur-field 3 c))
                            (octet (mv-nth 1 (fn-hsrcb-supply (fn-hrcur-field 1 c) position byte)))))
           :in-theory (e/d (fn-hpe-supply fn-hpert-invariantp fn-hpert-partial-supply)
                           (fn-hpert-emitter-invariantp fn-hpe-shapep fn-hpert-carried-fields
                            fn-hsrcb-supply fn-hsrcb-tick fn-hsrcb-invariantp
                            fn-hrcur-word-push fn-hrcur-word-finish fn-hpb-put
                             
                            fn-hrcur-word-push-refines-pack8
                            fn-hp-pack8 adt-unle unsigned-byte-p fn-scc-octetp ))))))

(local
 (defthm fn-hperts-emit-room
  (implies (and (fn-hsrcb-demandp (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c))))
                (equal position (fn-hrcur-field 1 (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c)))))
                (equal byte (nth position pool))
                (fn-hpert-emitter-invariantp c pool)
                (equal (mv-nth 0 (fn-hsrcb-supply (fn-hrcur-field 1 c) position byte)) :emit))
           (and (fn-scc-octetp (mv-nth 1 (fn-hsrcb-supply (fn-hrcur-field 1 c) position byte)))
                (< (+ 1 (fn-hrcur-field 4 c)) 18446744073709551616)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hpert-carried-fields)
                 (:instance fn-hsrcb-supply-preserves-canonical-residual (c (fn-hrcur-field 1 c)))
                 (:instance fn-hsrcb-supply-preserves-canonical-residual (c (fn-hrcur-field 1 c))))
           :in-theory (e/d (fn-hpert-emitter-invariantp fn-hpert-total fn-hpe-shapep )
                           (fn-hsrcb-tick fn-hsrcb-rest fn-hsrcb-invariantp
                            fn-hpert-carried-fields 
                             fn-hrcur-wordp))))))

(local
 (defthm fn-hperts-codec-nonemit-pending
  (implies (and (fn-hsrcb-demandp (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c))))
                (equal position (fn-hrcur-field 1 (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c)))))
                (equal byte (nth position pool))
                (fn-hpert-invariantp c partial pool)
                (equal (fn-hrcur-field 0 c) :codec)
                (not (fn-hpb-ready fn-hpb))
                (not (equal (mv-nth 0 (fn-hsrcb-supply (fn-hrcur-field 1 c) position byte)) :emit)))
           (and (equal (fn-hpert-pending c partial pool)
                       (fn-hpert-pending (mv-nth 1 (fn-hpe-supply c position byte fn-hpb))
                                        (fn-hpert-partial-supply c partial position byte fn-hpb) pool))
                (equal (mv-nth 2 (fn-hpe-supply c position byte fn-hpb)) fn-hpb)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hpert-carried-fields)
                 (:instance fn-hsrcb-supply-preserves-canonical-residual (c (fn-hrcur-field 1 c)))
                 (:instance fn-hsrcb-supply-preserves-canonical-residual (c (fn-hrcur-field 1 c))))
           :in-theory (e/d (fn-hpe-supply fn-hpert-invariantp fn-hpert-pending fn-hpert-partial-supply)
                           (fn-hpert-emitter-invariantp fn-hpe-shapep fn-hpert-carried-fields
                            fn-hsrcb-supply fn-hsrcb-tick fn-hsrcb-invariantp fn-hsrcb-rest
                            fn-hrcur-word-push fn-hrcur-word-finish fn-hpb-put
                            fn-hper-pack 
                             adt-unle ))))))

(local
 (defthm fn-hperts-codec-partial-pending
  (implies (and (fn-hsrcb-demandp (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c))))
                (equal position (fn-hrcur-field 1 (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c)))))
                (equal byte (nth position pool))
                (fn-hpert-invariantp c partial pool)
                (equal (fn-hrcur-field 0 c) :codec)
                (not (fn-hpb-ready fn-hpb))
                (< (fn-hrcur-field 2 c) 7)
                (equal (mv-nth 0 (fn-hsrcb-supply (fn-hrcur-field 1 c) position byte)) :emit))
           (and (equal (fn-hpert-pending c partial pool)
                       (fn-hpert-pending (mv-nth 1 (fn-hpe-supply c position byte fn-hpb))
                                        (fn-hpert-partial-supply c partial position byte fn-hpb) pool))
                (equal (mv-nth 2 (fn-hpe-supply c position byte fn-hpb)) fn-hpb)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hpert-carried-fields)
                 (:instance fn-hperts-emit-room)
                 (:instance fn-hsrcb-supply-preserves-canonical-residual (c (fn-hrcur-field 1 c)))
                 (:instance fn-hrcur-word-push-refines-partial
                            (prefix partial) (k (fn-hrcur-field 2 c)) (w (fn-hrcur-field 3 c))
                            (octet (mv-nth 1 (fn-hsrcb-supply (fn-hrcur-field 1 c) position byte)))))
           :in-theory (e/d (fn-hpe-supply fn-hpert-invariantp fn-hpert-pending fn-hpert-partial-supply)
                           (fn-hpert-emitter-invariantp fn-hpe-shapep fn-hpert-carried-fields
                            fn-hsrcb-supply fn-hsrcb-tick fn-hsrcb-invariantp fn-hsrcb-rest
                            fn-hrcur-word-push fn-hrcur-word-finish fn-hpb-put
                            fn-hper-pack fn-hperts-emit-room
                            fn-hrcur-word-push-refines-partial
                             adt-unle unsigned-byte-p fn-scc-octetp ))))))

(local
 (defthm fn-hperts-codec-eighth-pending
  (implies (and (fn-hsrcb-demandp (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c))))
                (equal position (fn-hrcur-field 1 (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c)))))
                (equal byte (nth position pool))
                (fn-hpert-invariantp c partial pool) (fn-hpbp fn-hpb)
                (equal (fn-hrcur-field 0 c) :codec)
                (not (fn-hpb-ready fn-hpb))
                (equal (fn-hrcur-field 2 c) 7)
                (equal (mv-nth 0 (fn-hsrcb-supply (fn-hrcur-field 1 c) position byte)) :emit))
           (equal (append (fn-hpb-prefix fn-hpb) (fn-hpert-pending c partial pool))
                  (append (fn-hpb-prefix (mv-nth 2 (fn-hpe-supply c position byte fn-hpb)))
                          (fn-hpert-pending (mv-nth 1 (fn-hpe-supply c position byte fn-hpb))
                                           (fn-hpert-partial-supply c partial position byte fn-hpb) pool))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hpert-carried-fields)
                 (:instance fn-hperts-emit-room)
                 (:instance fn-hpert-scratch-room)
                 (:instance fn-hsrcb-supply-preserves-canonical-residual (c (fn-hrcur-field 1 c)))
                 (:instance fn-hper-eight-byte-prefix
                   (prefix (append partial (list (mv-nth 1 (fn-hsrcb-supply (fn-hrcur-field 1 c) position byte)))))
                   (rest (fn-hsrcb-rest (mv-nth 2 (fn-hsrcb-supply (fn-hrcur-field 1 c) position byte)) pool)))
                 (:instance fn-hperts-eighth-byte-refines-pool-word (prefix partial))
                 (:instance fn-hrcur-word-push-refines-pack8
                            (prefix partial) (w (fn-hrcur-field 3 c))
                            (octet (mv-nth 1 (fn-hsrcb-supply (fn-hrcur-field 1 c) position byte)))))
           :in-theory (e/d (fn-hpe-supply fn-hpert-invariantp fn-hpert-pending fn-hpert-partial-supply
                            fn-scc-octet-listp)
                           (fn-hpert-emitter-invariantp fn-hpe-shapep fn-hpert-carried-fields
                            fn-hsrcb-supply fn-hsrcb-tick fn-hsrcb-invariantp fn-hsrcb-rest
                            fn-hrcur-word-push fn-hrcur-word-finish fn-hpb-put fn-hpb-prefix
                            fn-hper-pack fn-hperts-emit-room fn-hpert-scratch-room
                            fn-hper-eight-byte-prefix fn-hperts-eighth-byte-refines-pool-word
                            fn-hrcur-word-push-refines-pack8 fn-hp-pack8
                             adt-unle unsigned-byte-p fn-scc-octetp ))))))

(local
 (defthm fn-hperts-stationary
  (implies (and (fn-hpert-invariantp c partial pool)
                (or (fn-hpb-ready fn-hpb) (not (eq (fn-hrcur-field 0 c) :codec))))
    (and (equal (mv-nth 1 (fn-hpe-supply c position byte fn-hpb)) c)
         (equal (mv-nth 2 (fn-hpe-supply c position byte fn-hpb)) fn-hpb)
         (equal (fn-hpert-partial-supply c partial position byte fn-hpb) partial)))
  :hints (("Goal" :use ((:instance fn-hpert-carried-fields))
    :in-theory (e/d (fn-hpe-supply fn-hpert-invariantp fn-hpert-partial-supply)
                    (fn-hpert-emitter-invariantp fn-hpe-shapep fn-hpert-carried-fields
                     fn-hsrcb-supply fn-hrcur-word-push fn-hpb-put))))))

(defthm fn-hpert-supply-preserves-packing-carry
  (implies (and (fn-hpert-invariantp c partial pool)
                (fn-hsrcb-demandp (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c))))
                (equal position (fn-hrcur-field 1 (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c)))))
                (equal byte (nth position pool)))
    (fn-hpert-invariantp (mv-nth 1 (fn-hpe-supply c position byte fn-hpb))
                         (fn-hpert-partial-supply c partial position byte fn-hpb) pool))
  :hints (("Goal" :do-not-induct t
    :use ((:instance fn-hpert-phase-range)
          (:instance fn-hperts-stationary)
          (:instance fn-hperts-codec-nonemit-carry)
          (:instance fn-hperts-codec-partial-carry)
          (:instance fn-hperts-codec-eighth-carry))
    :in-theory (disable fn-hpert-invariantp fn-hpert-partial-supply fn-hpe-supply
                        fn-hsrcb-supply fn-hsrcb-tick fn-hsrcb-demandp
                        fn-hpert-phase-range fn-hperts-stationary fn-hperts-codec-nonemit-carry
                        fn-hperts-codec-partial-carry fn-hperts-codec-eighth-carry))))

(defthm fn-hpert-supply-refines-pool-residual
  (implies (and (fn-hpert-invariantp c partial pool) (fn-hpbp fn-hpb)
                (fn-hsrcb-demandp (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c))))
                (equal position (fn-hrcur-field 1 (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c)))))
                (equal byte (nth position pool)))
    (equal (append (fn-hpb-prefix fn-hpb) (fn-hpert-pending c partial pool))
           (append (fn-hpb-prefix (mv-nth 2 (fn-hpe-supply c position byte fn-hpb)))
                   (fn-hpert-pending (mv-nth 1 (fn-hpe-supply c position byte fn-hpb))
                                    (fn-hpert-partial-supply c partial position byte fn-hpb) pool))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use ((:instance fn-hpert-phase-range)
          (:instance fn-hperts-stationary)
          (:instance fn-hperts-codec-nonemit-pending)
          (:instance fn-hperts-codec-partial-pending)
          (:instance fn-hperts-codec-eighth-pending))
    :in-theory (disable fn-hpert-invariantp fn-hpert-partial-supply fn-hpert-pending
                        fn-hpe-supply fn-hsrcb-supply fn-hsrcb-tick fn-hsrcb-demandp
                        fn-hpbp fn-hpb-prefix fn-hpert-phase-range fn-hperts-stationary
                        fn-hperts-codec-nonemit-pending fn-hperts-codec-partial-pending
                        fn-hperts-codec-eighth-pending))))

; Full outputs and effects of the actual host-called pool child. The concrete
; prefix is carried in the stobj, the partial and immutable pool in the proof.
(defthm fn-hpert-tick-current-codec-boundary
  (implies (and (fn-hpert-invariantp c partial pool) (fn-hpbp fn-hpb))
    (let ((next (mv-nth 2 (fn-hpe-tick c fn-hpb)))
          (next-partial (fn-hpert-partial-next c partial fn-hpb))
          (next-buffer (mv-nth 3 (fn-hpe-tick c fn-hpb))))
      (and (fn-hpert-invariantp next next-partial pool) (fn-hpbp next-buffer)
           (equal (fn-hpert-total next pool) (fn-hpert-total c pool))
           (equal (append (fn-hpb-prefix fn-hpb) (fn-hpert-pending c partial pool))
                  (append (fn-hpb-prefix next-buffer) (fn-hpert-pending next next-partial pool)))
           (or (member-eq (mv-nth 0 (fn-hpe-tick c fn-hpb)) '(:continue :prepared :page-full))
               (fn-hsrcb-demandp (mv-nth 0 (fn-hpe-tick c fn-hpb))))
           (implies (eq (mv-nth 0 (fn-hpe-tick c fn-hpb)) :prepared)
                    (equal (mv-nth 1 (fn-hpe-tick c fn-hpb)) (fn-hpert-total c pool))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use (fn-hpert-tick-refines-pool-residual fn-hpert-tick-preserves-packing-carry
          fn-hpert-tick-preserves-byte-total fn-hpe-tick-keeps-concrete)
    :in-theory (e/d (fn-hpert-invariantp)
                    (fn-hpert-emitter-invariantp fn-hpert-total fn-hpert-pending fn-hpert-partial-next
                     fn-hpe-tick fn-hpbp fn-hpb-prefix fn-hsrcb-demandp
                     fn-hpert-tick-preserves-packing-carry fn-hpe-tick-keeps-concrete)))))

(defthm fn-hpert-supply-current-codec-boundary
  (implies (and (fn-hpert-invariantp c partial pool) (fn-hpbp fn-hpb)
                (fn-hsrcb-demandp (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c))))
                (equal position (fn-hrcur-field 1 (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c)))))
                (equal byte (nth position pool)))
    (let ((next (mv-nth 1 (fn-hpe-supply c position byte fn-hpb)))
          (next-partial (fn-hpert-partial-supply c partial position byte fn-hpb))
          (next-buffer (mv-nth 2 (fn-hpe-supply c position byte fn-hpb))))
      (and (fn-hpert-invariantp next next-partial pool) (fn-hpbp next-buffer)
           (equal (fn-hpert-total next pool) (fn-hpert-total c pool))
           (equal (append (fn-hpb-prefix fn-hpb) (fn-hpert-pending c partial pool))
                  (append (fn-hpb-prefix next-buffer) (fn-hpert-pending next next-partial pool)))
           (equal (mv-nth 0 (fn-hpe-supply c position byte fn-hpb))
                  (if (eq (fn-hrcur-field 0 c) :codec)
                      (if (fn-hpb-ready fn-hpb) :page-full :continue)
                    '(:refused :not-awaiting-cold-byte))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use (fn-hpert-supply-refines-pool-residual fn-hpert-supply-preserves-packing-carry
          fn-hpert-supply-preserves-byte-total)
    :in-theory (e/d (fn-hpert-invariantp fn-hpe-supply)
                    (fn-hpert-emitter-invariantp fn-hpert-total fn-hpert-pending fn-hpert-partial-supply
                     fn-hsrcb-supply fn-hsrcb-tick fn-hsrcb-demandp fn-hpbp fn-hpb-prefix
                     fn-hrcur-word-push fn-hpb-put fn-hpe-shapep
                     fn-hpert-supply-preserves-packing-carry)))))

; Proof-only scheduling trace. A ready page is transferred before reset;
; authenticated demands call the actual supply, never a copied byte machine.
(defun fn-hpert-run (fuel c partial completed pool fn-hpb)
  (declare (xargs :stobjs fn-hpb :verify-guards nil))
  (if (zp fuel) (mv c partial completed fn-hpb)
    (if (fn-hpb-ready fn-hpb)
        (let* ((next-completed (append completed (fn-hpb-prefix fn-hpb)))
               (epoch (fn-hpb-epoch fn-hpb)) (lease (fn-hpb-lease fn-hpb))
               (fn-hpb (fn-hpb-begin epoch lease fn-hpb)))
          (fn-hpert-run (1- fuel) c partial next-completed pool fn-hpb))
      (mv-let (demand ignored-byte ignored-next) (fn-hsrcb-tick (fn-hrcur-field 1 c))
        (declare (ignore ignored-byte ignored-next))
        (if (and (eq (fn-hrcur-field 0 c) :codec) (fn-hsrcb-demandp demand))
            (let* ((position (fn-hrcur-field 1 demand)) (byte (nth position pool))
                   (next-partial (fn-hpert-partial-supply c partial position byte fn-hpb)))
              (mv-let (verdict next fn-hpb) (fn-hpe-supply c position byte fn-hpb)
                (declare (ignore verdict))
                (fn-hpert-run (1- fuel) next next-partial completed pool fn-hpb)))
          (let ((next-partial (fn-hpert-partial-next c partial fn-hpb)))
            (mv-let (verdict summary next fn-hpb) (fn-hpe-tick c fn-hpb)
              (declare (ignore verdict summary))
              (fn-hpert-run (1- fuel) next next-partial completed pool fn-hpb))))))))

(local
 (defthm fn-hpert-supply-keeps-concrete
   (implies (fn-hpbp fn-hpb)
            (fn-hpbp (mv-nth 2 (fn-hpe-supply c position byte fn-hpb))))
   :hints (("Goal" :in-theory (e/d (fn-hpe-supply)
                       (fn-hsrcb-supply fn-hrcur-word-push fn-hpe-shapep fn-hpbp fn-hpb-put))))))

(defthm fn-hpert-run-preserves-carried-state
  (implies (and (fn-hpert-invariantp c partial pool) (fn-hpbp fn-hpb))
    (and (fn-hpert-invariantp (mv-nth 0 (fn-hpert-run fuel c partial completed pool fn-hpb))
                             (mv-nth 1 (fn-hpert-run fuel c partial completed pool fn-hpb)) pool)
         (fn-hpbp (mv-nth 3 (fn-hpert-run fuel c partial completed pool fn-hpb)))))
  :hints (("Goal" :induct (fn-hpert-run fuel c partial completed pool fn-hpb)
    :in-theory (e/d (fn-hpert-run)
                    (fn-hpert-invariantp fn-hpert-partial-next fn-hpert-partial-supply
                     fn-hpe-tick fn-hpe-supply fn-hpbp fn-hpb-begin fn-hpb-prefix
                     fn-hsrcb-tick fn-hsrcb-demandp)))))

(defthm fn-hpert-run-refines-pool-stream
  (implies (and (fn-hpert-invariantp c partial pool) (fn-hpbp fn-hpb))
    (equal (append completed (append (fn-hpb-prefix fn-hpb) (fn-hpert-pending c partial pool)))
           (append (mv-nth 2 (fn-hpert-run fuel c partial completed pool fn-hpb))
                   (append (fn-hpb-prefix (mv-nth 3 (fn-hpert-run fuel c partial completed pool fn-hpb)))
                           (fn-hpert-pending (mv-nth 0 (fn-hpert-run fuel c partial completed pool fn-hpb))
                                            (mv-nth 1 (fn-hpert-run fuel c partial completed pool fn-hpb)) pool)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-hpert-run fuel c partial completed pool fn-hpb)
    :in-theory (e/d (fn-hpert-run)
                    (fn-hpert-invariantp fn-hpert-partial-next fn-hpert-partial-supply fn-hpert-pending
                     fn-hpe-tick fn-hpe-supply fn-hpbp fn-hpb-begin fn-hpb-prefix
                     fn-hsrcb-tick fn-hsrcb-demandp)))
   ("Subgoal *1/4" :use ((:instance fn-hpert-tick-refines-pool-residual)))
   ("Subgoal *1/3" :use ((:instance fn-hpert-supply-refines-pool-residual
                          (position (fn-hrcur-field 1 (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c)))))
                          (byte (nth (fn-hrcur-field 1 (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c)))) pool)))))))

(local
 (defthm fn-hpert-packed-emitter-invariant
   (implies (fn-hpert-invariantp c partial pool) (fn-hpert-emitter-invariantp c pool))
   :hints (("Goal" :in-theory (e/d (fn-hpert-invariantp) (fn-hpert-emitter-invariantp))))))

(defthm fn-hpert-run-preserves-byte-total
  (implies (and (fn-hpert-invariantp c partial pool) (fn-hpbp fn-hpb))
    (equal (fn-hpert-total (mv-nth 0 (fn-hpert-run fuel c partial completed pool fn-hpb)) pool)
           (fn-hpert-total c pool)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-hpert-run fuel c partial completed pool fn-hpb)
    :in-theory (e/d (fn-hpert-run)
                    (fn-hpert-emitter-invariantp fn-hpert-invariantp fn-hpert-partial-next fn-hpert-partial-supply fn-hpert-total
                     fn-hpe-tick fn-hpe-supply fn-hpbp fn-hpb-begin fn-hpb-prefix
                     fn-hsrcb-tick fn-hsrcb-demandp)))
   ("Subgoal *1/4" :use ((:instance fn-hpert-tick-preserves-byte-total)))
   ("Subgoal *1/3" :use ((:instance fn-hpert-supply-preserves-byte-total
                          (position (fn-hrcur-field 1 (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c)))))
                          (byte (nth (fn-hrcur-field 1 (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c)))) pool)))))))

(local
 (defthm fn-hpert-prepared-total-is-count
   (implies (and (fn-hpert-invariantp c partial pool)
                 (equal (fn-hrcur-field 0 c) :prepared))
            (equal (fn-hpert-total c pool) (fn-hrcur-field 4 c)))
   :hints (("Goal" :in-theory (e/d (fn-hpert-invariantp fn-hpert-emitter-invariantp
                                     fn-hpe-shapep fn-hpert-total)
                                    (fn-hsrcb-rest fn-hrcur-wordp))))))

; Conditional completion over the actual tagged tick/supply/page-reset trace.
; The captured row denotation remains a real carried source obligation.
; This theorem asserts no physical write ACK, source lineage or termination bound.
(defthm fn-hpert-completed-trace-is-current-codec-pool
  (let ((result (fn-hpert-run fuel c nil nil pool fn-hpb)))
    (implies (and (fn-hpert-invariantp c nil pool) (fn-hpbp fn-hpb)
                  (equal (fn-hpb-prefix fn-hpb) nil)
                  (equal (fn-hrcur-field 4 c) 0)
                  (equal (fn-hsrcb-rest (fn-hrcur-field 1 c) pool) (fn-scc-encode row))
                  (equal (fn-hrcur-field 0 (mv-nth 0 result)) :prepared))
      (and (equal (append (mv-nth 2 result) (fn-hpb-prefix (mv-nth 3 result)))
                  (fn-hper-pack (fn-scc-encode row)))
           (equal (fn-hrcur-field 4 (mv-nth 0 result)) (len (fn-scc-encode row))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use ((:instance fn-hpert-run-preserves-carried-state (partial nil) (completed nil))
          (:instance fn-hpert-run-refines-pool-stream (partial nil) (completed nil))
          (:instance fn-hpert-run-preserves-byte-total (partial nil) (completed nil))
          (:instance fn-hpert-prepared-has-no-pending
             (c (mv-nth 0 (fn-hpert-run fuel c nil nil pool fn-hpb)))
             (partial (mv-nth 1 (fn-hpert-run fuel c nil nil pool fn-hpb))))
          (:instance fn-hpert-prepared-total-is-count
             (c (mv-nth 0 (fn-hpert-run fuel c nil nil pool fn-hpb)))
             (partial (mv-nth 1 (fn-hpert-run fuel c nil nil pool fn-hpb)))))
    :expand ((fn-hpert-pending c nil pool) (fn-hpert-total c pool))
    :in-theory (e/d ()
                    (fn-hpert-run fn-hpert-invariantp fn-hpert-emitter-invariantp fn-hper-pack
                     fn-hpert-pending fn-hpert-total fn-hpert-prepared-has-no-pending
                     fn-hpert-prepared-total-is-count
                     fn-hpbp fn-hpb-prefix fn-hsrcb-rest fn-scc-encode fn-scc-program fn-scc-encode-is-program
                     fn-hpert-run-preserves-carried-state)))))

(in-theory (disable fn-hpert-total fn-hpert-emitter-invariantp fn-hpert-invariantp
                    fn-hpert-pending fn-hpert-partial-next fn-hpert-partial-supply fn-hpert-run))
