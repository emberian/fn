; One source codec tick and at most one concrete pool word per scheduling step.
(in-package "ACL2")
(include-book "history-source-byte-cursor")
(include-book "history-page-buffer")

(defun fn-hpe-shapep (c)
  (declare (xargs :guard t))
  (and (fn-hrcur-widthp c 7)
       (member-eq (fn-hrcur-field 0 c) '(:codec :finish :prepared :refused))
       (fn-hrcur-wordp (fn-hrcur-field 2 c) (fn-hrcur-field 3 c))
       (unsigned-byte-p 64 (fn-hrcur-field 4 c))))

(defun fn-hpe-begin (source capture lease)
  (declare (xargs :guard t))
  (list :codec (fn-hsrcb-begin source capture lease) 0 0 0 capture lease))

(defun fn-hpe-tick (c fn-hpb)
  (declare (xargs :stobjs fn-hpb))
  (let ((phase (fn-hrcur-field 0 c)) (codec (fn-hrcur-field 1 c))
        (k (fn-hrcur-field 2 c)) (w (fn-hrcur-field 3 c))
        (n (fn-hrcur-field 4 c)) (capture (fn-hrcur-field 5 c))
        (lease (fn-hrcur-field 6 c)))
    (cond
     ((not (fn-hpe-shapep c)) (mv '(:refused :cursor) nil c fn-hpb))
     ((eq phase :prepared) (mv :prepared n c fn-hpb))
     ((eq phase :refused) (mv '(:refused :codec) nil c fn-hpb))
     ; No child byte is consumed while physical page ownership is outstanding.
     ((fn-hpb-ready fn-hpb) (mv :page-full nil c fn-hpb))
     ((eq phase :finish)
      (mv-let (v word k2 w2) (fn-hrcur-word-finish k w)
        (declare (ignore k2 w2))
        (if (and (eq v :emit) (unsigned-byte-p 64 word))
            (mv-let (stored fn-hpb) (fn-hpb-put word fn-hpb)
              (declare (ignore stored))
              (mv :prepared n (list :prepared codec 0 0 n capture lease) fn-hpb))
          (if (eq v :prepared)
              (mv :prepared n (list :prepared codec 0 0 n capture lease) fn-hpb)
            (mv '(:refused :packing) nil c fn-hpb)))))
     (t
      (mv-let (v byte next) (fn-hsrcb-tick codec)
        (cond
         ((fn-hsrcb-demandp v) (mv v nil c fn-hpb))
         ((eq v :continue)
          (mv :continue nil (list :codec next k w n capture lease) fn-hpb))
         ((eq v :prepared)
          (mv :continue nil (list :finish next k w n capture lease) fn-hpb))
         ((and (eq v :emit) (fn-scc-octetp byte) (< (+ 1 n) 18446744073709551616))
          (mv-let (packed word k2 w2) (fn-hrcur-word-push byte k w)
            (cond
             ((and (eq packed :emit) (unsigned-byte-p 64 word))
              (mv-let (stored fn-hpb) (fn-hpb-put word fn-hpb)
                (declare (ignore stored))
                (mv :continue nil (list :codec next k2 w2 (+ 1 n) capture lease) fn-hpb)))
             ((eq packed :continue)
              (mv :continue nil (list :codec next k2 w2 (+ 1 n) capture lease) fn-hpb))
             (t (mv '(:refused :packing) nil c fn-hpb)))))
         (t (mv '(:refused :codec) nil (list :refused next k w n capture lease) fn-hpb))))))))

; Authenticated supply is a separate scheduling step. An outstanding page
; stays immutable and the byte is not consumed until its exact write ACK.
(defun fn-hpe-supply (c position byte fn-hpb)
  (declare (xargs :stobjs fn-hpb))
  (let ((codec (fn-hrcur-field 1 c)) (k (fn-hrcur-field 2 c))
        (w (fn-hrcur-field 3 c)) (n (fn-hrcur-field 4 c))
        (capture (fn-hrcur-field 5 c)) (lease (fn-hrcur-field 6 c)))
    (cond
     ((not (and (fn-hpe-shapep c) (eq (fn-hrcur-field 0 c) :codec)))
      (mv '(:refused :not-awaiting-cold-byte) c fn-hpb))
     ((fn-hpb-ready fn-hpb) (mv :page-full c fn-hpb))
     (t
      (mv-let (v emitted next) (fn-hsrcb-supply codec position byte)
        (cond
         ((eq v :continue)
          (mv :continue (list :codec next k w n capture lease) fn-hpb))
         ((and (eq v :emit) (fn-scc-octetp emitted)
               (< (+ 1 n) *fn-hrcur-u64-bound*))
          (mv-let (packed word k2 w2) (fn-hrcur-word-push emitted k w)
            (cond
             ((and (eq packed :emit) (unsigned-byte-p 64 word))
              (mv-let (stored fn-hpb) (fn-hpb-put word fn-hpb)
                (declare (ignore stored))
                (mv :continue (list :codec next k2 w2 (+ 1 n) capture lease) fn-hpb)))
             ((eq packed :continue)
              (mv :continue (list :codec next k2 w2 (+ 1 n) capture lease) fn-hpb))
             (t (mv '(:refused :packing) c fn-hpb)))))
         (t (mv v c fn-hpb))))))))

(defthm fn-hpe-supply-keeps-shape
  (implies (fn-hpe-shapep c)
           (fn-hpe-shapep (mv-nth 1 (fn-hpe-supply c position byte fn-hpb))))
  :hints (("Goal"
           :use ((:instance fn-hrcur-word-push-preserves
                    (octet (mv-nth 1 (fn-hsrcb-supply (fn-hrcur-field 1 c) position byte)))
                    (k (fn-hrcur-field 2 c)) (w (fn-hrcur-field 3 c))))
           :in-theory (e/d (fn-hpe-shapep fn-hpe-supply)
                 (fn-hsrcb-supply fn-hrcur-word-push fn-hpb-put
                  fn-hrcur-word-push-preserves)))))

(defthm fn-hpe-full-supply-does-not-consume
  (implies (and (fn-hpe-shapep c) (eq (fn-hrcur-field 0 c) :codec)
                (fn-hpb-ready fn-hpb))
           (equal (fn-hpe-supply c position byte fn-hpb)
                  (mv :page-full c fn-hpb)))
  :hints (("Goal" :in-theory (e/d (fn-hpe-supply)
                           (fn-hsrcb-supply fn-hrcur-word-push fn-hpb-put)))))

(defthm fn-hpe-begin-keeps-shape
  (fn-hpe-shapep (fn-hpe-begin source capture lease))
  :hints (("Goal" :in-theory (disable fn-hsrcb-begin fn-hrcur-byte-begin))))

(defthm fn-hpe-full-yields-before-consuming
  (implies (and (fn-hpe-shapep c)
                (member-eq (fn-hrcur-field 0 c) '(:codec :finish))
                (fn-hpb-ready fn-hpb))
           (and (equal (mv-nth 0 (fn-hpe-tick c fn-hpb)) :page-full)
                (equal (mv-nth 2 (fn-hpe-tick c fn-hpb)) c)
                (equal (mv-nth 3 (fn-hpe-tick c fn-hpb)) fn-hpb)))
  :hints (("Goal" :in-theory (disable fn-hsrcb-tick fn-hrcur-byte-tick fn-hrcur-word-push
                                      fn-hrcur-word-finish fn-hpb-put))))

(defthm fn-hpe-tick-keeps-shape
  (implies (fn-hpe-shapep c)
           (fn-hpe-shapep (mv-nth 2 (fn-hpe-tick c fn-hpb))))
  :hints (("Goal"
           :use ((:instance fn-hrcur-word-push-preserves
                            (octet (mv-nth 1 (fn-hsrcb-tick (fn-hrcur-field 1 c))))
                            (k (fn-hrcur-field 2 c)) (w (fn-hrcur-field 3 c))))
           :in-theory (disable fn-hsrcb-tick fn-hrcur-word-push
                         fn-hrcur-word-finish fn-hpb-put fn-hrcur-word-push-preserves))))

(defthm fn-hpe-tick-keeps-concrete
  (implies (fn-hpbp fn-hpb)
           (fn-hpbp (mv-nth 3 (fn-hpe-tick c fn-hpb))))
  :hints (("Goal" :in-theory (disable fn-hsrcb-tick fn-hrcur-word-push
                                      fn-hrcur-word-finish fn-hpb-put fn-hpbp))))

(defthm fn-hpe-tick-keeps-identities
  (and (equal (fn-hrcur-field 5 (mv-nth 2 (fn-hpe-tick c fn-hpb))) (fn-hrcur-field 5 c))
       (equal (fn-hrcur-field 6 (mv-nth 2 (fn-hpe-tick c fn-hpb))) (fn-hrcur-field 6 c))
       (equal (fn-hpb-epoch (mv-nth 3 (fn-hpe-tick c fn-hpb))) (fn-hpb-epoch fn-hpb))
       (equal (fn-hpb-lease (mv-nth 3 (fn-hpe-tick c fn-hpb))) (fn-hpb-lease fn-hpb)))
  :hints (("Goal" :in-theory (disable fn-hsrcb-tick fn-hrcur-word-push
                             fn-hrcur-word-finish fn-hpb-put fn-hpb-epoch fn-hpb-lease))))

; Proof-only byte accounting; no residual traversal occurs in tick or guards.
(defun fn-hpe-total (c)
  (declare (xargs :guard t :verify-guards nil))
  (+ (nfix (fn-hrcur-field 4 c)) (len (fn-hrcur-byte-rest (fn-hrcur-field 1 c)))))

(defun fn-hpe-invariantp (c)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-hpe-shapep c)
       (member-eq (fn-hrcur-field 0 c) '(:codec :finish :prepared))
       (fn-hrcur-byte-invariantp (fn-hrcur-field 1 c))
       (< (fn-hpe-total c) 18446744073709551616)
       (implies (member-eq (fn-hrcur-field 0 c) '(:finish :prepared))
                (equal (fn-hrcur-byte-rest (fn-hrcur-field 1 c)) nil))))

(defthm fn-hpe-begin-refines-byte-total
  (implies (and (fn-hrcur-tree-domainp row)
                (< (len (fn-scc-encode row)) 18446744073709551616))
           (and (fn-hpe-invariantp (fn-hpe-begin (list :resident row) capture lease))
                (equal (fn-hpe-total (fn-hpe-begin (list :resident row) capture lease))
                       (len (fn-scc-encode row)))))
  :hints (("Goal" :use ((:instance fn-hrcur-byte-begin-refines-encode))
           :in-theory (disable fn-hrcur-byte-begin fn-hrcur-byte-invariantp
                        fn-hrcur-byte-rest fn-hrcur-tree-domainp fn-scc-encode
                        fn-scc-program fn-scc-encode-is-program
                        fn-hrcur-byte-begin-refines-encode))))

(local
 (defthm fn-hpe-finish-permitted
   (implies (fn-hrcur-wordp k w)
            (and (member-eq (mv-nth 0 (fn-hrcur-word-finish k w)) '(:emit :prepared))
                 (implies (equal (mv-nth 0 (fn-hrcur-word-finish k w)) :emit)
                          (unsigned-byte-p 64 (mv-nth 1 (fn-hrcur-word-finish k w))))))
   :hints (("Goal" :cases ((equal k 0) (equal k 1) (equal k 2) (equal k 3)
                           (equal k 4) (equal k 5) (equal k 6) (equal k 7))
            :in-theory (enable fn-hrcur-wordp fn-hrcur-word-finish)))))

(local
 (defthm fn-hpe-shape-scalars
   (implies (fn-hpe-shapep c)
            (and (unsigned-byte-p 64 (fn-hrcur-field 4 c))
                 (fn-hrcur-wordp (fn-hrcur-field 2 c) (fn-hrcur-field 3 c))))))

(defthm fn-hpe-tick-preserves-byte-total
  (implies (fn-hpe-invariantp c)
           (and (fn-hpe-invariantp (mv-nth 2 (fn-hpe-tick c fn-hpb)))
                (equal (fn-hpe-total (mv-nth 2 (fn-hpe-tick c fn-hpb))) (fn-hpe-total c))
                (member-eq (mv-nth 0 (fn-hpe-tick c fn-hpb)) '(:continue :prepared :page-full))
                (implies (eq (mv-nth 0 (fn-hpe-tick c fn-hpb)) :prepared)
                         (equal (mv-nth 1 (fn-hpe-tick c fn-hpb)) (fn-hpe-total c)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrcur-byte-tick-preserves (c (fn-hrcur-field 1 c)))
                 (:instance fn-hrcur-byte-tick-refines-residual (c (fn-hrcur-field 1 c)))
                 (:instance fn-hrcur-byte-prepared-empty (c (fn-hrcur-field 1 c)))
                 (:instance fn-hpe-shape-scalars)
                 (:instance fn-hpe-tick-keeps-shape)
                 (:instance fn-hpe-finish-permitted (k (fn-hrcur-field 2 c)) (w (fn-hrcur-field 3 c)))
                 (:instance fn-hrcur-word-push-preserves
                            (octet (mv-nth 1 (fn-hrcur-byte-tick (fn-hrcur-field 1 c))))
                            (k (fn-hrcur-field 2 c)) (w (fn-hrcur-field 3 c))))
           :in-theory (disable fn-hsrcb-tick fn-hpe-shape-scalars fn-hpe-shapep fn-hrcur-byte-tick fn-hrcur-byte-invariantp
                        fn-hrcur-byte-rest fn-hpb-put fn-hrcur-word-push-preserves
                        fn-hrcur-byte-tick-preserves fn-hrcur-byte-tick-refines-residual
                        fn-hrcur-byte-prepared-empty fn-hpe-tick-keeps-shape))))

(local
 (defthm fn-hpe-old-emission-is-resident
   (implies (equal (mv-nth 0 (fn-hrcur-byte-tick c)) :emit)
            (not (fn-hsrcb-coldp c)))
   :hints (("Goal" :in-theory (e/d (fn-hrcur-byte-tick fn-hsrcb-coldp
                                    fn-hrcur-widthp)
                       (fn-hrcur-tree-tick fn-hrsc-tick fn-hrcur-leaf-tick))))))

; Actual concrete eighth-byte write, connected to existing fn-hp-pack8.
(defthm fn-hpe-eighth-byte-refines-pool-word
  (let ((byte (mv-nth 1 (fn-hrcur-byte-tick (fn-hrcur-field 1 c)))))
    (implies
     (and (fn-hpe-shapep c) (equal (fn-hrcur-field 0 c) :codec)
          (natp (fn-hpb-used fn-hpb)) (< (fn-hpb-used fn-hpb) 2048)
          (equal (fn-hrcur-field 2 c) 7) (equal (len prefix) 7)
          (equal (fn-hrcur-field 3 c) (adt-unle 7 prefix))
          (equal (mv-nth 0 (fn-hrcur-byte-tick (fn-hrcur-field 1 c))) :emit)
          (fn-scc-octetp byte) (< (+ 1 (fn-hrcur-field 4 c)) 18446744073709551616))
     (equal (fn-hpb-prefix (mv-nth 3 (fn-hpe-tick c fn-hpb)))
            (append (fn-hpb-prefix fn-hpb)
                    (list (car (fn-hp-pack8 1 (append prefix (list byte)))))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrcur-word-push-refines-pack8
                   (w (fn-hrcur-field 3 c))
                   (octet (mv-nth 1 (fn-hrcur-byte-tick (fn-hrcur-field 1 c)))))
                 (:instance fn-hrcur-word-push-preserves (k 7) (w (fn-hrcur-field 3 c))
                   (octet (mv-nth 1 (fn-hrcur-byte-tick (fn-hrcur-field 1 c))))))
           :in-theory (disable fn-hsrcb-tick fn-hrcur-byte-tick fn-hrcur-word-push fn-hrcur-word-finish
                        fn-hpb-put fn-hpb-prefix fn-hp-pack8 adt-unle fn-hrcur-wordp
                        fn-hrcur-word-push-refines-pack8 fn-hrcur-word-push-preserves))))

(defthm fn-hpe-finish-refines-padded-pool-word
  (implies
   (and (fn-hpe-shapep c) (equal (fn-hrcur-field 0 c) :finish)
        (natp (fn-hpb-used fn-hpb)) (< (fn-hpb-used fn-hpb) 2048)
        (equal (fn-hrcur-field 2 c) (len prefix)) (< 0 (fn-hrcur-field 2 c))
        (equal (fn-hrcur-field 3 c) (adt-unle (fn-hrcur-field 2 c) prefix)))
   (and (equal (mv-nth 0 (fn-hpe-tick c fn-hpb)) :prepared)
        (equal (fn-hpb-prefix (mv-nth 3 (fn-hpe-tick c fn-hpb)))
               (append (fn-hpb-prefix fn-hpb)
                       (list (car (fn-hp-pack8 1 (append prefix (adt-zeros (- 8 (len prefix)))))))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrcur-word-finish-refines-pad8
                            (k (fn-hrcur-field 2 c)) (w (fn-hrcur-field 3 c)))
                 (:instance fn-hpe-finish-permitted
                            (k (fn-hrcur-field 2 c)) (w (fn-hrcur-field 3 c))))
           :in-theory (disable fn-hsrcb-tick fn-hrcur-byte-tick fn-hrcur-word-push fn-hrcur-word-finish
                        fn-hpb-put fn-hpb-prefix fn-hp-pack8 adt-zeros adt-unle
                        fn-hrcur-word-finish-refines-pad8 fn-hpe-finish-permitted))))

(in-theory (disable fn-hpe-begin fn-hpe-shapep fn-hpe-tick fn-hpe-total fn-hpe-invariantp))
