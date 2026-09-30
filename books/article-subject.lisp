; relay-v1 legacy article subjects. RFC 5537 3.6/3.7 permits only Path/Xref
; changes; the received-bytes subject and exact signed-source subject retain
; their existing meanings. This projection calls the existing raw-line walker.
(in-package "ACL2")
(include-book "path-update")
(include-book "identity")

(defconst *fn-asj-profile-relay-v1* '(114 101 108 97 121 45 118 49))
(defconst *fn-asj-label* '(102 110 47 97 114 116 105 99 108 101 45 115 117 98 106 101 99 116 47 118 49))
(defun fn-asj-project (w)
  (declare (xargs :guard t))
  (fn-pu-strip w nil))
(defun fn-asj-preimage (w)
  (declare (xargs :guard (and (fn-cbor-octet-listp (fn-asj-project w))
                            (<= (len (fn-asj-project w)) *fn-cbor-max-uint*))))
  (let ((p (fn-asj-project w)))
    (append *fn-asj-label*
            (cons *fn-id-separator*
                  (append (fn-cbor-u32-bytes (len *fn-asj-profile-relay-v1*))
                          *fn-asj-profile-relay-v1*
                          (fn-cbor-u32-bytes (len p)) p)))))
(defun fn-asj-subject (w)
  (declare (xargs :guard (and (fn-cbor-octet-listp (fn-asj-project w))
                            (<= (len (fn-asj-project w)) *fn-cbor-max-uint*))
                  :verify-guards nil))
  (fn-id-render *fn-asj-label* (fn-frame-digest (fn-asj-preimage w))))

(defthm fn-asj-project-of-relay-article
  (equal (fn-asj-project (fn-pu-relay-article w identity expected))
         (fn-asj-project w))
  :hints (("Goal" :in-theory (enable fn-asj-project))))
(defthm fn-asj-subject-of-equal-projections-by-definition
  (implies (equal (fn-asj-project w) (fn-asj-project w2))
           (equal (fn-asj-subject w) (fn-asj-subject w2)))
  :hints (("Goal" :in-theory (e/d (fn-asj-subject fn-asj-preimage)
                                 (fn-asj-project fn-id-render)))))

; Body includes the separating CRLF. No header parser normalization appears.
(defun fn-asj-body (w)
  (declare (xargs :guard t :measure (acl2-count w)))
  (cond ((atom w) w)
        ((equal (fn-pu-line w) '(13 10)) w)
        (t (fn-asj-body (fn-pu-after-line w)))))

(local (defthm fn-asj-append-is-append
  (equal (fn-pu-append a b) (append a b))
  :hints (("Goal" :in-theory (enable fn-pu-append)))))
(local (defthm fn-asj-line-reconstructs
  (implies (true-listp w)
           (equal (append (fn-pu-line w) (fn-pu-after-line w)) w))
  :hints (("Goal" :induct (fn-pu-after-line w)
                  :in-theory (enable fn-pu-line fn-pu-after-line fn-pu-crlf-atp)))))

(local (defthm fn-asj-line-of-crlf-piece
  (implies (fn-pu-crlf-endedp l)
           (and (equal (fn-pu-line (append l z)) (fn-pu-line l))
                (equal (fn-pu-after-line (append l z)) z)))
  :hints (("Goal" :induct (fn-pu-crlf-endedp l)
                  :in-theory (enable fn-pu-crlf-endedp fn-pu-line fn-pu-after-line fn-pu-crlf-atp)))))
(local (defthm fn-asj-line-with-crlf-ended
  (implies (fn-pu-has-crlfp w) (fn-pu-crlf-endedp (fn-pu-line w)))
  :hints (("Goal" :induct (fn-pu-has-crlfp w)
                  :in-theory (enable fn-pu-has-crlfp fn-pu-crlf-endedp fn-pu-line fn-pu-crlf-atp)))))
(local (defthm fn-asj-no-crlf-after
  (implies (not (fn-pu-has-crlfp w)) (equal (fn-pu-after-line w) nil))
  :hints (("Goal" :induct (fn-pu-after-line w)
                  :in-theory (enable fn-pu-after-line fn-pu-has-crlfp)))))
(local (defthm fn-asj-line-of-line
  (and (equal (fn-pu-line (fn-pu-line w)) (fn-pu-line w))
       (equal (fn-pu-after-line (fn-pu-line w)) nil))
  :hints (("Goal" :induct (fn-pu-line w)
                  :in-theory (enable fn-pu-line fn-pu-after-line fn-pu-crlf-atp)))))
(local (defthm fn-asj-body-of-kept-line
  (implies (and (consp w) (not (equal (fn-pu-line w) '(13 10)))
                (or (fn-pu-has-crlfp w) (equal z nil)))
           (equal (fn-asj-body (append (fn-pu-line w) z)) (fn-asj-body z)))
  :hints (("Goal" :cases ((fn-pu-has-crlfp w))
                  :expand ((fn-asj-body (append (fn-pu-line w) z)))
                  :in-theory (e/d (fn-asj-body) (fn-pu-line fn-pu-after-line))))))
(defthm fn-asj-body-of-strip
  (equal (fn-asj-body (fn-pu-strip w dropping)) (fn-asj-body w))
  :hints (("Goal" :induct (fn-pu-strip w dropping)
                  :in-theory (e/d (fn-pu-strip fn-asj-body)
                                   (fn-pu-line fn-pu-after-line fn-pu-named-p fn-pu-wspp)))
          ("Subgoal *1/6" :cases ((fn-pu-has-crlfp w)))
          ("Subgoal *1/4" :cases ((fn-pu-has-crlfp w)))
          ("Subgoal *1/3" :cases ((fn-pu-has-crlfp w)))))

(local (defthm fn-asj-preimage-octets
  (implies (and (fn-cbor-octet-listp (fn-asj-project w))
                (<= (len (fn-asj-project w)) *fn-cbor-max-uint*))
           (fn-cbor-octet-listp (fn-asj-preimage w)))
  ; Frame and CBOR deliberately close these representation lemmas on export.
  ; Name the two facts this preimage needs instead of relying on include order.
  :hints (("Goal" :in-theory
           (e/d (fn-asj-preimage fn-cbor-octet-listp fn-cbor-octetp
                 fn-frame-octet-listp-of-append)
                (fn-asj-project fn-cbor-u32-bytes))
           :use ((:instance fn-cbor-u32-bytes-are-octets
                            (n (len (fn-asj-project w)))))))))
(verify-guards fn-asj-subject
  :hints (("Goal" :in-theory (enable fn-id-digestp))))

; The complement promises the exact protected header/body byte string and
; independently proves that its body is the original body's exact suffix.
(defthm fn-asj-equal-projections-preserve-body
  (implies (equal (fn-asj-project w) (fn-asj-project w2))
           (equal (fn-asj-body w) (fn-asj-body w2)))
  :hints (("Goal" :use ((:instance fn-asj-body-of-strip (dropping nil))
                        (:instance fn-asj-body-of-strip (w w2) (dropping nil)))
                  :in-theory (e/d (fn-asj-project)
                                   (fn-asj-body fn-pu-strip fn-asj-body-of-strip))))
  :rule-classes nil)

; Non-WSP boundary excludes accidentally swallowing another field's
; continuation when a trace block is inserted.
(defun fn-asj-boundaryp (w)
  (declare (xargs :guard t))
  (or (atom w) (equal (fn-pu-line w) '(13 10))
      (not (fn-pu-wspp (car (fn-pu-line w))))))
(defun fn-asj-continuationsp (f)
  (declare (xargs :guard t :measure (acl2-count f)))
  (if (atom f) (null f)
    (and (fn-pu-has-crlfp f) (fn-pu-wspp (car f))
         (fn-asj-continuationsp (fn-pu-after-line f)))))
(defun fn-asj-trace-blockp (f)
  (declare (xargs :guard t))
  (and (consp f) (true-listp f) (fn-pu-has-crlfp f)
       (not (fn-pu-wspp (car f)))
       (or (fn-pu-named-p (fn-pu-line f) *fn-pu-path-colon*)
           (fn-pu-named-p (fn-pu-line f) *fn-pu-xref-colon*))
       (fn-asj-continuationsp (fn-pu-after-line f))))

(local (defthm fn-asj-strip-boundary
  (implies (fn-asj-boundaryp w)
           (equal (fn-pu-strip w t) (fn-pu-strip w nil)))
  :hints (("Goal" :expand ((fn-pu-strip w t) (fn-pu-strip w nil))
                  :in-theory (enable fn-asj-boundaryp)))))
(local (defthm fn-asj-first-line-of-append
  (implies (fn-pu-has-crlfp f)
           (and (equal (fn-pu-line (append f w)) (fn-pu-line f))
                (equal (fn-pu-after-line (append f w))
                       (append (fn-pu-after-line f) w))))
  :hints (("Goal" :induct (fn-pu-after-line f)
                  :in-theory (enable fn-pu-has-crlfp fn-pu-line fn-pu-after-line fn-pu-crlf-atp)))))
(local (defthm fn-asj-car-of-line
  (implies (consp f) (equal (car (fn-pu-line f)) (car f)))
  :hints (("Goal" :expand ((fn-pu-line f)) :in-theory (enable fn-pu-crlf-atp)))))
(local (defthm fn-asj-blank-first-octet
  (implies (equal (fn-pu-line f) '(13 10)) (equal (car f) 13))
  :rule-classes :forward-chaining
  :hints (("Goal" :expand ((fn-pu-line f)) :in-theory (enable fn-pu-crlf-atp)))))
(local (defthm fn-asj-strip-continuations
  (implies (and (fn-asj-continuationsp f) (fn-asj-boundaryp w))
           (equal (fn-pu-strip (append f w) t) (fn-pu-strip w nil)))
  :hints (("Goal" :induct (fn-asj-continuationsp f)
                  :expand ((fn-pu-strip (append f w) t))
                  :in-theory (e/d (fn-asj-continuationsp fn-pu-wspp)
                                   (fn-pu-line fn-pu-after-line fn-pu-strip fn-pu-named-p fn-asj-boundaryp))))))
(defthm fn-asj-project-of-inserted-trace-block
  (implies (and (fn-asj-trace-blockp f) (fn-asj-boundaryp w))
           (equal (fn-asj-project (append f w)) (fn-asj-project w)))
  :hints (("Goal" :expand ((fn-pu-strip (append f w) nil))
                  :in-theory (e/d (fn-asj-project fn-asj-trace-blockp)
                                   (fn-pu-line fn-pu-after-line fn-pu-strip fn-pu-named-p fn-pu-wspp)))))

(defun fn-asj-insert-at (w n f)
  (declare (xargs :guard (and (natp n) (true-listp f)) :measure (nfix n)))
  (if (zp n) (append f w)
    (append (fn-pu-line w) (fn-asj-insert-at (fn-pu-after-line w) (1- n) f))))
(defun fn-asj-insertion-boundaryp (w n)
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (zp n) (fn-asj-boundaryp w)
    (and (consp w) (fn-pu-has-crlfp w)
         (not (equal (fn-pu-line w) '(13 10)))
         (fn-asj-insertion-boundaryp (fn-pu-after-line w) (1- n)))))
(local (defthm fn-asj-line-consp
  (equal (consp (fn-pu-line w)) (consp w))
  :hints (("Goal" :expand ((fn-pu-line w)) :in-theory (enable fn-pu-crlf-atp)))))
(local (defthm fn-asj-consp-append
  (equal (consp (append a b)) (or (consp a) (consp b)))
  :hints (("Goal" :in-theory (enable binary-append)))))
(local (defthm fn-asj-strip-of-front-line
  (implies (and (consp w) (fn-pu-has-crlfp w) (not (equal (fn-pu-line w) '(13 10))))
           (equal (fn-pu-strip (append (fn-pu-line w) z) d)
                  (let ((line (fn-pu-line w)))
                    (cond ((fn-pu-wspp (car line))
                           (if d (fn-pu-strip z t)
                             (append line (fn-pu-strip z nil))))
                          ((or (fn-pu-named-p line *fn-pu-xref-colon*)
                               (fn-pu-named-p line *fn-pu-path-colon*))
                           (fn-pu-strip z t))
                          (t (append line (fn-pu-strip z nil)))))))
  :hints (("Goal" :expand ((fn-pu-strip (append (fn-pu-line w) z) d))
                  :in-theory (disable fn-pu-strip fn-pu-line fn-pu-after-line fn-pu-wspp fn-pu-named-p)))))
(local (defthm fn-asj-strip-trace-block
  (implies (and (fn-asj-trace-blockp f) (fn-asj-boundaryp w))
           (equal (fn-pu-strip (append f w) d) (fn-pu-strip w nil)))
  :hints (("Goal" :expand ((fn-pu-strip (append f w) d))
                  :in-theory (e/d (fn-asj-trace-blockp)
                                   (fn-pu-line fn-pu-after-line fn-pu-strip fn-pu-wspp fn-pu-named-p fn-asj-boundaryp))))))
(local (defthm fn-asj-strip-insert-at
  (implies (and (fn-asj-trace-blockp f) (fn-asj-insertion-boundaryp w n))
           (and (equal (fn-pu-strip (fn-asj-insert-at w n f) nil) (fn-pu-strip w nil))
                (equal (fn-pu-strip (fn-asj-insert-at w n f) t) (fn-pu-strip w t))))
  :hints (("Goal" :induct (fn-asj-insert-at w n f)
                  :in-theory (e/d (fn-asj-insert-at fn-asj-insertion-boundaryp)
                                   (fn-pu-line fn-pu-after-line fn-pu-strip fn-pu-wspp fn-pu-named-p fn-asj-trace-blockp fn-asj-boundaryp)))
          ("Subgoal *1/2" :expand ((fn-pu-strip w nil) (fn-pu-strip w t))))))
(defthm fn-asj-project-of-permitted-insertion
  (implies (and (fn-asj-trace-blockp f) (fn-asj-insertion-boundaryp w n))
           (equal (fn-asj-project (fn-asj-insert-at w n f)) (fn-asj-project w)))
  :hints (("Goal" :in-theory (enable fn-asj-project))))

(local (defthm fn-asj-strip-of-line-only
  (implies (consp w)
    (equal (fn-pu-strip (fn-pu-line w) nil)
         (if (or (and (not (fn-pu-wspp (car (fn-pu-line w))))
                       (or (fn-pu-named-p (fn-pu-line w) *fn-pu-path-colon*)
                           (fn-pu-named-p (fn-pu-line w) *fn-pu-xref-colon*))))
             nil (fn-pu-line w))))
  :hints (("Goal" :expand ((fn-pu-strip (fn-pu-line w) nil))
                  :in-theory (e/d (fn-pu-append) (fn-pu-strip fn-pu-line fn-pu-after-line fn-pu-wspp fn-pu-named-p))))))
(defthm fn-asj-strip-idempotent
  (equal (fn-pu-strip (fn-pu-strip w d) nil) (fn-pu-strip w d))
  :hints (("Goal" :induct (fn-pu-strip w d)
                  :in-theory (e/d (fn-pu-strip)
                                   (fn-pu-line fn-pu-after-line fn-pu-wspp fn-pu-named-p)))
          ("Subgoal *1/6" :cases ((fn-pu-has-crlfp w)))
          ("Subgoal *1/4" :cases ((fn-pu-has-crlfp w)))
          ("Subgoal *1/3" :cases ((fn-pu-has-crlfp w)))))
(defthm fn-asj-project-idempotent
  (equal (fn-asj-project (fn-asj-project w)) (fn-asj-project w))
  :hints (("Goal" :in-theory (enable fn-asj-project))))

(defun fn-asj-step-shapep (s)
  (declare (xargs :guard t))
  (and (true-listp s) (equal (len s) 2) (natp (car s)) (true-listp (cadr s))))
(defun fn-asj-insert-all (w steps)
  (declare (xargs :guard t))
  (if (atom steps) w
    (if (fn-asj-step-shapep (car steps))
        (fn-asj-insert-all (fn-asj-insert-at w (caar steps) (cadar steps)) (cdr steps))
      w)))
(defun fn-asj-steps-validp (w steps)
  (declare (xargs :guard t :measure (acl2-count steps)))
  (if (atom steps) (null steps)
    (and (fn-asj-step-shapep (car steps))
         (fn-asj-trace-blockp (cadar steps))
         (fn-asj-insertion-boundaryp w (caar steps))
         (fn-asj-steps-validp (fn-asj-insert-at w (caar steps) (cadar steps)) (cdr steps)))))
(defthm fn-asj-project-of-insert-all
  (implies (fn-asj-steps-validp w steps)
           (equal (fn-asj-project (fn-asj-insert-all w steps)) (fn-asj-project w)))
  :hints (("Goal" :induct (fn-asj-insert-all w steps)
                  :in-theory (e/d (fn-asj-insert-all fn-asj-steps-validp fn-asj-step-shapep)
                                   (fn-asj-project fn-asj-insert-at fn-asj-trace-blockp fn-asj-insertion-boundaryp)))))
(defun fn-asj-permitted-relay-transformp (w w2 steps)
  (declare (xargs :guard t))
  (and (fn-asj-steps-validp (fn-asj-project w) steps)
       (equal w2 (fn-asj-insert-all (fn-asj-project w) steps))))
(defthm fn-asj-permitted-relay-transform-preserves-projection
  (implies (fn-asj-permitted-relay-transformp w w2 steps)
           (equal (fn-asj-project w2) (fn-asj-project w)))
  :hints (("Goal" :in-theory (e/d (fn-asj-permitted-relay-transformp) (fn-asj-project)))))

(defun fn-asj-subsequencep (xs ys)
  ; Proof-only observer: existential deletion of bytes, never a served walk.
  (declare (xargs :guard t :measure (acl2-count ys)))
  (if (atom xs) (null xs)
    (and (consp ys)
         (or (and (equal (car xs) (car ys)) (fn-asj-subsequencep (cdr xs) (cdr ys)))
             (fn-asj-subsequencep xs (cdr ys))))))
(local (defthm fn-asj-subsequence-reflexive
  (implies (true-listp xs) (fn-asj-subsequencep xs xs))
  :hints (("Goal" :induct (true-listp xs) :in-theory (enable fn-asj-subsequencep)))))
(local (defthm fn-asj-subsequence-skip-prefix
  (implies (fn-asj-subsequencep xs ys) (fn-asj-subsequencep xs (append a ys)))
  :hints (("Goal" :induct (append a ys) :in-theory (enable fn-asj-subsequencep)))))
(local (defthm fn-asj-subsequence-kept-prefix
  (implies (fn-asj-subsequencep xs ys)
           (fn-asj-subsequencep (append a xs) (append a ys)))
  :hints (("Goal" :induct (append a ys) :in-theory (enable fn-asj-subsequencep)))))
(local (defthm fn-asj-after-line-true-list
  (implies (true-listp w) (true-listp (fn-pu-after-line w)))
  :hints (("Goal" :induct (fn-pu-after-line w) :in-theory (enable fn-pu-after-line)))))
(defthm fn-asj-strip-preserves-byte-order
  (implies (true-listp w) (fn-asj-subsequencep (fn-pu-strip w d) w))
  :hints (("Goal" :induct (fn-pu-strip w d)
                  :in-theory (e/d (fn-pu-strip)
                                   (fn-pu-line fn-pu-after-line fn-pu-wspp fn-pu-named-p fn-asj-subsequencep)))
          ("Subgoal *1/6" :use ((:instance fn-asj-subsequence-kept-prefix
                                   (a (fn-pu-line w)) (ys (fn-pu-after-line w))
                                   (xs (fn-pu-strip (fn-pu-after-line w) nil))))
                           :expand ((fn-pu-strip w d) (fn-pu-strip w nil) (fn-pu-strip w t))
                           :in-theory (disable fn-asj-subsequencep fn-asj-subsequence-kept-prefix fn-pu-strip fn-pu-line fn-pu-after-line fn-pu-wspp fn-pu-named-p))
          ("Subgoal *1/5" :use ((:instance fn-asj-subsequence-skip-prefix
                                   (a (fn-pu-line w)) (ys (fn-pu-after-line w))
                                   (xs (fn-pu-strip (fn-pu-after-line w) t))))
                           :expand ((fn-pu-strip w d) (fn-pu-strip w nil) (fn-pu-strip w t))
                           :in-theory (disable fn-asj-subsequencep fn-asj-subsequence-skip-prefix fn-pu-strip fn-pu-line fn-pu-after-line fn-pu-wspp fn-pu-named-p))
          ("Subgoal *1/4" :use ((:instance fn-asj-subsequence-kept-prefix
                                   (a (fn-pu-line w)) (ys (fn-pu-after-line w))
                                   (xs (fn-pu-strip (fn-pu-after-line w) nil))))
                           :expand ((fn-pu-strip w d) (fn-pu-strip w nil) (fn-pu-strip w t))
                           :in-theory (disable fn-asj-subsequencep fn-asj-subsequence-kept-prefix fn-pu-strip fn-pu-line fn-pu-after-line fn-pu-wspp fn-pu-named-p))
          ("Subgoal *1/3" :use ((:instance fn-asj-subsequence-skip-prefix
                                   (a (fn-pu-line w)) (ys (fn-pu-after-line w))
                                   (xs (fn-pu-strip (fn-pu-after-line w) t))))
                           :expand ((fn-pu-strip w d) (fn-pu-strip w nil) (fn-pu-strip w t))
                           :in-theory (disable fn-asj-subsequencep fn-asj-subsequence-skip-prefix fn-pu-strip fn-pu-line fn-pu-after-line fn-pu-wspp fn-pu-named-p))
))

; Keystones stay closed outside their particular proof hints.
(in-theory (disable fn-asj-project fn-asj-preimage fn-asj-subject fn-asj-body fn-asj-boundaryp fn-asj-continuationsp fn-asj-trace-blockp
                    fn-asj-insert-at fn-asj-insertion-boundaryp fn-asj-step-shapep
                    fn-asj-insert-all fn-asj-steps-validp fn-asj-permitted-relay-transformp fn-asj-subsequencep))
