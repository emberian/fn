; OVER's pool-window proof interface: a writable position, preserved pool
; metadata, and composition of adjacent splices. No renderer dependency.
; C20 keeps its accessor/shape lemmas local to def-span-scan-window. This
; book re-proves the subset used by OVER's guard and splice proofs.
(in-package "ACL2")
(include-book "def-span-scan-window")
(local (include-book "arithmetic-5/top" :dir :system))
(defthm fn-ovrqp-get-of-set
  (equal (fn-rtc-get i (fn-rtc-set j v l))
         (if (and (equal (nfix i) (nfix j)) (< (nfix j) (len l))) v (fn-rtc-get i l))))

(defthm fn-ovrqp-set-of-set
  (equal (fn-rtc-set j v2 (fn-rtc-set j v1 l)) (fn-rtc-set j v2 l)))

(defthm fn-ovrqp-len-of-set (equal (len (fn-rtc-set j v l)) (len l)))

(defthm fn-ovrqp-get-past-len (implies (<= (len l) (nfix i)) (equal (fn-rtc-get i l) nil)))

(defthm fn-ovrqp-with-buffer-accessors
  (and (equal (fn-rtc-config (fn-rtc-with-buffer h b s)) (fn-rtc-config s))
       (equal (fn-rtc-uses (fn-rtc-with-buffer h b s)) (fn-rtc-uses s))
       (equal (fn-rtc-buffer k (fn-rtc-with-buffer h b s))
              (if (and (equal (nfix k) (nfix h)) (< (nfix h) (len (fn-rtc-pool s)))) b (fn-rtc-buffer k s)))
       (equal (fn-rtc-with-buffer h b2 (fn-rtc-with-buffer h b1 s)) (fn-rtc-with-buffer h b2 s)))
  :hints (("Goal" :in-theory (enable fn-rtc-with-buffer fn-rtc-config fn-rtc-uses fn-rtc-buffer fn-rtc-pool
                                     fn-rtc-make fn-rtc-slots fn-rtc-mstates fn-rtc-next-op))))
(defthm fn-ovrqp-pool-length
 (implies (fn-rtc-st$ap s) (equal (len (fn-rtc-pool s)) (fn-rtc-nbufs (fn-rtc-config s))))
 :hints (("Goal" :in-theory (union-theories '(fn-rtc-st$ap fn-rtc-shapep) (theory 'minimal-theory)))))

(defthm fn-ovrqp-buffer-shape
 (implies (fn-rtc-st$ap s)
  (and (fn-cbor-octet-listp (fn-rtc-b-bytes (fn-rtc-buffer h s)))
       (implies (< (nfix h) (fn-rtc-nbufs (fn-rtc-config s)))
         (and (true-listp (fn-rtc-buffer h s)) (equal (len (fn-rtc-buffer h s)) 3)))))
 :hints (("Goal" :use fn-rtc-c-shapep-buffer
          :in-theory (union-theories '(fn-rtc-st$ap fn-rtc-b-bytes) (theory 'minimal-theory)))))

(defthm fn-ovrqp-splice-preserves-ap
 (implies (fn-rtc-st$ap s) (fn-rtc-st$ap (fn-rtc-st$a-splice h j data s)))
 :hints (("Goal" :use ((:instance fn-rtc-st-splice{preserved} (fn-rtc-st s) (off j)))
          :in-theory (theory 'minimal-theory))))

(defun fn-ovrqp-roomp (h j limit s)
 (declare (xargs :verify-guards nil))
 (and (fn-rtc-st$ap s) (natp j) (natp limit) (<= j limit)
      (<= limit (fn-rtc-buf-cap h (fn-rtc-config s))) (fn-rtc-splice-okp h j nil s)))
(defthm fn-ovrqp-splice-frames
 (implies (and (fn-rtc-st$ap s) (fn-rtc-splice-okp h j data s))
   (and (equal (fn-rtc-config (fn-rtc-st$a-splice h j data s)) (fn-rtc-config s))
        (equal (fn-rtc-uses (fn-rtc-st$a-splice h j data s)) (fn-rtc-uses s))
        (equal (fn-rtc-b-owner (fn-rtc-buffer h (fn-rtc-st$a-splice h j data s)))
               (fn-rtc-b-owner (fn-rtc-buffer h s)))
        (equal (fn-rtc-b-bytes (fn-rtc-buffer h (fn-rtc-st$a-splice h j data s)))
               (fn-rtc-splice (fn-rtc-b-bytes (fn-rtc-buffer h s)) j data))))
 :hints (("Goal" :in-theory
  (union-theories '(fn-rtc-st$a-splice fn-rtc-splice-okp fn-rtc-b-owner fn-rtc-b-bytes fn-rtc-get
                   fn-ovrqp-with-buffer-accessors fn-ovrqp-pool-length fn-ovrqp-buffer-shape
                   natp nfix zp car-cons cdr-cons len)
                  (theory 'minimal-theory)))))
(defthm fn-ovrqp-room-after-splice
 (implies (and (fn-ovrqp-roomp h j limit s) (fn-cbor-octet-listp data) (<= (+ j (len data)) limit))
   (and (fn-rtc-splice-okp h j data s)
        (fn-ovrqp-roomp h (+ j (len data)) limit (fn-rtc-st$a-splice h j data s))))
 :hints (("Goal" :do-not-induct t :in-theory
   (union-theories '(fn-ovrqp-roomp fn-rtc-splice-okp
      fn-ovrqp-splice-frames fn-ovrqp-splice-preserves-ap fn-ovrqp-buffer-shape
      fn-rtc-c-l-splice-length fn-cbor-octet-listp-implies-true-listp
      natp nfix max len zp car-cons cdr-cons (:type-prescription len)
      (:executable-counterpart fn-cbor-octet-listp))
      (theory 'minimal-theory)))))
(defthm fn-ovrqp-nfix-natural (implies (natp x) (equal (nfix x) x)))
(defthm fn-ovrqp-natural-nfix (natp (nfix x)) :rule-classes :type-prescription)
(defthm fn-ovrqp-len-append
 (equal (len (append a b)) (+ (len a) (len b)))
 :hints (("Goal" :induct (append a b) :in-theory (enable binary-append len))))
(defthm fn-ovrqp-puts-compose
 (implies (natp j)
  (equal (fn-rtc-st$a-puts h (+ j (len a)) b (fn-rtc-st$a-puts h j a s))
         (fn-rtc-st$a-puts h j (append a b) s)))
 :hints (("Goal" :induct (fn-rtc-st$a-puts h j a s)
    :in-theory (e/d (fn-rtc-st$a-puts binary-append) (fn-rtc-st$a-put fn-rtc-st$a-splice fn-rtc-splice)))))
(defthm fn-ovrqp-room-properties
 (implies (fn-ovrqp-roomp h j limit s)
   (and (fn-rtc-st$ap s) (natp j) (natp limit)))
 :rule-classes (:rewrite :forward-chaining)
 :hints (("Goal" :in-theory (union-theories '(fn-ovrqp-roomp) (theory 'minimal-theory)))))
(defthm fn-ovrqp-splice-compose
 (implies (and (fn-ovrqp-roomp h j limit s) (fn-cbor-octet-listp a) (fn-cbor-octet-listp b)
               (<= (+ j (len a) (len b)) limit))
   (equal (fn-rtc-st$a-splice h (+ j (len a)) b (fn-rtc-st$a-splice h j a s))
          (fn-rtc-st$a-splice h j (append a b) s)))
 :hints (("Goal" :do-not-induct t
   :use ((:instance fn-ovrqp-room-after-splice (data a))
         (:instance fn-ovrqp-room-after-splice (data b) (j (+ j (len a)))
                    (s (fn-rtc-st$a-splice h j a s)))
         (:instance fn-dsw-splice-is-puts (data a))
         (:instance fn-dsw-splice-is-puts (data b) (j (+ j (len a)))
                    (s (fn-rtc-st$a-splice h j a s)))
         (:instance fn-dsw-splice-is-puts (data (append a b))))
   :in-theory (union-theories '(fn-ovrqp-room-properties fn-ovrqp-room-after-splice
                  fn-ovrqp-splice-preserves-ap fn-ovrqp-len-append fn-ovrqp-puts-compose
                  fn-rtc-c-l-octets-append natp nfix (:type-prescription len))
                 (theory 'minimal-theory)))))

; Positions may be arithmetically normalized before splice facts rewrite.
(defthm fn-ovrqp-empty-append-keeps-state
 (equal (mv-nth 2 (fn-dsw-append h j nil st)) st)
 :hints (("Goal" :in-theory (union-theories '(fn-dsw-append fn-dsw-append-loop mv-nth car-cons cdr-cons
                (:executable-counterpart fn-cbor-octet-listp) len) (theory 'minimal-theory)))))
(defthm fn-ovrqp-empty-append-position
 (implies (natp j) (equal (mv-nth 1 (fn-dsw-append h j nil st)) j))
 :hints (("Goal" :in-theory (union-theories '(fn-dsw-append fn-dsw-append-loop mv-nth car-cons cdr-cons
                (:executable-counterpart fn-cbor-octet-listp) len default-+-1 default-+-2)
                (fn-dss-measure-theory)))))
(defthm fn-ovrqp-empty-splice
 (implies (and (fn-rtc-st$ap st) (fn-rtc-splice-okp h j nil st))
   (equal (fn-rtc-st$a-splice h j nil st) st))
 :hints (("Goal" :use ((:instance fn-dsw-append-is-splice (data nil) (s st))
                      fn-ovrqp-empty-append-keeps-state)
    :in-theory (union-theories '(mv-nth car-cons cdr-cons zp len) (theory 'minimal-theory)))))
(defthm fn-ovrqp-room-at-splice-position
 (implies (and (fn-ovrqp-roomp h j limit s) (fn-cbor-octet-listp data)
               (equal j2 (+ j (len data))) (<= j2 limit))
  (fn-ovrqp-roomp h j2 limit (fn-rtc-st$a-splice h j data s)))
 :hints (("Goal" :use fn-ovrqp-room-after-splice :in-theory (theory 'minimal-theory))))
(defthm fn-ovrqp-compose-at-splice-position
 (implies (and (fn-ovrqp-roomp h j limit s) (fn-cbor-octet-listp a) (fn-cbor-octet-listp b)
               (equal j2 (+ j (len a))) (<= (+ j2 (len b)) limit))
   (equal (fn-rtc-st$a-splice h j2 b (fn-rtc-st$a-splice h j a s))
          (fn-rtc-st$a-splice h j (append a b) s)))
 :hints (("Goal" :use fn-ovrqp-splice-compose :in-theory
    (union-theories '(associativity-of-+) (theory 'minimal-theory)))))
(defthm fn-ovrqp-append-associates
 (equal (append (append a b) c) (append a (append b c)))
 :hints (("Goal" :induct (append a b) :in-theory (enable binary-append))))
(defthm fn-ovrqp-fold-sums
 (implies (syntaxp (and (quotep a) (quotep b)))
  (equal (+ a b x) (+ (+ a b) x)))
 :hints (("Goal" :use ((:instance associativity-of-+ (x a) (y b) (z x)))
  :in-theory (theory 'minimal-theory))))

(defthm fn-ovrqp-room-bounds
 (implies (fn-ovrqp-roomp h j limit s)
  (and (<= j limit) (<= limit (fn-rtc-buf-cap h (fn-rtc-config s))) (fn-rtc-splice-okp h j nil s)))
 :hints (("Goal" :in-theory (union-theories '(fn-ovrqp-roomp) (theory 'minimal-theory)))))

; Octet concatenation is used when preserving the room predicate.
(defthm fn-ovrqp-octets-append
 (implies (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b))
  (fn-cbor-octet-listp (append a b)))
 :hints (("Goal" :induct (append a b)
   :in-theory (union-theories '(fn-cbor-octet-listp binary-append car-cons cdr-cons) (theory 'minimal-theory)))))
(defthm fn-ovrqp-octets-cons
 (equal (fn-cbor-octet-listp (cons x xs))
        (and (fn-cbor-octetp x) (fn-cbor-octet-listp xs)))
 :hints (("Goal" :in-theory (enable fn-cbor-octet-listp))))
