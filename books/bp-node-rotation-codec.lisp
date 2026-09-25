; FNBS kind 19: the BP node's held-row checkpoint (spec bp-node-machine 3.6,
; slice E, trace N16).
;
; A checkpoint is the exact accumulator of the ordered received-FNBS replay
; (books/bp-fnbs-family-replay.lisp) at a generation boundary: the held rows,
; the receipt handoffs, the operation frontier (the last replayed
; (epoch . operation-id) pair), the arrival frontier, and the count of
; received finals the generation retires (its journal credit).  It is not
; history compaction: it holds the state replay would reach, not a summary.
;
; The bytes are one file: the four magic octets "FNBR", version 1, kind 19,
; the u64 payload length, the payload, and the 32-octet frame trailer over
; everything before it (fn-frame-trailer, the digest every FNBS record
; carries).  The payload is a bounded tree codec over the value: every
; recursion of the decoder consumes one level of a depth budget that the
; store profile sets (fn-bpnr-depth-budget), so decoding is bounded work;
; no constant caps the data.  Parsing never calls the Lisp reader.
(in-package "ACL2")
(include-book "bp-fnbs-codec")
(include-book "bp-primary-cbor")
(set-verify-guards-eagerness 0)

(defconst *fn-bpnr-checkpoint-code* 19)
(defconst *fn-bpnr-head* '(70 78 66 82 1 19))

; The decoder's recursion budget.  It bounds work per decode, not data:
; it grows with the profile's held-row slots, the longest list a checkpoint
; carries, and fails closed (the rotation is refused) when a value needs more.
(defun fn-bpnr-depth-budget (max-jobs)
  (declare (xargs :guard t))
  (+ 4096 (* 4 (nfix max-jobs))))

(defun fn-bpnr-codes (chars)
  (declare (xargs :guard t))
  (if (atom chars) nil
    (cons (if (characterp (car chars)) (char-code (car chars)) 0)
          (fn-bpnr-codes (cdr chars)))))

(defun fn-bpnr-chars (codes)
  (declare (xargs :guard t))
  (if (atom codes) nil
    (cons (if (fn-cbor-octetp (car codes)) (code-char (car codes)) (code-char 0))
          (fn-bpnr-chars (cdr codes)))))

(defun fn-bpnr-counted (tag codes)
  (declare (xargs :guard t))
  (if (and (fn-cbor-octet-listp codes) (<= (len codes) *fn-bpc-max-uint*))
      (cons tag (append (fn-bpc-u64-bytes (len codes)) codes))
    nil))

(defun fn-bpnr-symbol-tag (x)
  (declare (xargs :guard (symbolp x)))
  (cond ((equal (symbol-package-name x) "KEYWORD") 2)
        ((equal (symbol-package-name x) "ACL2") 3)
        ((equal (symbol-package-name x) "COMMON-LISP") 4)
        (t nil)))

; Nil means "not encodable within this budget"; every encoding is a cons.
(defun fn-bpnr-enc (x d)
  (declare (xargs :guard (natp d) :measure (nfix d)))
  (cond ((zp d) nil)
        ((null x) (list 0))
        ((equal x t) (list 1))
        ((symbolp x)
         (let ((tag (fn-bpnr-symbol-tag x)))
           (and tag
                (fn-bpnr-counted tag (fn-bpnr-codes
                                      (coerce (symbol-name x) 'list))))))
        ((natp x) (and (<= x *fn-bpc-max-uint*) (cons 5 (fn-bpc-u64-bytes x))))
        ((integerp x)
         (and (<= (- x) *fn-bpc-max-uint*) (cons 6 (fn-bpc-u64-bytes (- x)))))
        ((stringp x) (fn-bpnr-counted 7 (fn-bpnr-codes (coerce x 'list))))
        ((characterp x) (list 8 (char-code x)))
        ((consp x)
         (if (fn-cbor-octet-listp x)
             (fn-bpnr-counted 9 x)
           (let ((a (fn-bpnr-enc (car x) (1- d)))
                 (b (fn-bpnr-enc (cdr x) (1- d))))
             (and a b (cons 10 (append a b))))))
        (t nil)))

(verify-guards fn-bpnr-codes)
(verify-guards fn-bpnr-chars)
(verify-guards fn-bpnr-counted
  :hints (("Goal" :in-theory (disable fn-bpc-u64-bytes floor mod))))
(verify-guards fn-bpnr-symbol-tag)
(verify-guards fn-bpnr-depth-budget)

(defun fn-bpnr-read-u64 (bytes)
  (declare (xargs :guard t))
  (let ((split (fn-frame-split 8 (if (true-listp bytes) bytes nil))))
    (if (and (consp split) (fn-cbor-octet-listp (car split))
             (equal (len (car split)) 8))
        (cons (fn-bpc-u64-from (car split)) (cdr split))
      nil)))

(defun fn-bpnr-read-counted (bytes)
  (declare (xargs :guard t))
  (let ((n (fn-bpnr-read-u64 bytes)))
    (if (not (consp n)) nil
      (let ((split (fn-frame-split (nfix (car n))
                                   (if (true-listp (cdr n)) (cdr n) nil))))
        (if (and (consp split) (fn-cbor-octet-listp (car split))) split nil)))))

(defun fn-bpnr-dec (bytes d)
  (declare (xargs :guard (natp d) :measure (nfix d)))
  (if (or (zp d) (atom bytes)) nil
    (let ((tag (car bytes)) (rest (cdr bytes)))
      (cond ((equal tag 0) (cons nil rest))
            ((equal tag 1) (cons t rest))
            ((or (equal tag 2) (equal tag 3) (equal tag 4) (equal tag 7))
             (let ((c (fn-bpnr-read-counted rest)))
               (if (not (consp c)) nil
                 (let ((s (coerce (fn-bpnr-chars (car c)) 'string)))
                   (cons (cond ((equal tag 2) (intern-in-package-of-symbol s :fn))
                               ((equal tag 3)
                                (intern-in-package-of-symbol s 'fn-bpnr-dec))
                               ((equal tag 4) (intern-in-package-of-symbol s 'car))
                               (t s))
                         (cdr c))))))
            ((equal tag 5) (fn-bpnr-read-u64 rest))
            ((equal tag 6)
             (let ((n (fn-bpnr-read-u64 rest)))
               (and (consp n) (cons (- (nfix (car n))) (cdr n)))))
            ((equal tag 8)
             (if (and (consp rest) (fn-cbor-octetp (car rest)))
                 (cons (code-char (car rest)) (cdr rest))
               nil))
            ((equal tag 9) (fn-bpnr-read-counted rest))
            ((equal tag 10)
             (let ((a (fn-bpnr-dec rest (1- d))))
               (if (not (consp a)) nil
                 (let ((b (fn-bpnr-dec (cdr a) (1- d))))
                   (if (not (consp b)) nil
                     (cons (cons (car a) (car b)) (cdr b)))))))
            (t nil)))))

(defthm fn-bpnr-chars-character-listp
  (character-listp (fn-bpnr-chars codes)))

(verify-guards fn-bpnr-read-u64)
(verify-guards fn-bpnr-read-counted)
(verify-guards fn-bpnr-dec)

; ---------------------------------------------------------------------------
; The round trip of the tree codec.

(local
 (defthm fn-bpnr-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm fn-bpnr-codes-octets
   (fn-cbor-octet-listp (fn-bpnr-codes chars))))

(local
 (defthm fn-bpnr-chars-of-codes
   (implies (character-listp chars)
            (equal (fn-bpnr-chars (fn-bpnr-codes chars)) chars))))

(local
 (defthm fn-bpnr-u64-shape
   (implies (natp n)
            (and (true-listp (fn-bpc-u64-bytes n))
                 (equal (len (fn-bpc-u64-bytes n)) 8)
                 (fn-cbor-octet-listp (fn-bpc-u64-bytes n))))
   :hints (("Goal" :use fn-bpc-u64-bytes-have-eight-octets
            :in-theory (disable fn-bpc-u64-bytes fn-bpc-u64-bytes-have-eight-octets)))))

(local
 (defthm fn-bpnr-read-u64-of-append
   (implies (and (natp n) (<= n *fn-bpc-max-uint*) (true-listp rest))
            (equal (fn-bpnr-read-u64 (append (fn-bpc-u64-bytes n) rest))
                   (cons n rest)))
   :hints (("Goal" :in-theory (disable fn-bpc-u64-bytes fn-bpc-u64-from fn-frame-split
                                       fn-bpc-u64-from-u64-bytes)
            :use ((:instance fn-bpc-u64-from-of-u64-bytes)
                  (:instance fn-frame-split-of-append
                             (a (fn-bpc-u64-bytes n)) (b rest) (n 8)))))))

(local
 (defthm fn-bpnr-octet-list-true-listp
   (implies (fn-cbor-octet-listp x) (true-listp x))))

(local
 (defthm fn-bpnr-read-counted-of-append
   (implies (and (fn-cbor-octet-listp codes) (<= (len codes) *fn-bpc-max-uint*)
                 (true-listp rest))
            (equal (fn-bpnr-read-counted
                    (append (fn-bpc-u64-bytes (len codes)) (append codes rest)))
                   (cons codes rest)))
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-bpc-u64-bytes fn-bpnr-read-u64 fn-frame-split)
            :use ((:instance fn-frame-split-of-append (a codes) (b rest)
                             (n (len codes))))))))

(local
 (defthm fn-bpnr-enc-shape
   (implies (fn-bpnr-enc x d)
            (and (consp (fn-bpnr-enc x d))
                 (true-listp (fn-bpnr-enc x d))
                 (fn-cbor-octet-listp (fn-bpnr-enc x d))))
   :hints (("Goal" :in-theory (disable fn-bpc-u64-bytes)))))

(local
 (defthm fn-bpnr-character-list-of-coerce
   (character-listp (coerce x 'list))))

;; The atoms, then octet lists, then the pairs by an induction that carries
;; the encoded cdr as the car's remaining input.
(local
 (defthm fn-bpnr-dec-of-enc-atom
   (implies (and (not (consp x)) (fn-bpnr-enc x d) (true-listp rest))
            (equal (fn-bpnr-dec (append (fn-bpnr-enc x d) rest) d)
                   (cons x rest)))
   :hints (("Goal" :do-not-induct t
            :expand ((fn-bpnr-enc x d)
                     (:free (bytes) (fn-bpnr-dec bytes d)))
            :in-theory (disable fn-bpc-u64-bytes fn-bpnr-read-u64
                                fn-bpnr-read-counted fn-bpnr-dec)))))

(local
 (defthm fn-bpnr-dec-of-enc-octets
   (implies (and (consp x) (fn-cbor-octet-listp x) (fn-bpnr-enc x d)
                 (true-listp rest))
            (equal (fn-bpnr-dec (append (fn-bpnr-enc x d) rest) d)
                   (cons x rest)))
   :hints (("Goal" :do-not-induct t
            :expand ((fn-bpnr-enc x d)
                     (:free (bytes) (fn-bpnr-dec bytes d)))
            :in-theory (disable fn-bpc-u64-bytes fn-bpnr-read-u64
                                fn-bpnr-read-counted fn-bpnr-dec)))))

(local
 (defun fn-bpnr-rt-induct (x d rest)
   (declare (xargs :measure (nfix d)))
   (if (or (zp d) (atom x)) (list x rest)
     (list (fn-bpnr-rt-induct (car x) (1- d)
                              (append (fn-bpnr-enc (cdr x) (1- d)) rest))
           (fn-bpnr-rt-induct (cdr x) (1- d) rest)))))

(local
 (defthm fn-bpnr-enc-zp
   (implies (zp d) (not (fn-bpnr-enc x d)))))

;; KEYSTONE (codec).  Every value the encoder accepts within a budget
;; decodes, under the same budget, to itself, leaving the following input.
(defthm fn-bpnr-dec-of-enc
  (implies (and (fn-bpnr-enc x d) (true-listp rest))
           (equal (fn-bpnr-dec (append (fn-bpnr-enc x d) rest) d)
                  (cons x rest)))
  :hints (("Goal" :induct (fn-bpnr-rt-induct x d rest)
           :in-theory (disable fn-bpc-u64-bytes fn-bpnr-read-u64
                               fn-bpnr-read-counted fn-bpnr-dec fn-bpnr-enc))
          ("Subgoal *1/2" :cases ((fn-cbor-octet-listp x)))
          ("Subgoal *1/2.2" :expand ((fn-bpnr-enc x d)
                                     (:free (bytes) (fn-bpnr-dec bytes d))))))

;; The octets are octets; the file round-trips.
(defthm fn-bpnr-enc-octets
  (implies (fn-bpnr-enc x d)
           (and (consp (fn-bpnr-enc x d))
                (true-listp (fn-bpnr-enc x d))
                (fn-cbor-octet-listp (fn-bpnr-enc x d))))
  :hints (("Goal" :use fn-bpnr-enc-shape :in-theory nil)))

(verify-guards fn-bpnr-enc
  :hints (("Goal" :in-theory (disable fn-bpc-u64-bytes floor mod))))

; ---------------------------------------------------------------------------
; The checkpoint value (kind 19).
;
; Layout: (:bpnr-checkpoint generation held handoffs prior next-arrival covered)
;   generation    the journal generation whose namespace follows it
;   held          the replay's held rows, exactly
;   handoffs      the replay's receipt handoffs, exactly
;   prior         the last replayed (epoch . operation-id), or nil
;   next-arrival  the replay's arrival frontier
;   covered       the received finals the checkpoint retires (the journal
;                 credit the old generation had consumed); evidence only,
;                 replay never reads it
(defun fn-bpnr-checkpoint (generation held handoffs prior next-arrival covered)
  (declare (xargs :guard t))
  (list :bpnr-checkpoint generation held handoffs prior next-arrival covered))

(defun fn-bpnr-checkpointp (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 7)
       (equal (car x) :bpnr-checkpoint)
       (natp (nth 1 x))
       (true-listp (nth 2 x))
       (true-listp (nth 3 x))
       (or (null (nth 4 x))
           (and (consp (nth 4 x)) (natp (car (nth 4 x)))
                (natp (cdr (nth 4 x)))))
       (natp (nth 5 x))
       (natp (nth 6 x))))
(verify-guards fn-bpnr-checkpointp)

(defun fn-bpnr-checkpoint-generation (x) (declare (xargs :guard t)) (fn-bpn-nth 1 x))
(defun fn-bpnr-checkpoint-held (x) (declare (xargs :guard t)) (fn-bpn-nth 2 x))
(defun fn-bpnr-checkpoint-handoffs (x) (declare (xargs :guard t)) (fn-bpn-nth 3 x))
(defun fn-bpnr-checkpoint-prior (x) (declare (xargs :guard t)) (fn-bpn-nth 4 x))
(defun fn-bpnr-checkpoint-next-arrival (x) (declare (xargs :guard t)) (fn-bpn-nth 5 x))
(defun fn-bpnr-checkpoint-covered (x) (declare (xargs :guard t)) (fn-bpn-nth 6 x))
(verify-guards fn-bpnr-checkpoint-generation)
(verify-guards fn-bpnr-checkpoint-held)
(verify-guards fn-bpnr-checkpoint-handoffs)
(verify-guards fn-bpnr-checkpoint-prior)
(verify-guards fn-bpnr-checkpoint-next-arrival)
(verify-guards fn-bpnr-checkpoint-covered)

(defun fn-bpnr-checkpoint-prefix (payload)
  (declare (xargs :guard t))
  (append *fn-bpnr-head*
          (append (fn-bpc-u64-bytes (len payload)) payload)))

; The file the host publishes: every octet, the trailer included, is ACL2's.
; Nil when the value is not a checkpoint or does not fit the budget.
(defun fn-bpnr-checkpoint-octets (ck budget)
  (declare (xargs :guard t))
  (let ((payload (and (fn-bpnr-checkpointp ck) (natp budget)
                      (fn-bpnr-enc ck budget))))
    (if (and payload (<= (len payload) *fn-bpc-max-uint*))
        (let ((prefix (fn-bpnr-checkpoint-prefix payload)))
          (append prefix (fn-frame-trailer prefix)))
      nil)))

; The inverse the host calls at open on the selected file's octets.  Nil is
; a damaged selection: recovery fences (spec 3.6's damaged row).
(defun fn-bpnr-checkpoint-decode (octets budget)
  (declare (xargs :guard t))
  (if (not (and (fn-cbor-octet-listp octets) (natp budget))) nil
    (let ((head (fn-frame-split 6 octets)))
      (if (not (and (consp head) (equal (car head) *fn-bpnr-head*))) nil
        (let ((n (fn-bpnr-read-u64 (cdr head))))
          (if (not (consp n)) nil
            (let ((body (fn-frame-split (nfix (car n))
                                        (if (true-listp (cdr n)) (cdr n) nil))))
              (if (not (consp body)) nil
                (if (not (equal (cdr body)
                                (fn-frame-trailer
                                 (fn-bpnr-checkpoint-prefix (car body)))))
                    nil
                  (let ((v (fn-bpnr-dec (car body) budget)))
                    (if (and (consp v) (null (cdr v))
                             (fn-bpnr-checkpointp (car v)))
                        (car v)
                      nil)))))))))))

(local
 (defthm fn-bpnr-octet-listp-append
   (implies (fn-cbor-octet-listp a)
            (equal (fn-cbor-octet-listp (append a b)) (fn-cbor-octet-listp b)))))

(local
 (defthm fn-bpnr-trailer-octets
   (implies (fn-cbor-octet-listp octets)
            (fn-cbor-octet-listp (fn-frame-trailer octets)))
   :hints (("Goal" :use fn-frame-trailer-is-a-digest
            :in-theory (e/d (fn-frame-digestp) (fn-frame-trailer-is-a-digest))))))

(verify-guards fn-bpnr-checkpoint-prefix)
(verify-guards fn-bpnr-checkpoint-octets)
(verify-guards fn-bpnr-checkpoint-decode)

;; KEYSTONE (kind 19 round trip).  Every file fn-bpnr-checkpoint-octets
;; writes decodes, under the same budget, to exactly the checkpoint written.
(defthm fn-bpnr-checkpoint-decode-of-octets
  (implies (fn-bpnr-checkpoint-octets ck budget)
           (equal (fn-bpnr-checkpoint-decode
                   (fn-bpnr-checkpoint-octets ck budget) budget)
                  ck))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-bpc-u64-bytes fn-bpnr-read-u64 fn-frame-split
                               fn-bpnr-enc fn-bpnr-dec fn-bpnr-checkpointp
                               fn-frame-trailer)
           :use ((:instance fn-frame-split-of-append
                            (a *fn-bpnr-head*) (n 6)
                            (b (append (fn-bpc-u64-bytes (len (fn-bpnr-enc ck budget)))
                                       (append (fn-bpnr-enc ck budget)
                                               (fn-frame-trailer
                                                (fn-bpnr-checkpoint-prefix
                                                 (fn-bpnr-enc ck budget)))))))
                 (:instance fn-frame-split-of-append
                            (a (fn-bpnr-enc ck budget))
                            (n (len (fn-bpnr-enc ck budget)))
                            (b (fn-frame-trailer
                                (fn-bpnr-checkpoint-prefix
                                 (fn-bpnr-enc ck budget)))))
                 (:instance fn-bpnr-read-u64-of-append
                            (n (len (fn-bpnr-enc ck budget)))
                            (rest (append (fn-bpnr-enc ck budget)
                                          (fn-frame-trailer
                                           (fn-bpnr-checkpoint-prefix
                                            (fn-bpnr-enc ck budget))))))
                 (:instance fn-bpnr-dec-of-enc (x ck) (d budget) (rest nil))))))

; ---------------------------------------------------------------------------
; The generation namespace.  Generation 0 is the original lifecycle
; directory; generation g > 0 is its own directory under the journal root.
; The selection file names the generation whose rows follow its checkpoint;
; no selection file means generation 0 with no checkpoint.

(defun fn-bpnr-selection-name ()
  (declare (xargs :guard t))
  "bp-generation.fnb")

(defun fn-bpnr-generation-directory (generation)
  (declare (xargs :guard t :verify-guards nil))
  (if (or (not (natp generation)) (zp generation))
      "lifecycle"
    (coerce (append (coerce "lifecycle-g" 'list)
                    (fn-bs-txn-digits generation))
            'string)))

; The next generation: greater than the selected one and than every
; generation directory observed (an unselected staging is never reused).
(defun fn-bpnr-generation-of-name (name)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (stringp name) (equal (length name) 31)
           (equal (subseq name 0 11) "lifecycle-g")
           (fn-bs-txn-digit-char-listp (nthcdr 11 (coerce name 'list))))
      (fn-bs-txn-decode-digits (nthcdr 11 (coerce name 'list)))
    nil))

(defun fn-bpnr-next-generation (selected names)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom names)
      (1+ (nfix selected))
    (let ((g (fn-bpnr-generation-of-name (car names))))
      (fn-bpnr-next-generation (if (and (natp g) (< (nfix selected) g)) g
                                 (nfix selected))
                               (cdr names)))))

(verify-guards fn-bpnr-generation-of-name)
(verify-guards fn-bpnr-next-generation)

(defthm fn-bpnr-next-generation-exceeds-selected
  (< (nfix selected) (fn-bpnr-next-generation selected names))
  :rule-classes :linear)

; The work bound on the selected file the host reads at open: a function of
; the profile's held capacity, never a constant on the data.  A checkpoint
; that would exceed it is refused at rotation (fn-bpnp-rotate-step), so a
; file recovery must read always fits it.
(defun fn-bpnr-read-bound (max-jobs max-octets)
  (declare (xargs :guard t))
  (+ 65536 (* 4 (nfix max-octets)) (* 65536 (nfix max-jobs))))

(verify-guards fn-bpnr-read-bound)

; ---------------------------------------------------------------------------
; The publication program of a new generation, as a phase driver the host
; loop follows (host/native/bp-service.lisp fnn-bps-publish-generation).
; It is the Store marker program's driver (books/checkpoint-publish.lisp
; fn-cpp-marker-driver-*) with one step in front: the new generation's
; directory is created and barriered before the selection is staged, so a
; selected generation's namespace always exists.  The Store driver itself
; is not in the BP image's closure; the phases and outcomes are the same.
(defun fn-bpnr-publish-action (phase)
  (declare (xargs :guard t))
  (cond ((equal phase :directory) :make-directory)
        ((equal phase :marker-staged) :stage-and-file-barrier)
        ((equal phase :marker-data-durable) :replace)
        ((equal phase :marker-attempted) :directory-barrier)
        (t :done)))

(defun fn-bpnr-publish-step (phase result)
  (declare (xargs :guard t))
  (cond ((equal phase :directory)
         (if (equal result :ok) :marker-staged :refused))
        ((equal phase :marker-staged)
         (cond ((equal result :ok) :marker-data-durable)
               ((equal result :known-fail) :refused)
               (t phase)))
        ((or (equal phase :marker-data-durable)
             (equal phase :marker-attempted))
         (cond ((equal result :ok)
                (if (equal phase :marker-data-durable) :marker-attempted :idle))
               ((equal result :error) :fenced-marker)
               (t phase)))
        (t phase)))

(defun fn-bpnr-publish-outcome (phase)
  (declare (xargs :guard t))
  (cond ((equal phase :idle) :durable)
        ((equal phase :refused) :refused)
        ((equal phase :fenced-marker) :uncertain)
        (t :pending)))
