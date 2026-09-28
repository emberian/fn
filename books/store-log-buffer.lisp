; fn: the record log's walk over an octet BUFFER (lane snapshot-open-3,
; 2026-09-27; ember: "far too much work at startup").  Prefix `fn-lgb-'.
;
; books/store-log-stream.lisp walks a log segment one entry at a time: the
; host reads the entry's octets and ACL2 decides it (fn-lgw-step).  The entry
; arrived as an octet LIST, and the decision opened it as a list: the frame
; decoder split it three times (header, payload, trailer), the trailer was
; SHA-256 over the list, the batch body was unpacked by take/nthcdr with a
; `len' of the remaining body at every record (quadratic in the entry), and
; the unpack ran twice (once to check, once to answer).  At 1M x 2 KiB that
; walk was 449 of the full replay's 931 s (planning/evidence/
; snapshot-open-2-2026-09-27.md section 6).
;
; Here the host preads the entry into the octet buffer `fn-octets-lg' (its
; own live object, congruent to fn-octets) and ACL2 decides it in place:
; the header by index, the trailer as the frame digest of the window [0, n-32)
; read by index (books/frame-digest-buffer.lisp fn-frame-digest-range), the
; chain's predecessor compared at [10, 42), the batch's lengths walked by
; index, and each record sliced into a list ONCE, only when the entry is
; accepted.  An entry shorter than 74 octets (a frame whose payload cannot
; hold the chain) or a payload bound outside the frame grammar's is decided
; by the list step on the buffer's list: never on a log the node wrote, and
; it keeps the proof to the case that matters.
;
; KEYSTONE fn-lgw-step-buf-is-step: the buffer step IS the list step on the
; buffer's octets (fn-lgw-step), with the buffer's representation invariant
; (fn-octets-p) the only hypothesis.  So fn-lgw-run-is-the-open (the run
; emits the recovered kernel's committed records and ends in its fn-lgc-of)
; holds of the host's loop unchanged.  Host: host/native/io.lisp
; fnn-log-stream-segment calls fn-lgw-step-buf and fn-lgb-places over the
; buffer it filled.
;
; The records' places (fn-lgb-places): each accepted record's (START N ROFF
; RLEN) in the segment, from the same index walk, for the full replay's
; extent seals (books/payload-extent.lisp).  KEYSTONE
; fn-lgb-places-is-list-places: they are fn-arx-list-places over the
; buffer's octets for an accepted entry.

(in-package "ACL2")
(include-book "store-log-stream")
(include-book "frame-digest-buffer")
(include-book "payload-extent")
(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (disable floor mod)))

; The walk's buffer: its own live object, congruent to fn-octets (the served
; attempt's buffer and the realizer's are never touched by the open's walk).
(defabsstobj fn-octets-lg
  :foundation fn-octets$c
  :recognizer (fn-octets-lg-p :logic fn-octets$ap :exec fn-octets$cp)
  :creator (create-fn-octets-lg :logic create-fn-octets$a :exec create-fn-octets$c)
  :exports ((fn-octets-lg-len :logic fn-octets$a-len :exec fn-octets$c-len)
            (fn-octets-lg-get :logic fn-octets$a-get :exec fn-octets$c-get)
            (fn-octets-lg-put :logic fn-octets$a-put :exec fn-octets$c-put :protect t)
            (fn-octets-lg-append-octet :logic fn-octets$a-append-octet
                                       :exec fn-octets$c-append-octet :protect t)
            (fn-octets-lg-clear :logic fn-octets$a-clear :exec fn-octets$c-clear)
            (fn-octets-lg-reserve :logic fn-octets$a-reserve :exec fn-octets$c-reserve
                                  :protect t)
            (fn-octets-lg-list :logic fn-octets$a-list :exec fn-octets$c-list)
            (fn-octets-lg-from-list :logic fn-octets$a-from-list
                                    :exec fn-octets$c-from-list :protect t)
            (fn-octets-lg-append-list :logic fn-octets$a-append-list
                                      :exec fn-oct-write-list :protect t)
            (fn-octets-lg-append-back :logic fn-octets$a-append-back
                                      :exec fn-octets$c-append-back :protect t)
            (fn-octets-lg-get-word :logic fn-octets$a-get-word :exec fn-octets$c-get-word)
            (fn-octets-lg-append-word :logic fn-octets$a-append-word
                                      :exec fn-octets$c-append-word :protect t))
  :congruent-to fn-octets)

; -----------------------------------------------------------------------------
; 1. The list step's decision, in closed form, for an entry of at least 74
;    octets under a payload bound the frame grammar admits.

(defconst *fn-lgb-min* 74)   ; header 10 + chain 32 + trailer 32

(defun fn-lgb-flat (e prev max)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((n (len e))
         (kind (nth 5 e))
         (bound (if (equal kind *fn-lg-batch-kind*) *fn-frame-max-payload* max))
         (declared (fn-cbor-u32-from (take 4 (nthcdr 6 e))))
         (body (take (- n *fn-lgb-min*) (nthcdr 42 e))))
    (if (and (<= declared bound)
             (equal n (+ declared 42))
             (equal (nthcdr (- n 32) e) (fn-frame-digest (take (- n 32) e)))
             (equal (take 4 e) *fn-lg-magic*)
             (equal (nth 4 e) *fn-lg-version*)
             (or (equal kind *fn-lg-record-kind*)
                 (and (equal kind *fn-lg-batch-kind*)
                      (fn-lgw-unpack-okp body max)))
             (equal (take 32 (nthcdr 10 e)) prev))
        (mv t (if (equal kind *fn-lg-batch-kind*) (fn-lgw-unpack body) (list body)))
      (mv nil nil))))

;; The list algebra the closed form needs, with take and nthcdr closed.
(local
 (defthm fn-lgb-split-is-take-nthcdr
   (implies (and (natp n) (<= n (len xs)))
            (equal (fn-frame-split n xs) (cons (take n xs) (nthcdr n xs))))
   :hints (("Goal" :induct (fn-frame-split n xs) :in-theory (enable fn-frame-split)))))
(local (defthm fn-lgb-len-take (equal (len (take n x)) (nfix n))))
(local (defthm fn-lgb-take-take
         (implies (and (natp a) (natp b) (<= a b)) (equal (take a (take b x)) (take a x)))))
(local (defthm fn-lgb-nthcdr-take
         (implies (and (natp a) (natp b) (<= a b))
                  (equal (nthcdr a (take b x)) (take (- b a) (nthcdr a x))))))
(local (defthm fn-lgb-at-mostp-is-len
         (implies (natp b) (equal (fn-cbor-at-mostp x b) (<= (len x) b)))))
(local (defthm fn-lgb-take-zero (implies (zp n) (equal (take n x) nil))))
(local (defthm fn-lgb-consp-take (implies (posp n) (consp (take n x)))))
(local (defthm fn-lgb-car-take (implies (posp n) (equal (car (take n x)) (car x)))))
(local (defthm fn-lgb-cdr-take
         (implies (posp n) (equal (cdr (take n x)) (take (1- n) (cdr x))))))
(local (defthm fn-lgb-car-nthcdr (equal (car (nthcdr i x)) (nth i x))
         :hints (("Goal" :in-theory (enable nth nthcdr)))))
(local (defthm fn-lgb-cdr-nthcdr
         (implies (natp i) (equal (cdr (nthcdr i x)) (nthcdr (1+ i) x)))
         :hints (("Goal" :in-theory (enable nthcdr)))))
(local (defthm fn-lgb-item-take
         (implies (and (natp i) (natp n) (< i n)) (equal (fn-frame-item i (take n y)) (nth i y)))
         :hints (("Goal" :in-theory (enable fn-frame-item nth)))))
(local (defthm fn-lgb-nth-nthcdr
         (implies (and (natp i) (natp j)) (equal (nth i (nthcdr j x)) (nth (+ i j) x)))
         :hints (("Goal" :in-theory (enable nth nthcdr)))))
(local (defthm fn-lgb-bs-take-is-take
         (implies (and (natp k) (<= k (len y))) (equal (fn-bs-take k y) (take k y)))
         :hints (("Goal" :in-theory (enable fn-bs-take take)))))
; The header's declared length is the frame's: N = declared + 42.  Written
; for the declared term only (syntaxp), or the rules rewrite their own
; right-hand sides.
(local (defthm fn-lgb-nthcdr-declared
         (implies (and (syntaxp (and (consp u) (eq (car u) 'fn-cbor-u32-from)))
                       (equal (+ -10 (len e)) (+ 32 u)))
                  (equal (nthcdr (+ 10 u) e) (nthcdr (+ -32 (len e)) e)))
         :hints (("Goal" :in-theory (disable nthcdr len) :cases ((equal u (+ -42 (len e))))))))
(local (defthm fn-lgb-take-declared
         (implies (and (syntaxp (and (consp u) (eq (car u) 'fn-cbor-u32-from)))
                       (equal (+ -10 (len e)) (+ 32 u)))
                  (equal (take (+ -32 u) y) (take (+ -74 (len e)) y)))
         :hints (("Goal" :in-theory (disable take len) :cases ((equal u (+ -42 (len e))))))))
(local (defthm fn-lgb-nthcdr-zero (equal (nthcdr 0 x) x) :hints (("Goal" :in-theory (enable nthcdr)))))
(local (defthm fn-lgb-octets-of-take
         (implies (and (fn-cbor-octet-listp l) (<= (nfix n) (len l)))
                  (fn-cbor-octet-listp (take n l)))
         :hints (("Goal" :in-theory (enable take fn-cbor-octet-listp)))))
(local (defthm fn-lgb-octets-of-nthcdr
         (implies (fn-cbor-octet-listp l) (fn-cbor-octet-listp (nthcdr j l)))
         :hints (("Goal" :in-theory (enable nthcdr fn-cbor-octet-listp)))))
(local (defthm fn-lgb-octets-true-listp
         (implies (fn-cbor-octet-listp x) (true-listp x))
         :rule-classes :forward-chaining :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))
(local (defthm fn-lgb-octets-p-is-octet-listp
         (implies (fn-octets-p x) (fn-cbor-octet-listp x))
         :rule-classes :forward-chaining :hints (("Goal" :in-theory (enable fn-octets-p)))))
(local (defthm fn-lgb-nth-beyond
         (implies (and (true-listp l) (natp j) (<= (len l) j)) (equal (nth j l) nil))
         :hints (("Goal" :in-theory (enable nth)))))
(local (defthm fn-lgb-take-len
         (implies (and (true-listp x) (equal k (len x))) (equal (take k x) x))
         :hints (("Goal" :in-theory (enable take)))))
(local (defthm fn-lgb-len-nthcdr
         (implies (natp k) (equal (len (nthcdr k x)) (nfix (- (len x) k))))
         :hints (("Goal" :in-theory (enable nthcdr)))))
(local (defthm fn-lgb-true-listp-nthcdr
         (implies (true-listp x) (true-listp (nthcdr k x)))
         :hints (("Goal" :in-theory (enable nthcdr)))))
(local (defthm fn-lgb-consp-nthcdr-is-len
         (implies (and (true-listp l) (natp k)) (equal (consp (nthcdr k l)) (< k (len l))))
         :hints (("Goal" :in-theory (enable nthcdr)))))
(local (defthm fn-lgb-nthcdr-nthcdr
         (implies (and (natp a) (natp b)) (equal (nthcdr a (nthcdr b l)) (nthcdr (+ a b) l)))
         :hints (("Goal" :in-theory (enable nthcdr)))))
(local (defthm fn-lgb-list-prefixp-is-take
         (implies (and (true-listp xs) (<= (len xs) (len l)))
                  (equal (fn-oct-list-prefixp xs l) (equal (take (len xs) l) xs)))
         :hints (("Goal" :induct (fn-oct-list-prefixp xs l) :in-theory (enable take)))))

(local (in-theory (disable take nthcdr)))

(defthm fn-lgb-decide-is-flat
  (implies (and (fn-cbor-octet-listp e) (<= *fn-lgb-min* (len e))
                (natp max) (<= max *fn-frame-max-payload*))
           (equal (fn-lgw-decide e prev max) (fn-lgb-flat e prev max)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-frame-open fn-frame-decode fn-frame-head-fields
                            fn-frame-protected-prefix fn-lg-open-bound fn-frame-item
                            fn-frame-digestp)
                           (fn-lgw-unpack-okp fn-lgw-unpack fn-lg-unpack-okp fn-lg-unpack
                            fn-cbor-u32-from len fn-bs-take)))))

(in-theory (disable fn-lgb-flat))

; -----------------------------------------------------------------------------
; 2. The same decision read from the buffer by index.

;; One cell, read as the natural it is (the export's logical value is `nth',
;; about which type reasoning knows nothing inside a sum).
(defun fn-lgb-cell (i fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (< i (fn-octets-len fn-octets)))
                  :guard-hints (("Goal" :use ((:instance fn-oct-nth-of-octet-listp-is-octet
                                                         (xs fn-octets) (k i)))))))
  (mbe :logic (nfix (fn-octets-get i fn-octets))
       :exec (fn-octets-get i fn-octets)))

(defthm fn-lgb-cell-natp (natp (fn-lgb-cell i fn-octets)) :rule-classes :type-prescription)

(defthm fn-lgb-cell-is-nth
  (implies (and (fn-octets-p fn-octets) (natp i) (< i (len fn-octets)))
           (equal (fn-lgb-cell i fn-octets) (nth i fn-octets)))
  :hints (("Goal" :use ((:instance fn-oct-nth-of-octet-listp-is-octet (xs fn-octets) (k i))))))

(in-theory (disable fn-lgb-cell))

; A big-endian u32 at I.
(defun fn-lgb-u32-at (i fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (<= (+ i 4) (fn-octets-len fn-octets)))))
  (+ (* 16777216 (fn-lgb-cell i fn-octets))
     (* 65536 (fn-lgb-cell (+ i 1) fn-octets))
     (* 256 (fn-lgb-cell (+ i 2) fn-octets))
     (fn-lgb-cell (+ i 3) fn-octets)))

(defthm fn-lgb-u32-at-is-u32
  (implies (and (fn-octets-p fn-octets) (natp i) (<= (+ i 4) (len fn-octets)))
           (equal (fn-lgb-u32-at i fn-octets)
                  (fn-cbor-u32-from (take 4 (nthcdr i fn-octets)))))
  :hints (("Goal" :in-theory (enable fn-cbor-u32-from))))

(local
 (defthm fn-lgb-u32-natp
   (implies (and (fn-octets-p fn-octets) (natp i) (<= (+ i 4) (len fn-octets)))
            (natp (fn-cbor-u32-from (take 4 (nthcdr i fn-octets)))))
   :rule-classes (:rewrite :type-prescription)
   :hints (("Goal" :use fn-lgb-u32-at-is-u32
            :in-theory (disable fn-lgb-u32-at-is-u32 fn-cbor-u32-from)))))

; The batch body [I, END): exactly its records, each after its u32 length.
(defun fn-lgb-exactp (i end fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp end) (<= end (fn-octets-len fn-octets)))
                  :measure (nfix (- end i))))
  (if (and (natp i) (natp end) (< i end))
      (and (<= (+ i 4) end)
           (let ((n (fn-lgb-u32-at i fn-octets)))
             (and (natp n)
                  (<= (+ i 4 n) end)
                  (fn-lgb-exactp (+ i 4 n) end fn-octets))))
    t))

; How many records the unpack takes from [I, END).
(defun fn-lgb-count (i end fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp end) (<= end (fn-octets-len fn-octets)))
                  :measure (nfix (- end i))))
  (if (and (natp i) (natp end) (< i end) (<= (+ i 4) end))
      (let ((n (fn-lgb-u32-at i fn-octets)))
        (if (and (natp n) (<= (+ i 4 n) end))
            (+ 1 (fn-lgb-count (+ i 4 n) end fn-octets))
          0))
    0))

; Each record the unpack takes fits the log's payload bound MAX.
(defun fn-lgb-records-okp (i end max fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp end) (<= end (fn-octets-len fn-octets)))
                  :measure (nfix (- end i))))
  (if (and (natp i) (natp end) (< i end) (<= (+ i 4) end))
      (let ((n (fn-lgb-u32-at i fn-octets)))
        (if (and (natp n) (<= (+ i 4 n) end))
            (and (<= (+ 32 n) (nfix max))
                 (fn-lgb-records-okp (+ i 4 n) end max fn-octets))
          t))
    t))

; A window [I, J) as a list, consed from its end: one pass, no stack.
(defun fn-lgb-slice-acc (i j acc fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp j) (<= i j) (<= j (fn-octets-len fn-octets))
                              (< j (expt 2 59)) (true-listp acc))
                  :measure (nfix (- j i))))
  (declare (type (unsigned-byte 59) i j))
  (if (mbe :logic (and (natp i) (natp j) (< i j)) :exec (< i j))
      (fn-lgb-slice-acc i (the (unsigned-byte 59) (1- j))
                        (cons (fn-octets-get (the (unsigned-byte 59) (1- j)) fn-octets) acc)
                        fn-octets)
    acc))

(local
 (defthm fn-lgb-take-snoc
   (implies (and (natp k) (< k (len x)))
            (equal (take (+ 1 k) x) (append (take k x) (list (nth k x)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable take nth)))))

(defthm fn-lgb-slice-acc-is-take
  (implies (and (natp i) (natp j) (<= i j) (<= j (len fn-octets)))
           (equal (fn-lgb-slice-acc i j acc fn-octets)
                  (append (take (- j i) (nthcdr i fn-octets)) acc)))
  :hints (("Goal" :induct (fn-lgb-slice-acc i j acc fn-octets))
          ("Subgoal *1/1" :use ((:instance fn-lgb-take-snoc (k (- (- j i) 1))
                                           (x (nthcdr i fn-octets)))))))

(in-theory (disable fn-lgb-slice-acc))

; The records, each sliced once.
; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-lgb-unpack-loop (i end fn-octets acc)
  (declare (xargs :stobjs fn-octets :measure (nfix (- end i)) :guard (and (and (natp i) (natp end) (<= end (fn-octets-len fn-octets)) (< end (expt 2 59))) (true-listp acc)) :verify-guards nil))
  (if (and (natp i) (natp end) (< i end) (<= (+ i 4) end))
      (let ((n (fn-lgb-u32-at i fn-octets)))
        (if (and (natp n) (<= (+ i 4 n) end))
            (fn-lgb-unpack-loop (+ i 4 n)
                                end
                                fn-octets
                                (cons (fn-lgb-slice-acc (+ i 4) (+ i 4 n) nil fn-octets)
                                      acc))
          (revappend acc nil)))
    (revappend acc nil)))

(defun fn-lgb-unpack (i end fn-octets)
  (declare (xargs :verify-guards nil :stobjs fn-octets
                  :guard (and (natp i) (natp end) (<= end (fn-octets-len fn-octets))
                              (< end (expt 2 59)))
                  :measure (nfix (- end i))))
  (mbe :logic
       (if (and (natp i) (natp end) (< i end) (<= (+ i 4) end))
           (let ((n (fn-lgb-u32-at i fn-octets)))
             (if (and (natp n) (<= (+ i 4 n) end))
                 (cons (fn-lgb-slice-acc (+ i 4) (+ i 4 n) nil fn-octets)
                       (fn-lgb-unpack (+ i 4 n) end fn-octets))
               nil))
         nil)
       :exec (fn-lgb-unpack-loop i end fn-octets nil)))

(local
 (defthm fn-lgb-unpack-loop-is-revappend
   (equal (fn-lgb-unpack-loop i end fn-octets acc)
          (revappend acc (fn-lgb-unpack i end fn-octets)))
   :hints (("Goal" :induct (fn-lgb-unpack-loop i end fn-octets acc)
                   :in-theory (union-theories '(fn-lgb-unpack-loop fn-lgb-unpack revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-lgb-unpack-loop)

(verify-guards fn-lgb-unpack
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-lgb-unpack)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-lgb-unpack-loop-is-revappend (acc nil))))))


; Each is its list twin over the window [I, END) of the buffer's octets.
(defthm fn-lgb-exactp-is-unpack-exactp
  (implies (and (fn-octets-p fn-octets) (natp i) (natp end) (<= i end) (<= end (len fn-octets)))
           (equal (fn-lgb-exactp i end fn-octets)
                  (fn-lg-unpack-exactp (take (- end i) (nthcdr i fn-octets)))))
  :hints (("Goal" :induct (fn-lgb-exactp i end fn-octets)
           :in-theory (disable fn-lgb-u32-at fn-cbor-u32-from)
           :expand ((fn-lg-unpack-exactp (take (- end i) (nthcdr i fn-octets)))))))

(defthm fn-lgb-unpack-is-unpack
  (implies (and (fn-octets-p fn-octets) (natp i) (natp end) (<= i end) (<= end (len fn-octets)))
           (equal (fn-lgb-unpack i end fn-octets)
                  (fn-lg-unpack (take (- end i) (nthcdr i fn-octets)))))
  :hints (("Goal" :induct (fn-lgb-unpack i end fn-octets)
           :in-theory (disable fn-lgb-u32-at fn-cbor-u32-from)
           :expand ((fn-lg-unpack (take (- end i) (nthcdr i fn-octets)))))))

(defthm fn-lgb-count-is-len-unpack
  (implies (and (fn-octets-p fn-octets) (natp i) (natp end) (<= i end) (<= end (len fn-octets)))
           (equal (fn-lgb-count i end fn-octets)
                  (len (fn-lg-unpack (take (- end i) (nthcdr i fn-octets))))))
  :hints (("Goal" :induct (fn-lgb-count i end fn-octets)
           :in-theory (disable fn-lgb-u32-at fn-cbor-u32-from)
           :expand ((fn-lg-unpack (take (- end i) (nthcdr i fn-octets)))))))

(defthm fn-lgb-records-okp-is-recordsp
  (implies (and (fn-octets-p fn-octets) (natp i) (natp end) (<= i end) (<= end (len fn-octets))
                (natp max) (<= max *fn-frame-max-payload*))
           (equal (fn-lgb-records-okp i end max fn-octets)
                  (fn-lg-recordsp (fn-lg-unpack (take (- end i) (nthcdr i fn-octets))) max)))
  :hints (("Goal" :induct (fn-lgb-records-okp i end max fn-octets)
           :in-theory (disable fn-lgb-u32-at fn-cbor-u32-from)
           :expand ((fn-lg-unpack (take (- end i) (nthcdr i fn-octets)))))))

(in-theory (disable fn-lgb-exactp fn-lgb-count fn-lgb-records-okp fn-lgb-unpack))

; The decision.  The trailer check comes last: a wrong chain link or kind is
; refused before any digest is computed.
(defun fn-lgb-decide-fast (prev max fn-octets)
  (declare (xargs :stobjs fn-octets :guard t
                  :guard-hints (("Goal" :in-theory (enable fn-octets-len)))))
  (let ((n (fn-octets-len fn-octets)))
    (if (and (<= *fn-lgb-min* n) (< n (expt 2 59))
             (natp max) (<= max *fn-frame-max-payload*))
        (let* ((kind (fn-lgb-cell 5 fn-octets))
               (bound (if (equal kind *fn-lg-batch-kind*) *fn-frame-max-payload* max))
               (declared (fn-lgb-u32-at 6 fn-octets))
               (end (- n 32)))
          (if (and (<= declared bound)
                   (equal n (+ declared 42))
                   (fn-oct-prefix-equalp 0 *fn-lg-magic* fn-octets)
                   (equal (fn-lgb-cell 4 fn-octets) *fn-lg-version*)
                   (or (equal kind *fn-lg-record-kind*)
                       (and (equal kind *fn-lg-batch-kind*)
                            (fn-lgb-exactp 42 end fn-octets)
                            (<= 2 (fn-lgb-count 42 end fn-octets))
                            (fn-lgb-records-okp 42 end max fn-octets)))
                   (true-listp prev)
                   (equal (len prev) 32)
                   (fn-oct-prefix-equalp 10 prev fn-octets)
                   (fn-oct-suffix-equalp end (fn-frame-digest-range nil 0 end fn-octets)
                                         fn-octets))
              (mv t (if (equal kind *fn-lg-batch-kind*)
                        (fn-lgb-unpack 42 end fn-octets)
                      (list (fn-lgb-slice-acc 42 end nil fn-octets))))
            (mv nil nil)))
      (fn-lgw-decide (fn-octets-list fn-octets) prev max))))

; On an octet buffer it is the list step's decision on the buffer's octets.
(defthm fn-lgb-decide-fast-is-decide
  (implies (fn-octets-p fn-octets)
           (equal (fn-lgb-decide-fast prev max fn-octets)
                  (fn-lgw-decide fn-octets prev max)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lgb-flat fn-shr-win)
                           (fn-lgw-decide fn-lg-unpack fn-lg-unpack-exactp fn-lg-recordsp
                            fn-cbor-u32-from)))))

(in-theory (disable fn-lgb-decide-fast))

; The decision the step makes.  Its logical value on a value that is not an
; octet list (never a live buffer: the stobj's recognizer is that) is the
; list step's, so the equality below needs no hypothesis.
(defun fn-lgb-decide (prev max fn-octets)
  (declare (xargs :stobjs fn-octets :guard t))
  (mbe :logic (if (fn-cbor-octet-listp (fn-octets-list fn-octets))
                  (fn-lgb-decide-fast prev max fn-octets)
                (fn-lgw-decide (fn-octets-list fn-octets) prev max))
       :exec (fn-lgb-decide-fast prev max fn-octets)))

(defthm fn-lgb-decide-is-decide
  (equal (fn-lgb-decide prev max fn-octets)
         (fn-lgw-decide fn-octets prev max))
  :hints (("Goal" :in-theory (enable fn-octets-p))))

(in-theory (disable fn-lgb-decide))

; The chain's next trailer: the entry's last 32 octets.
(defun fn-lgb-trailer-fast (fn-octets)
  (declare (xargs :stobjs fn-octets :guard t
                  :guard-hints (("Goal" :in-theory (enable fn-octets-len)))))
  (let ((n (fn-octets-len fn-octets)))
    (if (< n (expt 2 59))
        (fn-lgb-slice-acc (nfix (- n *fn-frame-trailer-octets*)) n nil fn-octets)
      (fn-oct-slice-list (nfix (- n *fn-frame-trailer-octets*)) n fn-octets))))

(defthm fn-lgb-trailer-fast-is-trailer
  (implies (fn-octets-p fn-octets)
           (equal (fn-lgb-trailer-fast fn-octets) (fn-lg-trailer fn-octets)))
  :hints (("Goal" :do-not-induct t :in-theory (enable fn-lg-trailer))))

(defun fn-lgb-trailer (fn-octets)
  (declare (xargs :stobjs fn-octets :guard t
                  :guard-hints (("Goal" :in-theory (enable fn-octets-p)))))
  (mbe :logic (if (fn-cbor-octet-listp (fn-octets-list fn-octets))
                  (fn-lgb-trailer-fast fn-octets)
                (fn-lg-trailer (fn-octets-list fn-octets)))
       :exec (fn-lgb-trailer-fast fn-octets)))

(defthm fn-lgb-trailer-is-trailer
  (equal (fn-lgb-trailer fn-octets) (fn-lg-trailer fn-octets))
  :hints (("Goal" :in-theory (enable fn-octets-p))))

(in-theory (disable fn-lgb-trailer fn-lgb-trailer-fast))

; -----------------------------------------------------------------------------
; 3. The step the host calls.  The buffer holds the octets fn-lgw-entry-len
;    named, read at POS (empty: no entry there).

(defun fn-lgw-step-buf (st unit max extent fn-octets)
  (declare (xargs :stobjs fn-octets :guard (true-listp st)))
  (let ((pos (fn-lgw-pos st)) (prev (fn-lgw-prev st))
        (count (fn-lgw-count st)) (next (fn-lgw-next st)))
    (cond ((fn-lgw-stop st) (mv nil nil st))
          (t (mv-let (ok records) (fn-lgb-decide prev max fn-octets)
               (if (not ok)
                   (mv nil nil (fn-lgw-make pos prev count next t
                                            (fn-lgw-broken-slice-p (fn-octets-list fn-octets)
                                                                   prev max)))
                 (let* ((n (fn-octets-len fn-octets))
                        (step (+ n (fn-lg-pad-len n unit)))
                        (last (fn-lgb-trailer fn-octets)))
                   (mv t records
                       (fn-lgw-make (+ pos step) last (+ count (len records))
                                    (fn-lgw-next-fold records next)
                                    (not (< (+ pos step) (nfix extent))) nil)))))))))

; KEYSTONE: the buffer step is the list step on the buffer's octets, with no
; hypothesis.
(defthm fn-lgw-step-buf-is-step
  (equal (fn-lgw-step-buf st unit max extent fn-octets)
         (fn-lgw-step fn-octets st unit max extent))
  :hints (("Goal" :in-theory (e/d (fn-lgw-step)
                                  (fn-lgw-decide fn-lg-trailer fn-lgw-broken-slice-p
                                   fn-lgw-next-fold fn-lg-pad-len)))))

; -----------------------------------------------------------------------------
; 4. The accepted entry's record places, from the buffer: fn-arx-list-places
;    by index (TAIL is the octets from J, QTAIL from QJ).

(defun fn-lgb-nth (j fn-octets)
  (declare (xargs :stobjs fn-octets :guard (natp j)))
  (if (and (natp j) (< j (fn-octets-len fn-octets))) (fn-lgb-cell j fn-octets) nil))

(defthm fn-lgb-nth-is-nth
  (implies (and (fn-octets-p fn-octets) (natp j))
           (equal (fn-lgb-nth j fn-octets) (nth j fn-octets)))
  :hints (("Goal" :in-theory (enable nth))))

(defun fn-lgb-u32-list-at (j fn-octets)
  (declare (xargs :stobjs fn-octets :guard (natp j)))
  (+ (* 16777216 (nfix (fn-lgb-nth j fn-octets))) (* 65536 (nfix (fn-lgb-nth (+ j 1) fn-octets)))
     (* 256 (nfix (fn-lgb-nth (+ j 2) fn-octets))) (nfix (fn-lgb-nth (+ j 3) fn-octets))))

(defthm fn-lgb-u32-list-at-is-u32-list
  (implies (and (fn-octets-p fn-octets) (natp j))
           (equal (fn-lgb-u32-list-at j fn-octets) (fn-arx-u32-list (nthcdr j fn-octets))))
  :hints (("Goal" :in-theory (enable fn-arx-u32-list))))

(in-theory (disable fn-lgb-nth fn-lgb-u32-list-at))

(defun fn-lgb-places (j p count unit ep en qj q qend acc fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp j) (natp p) (natp count) (natp ep) (natp en) (natp qj)
                              (natp q) (natp qend) (true-listp acc))
                  :measure (nfix count)
                  :hints (("Goal" :in-theory (disable fn-lg-pad-len)))))
  (cond ((zp count) (revappend acc nil))
        ((and (natp q) (natp qend) (< q qend))
         (let* ((rlen (fn-lgb-u32-list-at qj fn-octets))
                (r (+ q 4))
                (q2 (+ r rlen))
                (acc (cons (list (nfix ep) (nfix en) r rlen) acc)))
           (cond ((< qend q2) nil)
                 ((equal q2 qend)
                  (let ((np (+ (nfix ep) (nfix en) (fn-lg-pad-len en unit))))
                    (fn-lgb-places (+ (nfix j) (nfix (- np (nfix p)))) np (1- count) unit
                                   0 0 0 0 0 acc fn-octets)))
                 (t (fn-lgb-places j p (1- count) unit ep en (+ (nfix qj) 4 rlen) q2 qend acc
                                   fn-octets)))))
        (t
         (let* ((p (nfix p))
                (j (nfix j))
                (kind (nfix (fn-lgb-nth (+ j 5) fn-octets)))
                (l (fn-lgb-u32-list-at (+ j 6) fn-octets))
                (n (+ 10 l *fn-frame-trailer-octets*)))
           (cond ((not (< (+ j 9) (fn-octets-len fn-octets))) nil)
                 ((< l 32) nil)
                 ((equal kind 1)
                  (let ((np (+ p n (fn-lg-pad-len n unit))))
                    (fn-lgb-places (+ j (nfix (- np p))) np (1- count) unit 0 0 0 0 0
                                   (cons (list p n (+ p *fn-arx-record-at*) (- l 32)) acc)
                                   fn-octets)))
                 ((and (equal kind 2) (<= 4 (- l 32)))
                  (let* ((q (+ p *fn-arx-record-at*))
                         (qend (+ q (- l 32)))
                         (qj (+ j *fn-arx-record-at*))
                         (rlen (fn-lgb-u32-list-at qj fn-octets))
                         (r (+ q 4))
                         (q2 (+ r rlen))
                         (acc (cons (list p n r rlen) acc)))
                    (cond ((< qend q2) nil)
                          ((equal q2 qend)
                           (let ((np (+ p n (fn-lg-pad-len n unit))))
                             (fn-lgb-places (+ j (nfix (- np p))) np (1- count) unit
                                            0 0 0 0 0 acc fn-octets)))
                          (t (fn-lgb-places j p (1- count) unit p n (+ qj 4 rlen) q2 qend acc
                                            fn-octets)))))
                 (t nil))))))

; Outside a batch body the list walk never reads QTAIL.
(local
 (defthm fn-lgb-list-places-ignores-qtail
   (implies (and (syntaxp (not (equal qtail ''nil))) (not (and (natp q) (natp qend) (< q qend))))
            (equal (fn-arx-list-places tail p count unit ep en qtail q qend acc)
                   (fn-arx-list-places tail p count unit ep en nil q qend acc)))
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-lg-pad-len fn-arx-u32-list nth fn-arx-list-places)
            :expand ((fn-arx-list-places tail p count unit ep en qtail q qend acc)
                     (fn-arx-list-places tail p count unit ep en nil q qend acc))))))

(defthm fn-lgb-places-is-list-places
  (implies (and (fn-octets-p fn-octets) (natp j) (natp qj))
           (equal (fn-lgb-places j p count unit ep en qj q qend acc fn-octets)
                  (fn-arx-list-places (nthcdr j fn-octets) p count unit ep en
                                      (nthcdr qj fn-octets) q qend acc)))
  :hints (("Goal" :induct (fn-lgb-places j p count unit ep en qj q qend acc fn-octets)
           :in-theory (e/d ((:induction fn-lgb-places))
                           (fn-lg-pad-len fn-arx-u32-list (:definition fn-lgb-places)
                            fn-arx-list-places fn-lgb-nth-beyond true-listp fn-lgb-car-nthcdr
                            fn-lgb-take-len fn-lgc-take-all fn-cbor-octet-listp))
           ;; Each side opened once per induction case (:free: the places'
           ;; bounds and accumulator are rewritten before the expansion).
           :expand ((:free (p ep en q qend acc)
                           (fn-lgb-places j p count unit ep en qj q qend acc fn-octets))
                    (:free (p ep en q qend acc)
                           (fn-arx-list-places (nthcdr j fn-octets) p count unit ep en
                                               (nthcdr qj fn-octets) q qend acc))
                    (:free (p ep en q qend acc)
                           (fn-arx-list-places (nthcdr j fn-octets) p count unit ep en
                                               nil q qend acc))))))

; The host's call: the COUNT records of the entry at POS.
(defun fn-lgb-entry-places (pos count unit fn-octets)
  (declare (xargs :stobjs fn-octets :guard (and (natp pos) (natp count))
                  :guard-hints (("Goal" :in-theory (enable fn-octets-p)))))
  (mbe :logic (if (fn-cbor-octet-listp (fn-octets-list fn-octets))
                  (fn-lgb-places 0 pos count unit 0 0 0 0 0 nil fn-octets)
                (fn-arx-list-places (fn-octets-list fn-octets) pos count unit 0 0 nil 0 0 nil))
       :exec (fn-lgb-places 0 pos count unit 0 0 0 0 0 nil fn-octets)))

; KEYSTONE: they are fn-arx-list-places over the buffer's octets, with no
; hypothesis.
(defthm fn-lgb-entry-places-is-list-places
  (equal (fn-lgb-entry-places pos count unit fn-octets)
         (fn-arx-list-places fn-octets pos count unit 0 0 nil 0 0 nil))
  :hints (("Goal" :in-theory (enable fn-octets-p))))
