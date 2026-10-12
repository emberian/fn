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
; index.  The step answers the entry's record COUNT and copies no record; the
; host then walks a cursor over the buffer from offset 42 (fn-lgb-span: the
; record's START LEN NEXT) and copies one record at a time (fn-lgb-slice)
; while its sink has it (landing 2b(a), 2026-10-10: a step that answered the
; records as lists held a whole batch entry, to 16 MiB + 42 octets, as octet
; lists).  An entry shorter than 74 octets (a frame whose payload cannot hold
; the chain) or a payload bound outside the frame grammar's is decided by the
; list step on the buffer's list: never on a log the node wrote, and it keeps
; the proof to the case that matters.
;
; KEYSTONES (no hypothesis unless named):
; - fn-lgw-step-buf-count-is-step: the host's step is the list step on the
;   buffer's octets (fn-lgw-step) with its records answered by their count;
;   so fn-lgw-run-is-the-open holds of the host's loop.  Its decision and
;   refusal classification: fn-lgb-decide-count-is-decide,
;   fn-lgb-broken-is-broken-slice (both MBEs; the refusal's check reads the
;   claimed predecessor from the buffer, no copy of the entry).
; - fn-lgb-span-records-are-the-records: COUNT records by the cursor from 42
;   are the list decision's records, in order, accepted or not.
; - fn-lgb-span-within-max (J below COUNT): each record the cursor yields is
;   at most MAX octets, so the live record list of one step is one record.
; - fn-lgb-descriptor-is-the-attached-place (natural POS, J below COUNT): the
;   J-th record's extent descriptor (fn-lgb-descriptor) is the J-th place of
;   fn-arx-list-places with the entry's trailer attached
;   (fn-arx-attach-trailers-buffer), NIL where the places walk answers none.
; Host: host/native/io.lisp fnn-log-stream-segment.

(in-package "ACL2")
(include-book "store-log-stream")
(include-book "frame-digest-buffer")
(include-book "payload-extent")
(include-book "payload-extent-read")
(include-book "store-log-entry-bound")
(local (include-book "arithmetic/top" :dir :system))

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
;; Its work is proof time no prover step counts (docs/proof-style.md
;; 9.1); planning/evidence/tau-cost-*.json has this book's figures.
(local (in-theory (disable (tau-system))))

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-lg-entry-okp)
                          (:linear fn-cp-id-length-bound)
                          (:linear fn-record-accepted-input-length)
                          (:rewrite fn-lgc-consp-nthcdr)
                          (:rewrite fn-oct-nth-of-octet-listp-is-octet . 1))))

(local (in-theory (disable floor mod)))

; The walk's buffer: its own live object, congruent to fn-octets (the served
; attempt's buffer and the realizer's are never touched by the open's walk).
(include-book "def-buffer")
(def-buffer fn-octets-lg)

; -----------------------------------------------------------------------------
; 1. The list step's decision, in closed form, for an entry of at least 74
;    octets under a payload bound the frame grammar admits.

(defconst *fn-lgb-min* 74)   ; header 10 + chain 32 + trailer 32

(defun fn-lgb-flat (e prev max)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((n (len e))
         (kind (nth 5 e))
         (bound (if (equal kind *fn-lg-batch-kind*) *fn-lg-batch-payload-max* max))
         (declared (fn-cbor-u32-from (take 4 (nthcdr 6 e))))
         (body (take (- n *fn-lgb-min*) (nthcdr 42 e))))
    (if (and (<= declared bound)
             (equal n (+ declared 42))
             (equal (nthcdr (- n 32) e) (fn-frame-digest (take (- n 32) e)))
             (equal (take 4 e) *fn-lg-magic*)
             (equal (nth 4 e) *fn-lg-version*)
             (or (equal kind *fn-lg-record-kind*)
                 (and (equal kind *fn-lg-batch-kind*)
                      (fn-lgw-unpack-okp body max))
                 ; a rotation entry (lane store-lineage): no record
                 (and (equal kind *fn-lg-rotation-kind*)
                      (equal (len body) *fn-lg-rotation-body-octets*)))
             (equal (take 32 (nthcdr 10 e)) prev))
        (mv t (cond ((equal kind *fn-lg-batch-kind*) (fn-lgw-unpack body))
                    ((equal kind *fn-lg-rotation-kind*) nil)
                    (t (list body))))
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
; Executes by a loop (lane depth-debt, PRF-919): the recursion took one
; control-stack frame per element of data with no fixed cap.  The :logic is
; the recursion, unchanged; the :exec is the loop, equal by the lemma below.
(defun fn-lgb-count-loop (i end fn-octets acc)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp end) (<= end (fn-octets-len fn-octets))
                              (acl2-numberp acc))
                  :measure (nfix (- end i))))
  (if (and (natp i) (natp end) (< i end) (<= (+ i 4) end))
      (let ((n (fn-lgb-u32-at i fn-octets)))
        (if (and (natp n) (<= (+ i 4 n) end))
            (fn-lgb-count-loop (+ i 4 n) end fn-octets (+ 1 acc))
          acc))
    acc))

(defun fn-lgb-count (i end fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp end) (<= end (fn-octets-len fn-octets)))
                  :measure (nfix (- end i))
                  :verify-guards nil))
  (mbe :logic
       (if (and (natp i) (natp end) (< i end) (<= (+ i 4) end))
           (let ((n (fn-lgb-u32-at i fn-octets)))
             (if (and (natp n) (<= (+ i 4 n) end))
                 (+ 1 (fn-lgb-count (+ i 4 n) end fn-octets))
               0))
         0)
       :exec (fn-lgb-count-loop i end fn-octets 0)))

(defthm fn-lgb-count-loop-is-plus
  (implies (acl2-numberp acc)
           (equal (fn-lgb-count-loop i end fn-octets acc)
                  (+ acc (fn-lgb-count i end fn-octets))))
  :hints (("Goal" :induct (fn-lgb-count-loop i end fn-octets acc)
                  :in-theory (disable fn-lgb-u32-at))))

(verify-guards fn-lgb-count
  :hints (("Goal" :in-theory (disable fn-lgb-u32-at))))

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

;; The records, each sliced: the logic the count and the cursor are proved
;; against (no host caller: the host slices one record at a time, section 4).
(local
 (defun fn-lgb-unpack (i end fn-octets)
   (declare (xargs :stobjs fn-octets :verify-guards nil :measure (nfix (- end i))))
   (if (and (natp i) (natp end) (< i end) (<= (+ i 4) end))
       (let ((n (fn-lgb-u32-at i fn-octets)))
         (if (and (natp n) (<= (+ i 4 n) end))
             (cons (fn-lgb-slice-acc (+ i 4) (+ i 4 n) nil fn-octets)
                   (fn-lgb-unpack (+ i 4 n) end fn-octets))
           nil))
     nil)))

; Each is its list twin over the window [I, END) of the buffer's octets.
(defthm fn-lgb-exactp-is-unpack-exactp
  (implies (and (fn-octets-p fn-octets) (natp i) (natp end) (<= i end) (<= end (len fn-octets)))
           (equal (fn-lgb-exactp i end fn-octets)
                  (fn-lg-unpack-exactp (take (- end i) (nthcdr i fn-octets)))))
  :hints (("Goal" :induct (fn-lgb-exactp i end fn-octets)
           :in-theory (disable fn-lgb-u32-at fn-cbor-u32-from)
           :expand ((fn-lg-unpack-exactp (take (- end i) (nthcdr i fn-octets)))))))

(local
 (defthm fn-lgb-unpack-is-unpack
   (implies (and (fn-octets-p fn-octets) (natp i) (natp end) (<= i end) (<= end (len fn-octets)))
            (equal (fn-lgb-unpack i end fn-octets)
                   (fn-lg-unpack (take (- end i) (nthcdr i fn-octets)))))
   :hints (("Goal" :induct (fn-lgb-unpack i end fn-octets)
            :in-theory (disable fn-lgb-u32-at fn-cbor-u32-from)
            :expand ((fn-lg-unpack (take (- end i) (nthcdr i fn-octets))))))))

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

(in-theory (disable fn-lgb-exactp fn-lgb-count fn-lgb-records-okp))
(local (in-theory (disable fn-lgb-unpack)))

; -----------------------------------------------------------------------------
; 3. The decision from the buffer, no record copied.

; The range the buffer decision answers in place: an entry of at least 74
; octets under a payload bound the frame grammar admits.  Outside it the
; list decision runs on the buffer's octets (an entry below 74 octets holds
; at most 73; a MAX outside the range is never the host's, fn-lgu-log-max).
(defun fn-lgb-fast-range-p (max fn-octets)
  (declare (xargs :stobjs fn-octets :guard t))
  (let ((n (fn-octets-len fn-octets)))
    (and (<= *fn-lgb-min* n) (< n (expt 2 59)) (natp max) (<= max *fn-frame-max-payload*))))

; The acceptance, (mv OK KIND END), END the trailer's start.  The trailer
; check comes last: a wrong chain link or kind is refused before any digest
; is computed.
(defun fn-lgb-accept (prev max fn-octets)
  (declare (xargs :stobjs fn-octets :guard (fn-lgb-fast-range-p max fn-octets)
                  :guard-hints (("Goal" :in-theory (enable fn-octets-len)))))
  (let* ((n (fn-octets-len fn-octets))
         (kind (fn-lgb-cell 5 fn-octets))
         (bound (if (equal kind *fn-lg-batch-kind*) *fn-lg-batch-payload-max* max))
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
                      (fn-lgb-records-okp 42 end max fn-octets))
                 ; a rotation entry (lane store-lineage): no record
                 (and (equal kind *fn-lg-rotation-kind*)
                      (equal (- end 42) *fn-lg-rotation-body-octets*)))
             (true-listp prev)
             (equal (len prev) 32)
             (fn-oct-prefix-equalp 10 prev fn-octets)
             (fn-oct-suffix-equalp end (fn-frame-digest-range nil 0 end fn-octets)
                                   fn-octets))
        (mv t kind end)
      (mv nil 0 0))))

(defthm fn-lgb-accept-ok-boolean
  (booleanp (car (fn-lgb-accept prev max fn-octets)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-lgb-accept))))

(defthm fn-lgb-accept-end-bounds
  (implies (car (fn-lgb-accept prev max fn-octets))
           (and (natp (mv-nth 2 (fn-lgb-accept prev max fn-octets)))
                (<= (mv-nth 2 (fn-lgb-accept prev max fn-octets)) (fn-octets-len fn-octets))))
  :hints (("Goal" :in-theory (enable fn-lgb-accept))))

(defthm fn-lgb-accept-end-within-len
  (implies (car (fn-lgb-accept prev max fn-octets))
           (<= (mv-nth 2 (fn-lgb-accept prev max fn-octets)) (len fn-octets)))
  :hints (("Goal" :in-theory (enable fn-lgb-accept))))


; The list decision's records, from the acceptance (the logic the count is
; proved against; nothing executes it).
(local
 (defun fn-lgb-decide-fast (prev max fn-octets)
   (declare (xargs :stobjs fn-octets :verify-guards nil))
   (if (fn-lgb-fast-range-p max fn-octets)
       (mv-let (ok kind end) (fn-lgb-accept prev max fn-octets)
         (if ok
             (mv t (cond ((equal kind *fn-lg-batch-kind*) (fn-lgb-unpack 42 end fn-octets))
                         ((equal kind *fn-lg-rotation-kind*) nil)
                         (t (list (fn-lgb-slice-acc 42 end nil fn-octets)))))
           (mv nil nil)))
     (fn-lgw-decide (fn-octets-list fn-octets) prev max))))

(local
 (defthm fn-lgb-decide-fast-is-decide
   (implies (fn-octets-p fn-octets)
            (equal (fn-lgb-decide-fast prev max fn-octets)
                   (fn-lgw-decide fn-octets prev max)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-lgb-flat fn-shr-win fn-lgb-accept fn-lgb-fast-range-p)
                            (fn-lgw-decide fn-lg-unpack fn-lg-unpack-exactp fn-lg-recordsp
                             fn-cbor-u32-from))))))

; How many records the accepted entry carries.
(defun fn-lgb-entry-count (kind end fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp end) (<= end (fn-octets-len fn-octets)))))
  (cond ((equal kind *fn-lg-batch-kind*) (fn-lgb-count 42 end fn-octets))
        ((equal kind *fn-lg-rotation-kind*) 0)
        (t 1)))

(local
 (defthm fn-lgb-len-unpack-is-count
   (equal (len (fn-lgb-unpack i end fn-octets)) (fn-lgb-count i end fn-octets))
   :hints (("Goal" :induct (fn-lgb-unpack i end fn-octets)
            :in-theory (e/d (fn-lgb-unpack fn-lgb-count) (fn-lgb-u32-at fn-lgb-slice-acc))))))

(local
 (defthm fn-lgb-decide-fast-count
   (implies (fn-lgb-fast-range-p max fn-octets)
            (equal (mv-let (ok records) (fn-lgb-decide-fast prev max fn-octets)
                     (mv ok (len records)))
                   (mv-let (ok kind end) (fn-lgb-accept prev max fn-octets)
                     (mv ok (if ok (fn-lgb-entry-count kind end fn-octets) 0)))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-lgb-decide-fast fn-lgb-entry-count)
                            (fn-lgw-decide fn-lgb-accept fn-lgb-fast-range-p))))))

(local
 (defthm fn-lgb-decide-count-exec-is-logic
   (implies (and (fn-octets-p fn-octets) (fn-lgb-fast-range-p max fn-octets))
            (equal (mv-let (ok kind end) (fn-lgb-accept prev max fn-octets)
                     (mv ok (if ok (fn-lgb-entry-count kind end fn-octets) 0)))
                   (mv-let (ok records) (fn-lgw-decide fn-octets prev max)
                     (mv ok (len records)))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-lgb-decide-fast-is-decide) (:instance fn-lgb-decide-fast-count))
            :in-theory (theory 'minimal-theory)))))


; The decision and the record count, no record copied.
(defun fn-lgb-decide-count (prev max fn-octets)
  (declare (xargs :stobjs fn-octets :guard t :verify-guards nil))
  (mbe :logic (mv-let (ok records) (fn-lgw-decide (fn-octets-list fn-octets) prev max)
                (mv ok (len records)))
       :exec (if (fn-lgb-fast-range-p max fn-octets)
                 (mv-let (ok kind end) (fn-lgb-accept prev max fn-octets)
                   (mv ok (if ok (fn-lgb-entry-count kind end fn-octets) 0)))
               (mv-let (ok records) (fn-lgw-decide (fn-octets-list fn-octets) prev max)
                 (mv ok (len records))))))

(verify-guards fn-lgb-decide-count
  :hints (("Goal" :in-theory (e/d (fn-octets-p)
                                  (fn-lgw-decide fn-lgb-accept fn-lgb-fast-range-p fn-lgb-entry-count
                                   fn-lgw-decide-is-okp-and-records))
           :use ((:instance fn-lgb-decide-count-exec-is-logic)))))

; KEYSTONE: the count decision is the list decision on the buffer's octets,
; its records answered by their count; no hypothesis.
(defthm fn-lgb-decide-count-is-decide
  (equal (fn-lgb-decide-count prev max fn-octets)
         (mv-let (ok records) (fn-lgw-decide fn-octets prev max)
           (mv ok (len records))))
  :hints (("Goal" :in-theory (e/d (fn-lgb-decide-count fn-octets-p) (fn-lgw-decide)))))



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

; The predecessor a refused entry claims, as the broken check reads it: the
; chain field [10, 42), or zeros for a batch whose declared length passes
; MAX (where fn-lgs-claimed-prev's open under MAX answers no payload).  It is
; not fn-lgs-claimed-prev, which answers zeros wherever that open refuses;
; the two differ only where the entry validates under neither, so the broken
; check is the same (fn-lgb-broken's guard proof).
(defun fn-lgb-claimed (max fn-octets)
  (declare (xargs :stobjs fn-octets :guard (fn-lgb-fast-range-p max fn-octets)))
  (if (and (equal (fn-lgb-cell 5 fn-octets) *fn-lg-batch-kind*)
           (< max (fn-lgb-u32-at 6 fn-octets)))
      (fn-bs-zeros 32)
    (fn-lgb-slice-acc 10 42 nil fn-octets)))

; The refused entry's classification (fn-lgw-broken-slice-p) from the
; buffer: no copy of the entry in the range.
(defun fn-lgb-broken (last max fn-octets)
  (declare (xargs :stobjs fn-octets :guard t :verify-guards nil))
  (mbe :logic (fn-lgw-broken-slice-p (fn-octets-list fn-octets) last max)
       :exec (if (fn-lgb-fast-range-p max fn-octets)
                 (let ((claimed (fn-lgb-claimed max fn-octets)))
                   (mv-let (ok k) (fn-lgb-decide-count claimed max fn-octets)
                     (declare (ignore k))
                     (and ok (not (equal claimed last)) t)))
               (fn-lgw-broken-slice-p (fn-octets-list fn-octets) last max))))

(local
 (defthm fn-lgb-claimed-prev-flat
   (implies (and (fn-cbor-octet-listp e) (<= *fn-lgb-min* (len e))
                 (natp max) (<= max *fn-frame-max-payload*))
            (equal (fn-lgs-claimed-prev e max)
                   (let* ((n (len e))
                          (declared (fn-cbor-u32-from (take 4 (nthcdr 6 e)))))
                     (if (and (<= declared max)
                              (equal n (+ declared 42))
                              (equal (nthcdr (- n 32) e) (fn-frame-digest (take (- n 32) e))))
                         (take 32 (nthcdr 10 e))
                       (fn-bs-zeros 32)))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-lgs-claimed-prev fn-frame-open fn-frame-decode fn-frame-head-fields
                             fn-frame-protected-prefix fn-frame-item fn-frame-digestp)
                            (fn-lgw-unpack-okp fn-lgw-unpack fn-lg-unpack-okp fn-lg-unpack
                             fn-cbor-u32-from len fn-bs-take))))))

(local
 (defthm fn-lgb-entry-okp-is-flat
   (implies (and (fn-cbor-octet-listp e) (<= *fn-lgb-min* (len e))
                 (natp max) (<= max *fn-frame-max-payload*))
            (equal (fn-lg-entry-okp e p max)
                   (if (car (fn-lgb-flat e p max)) t nil)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-lgw-decide-is-okp-and-records (prev p))
                  (:instance fn-lgb-decide-is-flat (prev p)))
            :in-theory (disable fn-lgw-decide-is-okp-and-records fn-lgb-decide-is-flat
                                fn-lgw-decide fn-lg-entry-okp)))))

(local
 (defthm fn-lgb-broken-exec-is-logic
   (implies (and (fn-octets-p fn-octets) (fn-lgb-fast-range-p max fn-octets))
            (equal (let ((claimed (fn-lgb-claimed max fn-octets)))
                     (and (car (fn-lgw-decide fn-octets claimed max))
                          (not (equal claimed last)) t))
                   (fn-lgw-broken-slice-p fn-octets last max)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-lgb-claimed fn-lgb-fast-range-p fn-octets-p fn-octets-len
                             fn-lgb-flat)
                            (fn-lgw-decide fn-lg-entry-okp fn-lgs-claimed-prev
                             fn-lgw-unpack-okp fn-lgw-unpack fn-cbor-u32-from fn-frame-digest))))))

(verify-guards fn-lgb-broken
  :hints (("Goal" :in-theory (e/d (fn-octets-p fn-lgb-decide-count)
                                  (fn-lgw-decide fn-lgb-claimed fn-lgb-fast-range-p
                                   fn-lgw-broken-slice-p fn-lgw-decide-is-okp-and-records))
           :use ((:instance fn-lgb-broken-exec-is-logic)))))

; KEYSTONE (S6): the refused entry's classification from the buffer is the
; list step's; no hypothesis.
(defthm fn-lgb-broken-is-broken-slice
  (equal (fn-lgb-broken last max fn-octets)
         (fn-lgw-broken-slice-p fn-octets last max))
  :hints (("Goal" :in-theory (e/d (fn-lgb-broken fn-octets-p) (fn-lgw-broken-slice-p)))))


; -----------------------------------------------------------------------------
; 4. The cursor: one record at a time.
;
; The record at I of the entry in the buffer, as (mv START LEN NEXT): a batch
; entry's record is the u32-prefixed window at I, any other entry's [I, END),
; END the trailer's start.  Nothing is copied.
(defun fn-lgb-span (i fn-octets)
  (declare (xargs :stobjs fn-octets :guard (natp i)))
  (let* ((n (fn-octets-len fn-octets))
         (end (nfix (- n 32)))
         (i (nfix i)))
    (cond ((not (and (< 5 n) (<= i end))) (mv end 0 end))
          ((equal (fn-lgb-cell 5 fn-octets) *fn-lg-batch-kind*)
           (if (<= (+ i 4) end)
               (let ((rl (fn-lgb-u32-at i fn-octets)))
                 (if (<= (+ i 4 rl) end)
                     (mv (+ i 4) rl (+ i 4 rl))
                   (mv end 0 end)))
             (mv end 0 end)))
          (t (mv i (- end i) end)))))

; A span is a window of the entry: START + LEN <= NEXT <= the trailer's start.
(local
 (defthm fn-lgb-span-bounds
   (mv-let (start len next) (fn-lgb-span i fn-octets)
     (and (natp start) (natp len) (natp next)
          (<= (+ start len) next)
          (<= next (nfix (- (fn-octets-len fn-octets) 32)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-lgb-span)))))

(local
 (defthm fn-lgb-span-start-natp
   (natp (car (fn-lgb-span i fn-octets)))
   :rule-classes :type-prescription
   :hints (("Goal" :use fn-lgb-span-bounds))))

(local
 (defthm fn-lgb-span-len-natp
   (natp (mv-nth 1 (fn-lgb-span i fn-octets)))
   :rule-classes :type-prescription
   :hints (("Goal" :use fn-lgb-span-bounds))))

(local
 (defthm fn-lgb-span-next-natp
   (natp (mv-nth 2 (fn-lgb-span i fn-octets)))
   :rule-classes :type-prescription
   :hints (("Goal" :use fn-lgb-span-bounds))))

(local
 (defthm fn-lgb-span-window
   (and (<= (+ (car (fn-lgb-span i fn-octets)) (mv-nth 1 (fn-lgb-span i fn-octets)))
            (fn-octets-len fn-octets))
        (<= (mv-nth 2 (fn-lgb-span i fn-octets)) (fn-octets-len fn-octets)))
   :rule-classes :linear
   :hints (("Goal" :use fn-lgb-span-bounds))))


; The record a span names, copied as an octet list: the one copy the
; consumer holds.
(defun fn-lgb-slice (start len fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp start) (natp len)
                              (<= (+ start len) (fn-octets-len fn-octets))
                              (< (+ start len) (expt 2 59)))))
  (fn-lgb-slice-acc start (+ start len) nil fn-octets))

; K records by the cursor from I: the logic of the host's loop.
(defun fn-lgb-span-records (k i fn-octets)
  (declare (xargs :stobjs fn-octets :guard (natp i) :verify-guards nil
                  :measure (nfix k)))
  (if (zp k)
      nil
    (mv-let (start len next) (fn-lgb-span i fn-octets)
      (cons (fn-lgb-slice-acc start (+ start len) nil fn-octets)
            (fn-lgb-span-records (1- k) next fn-octets)))))

; The cursor after K records from I.
(defun fn-lgb-span-cursor (k i fn-octets)
  (declare (xargs :stobjs fn-octets :guard (natp i) :verify-guards nil
                  :measure (nfix k)))
  (if (zp k)
      (nfix i)
    (mv-let (start len next) (fn-lgb-span i fn-octets)
      (declare (ignore start len))
      (fn-lgb-span-cursor (1- k) next fn-octets))))

; The stream's txid fold over the K records from I, one record live at a
; time.
(defun fn-lgb-next-fold-spans (k i next fn-octets)
  (declare (xargs :stobjs fn-octets :verify-guards nil
                  :guard (and (natp k) (natp i) (< (fn-octets-len fn-octets) (expt 2 59)))
                  :measure (nfix k)))
  (if (zp k)
      (nfix next)
    (mv-let (start len i2) (fn-lgb-span i fn-octets)
      (fn-lgb-next-fold-spans (1- k) i2
                              (fn-lgw-next-after-one
                               (fn-lgb-slice-acc start (+ start len) nil fn-octets) next)
                              fn-octets))))


(verify-guards fn-lgb-next-fold-spans
  :hints (("Goal" :in-theory (e/d (fn-octets-len) (fn-lgb-span))
           :use ((:instance fn-lgb-span-bounds)))))

; The extent path's descriptor of the record a span names, in the entry at
; POS: the place (POS N START' LEN) with the entry's trailer attached as the
; host's places get it (fn-arx-attach-trailers-buffer); NIL when the
; declared payload is shorter than the chain field, where
; fn-arx-list-places answers no places: never for a record of an accepted
; entry (fn-lgb-descriptor-of-an-accepted-record).
(defun fn-lgb-descriptor (pos start len fn-octets)
  (declare (xargs :stobjs fn-octets :guard (and (natp pos) (natp start) (natp len))))
  (let ((n (fn-octets-len fn-octets)))
    (if (or (< n 10) (< (fn-lgb-u32-at 6 fn-octets) 32))
        nil
      (car (fn-arx-attach-trailers-buffer (list (list pos n (+ pos start) len)) pos fn-octets)))))

; -----------------------------------------------------------------------------
; The cursor's keystones.

(local
 (defthm fn-lgb-span-records-of-batch
   (implies (and (equal (fn-lgb-cell 5 fn-octets) *fn-lg-batch-kind*)
                 (equal end (nfix (- (fn-octets-len fn-octets) 32)))
                 (< 5 (fn-octets-len fn-octets))
                 (natp i) (<= i end))
            (equal (fn-lgb-span-records (fn-lgb-count i end fn-octets) i fn-octets)
                   (fn-lgb-unpack i end fn-octets)))
   :hints (("Goal" :induct (fn-lgb-unpack i end fn-octets)
            :in-theory (e/d (fn-lgb-unpack fn-lgb-count) (fn-lgb-u32-at fn-lgb-slice-acc fn-lgb-cell))))))

(local
 (defthm fn-lgb-split-short
   (implies (and (natp n) (< (len xs) n))
            (equal (fn-frame-split n xs) nil))
   :hints (("Goal" :induct (fn-frame-split n xs) :in-theory (enable fn-frame-split)))))

(local
 (defthm fn-lgb-take-declared-payload
   (implies (and (syntaxp (and (consp u) (eq (car u) 'fn-cbor-u32-from)))
                 (equal (+ -10 (len e)) (+ 32 u)))
            (equal (take u y) (take (+ -42 (len e)) y)))
   :hints (("Goal" :in-theory (disable take len) :cases ((equal u (+ -42 (len e))))))))

(local
 (defthm fn-lgb-frame-open-shape
   (implies (fn-frame-result-okp (fn-frame-open e b))
            (and (fn-cbor-octet-listp e)
                 (<= 42 (len e))
                 (equal (fn-frame-result-payload (fn-frame-open e b))
                        (take (- (len e) 42) (nthcdr 10 e)))
                 (equal (fn-frame-result-kind (fn-frame-open e b)) (nth 5 e))))
   :hints (("Goal" :do-not-induct t :cases ((< (len e) 10) (and (<= 10 (len e)) (< (len e) 42)))
            :in-theory (e/d (fn-frame-open fn-frame-decode fn-frame-head-fields
                             fn-frame-protected-prefix fn-frame-item fn-frame-digestp)
                            (fn-lgw-unpack-okp fn-lgw-unpack fn-lg-unpack-okp fn-lg-unpack fn-cbor-u32-from len fn-bs-take))))))

(local
 (defthm fn-lgw-decide-records-when-refused
   (implies (not (mv-nth 0 (fn-lgw-decide e prev max)))
            (equal (mv-nth 1 (fn-lgw-decide e prev max)) nil))
   :hints (("Goal" :in-theory (e/d (fn-lgw-decide) (fn-frame-open fn-lg-unpack-okp fn-lg-unpack fn-lgw-unpack-okp fn-lgw-unpack fn-bs-take fn-lg-open-bound fn-lgw-decide-is-okp-and-records fn-lgb-frame-open-shape))))))

(local
 (defthm fn-lgb-entry-okp-frame
   (implies (fn-lg-entry-okp e prev max)
            (and (fn-frame-result-okp (fn-frame-open e (fn-lg-open-bound e max)))
                 (member (nth 5 e) (list *fn-lg-record-kind* *fn-lg-batch-kind* *fn-lg-rotation-kind*))))
   :hints (("Goal" :in-theory (e/d (fn-lg-entry-okp) (fn-frame-open fn-lg-unpack-okp fn-lg-open-bound))
            :use ((:instance fn-lgb-frame-open-shape (b (fn-lg-open-bound e max))))))))

(local
 (defthm fn-lgb-nthcdr-past
   (implies (and (true-listp y) (natp a) (<= (len y) a))
            (equal (nthcdr a y) nil))
   :hints (("Goal" :in-theory (enable nthcdr)))))

(local
 (defthm fn-lgb-nthcdr-take-past
   (implies (and (natp a) (natp b) (< b a))
            (equal (nthcdr a (take b x)) nil))
   :hints (("Goal" :use ((:instance fn-lgb-nthcdr-past (y (take b x))))
            :in-theory (disable fn-lgb-nthcdr-past)))))

(local
 (defthm fn-lgb-cell-5-of-octets
   (implies (and (fn-cbor-octet-listp e) (< 5 (len e)))
            (equal (fn-lgb-cell 5 e) (nth 5 e)))
   :hints (("Goal" :use ((:instance fn-lgb-cell-is-nth (fn-octets e) (i 5)))
            :in-theory (enable fn-octets-p)))))

(local
 (defthm fn-lgb-span-records-of-record
   (implies (and (fn-cbor-octet-listp e) (<= 74 (len e)) (not (equal (nth 5 e) 2)))
            (equal (fn-lgb-span-records 1 42 e) (list (take (- (len e) 74) (nthcdr 42 e)))))
   :hints (("Goal" :expand ((fn-lgb-span-records 1 42 e))
            :in-theory (enable fn-lgb-span fn-octets-len fn-octets$a-len)))))

(local
 (defthm fn-lgb-span-records-of-short
   (implies (and (fn-cbor-octet-listp e) (< (len e) 74))
            (equal (fn-lgb-span-records 1 42 e) (list nil)))
   :hints (("Goal" :expand ((fn-lgb-span-records 1 42 e))
            :in-theory (enable fn-lgb-span fn-octets-len fn-octets$a-len)))))

(local
 (defthm fn-lgb-octets-p-of-octet-list-fc
   (implies (fn-cbor-octet-listp e) (fn-octets-p e))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-octets-p)))))

(local
 (defthm fn-lgb-span-records-are-the-records-on-a-list
   (equal (fn-lgb-span-records (len (mv-nth 1 (fn-lgw-decide e prev max))) 42 e)
          (mv-nth 1 (fn-lgw-decide e prev max)))
   :hints (("Goal" :do-not-induct t
            :cases ((not (fn-lg-entry-okp e prev max)) (< (len e) 74))
            :in-theory (e/d (fn-lg-slice-records)
                            (fn-lgw-decide fn-frame-open fn-lg-unpack fn-lg-entry-okp fn-lg-open-bound
                             fn-lgb-unpack-is-unpack fn-lgw-decide-is-okp-and-records fn-lgb-frame-open-shape fn-lgb-entry-okp-frame fn-lgb-span-records-of-batch fn-lgb-count-is-len-unpack))
            :use ((:instance fn-lgw-decide-is-okp-and-records)
                  (:instance fn-lgb-entry-okp-frame)
                  (:instance fn-lgb-frame-open-shape (b (fn-lg-open-bound e max)))
                  (:instance fn-lgb-unpack-is-unpack (fn-octets e) (i 42) (end (- (len e) 32)))
                  (:instance fn-lgb-span-records-of-batch (fn-octets e) (i 42) (end (- (len e) 32))))))))

; KEYSTONE (S2): the cursor yields the records, in order, and nothing else:
; COUNT records from 42 are the list decision's records, for every PREV and
; MAX, accepted or not.
(defthm fn-lgb-span-records-are-the-records
  (equal (fn-lgb-span-records (mv-nth 1 (fn-lgb-decide-count prev max fn-octets)) 42 fn-octets)
         (mv-nth 1 (fn-lgw-decide fn-octets prev max)))
  :hints (("Goal" :in-theory (disable fn-lgw-decide)
           :use ((:instance fn-lgb-span-records-are-the-records-on-a-list (e fn-octets))))))

(local
 (defthm fn-lgb-next-fold-spans-is-next-fold
   (equal (fn-lgb-next-fold-spans k i next fn-octets)
          (fn-lgw-next-fold (fn-lgb-span-records k i fn-octets) next))
   :hints (("Goal" :induct (fn-lgb-next-fold-spans k i next fn-octets)
            :in-theory (disable fn-lgb-span fn-lgw-next-after-one fn-lgw-next-fold-is-next-after)))))

(local
 (defthm fn-lgb-frame-open-len-bound
   (implies (fn-frame-result-okp (fn-frame-open e b))
            (< (len e) (expt 2 59)))
   :rule-classes :linear
   :hints (("Goal" :do-not-induct t :cases ((< (len e) 10) (and (<= 10 (len e)) (< (len e) 42)))
            :in-theory (e/d (fn-frame-open fn-frame-decode fn-frame-head-fields
                             fn-frame-protected-prefix fn-frame-item fn-frame-digestp)
                            (fn-lgw-unpack-okp fn-lgw-unpack fn-lg-unpack-okp fn-lg-unpack len fn-bs-take))))))

(local
 (defthm fn-lgb-frame-open-len-within-bound
   (implies (fn-frame-result-okp (fn-frame-open e b))
            (<= (len e) (+ 42 (nfix b))))
   :rule-classes :linear
   :hints (("Goal" :do-not-induct t :cases ((< (len e) 10) (and (<= 10 (len e)) (< (len e) 42)))
            :in-theory (e/d (fn-frame-open fn-frame-decode fn-frame-head-fields
                             fn-frame-protected-prefix fn-frame-item fn-frame-digestp)
                            (fn-lgw-unpack-okp fn-lgw-unpack fn-lg-unpack-okp fn-lg-unpack len fn-bs-take))))))

(local
 (defthm fn-lgb-recordsp-nth-within
   (implies (and (fn-lg-recordsp rs max) (< (nfix j) (len rs)))
            (<= (+ 32 (len (nth j rs))) (nfix max)))
   :hints (("Goal" :induct (nth j rs) :in-theory (enable nth)))))

(local
 (defthm fn-lgb-nth-singleton
   (equal (nth j (cons x nil)) (if (zp j) x nil))
   :hints (("Goal" :in-theory (enable nth)))))

(local
 (defthm fn-lgb-slice-records-within
   (implies (and (fn-lg-entry-okp e prev max)
                 (< (nfix j) (len (fn-lg-slice-records e max))))
            (<= (+ 32 (len (nth j (fn-lg-slice-records e max)))) (nfix max)))
   :hints (("Goal" :do-not-induct t
            :cases ((equal (nth 5 e) 2))
            :in-theory (e/d (fn-lg-slice-records fn-lg-entry-okp fn-lg-open-bound)
                            (fn-frame-open fn-lg-unpack fn-lg-recordsp fn-lg-unpack-exactp
                             fn-lgb-frame-open-shape fn-lgb-entry-okp-frame nth len
                             fn-lgb-recordsp-nth-within))
            :use ((:instance fn-lgb-recordsp-nth-within
                             (rs (fn-lg-unpack (nthcdr 32 (fn-frame-result-payload
                                                           (fn-frame-open e *fn-lg-batch-payload-max*))))))
                  (:instance fn-lgb-frame-open-shape (b max))
                  (:instance fn-lgb-frame-open-shape (b *fn-lg-batch-payload-max*)))))))

(local
 (defthm fn-lgb-decide-records-within
   (implies (< (nfix j) (len (mv-nth 1 (fn-lgw-decide e prev max))))
            (<= (+ 32 (len (nth j (mv-nth 1 (fn-lgw-decide e prev max))))) (nfix max)))
   :hints (("Goal" :do-not-induct t
            :cases ((fn-lg-entry-okp e prev max))
            :in-theory (disable fn-lgw-decide fn-lg-entry-okp fn-lg-slice-records
                                fn-lgw-decide-records-when-refused nth fn-lgb-slice-records-within)
            :use ((:instance fn-lgw-decide-records-when-refused)
                  (:instance fn-lgb-slice-records-within))))))

(local
 (defthm fn-lgb-nth-span-records
   (implies (and (natp i) (< (nfix j) (nfix k)))
            (equal (nth j (fn-lgb-span-records k i fn-octets))
                   (mv-let (start len next) (fn-lgb-span (fn-lgb-span-cursor j i fn-octets) fn-octets)
                     (declare (ignore next))
                     (fn-lgb-slice-acc start (+ start len) nil fn-octets))))
   :hints (("Goal" :induct (list (fn-lgb-span-cursor j i fn-octets) (fn-lgb-span-records k i fn-octets))
            :in-theory (e/d (nth) (fn-lgb-span))))))

(local
 (defthm fn-lgb-len-slice-of-span
   (mv-let (start len next) (fn-lgb-span i fn-octets)
     (declare (ignore next))
     (equal (len (fn-lgb-slice-acc start (+ start len) nil fn-octets)) len))
   :hints (("Goal" :in-theory (e/d (fn-octets-len) (fn-lgb-span))
            :use (fn-lgb-span-bounds)))))

; KEYSTONE (S4, the hold M's reopen term cites): each record the cursor yields
; of an accepted entry, with the 32-octet chain field its frame carries, is
; within the log's per-record payload bound MAX, so a consumer holding one
; slice holds at most MAX less 32 octets of list (LOG-DECIDE-SHORT-CHAIN-FIELD
; retired: the decision refuses a payload shorter than the chain field).
(defthm fn-lgb-span-within-max
  (implies (< (nfix j) (mv-nth 1 (fn-lgb-decide-count prev max fn-octets)))
           (<= (+ 32 (mv-nth 1 (fn-lgb-span (fn-lgb-span-cursor j 42 fn-octets) fn-octets)))
               (nfix max)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lgb-decide-count-is-decide)
                           (fn-lgw-decide fn-lgb-span fn-lgb-span-cursor fn-lgb-span-records
                            fn-lgb-nth-span-records fn-lgb-len-slice-of-span
                            fn-lgb-decide-records-within fn-lgb-span-records-are-the-records))
           :use ((:instance fn-lgb-span-records-are-the-records)
                 (:instance fn-lgb-nth-span-records (i 42)
                            (k (mv-nth 1 (fn-lgb-decide-count prev max fn-octets))))
                 (:instance fn-lgb-len-slice-of-span (i (fn-lgb-span-cursor j 42 fn-octets)))
                 (:instance fn-lgb-decide-records-within (e fn-octets))))))


; KEYSTONE (C1, the decision's floor): an entry the log accepts is at least
; 74 octets, header 10, chain field 32 and trailer 32
; (LOG-DECIDE-SHORT-CHAIN-FIELD: a 42-octet record frame under the genesis
; predecessor was accepted with one empty record before the chain-field
; conjunct of fn-lg-entry-okp).
(defthm fn-lg-entry-okp-holds-the-chain-field
  (implies (fn-lg-entry-okp e prev max)
           (<= 74 (len e)))
  :rule-classes :linear)

; The extent path's descriptor (S5): the places walk over an accepted entry
; is the cursor's, one place per record.

(local
 (defthm fn-lgb-attach-of-cons
   (equal (fn-arx-attach-trailers-buffer (cons x rest) base fn-octets)
          (cons (car (fn-arx-attach-trailers-buffer (list x) base fn-octets))
                (fn-arx-attach-trailers-buffer rest base fn-octets)))
   :hints (("Goal" :expand ((fn-arx-attach-trailers-buffer (cons x rest) base fn-octets)
                            (fn-arx-attach-trailers-buffer (list x) base fn-octets))))))

(local
 (defthm fn-lgb-attach-of-atom
   (implies (atom l) (equal (fn-arx-attach-trailers-buffer l base fn-octets) nil))
   :hints (("Goal" :expand ((fn-arx-attach-trailers-buffer l base fn-octets))))))

(local
 (defthm fn-lgb-attach-of-cons-rest
   (implies (syntaxp (not (equal rest ''nil)))
            (equal (fn-arx-attach-trailers-buffer (cons x rest) base fn-octets)
                   (cons (car (fn-arx-attach-trailers-buffer (list x) base fn-octets))
                         (fn-arx-attach-trailers-buffer rest base fn-octets))))
   :hints (("Goal" :in-theory (disable fn-lgb-attach-of-cons) :use fn-lgb-attach-of-cons))))

(local (in-theory (disable fn-lgb-attach-of-cons)))

(local
 (defun fn-lgb-nth-ind (j l)
   (if (or (zp j) (atom l)) (list j l) (fn-lgb-nth-ind (1- j) (cdr l)))))

(local
 (defthm fn-lgb-nth-attach
   (equal (nth j (fn-arx-attach-trailers-buffer l base fn-octets))
          (if (< (nfix j) (len l))
              (car (fn-arx-attach-trailers-buffer (list (nth j l)) base fn-octets))
            nil))
   :hints (("Goal" :induct (fn-lgb-nth-ind j l)
            :in-theory (e/d (nth) (fn-arx-attach-trailers-buffer)))
           ("Subgoal *1/2" :use ((:instance fn-lgb-attach-of-cons (x (car l)) (rest (cdr l)))))
           ("Subgoal *1/1" :cases ((consp l))
            :use ((:instance fn-lgb-attach-of-cons (x (car l)) (rest (cdr l))))))))

(local
 (defthm fn-lgb-arx-u32-is-u32-from
   (implies (and (fn-cbor-octet-listp x) (<= 4 (len x)))
            (equal (fn-arx-u32-list x) (fn-cbor-u32-from (take 4 x))))
   :hints (("Goal" :in-theory (enable fn-arx-u32-list fn-cbor-u32-from)
            :expand ((fn-cbor-octet-listp x) (fn-cbor-octet-listp (cdr x))
                     (fn-cbor-octet-listp (cddr x)) (fn-cbor-octet-listp (cdddr x)))))))

(local
 (defthm fn-lgb-u32-list-is-u32-at
   (implies (and (fn-octets-p e) (natp i) (<= (+ i 4) (len e)))
            (equal (fn-arx-u32-list (nthcdr i e)) (fn-lgb-u32-at i e)))
   :hints (("Goal" :in-theory (e/d (fn-octets-p) (fn-arx-u32-list fn-cbor-u32-from fn-lgb-u32-at))
            :use ((:instance fn-lgb-arx-u32-is-u32-from (x (nthcdr i e)))
                  (:instance fn-lgb-u32-at-is-u32 (fn-octets e)))))))

(local
 (defthm fn-lgb-frame-open-declared
   (implies (fn-frame-result-okp (fn-frame-open e b))
            (equal (fn-cbor-u32-from (take 4 (nthcdr 6 e))) (- (len e) 42)))
   :hints (("Goal" :do-not-induct t :cases ((< (len e) 10) (and (<= 10 (len e)) (< (len e) 42)))
            :in-theory (e/d (fn-frame-open fn-frame-decode fn-frame-head-fields
                             fn-frame-protected-prefix fn-frame-item fn-frame-digestp)
                            (fn-lgw-unpack-okp fn-lgw-unpack fn-lg-unpack-okp fn-lg-unpack len fn-bs-take))))))

(local
 (defun fn-lgb-span-places (k i pos n fn-octets)
   (declare (xargs :stobjs fn-octets :verify-guards nil :measure (nfix k)))
   (if (zp k)
       nil
     (mv-let (start len next) (fn-lgb-span i fn-octets)
       (cons (list pos n (+ pos start) len)
             (fn-lgb-span-places (1- k) next pos n fn-octets))))))

(local
 (defun fn-lgb-batch-ind (k i p n acc fn-octets)
   (declare (xargs :stobjs fn-octets :measure (nfix k) :verify-guards nil))
   (if (zp k)
       (list i acc)
     (fn-lgb-batch-ind (1- k) (+ (nfix i) 4 (fn-lgb-u32-at i fn-octets)) p n
                       (cons (list p n (+ p i 4) (fn-lgb-u32-at i fn-octets)) acc) fn-octets))))

(local
 (defthm fn-lgb-count-past-end
   (implies (<= (nfix end) (nfix i))
            (equal (fn-lgb-count i end fn-octets) 0))
   :hints (("Goal" :expand ((fn-lgb-count i end fn-octets))))))

(local
 (defthm fn-lgb-list-places-zero
   (equal (fn-arx-list-places tail p 0 unit ep en qtail q qend acc) (revappend acc nil))
   :hints (("Goal" :expand ((fn-arx-list-places tail p 0 unit ep en qtail q qend acc))))))

(local
 (defthm fn-lgb-list-places-batch-inner
   (implies (and (fn-octets-p fn-octets) (equal (nth 5 fn-octets) 2) (<= 6 (len fn-octets))
                 (natp i) (natp p) (natp n)
                 (< i (- (len fn-octets) 32))
                 (fn-lgb-exactp i (- (len fn-octets) 32) fn-octets)
                 (posp k) (<= k (fn-lgb-count i (- (len fn-octets) 32) fn-octets)))
            (equal (fn-arx-list-places tail p k unit p n (nthcdr i fn-octets) (+ p i)
                                       (+ p (- (len fn-octets) 32)) acc)
                   (revappend acc (fn-lgb-span-places k i p n fn-octets))))
   :hints (("Goal" :induct (fn-lgb-batch-ind k i p n acc fn-octets)
            :in-theory (e/d (fn-lgb-span fn-octets-len)
                            (fn-lgb-u32-at fn-lg-pad-len fn-arx-u32-list nthcdr
                             fn-lgb-u32-at-is-u32 fn-lgb-count-is-len-unpack
                             fn-lgb-exactp-is-unpack-exactp))
            :expand ((:free (tail q qend acc)
                            (fn-arx-list-places tail p k unit p n (nthcdr i fn-octets) q qend acc))
                     (fn-lgb-span-places k i p n fn-octets)
                     (fn-lgb-exactp i (+ -32 (len fn-octets)) fn-octets)
                     (fn-lgb-count i (+ -32 (len fn-octets)) fn-octets)
                     (:free (x y q z) (fn-arx-list-places x y 0 unit 0 0 nil 0 0 z)))))))

(local
 (defthm fn-lgb-list-places-batch
   (implies (and (fn-octets-p fn-octets) (equal (nth 5 fn-octets) 2) (natp pos)
                 (equal (fn-arx-u32-list (nthcdr 6 fn-octets)) (- (len fn-octets) 42))
                 (<= 78 (len fn-octets))
                 (fn-lgb-exactp 42 (- (len fn-octets) 32) fn-octets)
                 (posp count) (<= count (fn-lgb-count 42 (- (len fn-octets) 32) fn-octets)))
            (equal (fn-arx-list-places fn-octets pos count unit 0 0 nil 0 0 nil)
                   (fn-lgb-span-places count 42 pos (len fn-octets) fn-octets)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-octets-len)
                            (fn-lgb-u32-at fn-lg-pad-len fn-arx-u32-list fn-lgb-list-places-batch-inner
                             fn-lgb-u32-at-is-u32 fn-lgb-count-is-len-unpack
                             fn-lgb-exactp-is-unpack-exactp))
            :expand ((fn-arx-list-places fn-octets pos count unit 0 0 nil 0 0 nil)
                     (:free (q qend acc)
                            (fn-arx-list-places fn-octets pos count unit pos (len fn-octets)
                                                (nthcdr 42 fn-octets) q qend acc)))
            :use ((:instance fn-lgb-list-places-batch-inner
                             (tail fn-octets) (p pos) (k count) (i 42) (n (len fn-octets))
                             (acc nil)))))))

(local
 (defthm fn-lgb-frame-open-bound-in-range
   (implies (fn-frame-result-okp (fn-frame-open e b))
            (and (natp b) (<= b *fn-frame-max-payload*)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-frame-open fn-frame-decode)))))

(local
 (defthm fn-lgb-nth-span-places
   (implies (and (natp i) (< (nfix j) (nfix k)))
            (equal (nth j (fn-lgb-span-places k i pos n fn-octets))
                   (mv-let (start len next) (fn-lgb-span (fn-lgb-span-cursor j i fn-octets) fn-octets)
                     (declare (ignore next))
                     (list pos n (+ pos start) len))))
   :hints (("Goal" :induct (list (fn-lgb-span-cursor j i fn-octets) (fn-lgb-span-places k i pos n fn-octets))
            :in-theory (e/d (nth) (fn-lgb-span))))))

(local
 (defthm fn-lgb-len-span-places
   (equal (len (fn-lgb-span-places k i pos n fn-octets)) (nfix k))
   :hints (("Goal" :induct (fn-lgb-span-places k i pos n fn-octets) :in-theory (disable fn-lgb-span)))))

; A one-record entry (kind 1, declared payload at least the chain field):
; its one place is the cursor's.
(local
 (defthm fn-lgb-list-places-record
   (implies (and (fn-octets-p fn-octets) (not (equal (nth 5 fn-octets) 2)) (equal (nth 5 fn-octets) 1)
                 (natp pos)
                 (equal (fn-arx-u32-list (nthcdr 6 fn-octets)) (- (len fn-octets) 42))
                 (<= 74 (len fn-octets)))
            (equal (fn-arx-list-places fn-octets pos 1 unit 0 0 nil 0 0 nil)
                   (fn-lgb-span-places 1 42 pos (len fn-octets) fn-octets)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-octets-len fn-lgb-span fn-lgb-cell-is-nth)
                            (fn-lg-pad-len fn-arx-u32-list))
            :expand ((fn-arx-list-places fn-octets pos 1 unit 0 0 nil 0 0 nil)
                     (fn-lgb-span-places 1 42 pos (len fn-octets) fn-octets)
                     (fn-lgb-span-places 0 (+ -32 (len fn-octets)) pos (len fn-octets) fn-octets))))))

; An entry whose declared payload is shorter than the chain field has no places.
(local
 (defthm fn-lgb-list-places-short
   (implies (and (true-listp tail) (consp (nthcdr 9 tail)) (< (fn-arx-u32-list (nthcdr 6 tail)) 32)
                 (posp count))
            (equal (fn-arx-list-places tail pos count unit 0 0 nil 0 0 nil) nil))
   :hints (("Goal" :expand ((fn-arx-list-places tail pos count unit 0 0 nil 0 0 nil))
            :in-theory (disable fn-arx-u32-list)))))

(local
 (defthm fn-lgb-descriptor-of-span-places
   (implies (and (natp i) (< (nfix j) (nfix k)) (<= 10 (len fn-octets))
                 (<= 32 (fn-lgb-u32-at 6 fn-octets)))
            (equal (nth j (fn-arx-attach-trailers-buffer
                           (fn-lgb-span-places k i pos (len fn-octets) fn-octets) pos fn-octets))
                   (mv-let (start len next) (fn-lgb-span (fn-lgb-span-cursor j i fn-octets) fn-octets)
                     (declare (ignore next))
                     (fn-lgb-descriptor pos start len fn-octets))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-lgb-descriptor fn-octets-len)
                            (fn-lgb-span fn-lgb-span-cursor fn-lgb-span-places fn-lgb-u32-at
                             fn-arx-attach-trailers-buffer))))))

; The accepted entry, in the fast range, by its acceptance.
(local
 (defthm fn-lgb-accept-facts
   (implies (and (fn-octets-p fn-octets) (fn-lgb-fast-range-p max fn-octets)
                 (car (fn-lgb-accept prev max fn-octets)))
            (and (equal (mv-nth 1 (fn-lgb-accept prev max fn-octets)) (nth 5 fn-octets))
                 (equal (mv-nth 2 (fn-lgb-accept prev max fn-octets)) (- (len fn-octets) 32))
                 (equal (fn-lgb-u32-at 6 fn-octets) (- (len fn-octets) 42))
                 (member (nth 5 fn-octets) '(1 2 3))
                 (implies (equal (nth 5 fn-octets) 2)
                          (and (fn-lgb-exactp 42 (- (len fn-octets) 32) fn-octets)
                               (<= 2 (fn-lgb-count 42 (- (len fn-octets) 32) fn-octets))))))
   :hints (("Goal" :in-theory (e/d (fn-lgb-accept fn-lgb-fast-range-p fn-octets-len)
                                   (fn-lgb-u32-at fn-lgb-exactp fn-lgb-count fn-lgb-records-okp
                                    fn-lgb-u32-at-is-u32 fn-lgb-count-is-len-unpack
                                    fn-lgb-exactp-is-unpack-exactp))
            :use ((:instance fn-lgb-cell-is-nth (i 5)))))))

(local
 (defthm fn-lgb-recordsp-max-in-range
   (implies (and (fn-lg-recordsp rs max) (consp rs))
            (and (natp max) (<= max *fn-frame-max-payload*)))
   :rule-classes :forward-chaining
   :hints (("Goal" :expand ((fn-lg-recordsp rs max))))))

(local
 (defthm fn-lgb-accepted-outside-the-range
   (implies (and (car (fn-lgw-decide e prev max))
                 (not (and (<= *fn-lgb-min* (len e)) (< (len e) (expt 2 59))
                           (natp max) (<= max *fn-frame-max-payload*))))
            (and (fn-cbor-octet-listp e)
                 (<= 42 (len e)) (< (len e) *fn-lgb-min*)
                 (equal (fn-cbor-u32-from (take 4 (nthcdr 6 e))) (- (len e) 42))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-lg-entry-okp fn-lg-open-bound fn-lg-unpack-okp)
                            (fn-lgw-decide fn-frame-open fn-lg-unpack fn-lg-unpack-exactp
                             fn-lgw-decide-is-okp-and-records fn-lgb-entry-okp-frame
                             fn-lgb-frame-open-shape fn-lgb-frame-open-declared
                             fn-lgb-frame-open-len-bound fn-cbor-u32-from))
            :use ((:instance fn-lgw-decide-is-okp-and-records)
                  (:instance fn-lgb-frame-open-shape (b (fn-lg-open-bound e max)))
                  (:instance fn-lgb-frame-open-declared (b (fn-lg-open-bound e max)))
                  (:instance fn-lgb-frame-open-len-bound (b (fn-lg-open-bound e max))))))))

(local
 (defthm fn-lgb-count-positive-room
   (implies (< 0 (fn-lgb-count i end fn-octets))
            (<= (+ i 4) end))
   :rule-classes :forward-chaining
   :hints (("Goal" :expand ((fn-lgb-count i end fn-octets))))))

(local
 (defthm fn-lgb-count-in-range
   (implies (and (fn-octets-p fn-octets) (fn-lgb-fast-range-p max fn-octets))
            (equal (mv-nth 1 (fn-lgb-decide-count prev max fn-octets))
                   (if (car (fn-lgb-accept prev max fn-octets))
                       (fn-lgb-entry-count (nth 5 fn-octets) (- (len fn-octets) 32) fn-octets)
                     0)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-octets-p)
                            (fn-lgw-decide fn-lgb-decide-count fn-lgb-accept fn-lgb-fast-range-p
                             fn-lgb-entry-count fn-lgb-accept-facts fn-lgb-decide-count-exec-is-logic
                             fn-lgw-decide-is-okp-and-records))
            :use ((:instance fn-lgb-decide-count-is-decide)
                  (:instance fn-lgb-decide-count-exec-is-logic)
                  (:instance fn-lgb-accept-facts))))))

(local
 (defthm fn-lgb-count-out-of-range
   (implies (and (not (fn-lgb-fast-range-p max fn-octets))
                 (< 0 (mv-nth 1 (fn-lgb-decide-count prev max fn-octets))))
            (and (fn-cbor-octet-listp fn-octets)
                 (<= 42 (len fn-octets)) (< (len fn-octets) *fn-lgb-min*)
                 (equal (fn-cbor-u32-from (take 4 (nthcdr 6 fn-octets))) (- (len fn-octets) 42))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-lgb-fast-range-p fn-octets-len)
                            (fn-lgw-decide fn-lgb-decide-count fn-lgb-accepted-outside-the-range
                             fn-lgw-decide-records-when-refused fn-cbor-u32-from))
            :use ((:instance fn-lgb-decide-count-is-decide)
                  (:instance fn-lgw-decide-records-when-refused (e fn-octets))
                  (:instance fn-lgb-accepted-outside-the-range (e fn-octets)))))))

(local
 (defthm fn-lgb-count-of-non-octets
   (implies (not (fn-octets-p fn-octets))
            (equal (mv-nth 1 (fn-lgb-decide-count prev max fn-octets)) 0))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-octets-p) (fn-lgw-decide fn-lgb-decide-count
                                           fn-lgw-decide-records-when-refused))
            :use ((:instance fn-lgb-decide-count-is-decide)
                  (:instance fn-lgw-decide-records-when-refused (e fn-octets))
                  (:instance fn-lgw-decide-is-okp-and-records (e fn-octets))
                  (:instance fn-lgb-entry-okp-frame (e fn-octets))
                  (:instance fn-lgb-frame-open-shape (e fn-octets) (b (fn-lg-open-bound fn-octets max))))))))

(local
 (defthm fn-lgb-s5-short
   (implies (and (fn-cbor-octet-listp fn-octets) (<= 42 (len fn-octets)) (< (len fn-octets) *fn-lgb-min*)
                 (equal (fn-cbor-u32-from (take 4 (nthcdr 6 fn-octets))) (- (len fn-octets) 42))
                 (posp c))
            (and (equal (fn-arx-list-places fn-octets pos c unit 0 0 nil 0 0 nil) nil)
                 (equal (fn-lgb-descriptor pos start len fn-octets) nil)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-lgb-descriptor fn-octets-len)
                            (fn-arx-list-places fn-lgb-list-places-short fn-cbor-u32-from
                             fn-arx-u32-list fn-lgb-u32-at fn-arx-attach-trailers-buffer))
            :use ((:instance fn-lgb-arx-u32-is-u32-from (x (nthcdr 6 fn-octets)))
                  (:instance fn-lgb-u32-at-is-u32 (i 6))
                  (:instance fn-lgb-octets-p-of-octet-list-fc (e fn-octets))
                  (:instance fn-lgb-list-places-short (tail fn-octets) (count c)))))))

(defthm fn-lgb-decide-count-natp
  (natp (mv-nth 1 (fn-lgb-decide-count prev max fn-octets)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (fn-lgb-decide-count-is-decide) (fn-lgw-decide fn-lgb-decide-count)))))

(local
 (defthm fn-lgb-s5-out-of-range
   (implies (and (not (fn-lgb-fast-range-p max fn-octets))
                 (< (nfix j) (mv-nth 1 (fn-lgb-decide-count prev max fn-octets))))
            (and (equal (fn-arx-list-places fn-octets pos
                                            (mv-nth 1 (fn-lgb-decide-count prev max fn-octets))
                                            unit 0 0 nil 0 0 nil)
                        nil)
                 (equal (fn-lgb-descriptor pos start len fn-octets) nil)))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories (theory 'minimal-theory) '(nfix posp natp fn-lgb-decide-count-natp))
            :use ((:instance fn-lgb-count-out-of-range)
                  (:instance fn-lgb-s5-short (c (mv-nth 1 (fn-lgb-decide-count prev max fn-octets)))))))))

(local
 (defthm fn-lgb-s5-places-in-range
   (implies (and (fn-octets-p fn-octets) (fn-lgb-fast-range-p max fn-octets) (natp pos)
                 (< 0 (mv-nth 1 (fn-lgb-decide-count prev max fn-octets))))
            (and (equal (fn-arx-list-places fn-octets pos
                                            (mv-nth 1 (fn-lgb-decide-count prev max fn-octets))
                                            unit 0 0 nil 0 0 nil)
                        (fn-lgb-span-places (mv-nth 1 (fn-lgb-decide-count prev max fn-octets))
                                            42 pos (len fn-octets) fn-octets))
                 (<= 32 (fn-lgb-u32-at 6 fn-octets))
                 (<= 10 (len fn-octets))))
   :hints (("Goal" :do-not-induct t
            :cases ((equal (nth 5 fn-octets) 1) (equal (nth 5 fn-octets) 2))
            :in-theory (e/d (fn-lgb-entry-count fn-octets-len)
                            (fn-lgb-decide-count fn-lgb-accept fn-lgb-fast-range-p fn-arx-list-places fn-lgb-decide-count-is-decide fn-lgw-decide fn-lgb-decide-is-flat fn-lgw-decide-is-okp-and-records
                             fn-lgb-span-places fn-lgb-u32-at fn-lgb-count fn-lgb-exactp fn-arx-u32-list
                             fn-lgb-accept-facts fn-lgb-list-places-record fn-lgb-list-places-batch
                             fn-lgb-u32-list-is-u32-at fn-lgb-count-in-range
                             fn-lgb-count-is-len-unpack fn-lgb-exactp-is-unpack-exactp))
            :use ((:instance fn-lgb-count-in-range)
                  (:instance fn-lgb-accept-facts)
                  (:instance fn-lgb-fast-range-p)
                  (:instance fn-lgb-u32-list-is-u32-at (e fn-octets) (i 6))
                  (:instance fn-lgb-list-places-record)
                  (:instance fn-lgb-list-places-batch
                             (count (mv-nth 1 (fn-lgb-decide-count prev max fn-octets)))))))))

; KEYSTONE (S5, the extent path's descriptor): the J-th record's descriptor
; the host binds for the sink (the place with the entry's trailer attached,
; fn-arx-attach-trailers-buffer) is the cursor's, so the host forms each
; beside its record and holds no list of them (both sides non-NIL:
; fn-lgb-descriptor-of-an-accepted-record).
(defthm fn-lgb-descriptor-is-the-attached-place
  (implies (and (natp pos)
                (< (nfix j) (mv-nth 1 (fn-lgb-decide-count prev max fn-octets))))
           (equal (nth j (fn-arx-attach-trailers-buffer
                          (fn-arx-list-places fn-octets pos
                                              (mv-nth 1 (fn-lgb-decide-count prev max fn-octets))
                                              unit 0 0 nil 0 0 nil)
                          pos fn-octets))
                  (mv-let (start len next) (fn-lgb-span (fn-lgb-span-cursor j 42 fn-octets)
                                                        fn-octets)
                    (declare (ignore next))
                    (fn-lgb-descriptor pos start len fn-octets))))
  :hints (("Goal" :do-not-induct t
           :cases ((not (fn-octets-p fn-octets))
                   (not (fn-lgb-fast-range-p max fn-octets)))
           :in-theory (e/d (fn-octets-len)
                           (fn-lgw-decide fn-lgb-decide-count fn-lgb-decide-count-is-decide
                            fn-lgb-decide-is-flat fn-lgw-decide-is-okp-and-records
                            fn-lgb-fast-range-p fn-lgb-span fn-lgb-span-cursor fn-lgb-descriptor
                            fn-lgb-span-places fn-arx-list-places fn-arx-attach-trailers-buffer
                            fn-lgb-u32-at fn-lgb-count-of-non-octets fn-lgb-s5-out-of-range
                            fn-lgb-s5-places-in-range fn-lgb-descriptor-of-span-places))
           :use ((:instance fn-lgb-count-of-non-octets)
                 (:instance fn-lgb-s5-out-of-range
                            (start (car (fn-lgb-span (fn-lgb-span-cursor j 42 fn-octets) fn-octets)))
                            (len (mv-nth 1 (fn-lgb-span (fn-lgb-span-cursor j 42 fn-octets) fn-octets))))
                 (:instance fn-lgb-s5-places-in-range)
                 (:instance fn-lgb-descriptor-of-span-places (i 42)
                            (k (mv-nth 1 (fn-lgb-decide-count prev max fn-octets))))))))

; KEYSTONE (C4): every record of an accepted entry has a descriptor, at any
; POS, so S5's NIL arm is unreachable on the host's path
; (LOG-DECIDE-SHORT-CHAIN-FIELD).
(defthm fn-lgb-descriptor-of-an-accepted-record
  (implies (< (nfix j) (mv-nth 1 (fn-lgb-decide-count prev max fn-octets)))
           (mv-let (start len next) (fn-lgb-span (fn-lgb-span-cursor j 42 fn-octets) fn-octets)
             (declare (ignore next))
             (consp (fn-lgb-descriptor pos start len fn-octets))))
  :hints (("Goal" :do-not-induct t
           :cases ((not (fn-octets-p fn-octets)))
           :in-theory (e/d (fn-lgb-descriptor fn-octets-len fn-lgb-decide-count-is-decide)
                           (fn-lgw-decide fn-lgb-decide-count fn-lgb-span fn-lgb-span-cursor
                            fn-lg-entry-okp fn-frame-open fn-lgb-u32-at fn-cbor-u32-from
                            fn-arx-attach-trailers-buffer fn-lg-open-bound))
           :use ((:instance fn-lgb-count-of-non-octets)
                 (:instance fn-lgw-decide-is-okp-and-records (e fn-octets))
                 (:instance fn-lgw-decide-records-when-refused (e fn-octets))
                 (:instance fn-lg-entry-okp-holds-the-chain-field (e fn-octets))
                 (:instance fn-lgb-entry-okp-frame (e fn-octets))
                 (:instance fn-lgb-frame-open-declared (e fn-octets) (b (fn-lg-open-bound fn-octets max)))
                 (:instance fn-lgb-u32-at-is-u32 (i 6))))))

; The host's fused record entry: one slice, optional place, next cursor.
; The fixed statements use local default hints to preserve their exact bytes.
(encapsulate
 ()
(local (set-default-hints
 '((quote (:do-not-induct t
           :in-theory (e/d (fn-octets-len) (fn-lgb-span))
           :use ((:instance fn-lgb-span-bounds)))))))
(defun fn-lgb-next-record (i pos extentp fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp pos) (< (fn-octets-len fn-octets) (expt 2 59)))))
  (mv-let (start len next) (fn-lgb-span i fn-octets)
    (mv (fn-lgb-slice start len fn-octets)
        (if extentp (fn-lgb-descriptor pos start len fn-octets) nil)
        next)))

(verify-guards fn-lgb-next-record)

(local (set-default-hints nil))

(local
 (defthm fn-lgb-span-cursor-successor
   (implies (natp i)
            (equal (fn-lgb-span-cursor (+ 1 (nfix j)) i fn-octets)
                   (mv-nth 2 (fn-lgb-span (fn-lgb-span-cursor j i fn-octets) fn-octets))))
   :hints (("Goal" :induct (fn-lgb-span-cursor j i fn-octets)
            :expand ((fn-lgb-span-cursor 1 i fn-octets))
            :in-theory (e/d (fn-lgb-span-cursor) (fn-lgb-span))))))

(local (set-default-hints
 '((quote (:do-not-induct t
           :in-theory (union-theories (theory 'minimal-theory) '(fn-lgb-next-record fn-lgb-slice mv-nth natp nfix fn-lgb-decide-count-natp))
           :use ((:instance fn-lgb-span-records-are-the-records)
                 (:instance fn-lgb-nth-span-records (i 42)
                            (k (mv-nth 1 (fn-lgb-decide-count prev max fn-octets))))))))))

; KEYSTONE (NR-S2): the fused call yields the decision's J-th record.
(defthm fn-lgb-next-record-yields-the-records
  (implies (< (nfix j) (mv-nth 1 (fn-lgb-decide-count prev max fn-octets)))
           (equal (mv-nth 0 (fn-lgb-next-record (fn-lgb-span-cursor j 42 fn-octets) pos extentp fn-octets))
                  (nth j (mv-nth 1 (fn-lgw-decide fn-octets prev max))))))

(local (set-default-hints
 '((quote (:do-not-induct t
           :in-theory (union-theories (theory 'minimal-theory) '(fn-lgb-next-record fn-lgb-slice mv-nth natp nfix fn-lgb-decide-count-natp))
           :use ((:instance fn-lgb-span-cursor-successor (i 42))))))))

; KEYSTONE (NR-CUR): the fused call advances to the following cursor.
(defthm fn-lgb-next-record-advances-the-cursor
  (equal (mv-nth 2 (fn-lgb-next-record (fn-lgb-span-cursor j 42 fn-octets) pos extentp fn-octets))
         (fn-lgb-span-cursor (+ 1 (nfix j)) 42 fn-octets)))

(local (set-default-hints
 '((quote (:do-not-induct t
           :in-theory (union-theories (theory 'minimal-theory) '(fn-lgb-next-record fn-lgb-slice mv-nth natp nfix fn-lgb-decide-count-natp))
           :use ((:instance fn-lgb-span-within-max)
                 (:instance fn-lgb-len-slice-of-span (i (fn-lgb-span-cursor j 42 fn-octets)))))))))

; KEYSTONE (NR-S4): one live record with its chain field fits MAX.
(defthm fn-lgb-next-record-within-max
  (implies (< (nfix j) (mv-nth 1 (fn-lgb-decide-count prev max fn-octets)))
           (<= (+ 32 (len (mv-nth 0 (fn-lgb-next-record (fn-lgb-span-cursor j 42 fn-octets)
                                                        pos extentp fn-octets))))
               (nfix max))))

(local (set-default-hints
 '((quote (:do-not-induct t
           :in-theory (union-theories (theory 'minimal-theory) '(fn-lgb-next-record fn-lgb-slice mv-nth natp nfix fn-lgb-decide-count-natp))
           :use ((:instance fn-lgb-descriptor-is-the-attached-place)))))))

; KEYSTONE (NR-S5): the fused descriptor is the J-th attached place.
(defthm fn-lgb-next-record-descriptor-is-the-attached-place
  (implies (and (natp pos) extentp
                (< (nfix j) (mv-nth 1 (fn-lgb-decide-count prev max fn-octets))))
           (equal (mv-nth 1 (fn-lgb-next-record (fn-lgb-span-cursor j 42 fn-octets) pos extentp fn-octets))
                  (nth j (fn-arx-attach-trailers-buffer
                          (fn-arx-list-places fn-octets pos
                                              (mv-nth 1 (fn-lgb-decide-count prev max fn-octets))
                                              unit 0 0 nil 0 0 nil)
                          pos fn-octets)))))

(local (set-default-hints
 '((quote (:do-not-induct t
           :in-theory (union-theories (theory 'minimal-theory) '(fn-lgb-next-record fn-lgb-slice mv-nth natp nfix fn-lgb-decide-count-natp))
           :use ((:instance fn-lgb-descriptor-of-an-accepted-record)))))))

; KEYSTONE (NR-C4): every accepted record has a descriptor in extent mode.
(defthm fn-lgb-next-record-has-a-descriptor
  (implies (and extentp (< (nfix j) (mv-nth 1 (fn-lgb-decide-count prev max fn-octets))))
           (consp (mv-nth 1 (fn-lgb-next-record (fn-lgb-span-cursor j 42 fn-octets) pos extentp fn-octets)))))

(local (set-default-hints nil)))

; -----------------------------------------------------------------------------
; 5. The step the host calls: the list step with its records answered by
;    their count.  The buffer holds the octets fn-lgw-entry-len named, read
;    at POS (empty: no entry there).

(defun fn-lgw-step-buf-count (st unit max extent fn-octets)
  (declare (xargs :stobjs fn-octets :guard (true-listp st) :verify-guards nil))
  (let ((pos (fn-lgw-pos st)) (prev (fn-lgw-prev st))
        (count (fn-lgw-count st)) (next (fn-lgw-next st)))
    (cond ((fn-lgw-stop st) (mv nil 0 st))
          (t (mv-let (ok k) (fn-lgb-decide-count prev max fn-octets)
               (if (not ok)
                   (mv nil 0 (fn-lgw-make pos prev count next t
                                          (fn-lgb-broken prev max fn-octets)))
                 (let* ((n (fn-octets-len fn-octets))
                        (step (+ n (fn-lg-pad-len n unit)))
                        (last (fn-lgb-trailer fn-octets)))
                   (mv t k
                       (fn-lgw-make (+ pos step) last (+ count k)
                                    (fn-lgb-next-fold-spans k 42 next fn-octets)
                                    (not (< (+ pos step) (nfix extent))) nil)))))))))

; An entry the decision accepts is below 2^59 octets (its frame's declared
; length is a u32): the slices the fold makes are in the buffer's range.
(local
 (defthm fn-lgb-decide-count-ok-len-bound
   (implies (car (fn-lgb-decide-count prev max fn-octets))
            (< (fn-octets-len fn-octets) (expt 2 59)))
   :hints (("Goal" :in-theory (e/d (fn-lgb-decide-count-is-decide fn-octets-len)
                                   (fn-lgw-decide fn-lgb-decide-count fn-lg-entry-okp
                                    fn-lgb-entry-okp-frame))
            :use ((:instance fn-lgw-decide-is-okp-and-records (e fn-octets))
                  (:instance fn-lgb-entry-okp-frame (e fn-octets)))))))

(verify-guards fn-lgw-step-buf-count
  :hints (("Goal" :in-theory (disable fn-lgb-decide-count fn-lgb-broken fn-lgw-decide))))

; KEYSTONE (S1a): the counting step is the list step on the buffer's octets,
; its records answered by their count; no hypothesis.
(defthm fn-lgw-step-buf-count-is-step
  (equal (fn-lgw-step-buf-count st unit max extent fn-octets)
         (mv-let (took records st2) (fn-lgw-step fn-octets st unit max extent)
           (mv took (len records) st2)))
  :hints (("Goal" :in-theory (e/d (fn-lgw-step)
                                  (fn-lgw-decide fn-lg-trailer fn-lgw-broken-slice-p
                                   fn-lgw-next-fold fn-lg-pad-len fn-lgb-decide-count
                                   fn-lgb-span-records fn-lgb-next-fold-spans
                                   fn-lgw-decide-is-okp-and-records fn-lg-entry-okp
                                   fn-lg-open-bound))
           :use ((:instance fn-lgb-span-records-are-the-records (prev (fn-lgw-prev st)))))))

; KEYSTONE fn-lgw-entry-len-bounded-step-buf-count: the step the host runs
; (fn-lgw-step-buf-count, host/native/io.lisp fnn-log-stream-segment) over an
; entry longer than the open accepts (fn-lgw-entry-len-bounded NIL) is its
; step over no entry, which is what the host gives it (an empty buffer).  The
; list statement is books/store-log-entry-bound.lisp
; fn-lgw-entry-len-bounded-step; this is it over the hosted step.
(defthm fn-lgw-entry-len-bounded-step-buf-count
  (implies (and (not (fn-lgw-entry-len-bounded h st extent max))
                (equal (len e) (fn-lgw-entry-len h st extent))
                (equal (nth 5 e) (nth 5 h)))
           (equal (fn-lgw-step-buf-count st unit max extent e)
                  (fn-lgw-step-buf-count st unit max extent nil)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-lgw-step-buf-count-is-step) (theory 'minimal-theory))
           :use ((:instance fn-lgw-entry-len-bounded-step)))))

