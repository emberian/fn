; fn: the state checkpoint under the records flip: the ARENA run and the
; canonical capture (lane checkpoint-arena, 2026-09-27; D27, D33).
;
; Since the flip a retained article is a held row whose payload position is
; a HANDLE into the arena (books/store-intern.lisp), so the schema-3 tables
; of a capture over rows (books/store-checkpoint-tables.lisp) hold handles
; into an arena the file did not carry.  This book is the missing half:
;
;   THE CANONICAL INTERN.  The full recover interns the decoded journal into
;   the emptied arena under keyring NIL and generation 0
;   (host/store-node-host.lisp fn-store-sn-recover, fn-intern-events): the
;   k-th article-bearing event gets handle k and the arena is the list of
;   their payloads.  `fn-scka-intern-at' is that intern without the arena
;   (the handle is a counter) and `fn-scka-payloads' the arena it builds;
;   KEYSTONE `fn-intern-events-is-intern-at' says the intern IS the pair.
;   A checkpoint holds the tables of the capture of the canonical rows of
;   the live store's WIRE history (alpha, fn-rows-wire-of), whatever handles
;   and contexts the live rows carry, and the canonical arena.
;
;   THE ARENA RUN (A).  One more run of FNSC segments, written FIRST in the
;   file and framed and chained from the genesis with sequence S by the
;   codec's own `fn-scc-frames': chunk 0 is the tag and the payload count,
;   then one chunk per batch of whole payloads, each payload its length
;   (`fn-scc-nat-octets') and its octets.  The load verifies the run with the
;   reader's chain check (`fn-sctr-next-run'), then seals each payload
;   straight from its buffer range into the emptied arena
;   (`fn-arena-seal-range'), a bounded number per step; no list of a payload
;   is built.  The four tables follow unchanged and are read by
;   `fn-sct-load' (its keystone `fn-sct-load-is-decode-file').
;
;   THE OPEN.  `fn-scka-recover-rows' is what both host recovers call: the
;   records interned onto the arena, then the capture extended over them
;   (fn-rii-sco-extend).  KEYSTONE `fn-scka-recover-from-checkpoint-is-full-
;   recover': from the loaded checkpoint of a prefix and its arena, the
;   recover over the suffix is the full recover of prefix ++ suffix from the
;   emptied arena: the same extended capture (so the same opened store) and
;   the same arena.

(in-package "ACL2")
(include-book "store-intern")
(include-book "store-checkpoint-tables-reader")
; replay-identity-index (fn-rii-sco-extend) is red on dev (batch AU flip reds): see section 4.
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; 1. The canonical intern.

; One wire event's row with handle H (keyring NIL, generation 0), :bad as
; fn-intern-event refuses.
(defun fn-scka-intern-one (w h)
  (declare (xargs :guard (natp h)
                  :guard-hints (("Goal" :in-theory (enable fn-prin-keyringp)))))
  (cond ((fn-record-p w) (fn-intern-row-at w nil 0 h))
        ((fn-stxa-p w)
         (let ((a (fn-replay-composite-record w)))
           (if (fn-record-p a)
               (fn-hstxa-make w (fn-intern-row-at a nil 0 h))
             :bad)))
        ((fn-wire-event-p w) w)
        (t :bad)))

; Whether the intern seals a payload for W, and which.
(defun fn-scka-sealsp (w)
  (declare (xargs :guard t))
  (or (fn-record-p w) (fn-stxa-p w)))

(defun fn-scka-payload-of (w)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-record-p w)
      (fn-record-payload w)
    (fn-record-payload (fn-replay-composite-record w))))

(defun fn-scka-intern-at (ws h)
  (declare (xargs :guard (natp h) :verify-guards nil))
  (if (atom ws)
      nil
    (let ((row (fn-scka-intern-one (car ws) h)))
      (if (eq row :bad)
          :bad
        (let ((rest (fn-scka-intern-at (cdr ws) (if (fn-scka-sealsp (car ws)) (+ 1 h) h))))
          (if (eq rest :bad)
              :bad
            (cons row rest)))))))

(defun fn-scka-payloads (ws)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom ws)
      nil
    (if (fn-scka-sealsp (car ws))
        (cons (fn-scka-payload-of (car ws)) (fn-scka-payloads (cdr ws)))
      (fn-scka-payloads (cdr ws)))))

; The row of one event is the canonical row at the arena's count.
(defthm fn-scka-intern-event-row
  (equal (mv-nth 0 (fn-intern-event w nil 0 fn-arena))
         (fn-scka-intern-one w (fn-arena-count fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-intern-event fn-scka-intern-one fn-cat-intern-list
                                   fn-intern-row-at)
                                  (fn-arena-count-is-len fn-held-make fn-held-facts-of
                                   fn-held-context-of fn-arena-seal-list-is-append)))))

(local
 (defthm fn-scka-intern-event-row-len
   (equal (mv-nth 0 (fn-intern-event w nil 0 fn-arena))
          (fn-scka-intern-one w (len fn-arena)))
   :hints (("Goal" :use fn-scka-intern-event-row
            :in-theory (disable fn-scka-intern-event-row fn-intern-event fn-scka-intern-one)))))

(local
 (defthm fn-scka-len-seal-list
   (equal (len (fn-arena-seal-list x a)) (+ 1 (len a)))
   :hints (("Goal" :in-theory (enable fn-arena-seal-list fn-arena$a-seal-list fn-oct-snoc)))))

(local
 (defthm fn-scka-count-of-intern-event
   (implies (not (equal (fn-scka-intern-one w h) :bad))
            (equal (len (mv-nth 1 (fn-intern-event w nil 0 fn-arena)))
                   (if (fn-scka-sealsp w) (+ 1 (len fn-arena)) (len fn-arena))))
   :hints (("Goal" :in-theory (e/d (fn-scka-intern-one fn-scka-sealsp)
                                   (fn-intern-row-at fn-held-make fn-scka-intern-event-row
                                    fn-arena-seal-list-is-append fn-hstxa-make))))))

; The seal is an append on any true list (the arena's logical view).
(defthm fn-scka-seal-list-is-append
  (implies (true-listp a)
           (equal (fn-arena-seal-list x a) (append a (list x))))
  :hints (("Goal" :in-theory (enable fn-arena-seal-list fn-arena$a-seal-list fn-oct-snoc))))

; KEYSTONE (the canonical intern), rows: the journal intern's rows are the
; canonical rows from the arena's count, with no hypothesis (:bad for :bad).
(defthm fn-intern-events-is-intern-at
  (equal (mv-nth 0 (fn-intern-events ws nil 0 fn-arena))
         (fn-scka-intern-at ws (len fn-arena)))
  :hints (("Goal" :induct (fn-intern-events ws nil 0 fn-arena)
           :in-theory (e/d (fn-intern-events fn-scka-intern-at)
                           (fn-intern-event fn-scka-intern-one fn-intern-event-arena
                            fn-scka-sealsp fn-scka-intern-event-row)))))

; KEYSTONE (the canonical intern), arena: an intern that is not refused
; leaves the arena with the canonical payloads behind what it held.
(defthm fn-intern-events-arena-is-payloads
  (implies (and (true-listp fn-arena)
                (not (equal (fn-scka-intern-at ws (len fn-arena)) :bad)))
           (equal (mv-nth 1 (fn-intern-events ws nil 0 fn-arena))
                  (append fn-arena (fn-scka-payloads ws))))
  :hints (("Goal" :induct (fn-intern-events ws nil 0 fn-arena)
           :in-theory (e/d (fn-intern-events fn-scka-intern-at fn-scka-payloads
                            fn-scka-intern-one fn-scka-sealsp fn-scka-payload-of)
                           (fn-intern-event fn-intern-row-at fn-held-make fn-hstxa-make
                            fn-scka-intern-event-row fn-arena-seal-list-is-append)))))

; -----------------------------------------------------------------------------
; The codec's segment round trip (books/store-checkpoint-codec.lisp keeps it
; local; restated here for chunk lists that are not fn-scc-chunks').
(local
 (defthm fn-scc-long-enoughp-is-len
   (implies (natp n)
            (equal (fn-scc-long-enoughp n xs) (<= n (len xs))))))

(local
 (defthm fn-scc-take-of-append-len
   (implies (and (true-listp a) (equal n (len a)))
            (equal (take n (append a b)) a))))

(local
 (defthm fn-scc-nthcdr-of-append-len
   (implies (equal n (len a))
            (equal (nthcdr n (append a b)) b))))

(local
 (defthm fn-scc-len-nthcdr
   (implies (and (natp n) (<= n (len xs)))
            (equal (len (nthcdr n xs)) (- (len xs) n)))))

; -----------------------------------------------------------------------------
; Naturals: little-endian digits

(defun fn-scc-le-digits (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil (cons (mod n 256) (fn-scc-le-digits (floor n 256)))))

(defun fn-scc-le-value (xs)
  (declare (xargs :guard t))
  (if (consp xs) (+ (nfix (car xs)) (* 256 (fn-scc-le-value (cdr xs)))) 0))

(local
 (defthm fn-scc-le-value-of-digits
   (implies (natp n) (equal (fn-scc-le-value (fn-scc-le-digits n)) n))))

(local
 (defthm fn-scc-le-value-of-u64
   (implies (and (natp n) (natp k) (< n (expt 256 k)))
            (equal (fn-scc-le-value (fn-scc-u64 n k)) n))
   :hints (("Goal" :induct (fn-scc-u64 n k)))))

; The segment round trip

(local
 (defthm fn-scc-u64-true-listp
   (true-listp (fn-scc-u64 n k))))

(local
 (defthm fn-scc-header-shape
   (and (true-listp (fn-scc-header i n l q))
        (equal (len (fn-scc-header i n l q)) 37))))

(local
 (defthm fn-scc-long-enoughp-append
   (implies (and (natp k) (<= k (len a)))
            (fn-scc-long-enoughp k (append a b)))))

(local
 (defthm fn-scc-take-of-append-short
   (implies (and (true-listp a) (natp k) (<= k (len a)))
            (equal (take k (append a b)) (take k a)))))

(local
 (defthm fn-scc-take-all
   (implies (and (true-listp x) (equal k (len x)))
            (equal (take k x) x))))

(local
 (defthm fn-scc-u64-read
   (implies (and (natp n) (< n *fn-scc-u64-bound*))
            (equal (fn-scc-u64-at (append (fn-scc-u64 n 8) rest)) n))
   :hints (("Goal" :in-theory (disable fn-scc-u64)))))

(local
 (defthm fn-scc-parse-header-of-segment
   (implies (and (natp i) (< i *fn-scc-u64-bound*)
                 (natp n) (< n *fn-scc-u64-bound*)
                 (natp l) (< l *fn-scc-u64-bound*)
                 (natp q) (< q *fn-scc-u64-bound*))
            (equal (fn-scc-parse-header (append (fn-scc-header i n l q) rest))
                   (list i n l q rest)))
   :hints (("Goal" :in-theory (e/d (fn-scc-header) (fn-scc-u64 fn-scc-u64-at))))))

(local
 (defthm fn-scc-open-segment-of-frame
   (implies (and (natp i) (< i *fn-scc-u64-bound*)
                 (natp n) (< n *fn-scc-u64-bound*)
                 (true-listp chunk) (< (len chunk) *fn-scc-u64-bound*)
                 (natp q) (< q *fn-scc-u64-bound*))
            (equal (fn-scc-open-segment
                    (append (fn-scc-header i n (len chunk) q)
                            (append chunk
                                    (fn-scc-seal prev (fn-scc-header i n (len chunk) q)
                                                 chunk)))
                    i n q prev)
                   (list chunk (fn-scc-seal prev (fn-scc-header i n (len chunk) q)
                                            chunk))))
   :hints (("Goal" :in-theory (e/d () (fn-scc-header fn-scc-seal fn-scc-parse-header))))))

(local
 (defun fn-scc-join-ind (chunks i n q prev racc)
   (declare (xargs :verify-guards nil))
   (if (consp chunks)
       (let* ((h (fn-scc-header i n (len (car chunks)) q))
              (tr (fn-scc-seal prev h (car chunks))))
         (fn-scc-join-ind (cdr chunks) (+ 1 i) n q tr
                          (revappend (car chunks) racc)))
     (list i n q prev racc))))

(local
 (defthm fn-scc-true-list-fix-id
   (implies (true-listp x) (equal (true-list-fix x) x))))

(local
 (defthm fn-scc-join-of-frames
   (implies (and (fn-scc-chunk-listp chunks)
                 (natp i) (natp n) (<= (+ i (len chunks)) n)
                 (< n *fn-scc-u64-bound*)
                 (natp q) (< q *fn-scc-u64-bound*))
            (equal (fn-scc-join (fn-scc-frames chunks i n q prev) i n q prev racc)
                   (if (equal (+ i (len chunks)) n)
                       (list :ok (revappend (revappend (fn-scc-concat chunks) racc) nil))
                     (list :refused :truncated))))
   :hints (("Goal" :induct (fn-scc-join-ind chunks i n q prev racc)
            :in-theory (e/d () (fn-scc-header fn-scc-seal fn-scc-open-segment))))))


; -----------------------------------------------------------------------------
; 2. The arena run's program and segments.

(defconst *fn-scka-tag* '(102 110 65 49))

(defun fn-scka-payload-octets (p)
  (declare (xargs :guard (true-listp p)))
  (append (fn-scc-nat-octets (len p)) p))

(defun fn-scka-body (ps)
  (declare (xargs :guard (true-list-listp ps)))
  (if (atom ps)
      nil
    (append (fn-scka-payload-octets (car ps)) (fn-scka-body (cdr ps)))))

(defun fn-scka-head (n)
  (declare (xargs :guard (natp n)))
  (append *fn-scka-tag* (fn-scc-nat-octets n)))

(defun fn-scka-program (ps)
  (declare (xargs :guard (true-list-listp ps)))
  (append (fn-scka-head (len ps)) (fn-scka-body ps)))

; The batches: KS counts, one chunk per count, taken from the front.
(defun fn-scka-sum (ks)
  (declare (xargs :guard t))
  (if (atom ks) 0 (+ (nfix (car ks)) (fn-scka-sum (cdr ks)))))

(defun fn-scka-chunks (ps ks)
  (declare (xargs :guard (and (true-list-listp ps) (nat-listp ks)) :verify-guards nil))
  (if (atom ks)
      nil
    (cons (fn-scka-body (take (nfix (car ks)) ps))
          (fn-scka-chunks (nthcdr (nfix (car ks)) ps) (cdr ks)))))

(defun fn-scka-run-chunks (ps ks)
  (declare (xargs :guard (and (true-list-listp ps) (nat-listp ks)) :verify-guards nil))
  (cons (fn-scka-head (len ps)) (fn-scka-chunks ps ks)))

(defun fn-scka-run-segments (ps ks s)
  (declare (xargs :guard (and (true-list-listp ps) (nat-listp ks) (natp s)) :verify-guards nil))
  (fn-scc-frames (fn-scka-run-chunks ps ks) 0 (+ 1 (len ks)) s *fn-scc-genesis*))

(defthm fn-scka-body-of-append
  (equal (fn-scka-body (append a b)) (append (fn-scka-body a) (fn-scka-body b))))

(local
 (defthm fn-scka-append-take-nthcdr
   (implies (and (natp k) (<= k (len x)))
            (equal (append (take k x) (nthcdr k x)) x))))

(defthm fn-scka-body-true-listp
  (true-listp (fn-scka-body ps)))

(defthm fn-scka-concat-of-chunks
  (implies (and (true-listp ps) (equal (fn-scka-sum ks) (len ps)))
           (equal (fn-scc-concat (fn-scka-chunks ps ks)) (fn-scka-body ps)))
  :hints (("Goal" :induct (fn-scka-chunks ps ks)
           :in-theory (disable fn-scka-body-of-append fn-scka-body))
          ("Subgoal *1/2" :use ((:instance fn-scka-body-of-append
                                           (a (take (nfix (car ks)) ps))
                                           (b (nthcdr (nfix (car ks)) ps)))))))

(local
 (defthm fn-scka-len-frames
   (equal (len (fn-scc-frames chunks i n q prev)) (len chunks))))

(local
 (defthm fn-scka-take-segs-of-append
   (implies (equal n (len a))
            (equal (fn-sct-take-segs n (append a b)) (true-list-fix a)))
   :hints (("Goal" :induct (fn-sct-take-segs n a)))))

(local
 (defthm fn-scka-drop-segs-of-append
   (implies (equal n (len a))
            (equal (fn-sct-drop-segs n (append a b)) b))
   :hints (("Goal" :induct (fn-sct-drop-segs n a)))))

(local
 (defthm fn-scka-frames-true-listp
   (true-listp (fn-scc-frames chunks i n q prev))))

(local
 (defthm fn-scka-revappend-revappend-nil
   (implies (true-listp x) (equal (revappend (revappend x nil) nil) x))))

(local
 (defthm fn-scka-concat-true-listp
   (true-listp (fn-scc-concat x))))

(local
 (defthm fn-scka-len-chunks
   (equal (len (fn-scka-chunks ps ks)) (len ks))))

(local
 (defthm fn-scka-car-append
   (implies (consp a) (equal (car (append a b)) (car a)))))

(local
 (defthm fn-scka-consp-append
   (implies (consp a) (consp (append a b)))))

(defthm fn-scka-run-decode-of-run-segments
  (implies (and (true-listp ps) (equal (fn-scka-sum ks) (len ps))
                (fn-scc-chunk-listp (fn-scka-run-chunks ps ks))
                (< (+ 1 (len ks)) *fn-scc-u64-bound*)
                (natp s) (< s *fn-scc-u64-bound*))
           (equal (fn-sct-run-decode (append (fn-scka-run-segments ps ks s) rest) s)
                  (list :ok (fn-scka-program ps) rest)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-scc-parse-header-of-first-frame
                            (chunks (fn-scka-run-chunks ps ks)) (n (+ 1 (len ks))) (q s)
                            (prev *fn-scc-genesis*))
                 (:instance fn-scc-parse-header-of-first-frame-sequence
                            (chunks (fn-scka-run-chunks ps ks)) (n (+ 1 (len ks))) (q s)
                            (prev *fn-scc-genesis*))
                 (:instance fn-scc-join-of-frames
                            (chunks (fn-scka-run-chunks ps ks)) (i 0) (n (+ 1 (len ks))) (q s)
                            (prev *fn-scc-genesis*) (racc nil)))
           :in-theory (e/d (fn-sct-run-decode fn-scka-run-segments fn-scka-program)
                           (fn-scc-parse-header-of-first-frame fn-scc-join-of-frames
                            fn-scc-parse-header-of-first-frame-sequence
                            fn-scc-parse-header fn-scc-join fn-scc-frames fn-scka-chunks
                            fn-scka-head fn-scka-body)))))

; -----------------------------------------------------------------------------
; 3. The load: the seal loop, the arena run opened, the tables after it.

(local (in-theory (disable fn-cp-idp fn-sccr-scc-octet-listp-is-cbor-octet-listp
                           fn-sccr-cbor-octet-listp-is-scc-octet-listp)))

(defun fn-scka-seal-n (i end n fn-octets fn-arena)
  (declare (xargs :stobjs (fn-octets fn-arena)
                  :guard (and (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets)) (natp n))
                  :measure (nfix n)
                  :guard-hints (("Goal" :use ((:instance fn-sccr-read-nat-facts))
                                 :in-theory (disable fn-sccr-read-nat-facts)))))
  (if (zp n)
      (mv t i fn-arena)
    (let ((r (fn-sccr-read-nat i end fn-octets)))
      (if (not r)
          (mv nil i fn-arena)
        (let ((j (cdr r)) (l (car r)))
          (if (> (+ j l) end)
              (mv nil i fn-arena)
            (let ((fn-arena (fn-arena-seal-range j (+ j l) fn-octets fn-arena)))
              (fn-scka-seal-n (+ j l) end (1- n) fn-octets fn-arena))))))))

(local
 (defthm fn-scka-take-of-cons
   (implies (and (natp n) (< 0 n))
            (equal (take n (cons a x)) (cons a (take (- n 1) x))))))

(local
 (defthm fn-scka-nthcdr-of-cons
   (implies (and (natp n) (< 0 n))
            (equal (nthcdr n (cons a x)) (nthcdr (- n 1) x)))))

(local
 (defthm fn-scka-slice-prefix
   (implies (and (natp j) (natp k) (natp end) (<= j k) (<= k end))
            (equal (fn-oct-slice-list j k o)
                   (take (- k j) (fn-oct-slice-list j end o))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-oct-slice-list j k o)
            :in-theory (e/d (fn-oct-slice-list) (fn-oct-slice-list-is-take-nthcdr))
            :expand ((fn-oct-slice-list j end o) (fn-oct-slice-list j k o))))))

(local
 (defthm fn-scka-slice-suffix
   (implies (and (natp j) (natp k) (natp end) (<= j k) (<= k end))
            (equal (fn-oct-slice-list k end o)
                   (nthcdr (- k j) (fn-oct-slice-list j end o))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-oct-slice-list j k o)
            :in-theory (e/d (fn-oct-slice-list) (fn-oct-slice-list-is-take-nthcdr))
            :expand ((fn-oct-slice-list j end o) (fn-oct-slice-list j k o))))))

(local
 (defthm fn-scka-slice-len
   (implies (and (natp i) (natp n) (<= i n))
            (equal (len (fn-oct-slice-list i n o)) (- n i)))
   :hints (("Goal" :induct (fn-oct-slice-list i n o)
            :in-theory (e/d (fn-oct-slice-list) (fn-oct-slice-list-is-take-nthcdr))))))

(local
 (defthm fn-scka-read-payload
   (implies (and (fn-octets-p o) (natp i) (natp end) (<= i end) (<= end (len o))
                 (equal (fn-oct-slice-list i end o) (append (fn-scka-payload-octets p) rest))
                 (true-listp p))
            (let ((r (fn-sccr-read-nat i end o)))
              (and r
                   (equal (car r) (len p))
                   (<= (+ (cdr r) (len p)) end)
                   (equal (fn-oct-slice-list (cdr r) (+ (cdr r) (len p)) o) p)
                   (equal (fn-oct-slice-list (+ (cdr r) (len p)) end o) rest))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-sccr-read-nat-is-read-nat (fn-octets o))
                  (:instance fn-sccr-read-nat-facts (fn-octets o))
                  (:instance fn-scc-read-nat-of-octets (n (len p)) (rest (append p rest)))
                  (:instance fn-scka-slice-len (i (cdr (fn-sccr-read-nat i end o))) (n end))
                  (:instance fn-scka-slice-prefix (j (cdr (fn-sccr-read-nat i end o)))
                             (k (+ (cdr (fn-sccr-read-nat i end o)) (len p))))
                  (:instance fn-scka-slice-suffix (j (cdr (fn-sccr-read-nat i end o)))
                             (k (+ (cdr (fn-sccr-read-nat i end o)) (len p)))))
            :in-theory (e/d (fn-scka-payload-octets)
                            (fn-sccr-read-nat-is-read-nat fn-sccr-read-nat-facts
                             fn-scc-read-nat-of-octets fn-scka-slice-len
                             fn-oct-slice-list-is-take-nthcdr fn-scc-nat-octets
                             fn-scc-read-nat))))))

(local
 (defun fn-scka-seal-ind (i end ps fn-octets a)
   (declare (xargs :measure (len ps) :stobjs fn-octets :verify-guards nil))
   (if (atom ps)
       (list i end a)
     (let* ((r (fn-sccr-read-nat i end fn-octets)) (j (cdr r)) (l (car r)))
       (fn-scka-seal-ind (+ (nfix j) (nfix l)) end (cdr ps) fn-octets
                         (append a (list (car ps))))))))

(local
 (defthm fn-scka-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(defthm fn-scka-seal-n-of-body
  (implies (and (fn-octets-p fn-octets) (natp i) (natp end) (<= i end)
                (<= end (len fn-octets))
                (equal (fn-oct-slice-list i end fn-octets) (append (fn-scka-body ps) rest))
                (true-list-listp ps) (true-listp fn-arena))
           (let ((r (fn-scka-seal-n i end (len ps) fn-octets fn-arena)))
             (and (mv-nth 0 r)
                  (natp (mv-nth 1 r))
                  (<= (mv-nth 1 r) end)
                  (equal (mv-nth 2 r) (append fn-arena ps))
                  (equal (fn-oct-slice-list (mv-nth 1 r) end fn-octets) rest))))
  :hints (("Goal" :induct (fn-scka-seal-ind i end ps fn-octets fn-arena)
           :in-theory (e/d (fn-scka-seal-n fn-scka-body)
                           (fn-scka-payload-octets fn-oct-slice-list-is-take-nthcdr
                            fn-arena-seal-range-is-append)))
          ("Subgoal *1/2" :use ((:instance fn-scka-read-payload (o fn-octets) (p (car ps))
                                           (rest (append (fn-scka-body (cdr ps)) rest)))
                                (:instance fn-sccr-read-nat-facts))
           :in-theory (e/d (fn-scka-seal-n fn-scka-body)
                           (fn-scka-payload-octets fn-oct-slice-list-is-take-nthcdr
                            fn-arena-seal-range-is-append fn-scka-read-payload
                            fn-sccr-read-nat-facts)))))

(local
 (defthm fn-scka-take-of-append-short
   (implies (and (natp k) (<= k (len a)))
            (equal (take k (append a b)) (take k a)))))

(local
 (defthm fn-scka-nthcdr-of-append-short
   (implies (and (natp k) (<= k (len a)))
            (equal (nthcdr k (append a b)) (append (nthcdr k a) b)))))

(local
 (defthm fn-scka-nth-of-append-short
   (implies (and (natp k) (< k (len a)))
            (equal (nth k (append a b)) (nth k a)))))

(local
 (defthm fn-sctr-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn-sctr-long-enoughp-is-len
   (implies (natp n)
            (equal (fn-scc-long-enoughp n xs) (<= n (len xs))))))

(local
 (defthm fn-sctr-take-of-append-short
   (implies (and (natp k) (<= k (len a)))
            (equal (take k (append a b)) (take k a)))))

(local
 (defthm fn-sctr-nthcdr-of-append-short
   (implies (and (natp k) (<= k (len a)))
            (equal (nthcdr k (append a b)) (append (nthcdr k a) b)))))

(local
 (defthm fn-sctr-nth-of-append-short
   (implies (and (natp k) (< k (len a)))
            (equal (nth k (append a b)) (nth k a)))))

(local
 (defthm fn-sctr-take-all
   (implies (and (true-listp x) (equal k (len x)))
            (equal (take k x) x))))

(local
 (defthm fn-sctr-nthcdr-all
   (implies (and (true-listp x) (equal k (len x)))
            (equal (nthcdr k x) nil))))

(local
 (defthm fn-sctr-len-nthcdr
   (implies (and (natp n) (<= n (len xs)))
            (equal (len (nthcdr n xs)) (- (len xs) n)))))

(local
 (defthm fn-sctr-true-listp-nthcdr
   (implies (true-listp x) (true-listp (nthcdr n x)))))

(local
 (defthm fn-sctr-parse-header-of-append
   (implies (and (fn-scc-octet-listp header)
                 (equal (len header) *fn-scc-segment-header-octets*))
            (equal (fn-scc-parse-header (append header rest))
                   (and (fn-scc-parse-header header)
                        (list (nth 0 (fn-scc-parse-header header))
                              (nth 1 (fn-scc-parse-header header))
                              (nth 2 (fn-scc-parse-header header))
                              (nth 3 (fn-scc-parse-header header))
                              rest))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-scc-parse-header fn-scc-u64-at)
                            (fn-scc-le-value))))))

(local
 (defthm fn-sctr-parse-header-of-frame-octets
   (implies (and (fn-octets-p fn-octets) (fn-sccr-framep frame fn-octets))
            (equal (fn-scc-parse-header (fn-sccb-frame-octets frame fn-octets))
                   (and (fn-scc-parse-header (nth 0 frame))
                        (list (nth 0 (fn-scc-parse-header (nth 0 frame)))
                              (nth 1 (fn-scc-parse-header (nth 0 frame)))
                              (nth 2 (fn-scc-parse-header (nth 0 frame)))
                              (nth 3 (fn-scc-parse-header (nth 0 frame)))
                              (append (fn-oct-slice-list (nth 1 frame) (nth 2 frame)
                                                         fn-octets)
                                      (nth 3 frame))))))
   :hints (("Goal" :in-theory (e/d (fn-sccb-frame-octets fn-sccr-framep)
                                   (fn-scc-parse-header))))))

(defthm fn-scka-seal-n-compose
  (implies (and (natp n1) (natp n2))
           (equal (fn-scka-seal-n i end (+ n1 n2) fn-octets fn-arena)
                  (mv-let (ok i1 a1) (fn-scka-seal-n i end n1 fn-octets fn-arena)
                    (if ok
                        (fn-scka-seal-n i1 end n2 fn-octets a1)
                      (mv nil i1 a1)))))
  :hints (("Goal" :induct (fn-scka-seal-n i end n1 fn-octets fn-arena)
           :in-theory (e/d (fn-scka-seal-n) (fn-arena-seal-range-is-append)))))

(defun fn-scka-open-run (plan fn-octets)
  (declare (xargs :stobjs fn-octets :guard t :verify-guards nil))
  (let ((start (if (consp plan) (fn-sccr-at 1 (car plan)) 0)))
    (if (not (fn-sccr-planp plan start fn-octets))
        (list :refused :layout)
      (let ((h (and (consp plan) (fn-scc-parse-header (fn-sccr-at 0 (car plan))))))
        (if (not h)
            (list :refused :header)
          (let* ((s (nth 3 h))
                 (r (fn-sctr-next-run plan s fn-octets)))
            (if (not (eq (car r) :ok))
                r
              (let ((a (nth 1 r)) (b (nth 2 r)))
                (if (not (and (<= (+ a 4) b)
                              (equal (fn-oct-slice-list a (+ a 4) fn-octets) *fn-scka-tag*)))
                    (list :refused :arena)
                  (let ((n (fn-sccr-read-nat (+ a 4) b fn-octets)))
                    (if (not n)
                        (list :refused :arena)
                      (list :ok (cdr n) b (car n) (nth 3 r) s))))))))))))

(local
 (defun fn-sctr-frames-ind (n plan pos)
   (if (or (zp n) (not (consp plan)))
       (list plan pos)
     (fn-sctr-frames-ind (1- n) (cdr plan) (fn-sccr-at 2 (car plan))))))

(local
 (defthm fn-sctr-parse-header-count-natp
   (implies (and (fn-scc-octet-listp seg) (fn-scc-parse-header seg))
            (natp (nth 1 (fn-scc-parse-header seg))))
   :hints (("Goal" :in-theory (enable fn-scc-parse-header fn-scc-u64-at)))))

(local
 (defthm fn-sctr-plan-end-is-first-a
   (implies (and (fn-sccr-planp plan pos fn-octets)
                 (consp (fn-sctr-drop-frames n plan)))
            (equal (fn-sccr-at 1 (car (fn-sctr-drop-frames n plan)))
                   (fn-sctr-plan-end (fn-sctr-take-frames n plan) pos)))
   :hints (("Goal" :induct (fn-sctr-frames-ind n plan pos)
            :in-theory (e/d (fn-sccr-planp) (fn-sccr-framep fn-sccr-at-is-nth))))))

(local
 (defthm fn-sctr-join-end-is-plan-end
   (implies (and (fn-sccr-planp plan pos fn-octets)
                 (eq (car (fn-sccr-join plan pos index count sequence prev fn-octets)) :ok))
            (equal (nth 1 (fn-sccr-join plan pos index count sequence prev fn-octets))
                   (fn-sctr-plan-end plan pos)))
   :hints (("Goal" :induct (fn-sccr-join plan pos index count sequence prev fn-octets)
            :in-theory (e/d (fn-sccr-join fn-sccr-planp)
                            (fn-sccr-open-frame fn-sccr-framep fn-sccr-at-is-nth))))))

(local
 (defthm fn-sctr-run-decode-ok-shape
   (implies (and (fn-sccr-planp plan pos fn-octets)
                 (eq (car (fn-sctr-run-decode plan pos s fn-octets)) :ok))
            (and (equal (nth 1 (fn-sctr-run-decode plan pos s fn-octets)) pos)
                 (natp (nth 2 (fn-sctr-run-decode plan pos s fn-octets)))
                 (<= pos (nth 2 (fn-sctr-run-decode plan pos s fn-octets)))
                 (<= (nth 2 (fn-sctr-run-decode plan pos s fn-octets)) (len fn-octets))
                 (natp pos)
                 (fn-sccr-planp (nth 3 (fn-sctr-run-decode plan pos s fn-octets))
                                (nth 2 (fn-sctr-run-decode plan pos s fn-octets))
                                fn-octets)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-sccr-join-ok-end
                             (plan (fn-sctr-take-frames
                                    (nth 1 (fn-scc-parse-header (fn-sccr-at 0 (car plan)))) plan))
                             (index 0)
                             (count (nth 1 (fn-scc-parse-header (fn-sccr-at 0 (car plan)))))
                             (sequence s) (prev *fn-scc-genesis*))
                  (:instance fn-sctr-drop-frames-planp
                             (n (nth 1 (fn-scc-parse-header (fn-sccr-at 0 (car plan))))))
                  (:instance fn-sctr-join-end-is-plan-end
                             (plan (fn-sctr-take-frames
                                    (nth 1 (fn-scc-parse-header (fn-sccr-at 0 (car plan)))) plan))
                             (index 0)
                             (count (nth 1 (fn-scc-parse-header (fn-sccr-at 0 (car plan)))))
                             (sequence s) (prev *fn-scc-genesis*))
                  (:instance fn-sccr-planp-pos))
            :in-theory (e/d (fn-sctr-run-decode)
                            (fn-scc-parse-header fn-sccr-join fn-sccr-planp
                             fn-sccr-join-ok-end fn-sctr-drop-frames-planp
                             fn-sctr-join-end-is-plan-end fn-sccr-planp-pos
                             fn-sccr-at-is-nth))))))

(local
 (defthm fn-sctr-restp-of-plan
   (implies (fn-sccr-planp plan (if (consp plan) (fn-sccr-at 1 (car plan)) 0) fn-octets)
            (fn-sctr-restp plan fn-octets))
   :hints (("Goal" :in-theory (enable fn-sctr-restp)))))

(local
 (defthm fn-scka-plan-segments-car
   (implies (consp plan)
            (equal (car (fn-sccr-plan-segments plan fn-octets))
                   (fn-sccb-frame-octets (car plan) fn-octets)))
   :hints (("Goal" :in-theory (enable fn-sccr-plan-segments)))))

(local
 (defthm fn-scka-plan-segments-consp
   (equal (consp (fn-sccr-plan-segments plan fn-octets)) (consp plan))
   :hints (("Goal" :in-theory (enable fn-sccr-plan-segments)))))

(local
 (defthm fn-scka-planp-framep
   (implies (and (fn-sccr-planp plan pos fn-octets) (consp plan))
            (fn-sccr-framep (car plan) fn-octets))
   :hints (("Goal" :expand ((fn-sccr-planp plan pos fn-octets))))))

(local
 (defthm fn-scka-run-chunks-consp
   (consp (fn-scka-run-chunks ps ks))))

(local
 (defthm fn-scka-run-segments-consp
   (consp (fn-scka-run-segments ps ks s))
   :hints (("Goal" :in-theory (union-theories '(fn-scka-run-segments fn-scc-frames-consp
                                                fn-scka-run-chunks-consp)
                                              (theory 'minimal-theory))))))

(local
 (defthm fn-scka-car-run-segments
   (equal (car (fn-scka-run-segments ps ks s))
          (car (fn-scc-frames (fn-scka-run-chunks ps ks) 0 (+ 1 (len ks)) s *fn-scc-genesis*)))
   :hints (("Goal" :in-theory (union-theories '(fn-scka-run-segments) (theory 'minimal-theory))))))

(local
 (defthm fn-scka-first-header
   (implies (and (fn-octets-p fn-octets)
                 (fn-sccr-planp plan pos fn-octets)
                 (equal (fn-sccr-plan-segments plan fn-octets)
                        (append (fn-scka-run-segments ps ks s) tsegs))
                 (fn-scc-chunk-listp (fn-scka-run-chunks ps ks))
                 (< (+ 1 (len ks)) *fn-scc-u64-bound*) (natp s) (< s *fn-scc-u64-bound*))
            (and (consp plan)
                 (fn-scc-parse-header (fn-sccr-at 0 (car plan)))
                 (equal (nth 3 (fn-scc-parse-header (fn-sccr-at 0 (car plan)))) s)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-scc-parse-header-of-first-frame-sequence
                             (chunks (fn-scka-run-chunks ps ks)) (n (+ 1 (len ks))) (q s)
                             (prev *fn-scc-genesis*))
                  (:instance fn-sctr-parse-header-of-frame-octets (frame (car plan)))
                  (:instance fn-scka-plan-segments-car)
                  (:instance fn-scka-plan-segments-consp)
                  (:instance fn-scka-planp-framep)
                  (:instance fn-scka-run-segments-consp)
                  (:instance fn-scka-consp-append (a (fn-scka-run-segments ps ks s)) (b tsegs)))
            :in-theory (e/d (fn-scka-car-append fn-scka-consp-append)
                            (fn-scka-run-segments fn-scc-parse-header-of-first-frame-sequence
                             fn-sctr-parse-header-of-frame-octets fn-scka-plan-segments-car
                             fn-scka-plan-segments-consp fn-scka-planp-framep
                             fn-scka-run-segments-consp
                             fn-scc-parse-header fn-scc-frames fn-scka-run-chunks
                             fn-sccb-frame-octets fn-sccr-framep fn-sccr-planp))))))

(local
 (defthm fn-scka-next-run-of-written
   (implies (and (fn-octets-p fn-octets)
                 (fn-sccr-planp plan (fn-sccr-at 1 (car plan)) fn-octets)
                 (consp plan)
                 (equal (fn-sccr-plan-segments plan fn-octets)
                        (append (fn-scka-run-segments ps ks s) tsegs))
                 (true-listp ps) (equal (fn-scka-sum ks) (len ps))
                 (fn-scc-chunk-listp (fn-scka-run-chunks ps ks))
                 (< (+ 1 (len ks)) *fn-scc-u64-bound*) (natp s) (< s *fn-scc-u64-bound*))
            (let ((r (fn-sctr-next-run plan s fn-octets)))
              (and (equal (car r) :ok)
                   (natp (nth 1 r)) (natp (nth 2 r))
                   (<= (nth 1 r) (nth 2 r)) (<= (nth 2 r) (len fn-octets))
                   (equal (fn-oct-slice-list (nth 1 r) (nth 2 r) fn-octets) (fn-scka-program ps))
                   (equal (fn-sccr-plan-segments (nth 3 r) fn-octets) tsegs)
                   (fn-sccr-planp (nth 3 r) (nth 2 r) fn-octets))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-sctr-run-decode-is-run-decode)
                  (:instance fn-scka-run-decode-of-run-segments (rest tsegs))
                  (:instance fn-sctr-run-decode-ok-shape (pos (fn-sccr-at 1 (car plan)))))
            :in-theory (e/d (fn-sctr-next-run)
                            (fn-sctr-run-decode-is-run-decode fn-scka-run-decode-of-run-segments
                             fn-sctr-run-decode-ok-shape fn-sctr-run-decode fn-sct-run-decode
                             fn-scka-program fn-scka-run-segments fn-sccr-planp
                             fn-oct-slice-list-is-take-nthcdr))))))

(local
 (defthm fn-scka-program-split
   (and (equal (take 4 (fn-scka-program ps)) *fn-scka-tag*)
        (equal (nthcdr 4 (fn-scka-program ps))
               (append (fn-scc-nat-octets (len ps)) (fn-scka-body ps)))
        (<= 5 (len (fn-scka-program ps))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-scka-program fn-scka-head)))))

(local
 (defthm fn-scka-slice-head
   (implies (and (fn-octets-p o) (natp a) (natp b) (<= a b) (<= b (len o))
                 (equal (fn-oct-slice-list a b o) (fn-scka-program ps)))
            (let ((r (fn-sccr-read-nat (+ a 4) b o)))
              (and (<= (+ a 4) b)
                   (equal (fn-oct-slice-list a (+ a 4) o) *fn-scka-tag*)
                   r
                   (equal (car r) (len ps))
                   (natp (cdr r)) (<= (cdr r) b)
                   (equal (fn-oct-slice-list (cdr r) b o) (fn-scka-body ps)))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-scka-program-split)
                  (:instance fn-scka-slice-prefix (j a) (k (+ 4 a)) (end b))
                  (:instance fn-scka-slice-suffix (j a) (k (+ 4 a)) (end b))
                  (:instance fn-scka-slice-len (i a) (n b))
                  (:instance fn-sccr-read-nat-is-read-nat (i (+ 4 a)) (end b) (fn-octets o))
                  (:instance fn-sccr-read-nat-facts (i (+ 4 a)) (end b) (fn-octets o))
                  (:instance fn-scc-read-nat-of-octets (n (len ps)) (rest (fn-scka-body ps))))
            :in-theory (e/d ()
                            (fn-sccr-read-nat-is-read-nat fn-sccr-read-nat-facts
                             fn-scc-read-nat-of-octets fn-scka-slice-len
                             fn-scka-program fn-scka-body fn-scc-nat-octets fn-scc-read-nat
                             fn-oct-slice-list-is-take-nthcdr))))))

(defthm fn-scka-open-run-of-written
  (implies (and (fn-octets-p fn-octets)
                (fn-sccr-planp plan (if (consp plan) (fn-sccr-at 1 (car plan)) 0) fn-octets)
                (equal (fn-sccr-plan-segments plan fn-octets)
                       (append (fn-scka-run-segments ps ks s) tsegs))
                (true-listp ps) (equal (fn-scka-sum ks) (len ps))
                (fn-scc-chunk-listp (fn-scka-run-chunks ps ks))
                (< (+ 1 (len ks)) *fn-scc-u64-bound*) (natp s) (< s *fn-scc-u64-bound*))
           (let ((o (fn-scka-open-run plan fn-octets)))
             (and (equal (nth 0 o) :ok)
                  (equal (nth 3 o) (len ps))
                  (equal (nth 5 o) s)
                  (natp (nth 1 o)) (natp (nth 2 o)) (<= (nth 1 o) (nth 2 o))
                  (<= (nth 2 o) (len fn-octets))
                  (equal (fn-oct-slice-list (nth 1 o) (nth 2 o) fn-octets) (fn-scka-body ps))
                  (equal (fn-sccr-plan-segments (nth 4 o) fn-octets) tsegs)
                  (fn-sccr-planp (nth 4 o) (nth 2 o) fn-octets))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-scka-first-header (pos (if (consp plan) (fn-sccr-at 1 (car plan)) 0)))
                 (:instance fn-scka-next-run-of-written)
                 (:instance fn-scka-slice-head
                            (a (nth 1 (fn-sctr-next-run plan s fn-octets)))
                            (b (nth 2 (fn-sctr-next-run plan s fn-octets)))
                            (o fn-octets)))
           :in-theory (union-theories '(fn-scka-open-run car-cons cdr-cons nth-0-cons
                                        nth-add1 (:executable-counterpart nth)
                                        (:executable-counterpart equal)
                                        (:executable-counterpart not)
                                        (:executable-counterpart car)
                                        (:executable-counterpart zp)
                                        (:executable-counterpart binary-+)
                                        nth zp natp fix nfix)
                                      (theory 'minimal-theory)))))

(defun fn-scka-finish (rest s i b fn-octets)
  (declare (xargs :stobjs fn-octets :guard t))
  (if (not (equal i b))
      (list :refused :arena)
    (let ((loaded (fn-sct-load rest fn-octets)))
      (if (not (eq (car loaded) :ok))
          loaded
        (if (not (equal (fn-sco-at 1 (fn-sct-tables-f (cadr loaded))) s))
            (list :refused :close)
          loaded)))))

(defun fn-scka-load (plan fn-octets fn-arena)
  (declare (xargs :stobjs (fn-octets fn-arena) :verify-guards nil))
  (let ((o (fn-scka-open-run plan fn-octets)))
    (if (not (eq (car o) :ok))
        (mv o fn-arena)
      (let ((fn-arena (fn-arena-clear fn-arena)))
        (mv-let (ok i fn-arena)
          (fn-scka-seal-n (nth 1 o) (nth 2 o) (nth 3 o) fn-octets fn-arena)
          (if (not ok)
              (mv (list :refused :arena) fn-arena)
            (mv (fn-scka-finish (nth 4 o) (nth 5 o) i (nth 2 o) fn-octets) fn-arena)))))))

(local
 (defthm fn-scka-f-of-tables-of-capture
   (equal (nth 1 (nth 0 (fn-sct-tables-of-capture (fn-sco-capture configs records)
                                                  frontier revision)))
          (len records))
   :hints (("Goal" :in-theory (e/d (fn-sct-tables-of-capture fn-sco-capture fn-sco-make
                                    fn-sco-records fn-sco-at)
                                   (fn-sco-cpr-prefix fn-replay-identity-loop
                                    fn-cpe-projection-replay fn-th-prefix-loop
                                    fn-cei-build-aux))))))

(local
 (defthm fn-scka-planp-first-a
   (implies (and (fn-sccr-planp plan pos fn-octets) (consp plan))
            (equal (fn-sccr-at 1 (car plan)) pos))
   :hints (("Goal" :expand ((fn-sccr-planp plan pos fn-octets))))))

(local
 (defthm fn-scka-slice-nil-means-end
   (implies (and (natp i) (natp b) (<= i b) (equal (fn-oct-slice-list i b o) nil))
            (equal i b))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-scka-slice-len (n b)))
            :in-theory (disable fn-scka-slice-len fn-oct-slice-list-is-take-nthcdr)))))

(local
 (defthm fn-scka-seal-all
   (implies (and (fn-octets-p fn-octets) (natp i) (natp b) (<= i b) (<= b (len fn-octets))
                 (equal (fn-oct-slice-list i b fn-octets) (fn-scka-body ps))
                 (true-list-listp ps))
            (let ((r (fn-scka-seal-n i b (len ps) fn-octets nil)))
              (and (mv-nth 0 r)
                   (equal (mv-nth 1 r) b)
                   (equal (mv-nth 2 r) ps))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-scka-seal-n-of-body (end b) (rest nil) (fn-arena nil))
                  (:instance fn-scka-slice-nil-means-end
                             (i (mv-nth 1 (fn-scka-seal-n i b (len ps) fn-octets nil)))
                             (o fn-octets)))
            :in-theory (disable fn-scka-seal-n-of-body fn-scka-seal-n fn-scka-body
                                fn-oct-slice-list-is-take-nthcdr)))))

(local
 (defthm fn-scka-finish-when-load
   (implies (equal (fn-sct-load rest o) (list :ok tables))
            (equal (fn-scka-finish rest s b b o)
                   (if (equal (fn-sco-at 1 (fn-sct-tables-f tables)) s)
                       (list :ok tables)
                     (list :refused :close))))
   :hints (("Goal" :in-theory (e/d (fn-scka-finish) (fn-sct-load fn-sct-tables-f fn-sco-at))))))

(local
 (defthm fn-scka-chunks-consp
   (consp (fn-scc-chunks p seg))
   :hints (("Goal" :expand ((fn-scc-chunks p seg))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm fn-scka-file-segments-consp
   (consp (fn-sct-file-segments progs seg s))
   :hints (("Goal" :in-theory (union-theories '(fn-sct-file-segments fn-sct-run-segments
                                                fn-scka-chunks-consp fn-scc-frames-consp
                                                fn-scka-consp-append)
                                              (theory 'minimal-theory))))))

(local
 (defthm fn-scka-load-of-written-tables
   (let* ((c (fn-sco-capture configs records))
          (tables (fn-sct-tables-of-capture c frontier revision))
          (progs (fn-sct-table-programs tables (fn-sco-event-index c))))
     (implies (and (fn-octets-p fn-octets)
                   (fn-sccr-planp rest b fn-octets)
                   (equal (fn-sccr-plan-segments rest fn-octets)
                          (fn-sct-file-segments progs seg (len records)))
                   (fn-sct-tables-treep tables)
                   (<= (len records) (1+ *fn-cbor-max-uint*))
                   (fn-sct-programs-widthp progs))
              (equal (fn-sct-load rest fn-octets) (list :ok tables))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :cases ((consp rest))
            :use ((:instance fn-sct-load-is-decode-file (plan rest))
                  (:instance fn-sct-decode-file-of-file-is-the-capture)
                  (:instance fn-scka-planp-first-a (plan rest) (pos b))
                  (:instance fn-scka-plan-segments-consp (plan rest))
                  (:instance fn-scka-file-segments-consp (progs (fn-sct-table-programs
                     (fn-sct-tables-of-capture (fn-sco-capture configs records) frontier revision)
                     (fn-sco-event-index (fn-sco-capture configs records)))) (s (len records))))
            :in-theory (e/d ()
                            (fn-sct-load-is-decode-file fn-sct-decode-file-of-file-is-the-capture
                             fn-scka-planp-first-a fn-scka-plan-segments-consp
                             fn-scka-file-segments-consp fn-sct-load fn-sct-decode-file
                             fn-sct-file-segments fn-sct-tables-of-capture fn-sco-capture
                             fn-sct-table-programs fn-sct-tables-treep fn-sct-programs-widthp
                             fn-sccr-planp fn-sco-event-index))))))

(local
 (defthm fn-scka-f-count-of-tables-of-capture
   (equal (fn-sco-at 1 (fn-sct-tables-f (fn-sct-tables-of-capture (fn-sco-capture configs records)
                                                                  frontier revision)))
          (len records))
   :hints (("Goal" :in-theory (e/d (fn-sct-tables-f fn-sct-tables-of-capture fn-sco-capture
                                    fn-sco-make fn-sco-records fn-sco-at)
                                   (fn-sco-cpr-prefix fn-replay-identity-loop
                                    fn-cpe-projection-replay fn-th-prefix-loop
                                    fn-cei-build-aux))))))

(defthm fn-scka-load-of-written-file
  (let* ((c (fn-sco-capture configs records))
         (tables (fn-sct-tables-of-capture c frontier revision))
         (progs (fn-sct-table-programs tables (fn-sco-event-index c)))
         (s (len records)))
    (implies (and (fn-octets-p fn-octets)
                  (fn-sccr-planp plan (if (consp plan) (fn-sccr-at 1 (car plan)) 0) fn-octets)
                  (equal (fn-sccr-plan-segments plan fn-octets)
                         (append (fn-scka-run-segments ps ks s)
                                 (fn-sct-file-segments progs seg s)))
                  (true-list-listp ps) (equal (fn-scka-sum ks) (len ps))
                  (fn-scc-chunk-listp (fn-scka-run-chunks ps ks))
                  (< (+ 1 (len ks)) *fn-scc-u64-bound*) (< s *fn-scc-u64-bound*)
                  (fn-sct-tables-treep tables)
                  (<= (len records) (1+ *fn-cbor-max-uint*))
                  (fn-sct-programs-widthp progs))
             (and (equal (mv-nth 0 (fn-scka-load plan fn-octets fn-arena)) (list :ok tables))
                  (equal (mv-nth 1 (fn-scka-load plan fn-octets fn-arena)) ps))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-scka-open-run-of-written (s (len records))
                            (tsegs (fn-sct-file-segments
                                    (fn-sct-table-programs
                                     (fn-sct-tables-of-capture (fn-sco-capture configs records)
                                                               frontier revision)
                                     (fn-sco-event-index (fn-sco-capture configs records)))
                                    seg (len records))))
                 (:instance fn-scka-seal-all
                            (i (nth 1 (fn-scka-open-run plan fn-octets)))
                            (b (nth 2 (fn-scka-open-run plan fn-octets))))
                 (:instance fn-scka-load-of-written-tables
                            (rest (nth 4 (fn-scka-open-run plan fn-octets)))
                            (b (nth 2 (fn-scka-open-run plan fn-octets)))))
           :in-theory (e/d (fn-scka-load)
                           (fn-scka-open-run-of-written fn-scka-seal-all
                            fn-scka-open-run fn-scka-seal-n fn-scka-finish fn-sct-load
                            fn-sct-tables-of-capture fn-sco-capture fn-sct-table-programs
                            fn-sct-file-segments fn-scka-run-segments fn-scka-run-chunks
                            fn-sct-tables-treep fn-sct-programs-widthp fn-sccr-planp
                            fn-sco-event-index fn-sct-capture-of-tables fn-scka-body
                            fn-sct-tables-f fn-sco-at fn-oct-slice-list-is-take-nthcdr
                            fn-sccr-plan-segments fn-scka-sum fn-scka-car-run-segments
                            fn-scc-frames binary-append fn-cp-idp fn-scc-header
                            fn-sccr-scc-octet-listp-is-cbor-octet-listp
                            fn-sccr-cbor-octet-listp-is-scc-octet-listp)))))

; -----------------------------------------------------------------------------
; 4. The open.  What both host recovers call: the records interned onto the
; arena, then the capture extended over the rows.  The full recover passes
; the capture of no records and the emptied arena; the checkpoint recover
; passes the loaded capture and the loaded arena.  (mv E fn-arena), E :bad
; when the intern refuses a record.  The host's extension is the twin
; fn-rii-sco-extend, EQUAL with no hypothesis (fn-rii-sco-extend-is-sco-extend,
; books/replay-identity-index.lisp, red on dev at this writing: the twin of
; this function over it is a one-line theorem once that book is green).
(defun fn-scka-recover-rows (c configs records fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (rows fn-arena)
    (fn-intern-events records nil 0 fn-arena)
    (if (eq rows :bad)
        (mv :bad fn-arena)
      (mv (fn-sco-extend c configs rows) fn-arena))))

(defthm fn-scka-payloads-of-append
  (equal (fn-scka-payloads (append ws vs))
         (append (fn-scka-payloads ws) (fn-scka-payloads vs))))

(local
 (defthm fn-scka-append-is-bad
   (equal (equal (append x r) :bad) (and (atom x) (equal r :bad)))))

(defthm fn-scka-intern-at-of-append
  (implies (and (natp h) (not (equal (fn-scka-intern-at ws h) :bad)))
           (equal (fn-scka-intern-at (append ws vs) h)
                  (let ((r (fn-scka-intern-at vs (+ h (len (fn-scka-payloads ws))))))
                    (if (equal r :bad) :bad (append (fn-scka-intern-at ws h) r)))))
  :hints (("Goal" :induct (fn-scka-intern-at ws h)
           :in-theory (disable fn-scka-intern-one fn-scka-sealsp fn-scka-payload-of))))

(local
 (defthm fn-scka-record-valuesp-is-store-eventsp
   (equal (fn-sf-record-valuesp x) (fn-sco-store-eventsp x))
   :hints (("Goal" :in-theory (enable fn-sf-record-valuesp fn-sco-store-eventsp)))))

; The canonical rows are retained events (the intern's keystone, restated
; on the canonical view).
(defthm fn-scka-intern-at-store-eventsp
  (implies (not (equal (fn-scka-intern-at ws 0) :bad))
           (fn-sco-store-eventsp (fn-scka-intern-at ws 0)))
  :hints (("Goal" :use ((:instance fn-intern-events-are-store-events
                                   (keyring nil) (generation 0) (fn-arena nil))
                        (:instance fn-intern-events-is-intern-at (fn-arena nil)))
           :in-theory (disable fn-intern-events-are-store-events fn-intern-events-is-intern-at
                               fn-intern-events fn-scka-intern-at))))

(defthm fn-scka-intern-at-true-listp
  (implies (not (equal (fn-scka-intern-at ws h) :bad))
           (true-listp (fn-scka-intern-at ws h)))
  :hints (("Goal" :in-theory (disable fn-scka-intern-one fn-scka-sealsp))))

(local
 (defthm fn-scka-true-list-fix-id
   (implies (true-listp x) (equal (true-list-fix x) x))))

(local
 (defthm fn-scka-len-payloads-true-listp
   (true-listp (fn-scka-payloads ws))))

; KEYSTONE (the open).  From the checkpoint of a prefix WS (the capture of
; its canonical rows, and its canonical arena), the recover over the suffix
; VS is the full recover of WS ++ VS from the emptied arena: the same
; extended capture (so fn-store-sn-open-extended opens the same store) and
; the same arena.  The hypotheses: the prefix interns (a checkpoint is
; written only of an interned history) and so does the whole history (a
; record the intern refuses faults both opens, with different partial
; arenas that nothing reads).
(defthm fn-scka-recover-from-checkpoint-is-full-recover
  (implies (and (not (equal (fn-scka-intern-at ws 0) :bad))
                (not (equal (fn-scka-intern-at (append ws vs) 0) :bad)))
           (equal (fn-scka-recover-rows (fn-sco-capture configs (fn-scka-intern-at ws 0))
                                        configs vs (fn-scka-payloads ws))
                  (fn-scka-recover-rows (fn-sco-capture configs nil) configs
                                        (append ws vs) nil)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-intern-events-is-intern-at (ws vs) (fn-arena (fn-scka-payloads ws)))
                 (:instance fn-intern-events-arena-is-payloads (ws vs)
                            (fn-arena (fn-scka-payloads ws)))
                 (:instance fn-intern-events-is-intern-at (ws (append ws vs)) (fn-arena nil))
                 (:instance fn-intern-events-arena-is-payloads (ws (append ws vs)) (fn-arena nil))
                 (:instance fn-scka-intern-at-of-append (h 0))
                 (:instance fn-sco-extend-of-capture (prefix (fn-scka-intern-at ws 0))
                            (suffix (fn-scka-intern-at vs (len (fn-scka-payloads ws)))))
                 (:instance fn-sco-extend-of-capture (prefix nil)
                            (suffix (append (fn-scka-intern-at ws 0)
                                            (fn-scka-intern-at vs (len (fn-scka-payloads ws)))))))
           :in-theory (e/d (fn-scka-recover-rows)
                           (fn-intern-events-is-intern-at fn-intern-events-arena-is-payloads
                            fn-scka-intern-at-of-append fn-sco-extend-of-capture
                            fn-intern-events fn-scka-intern-at fn-scka-payloads
                            fn-sco-extend fn-sco-capture)))))

; -----------------------------------------------------------------------------
; 5. The writer's inputs, from the live store (rows and arena), per row.
; Alpha of each row (fn-row-wire-of: the payload read through the arena)
; is taken one row at a time, so the live store is never materialized as
; wire records; the canonical rows and payloads are those of alpha.

(defun fn-scka-canon-rows (rows fn-arena h)
  (declare (xargs :stobjs fn-arena :guard (natp h) :verify-guards nil))
  (if (atom rows)
      nil
    (let* ((w (fn-row-wire-of (car rows) fn-arena))
           (row (fn-scka-intern-one w h)))
      (if (eq row :bad)
          :bad
        (let ((rest (fn-scka-canon-rows (cdr rows) fn-arena
                                        (if (fn-scka-sealsp w) (+ 1 h) h))))
          (if (eq rest :bad)
              :bad
            (cons row rest)))))))

(defthm fn-scka-canon-rows-is-intern-at-of-alpha
  (equal (fn-scka-canon-rows rows fn-arena h)
         (fn-scka-intern-at (fn-rows-wire-of rows fn-arena) h))
  :hints (("Goal" :induct (fn-scka-canon-rows rows fn-arena h)
           :in-theory (disable fn-scka-intern-one fn-scka-sealsp fn-row-wire-of))))

(defun fn-scka-canon-payloads (rows fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (if (atom rows)
      nil
    (let ((w (fn-row-wire-of (car rows) fn-arena)))
      (if (fn-scka-sealsp w)
          (cons (fn-scka-payload-of w) (fn-scka-canon-payloads (cdr rows) fn-arena))
        (fn-scka-canon-payloads (cdr rows) fn-arena)))))

(defthm fn-scka-canon-payloads-is-payloads-of-alpha
  (equal (fn-scka-canon-payloads rows fn-arena)
         (fn-scka-payloads (fn-rows-wire-of rows fn-arena)))
  :hints (("Goal" :induct (fn-scka-canon-payloads rows fn-arena)
           :in-theory (disable fn-scka-sealsp fn-scka-payload-of fn-row-wire-of))))

; The batches: payloads in order while the chunk stays within SEG octets
; (at least one per batch, so every payload is written whatever its size;
; the reader's segment admission is the bound, checked per frame).
(defun fn-scka-lens (ps)
  (declare (xargs :guard t))
  (if (atom ps) nil (cons (len (car ps)) (fn-scka-lens (cdr ps)))))

(defun fn-scka-enc-len (l)
  (declare (xargs :guard (natp l)))
  (+ (len (fn-scc-nat-octets l)) l))

(defun fn-scka-batch-count (lens seg acc)
  (declare (xargs :guard (and (nat-listp lens) (natp seg) (natp acc))))
  (if (atom lens)
      0
    (let ((e (+ (nfix acc) (fn-scka-enc-len (nfix (car lens))))))
      (if (and (< 0 (nfix acc)) (< (nfix seg) e))
          0
        (+ 1 (fn-scka-batch-count (cdr lens) seg e))))))

(defthm fn-scka-batch-count-bounds
  (and (<= (fn-scka-batch-count lens seg acc) (len lens))
       (implies (and (consp lens) (zp acc)) (< 0 (fn-scka-batch-count lens seg acc))))
  :rule-classes :linear)

(defun fn-scka-batches (lens seg)
  (declare (xargs :guard (and (nat-listp lens) (natp seg)) :measure (len lens)
                  :verify-guards nil))
  (if (atom lens)
      nil
    (let ((k (fn-scka-batch-count lens seg 0)))
      (cons k (fn-scka-batches (nthcdr k lens) seg)))))

(defthm fn-scka-sum-of-batches
  (equal (fn-scka-sum (fn-scka-batches lens seg)) (len lens))
  :hints (("Goal" :induct (fn-scka-batches lens seg))))

(defthm fn-scka-len-lens
  (equal (len (fn-scka-lens ps)) (len ps)))
