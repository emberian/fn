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
;; The reader's two octet-list rules rewrite into each other, and the
;; parameter-record identity lemmas fire on every list: off everywhere here.
(local (in-theory (disable fn-cp-idp fn-cp-idp-true-listp
                           fn-sccr-scc-octet-listp-is-cbor-octet-listp
                           fn-sccr-cbor-octet-listp-is-scc-octet-listp)))

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
