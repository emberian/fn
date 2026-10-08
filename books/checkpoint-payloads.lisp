; fn: the durable payload file of the paged checkpoint (lane s-cpl, 2026-10-07;
; D27, D41-STAGE5-ONE-ROW-IMAGE).
;
; The paged checkpoint's tape rows carry metadata and a payload REF, not the
; payload octets (books/checkpoint-payload-ref.lisp, s-pck-host): the page
; image is one flat in-heap array, so octets in the tape put the whole store
; in anon.  The octets live in an append-only file `<store>/checkpoint.payloads`.
;
; The file is a concatenation of FRAMES.  A frame is the schema-3 segment
; codec's one frame (books/store-checkpoint-codec.lisp fn-scc-frames) of one
; payload, index 0 of count 1, sequence 0, chained from the genesis trailer: it
; is self-contained, so a frame is read and verified at its own offset.
; A ref is (offset len) as in books/checkpoint-payload-ref.lisp, offset the
; payload's first octet (the frame's start + 37), len its octet count; the frame
; is 37 + len + 32 octets.
;
;   `fn-cpl-open ref file': the payload octets when the frame at the ref's
;     offset is whole, well-formed, carries LEN octets and its trailer verifies;
;     else NIL.  (The host realizes a ref by the same path: one bounded read of
;     the frame, the extent digest check.)
;   `fn-cpl-plan L payloads': the append plan for a delta: the frames' octets
;     and the refs, at offset L.
;   `fn-cpl-compact file refs': the reclaim plan: the live payloads' frames in
;     a fresh file, and the ref map.

(in-package "ACL2")
(include-book "store-checkpoint-codec")
(include-book "checkpoint-payload-ref")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; 1. The frame, the ref, the open.

(defun fn-cpl-frame (payload)
  (declare (xargs :guard (true-listp payload) :verify-guards nil))
  (car (fn-scc-frames (list payload) 0 1 0 *fn-scc-genesis*)))

; The octets a frame of an n-octet payload occupies.
(defun fn-cpl-frame-octets (n)
  (declare (xargs :guard (natp n)))
  (+ *fn-scc-segment-header-octets* (nfix n) *fn-frame-trailer-octets*))

; A ref (books/checkpoint-payload-ref.lisp) names the payload's OCTETS inside
; its frame: offset = frame start + the header, len = the payload's count.
; fn-cpl-resolve answers those octets without the frame's trailer; fn-cpl-open
; is the verified read.
(defun fn-cpl-ref-offset (ref) (declare (xargs :guard (true-listp ref))) (nfix (nth 0 ref)))
(defun fn-cpl-ref-len (ref) (declare (xargs :guard (true-listp ref))) (nfix (nth 1 ref)))
(defun fn-cpl-ref-start (ref)       ; the frame's first octet
  (declare (xargs :guard (true-listp ref)))
  (nfix (- (fn-cpl-ref-offset ref) *fn-scc-segment-header-octets*)))
(defun fn-cpl-ref-end (ref)         ; one past the frame's last octet
  (declare (xargs :guard (true-listp ref)))
  (+ (fn-cpl-ref-offset ref) (fn-cpl-ref-len ref) *fn-frame-trailer-octets*))

; The payload a frame SEG answers for REF: SEG is well-formed at index 0 of 1,
; sequence 0, chained from the genesis trailer (its trailer verifies), and
; carries LEN octets.
(defun fn-cpl-open-seg (ref seg)
  (declare (xargs :guard (and (true-listp ref) (true-listp seg)) :verify-guards nil))
  (let ((o (fn-scc-open-segment seg 0 1 0 *fn-scc-genesis*)))
    (and o (equal (len (car o)) (fn-cpl-ref-len ref))
         (list (car o)))))

; The payload at REF in FILE, as (list octets), or NIL: the frame lies wholly
; in FILE and verifies.
(defun fn-cpl-open (ref file)
  (declare (xargs :guard (and (true-listp ref) (true-listp file)) :verify-guards nil))
  (let* ((n (fn-cpl-frame-octets (fn-cpl-ref-len ref)))
         (rest (nthcdr (fn-cpl-ref-start ref) file)))
    (and (<= *fn-scc-segment-header-octets* (fn-cpl-ref-offset ref))
         (fn-scc-long-enoughp n rest)
         (fn-cpl-open-seg ref (take n rest)))))

; A payload the file can hold: an octet list whose length fits a frame header.
(defun fn-cpl-payloadp (p)
  (declare (xargs :guard t))
  (and (true-listp p) (fn-scc-octet-listp p) (< (+ 1 (len p)) *fn-scc-u64-bound*)))

(defun fn-cpl-payload-listp (ps)
  (declare (xargs :guard t))
  (if (consp ps)
      (and (fn-cpl-payloadp (car ps)) (fn-cpl-payload-listp (cdr ps)))
    (null ps)))

; -----------------------------------------------------------------------------
; 2. The append plan.  The frames of the delta, and the refs at offset L.

(defun fn-cpl-frames (ps)
  (declare (xargs :guard (true-list-listp ps) :verify-guards nil))
  (if (consp ps)
      (append (fn-cpl-frame (car ps)) (fn-cpl-frames (cdr ps)))
    nil))

(defun fn-cpl-refs (offset ps)
  (declare (xargs :guard (and (natp offset) (true-list-listp ps))))
  (if (consp ps)
      (cons (fn-cpl-ref (+ offset *fn-scc-segment-header-octets*) (len (car ps)))
            (fn-cpl-refs (+ offset (fn-cpl-frame-octets (len (car ps)))) (cdr ps)))
    nil))

; The octets of the delta's frames: payload octets plus the frame overhead per
; payload; no term in the file's length.
(defun fn-cpl-delta-octets (ps)
  (declare (xargs :guard (true-list-listp ps)))
  (if (consp ps)
      (+ (fn-cpl-frame-octets (len (car ps))) (fn-cpl-delta-octets (cdr ps)))
    0))

; (list bytes refs): the octets to append at the committed length L, and the
; refs they will have.
(defun fn-cpl-append-plan (l ps)
  (declare (xargs :guard (and (natp l) (true-list-listp ps)) :verify-guards nil))
  (list (fn-cpl-frames ps) (fn-cpl-refs l ps)))

(defun fn-cpl-open-all (refs file)
  (declare (xargs :guard (and (true-list-listp refs) (true-listp file)) :verify-guards nil))
  (if (consp refs)
      (cons (fn-cpl-open (car refs) file) (fn-cpl-open-all (cdr refs) file))
    nil))

; (list p1 p2 ...) -> ((p1) (p2) ...): what open-all answers for a faithful ref list.
(defun fn-cpl-wrap (ps)
  (declare (xargs :guard t))
  (if (consp ps) (cons (list (car ps)) (fn-cpl-wrap (cdr ps))) nil))

; Every ref lies wholly below C.
(defun fn-cpl-refs-coveredp (refs c)
  (declare (xargs :guard (and (true-list-listp refs) (natp c))))
  (if (consp refs)
      (and (<= (fn-cpl-ref-end (car refs)) c) (fn-cpl-refs-coveredp (cdr refs) c))
    t))

; A root's claim: committed length C over a file of at least C durable octets,
; every ref below C.
(defun fn-cpl-durable-rootp (c refs file)
  (declare (xargs :guard (and (natp c) (true-list-listp refs) (true-listp file))))
  (and (<= c (len file)) (fn-cpl-refs-coveredp refs c)))

; -----------------------------------------------------------------------------
; 3. Reclaim.

(defun fn-cpl-all-openp (refs file)
  (declare (xargs :guard (and (true-list-listp refs) (true-listp file)) :verify-guards nil))
  (if (consp refs)
      (and (fn-cpl-open (car refs) file) (fn-cpl-all-openp (cdr refs) file))
    t))

; The payloads the refs name (NIL for a dead ref).
(defun fn-cpl-payloads-of (refs file)
  (declare (xargs :guard (and (true-list-listp refs) (true-listp file)) :verify-guards nil))
  (if (consp refs)
      (cons (car (fn-cpl-open (car refs) file)) (fn-cpl-payloads-of (cdr refs) file))
    nil))

(defun fn-cpl-ref-lens (refs)
  (declare (xargs :guard (true-list-listp refs)))
  (if (consp refs)
      (+ (fn-cpl-ref-len (car refs)) (fn-cpl-ref-lens (cdr refs)))
    0))

; (list bytes map): the live frames in a fresh file, and where each live ref went.
(defun fn-cpl-compact-plan (file refs)
  (declare (xargs :guard (and (true-listp file) (true-list-listp refs)) :verify-guards nil))
  (let ((ps (fn-cpl-payloads-of refs file)))
    (list (fn-cpl-frames ps) (fn-cpl-refs 0 ps))))

; -----------------------------------------------------------------------------
; 4. The frame's shape.

(local (include-book "store-checkpoint-buffer"))

(local
 (defthm cpl-frame-shape
   (equal (fn-cpl-frame p)
          (let ((h (fn-scc-header 0 1 (len p) 0)))
            (append h p (fn-scc-seal *fn-scc-genesis* h p))))
   :hints (("Goal" :in-theory (enable fn-cpl-frame fn-scc-frames)))))

(local
 (defthm cpl-u64-octets (fn-scc-octet-listp (fn-scc-u64 n k))
   :hints (("Goal" :in-theory (enable fn-scc-u64 fn-scc-octetp)))))

(local
 (defthm cpl-octets-append
   (implies (and (fn-scc-octet-listp a) (fn-scc-octet-listp b))
            (fn-scc-octet-listp (append a b)))
   :hints (("Goal" :induct (fn-scc-octet-listp a)
            :in-theory (e/d (fn-scc-octet-listp) (fn-scc-octet-listp-facts))))))

(local
 (defthm cpl-header-octets (fn-scc-octet-listp (fn-scc-header 0 1 l 0))
   :hints (("Goal" :in-theory (enable fn-scc-header fn-scc-octetp)))))

(local
 (defthm cpl-cbor-octets
   (implies (fn-scc-octet-listp x) (fn-cbor-octet-listp x))
   :hints (("Goal" :induct (fn-scc-octet-listp x)
            :in-theory (e/d (fn-scc-octet-listp fn-sccb-scc-octetp-is-cbor-octetp)
                            (fn-scc-octet-listp-facts))))))

(local
 (defthm cpl-cbor-scc
   (implies (fn-cbor-octet-listp x) (fn-scc-octet-listp x))
   :hints (("Goal" :induct (fn-cbor-octet-listp x)
            :in-theory (e/d (fn-scc-octet-listp fn-cbor-octet-listp
                                                fn-sccb-scc-octetp-is-cbor-octetp)
                            (fn-scc-octet-listp-facts))))))

(local
 (defthm cpl-trailer-facts
   (implies (fn-cbor-octet-listp x)
            (and (fn-scc-octet-listp (fn-frame-trailer x))
                 (equal (len (fn-frame-trailer x)) 32)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-frame-trailer-is-a-digest (octets x))
                  (:instance cpl-cbor-scc (x (fn-frame-trailer x))))
            :in-theory (e/d (fn-frame-digestp)
                            (fn-frame-trailer-is-a-digest cpl-cbor-scc))))))

(local (defthm cpl-tlf (implies (true-listp x) (equal (true-list-fix x) x))))

(local
 (defthm cpl-seal-facts-gen
   (implies (and (fn-scc-octet-listp q) (fn-scc-octet-listp h) (fn-scc-octet-listp p))
            (and (fn-scc-octet-listp (fn-scc-seal q h p))
                 (equal (len (fn-scc-seal q h p)) 32)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance cpl-trailer-facts (x (append q h p)))
                  (:instance cpl-cbor-octets (x (append q h p)))
                  (:instance cpl-octets-append (a h) (b p))
                  (:instance cpl-octets-append (a q) (b (append h p))))
            :in-theory (e/d (fn-scc-seal)
                            (cpl-trailer-facts cpl-cbor-octets cpl-octets-append))))))

(local
 (defthm cpl-seal-facts
   (implies (and (fn-scc-octet-listp h) (fn-scc-octet-listp p))
            (and (fn-scc-octet-listp (fn-scc-seal *fn-scc-genesis* h p))
                 (equal (len (fn-scc-seal *fn-scc-genesis* h p)) 32)))
   :hints (("Goal" :use ((:instance cpl-seal-facts-gen (q *fn-scc-genesis*)))))))

(local (defthm cpl-u64-len (equal (len (fn-scc-u64 n k)) (nfix k))
         :hints (("Goal" :in-theory (enable fn-scc-u64)))))
(local (defthm cpl-len-append (equal (len (append a b)) (+ (len a) (len b)))))
(local (defthm cpl-header-len (equal (len (fn-scc-header 0 1 l 0)) 37)
         :hints (("Goal" :in-theory (e/d (fn-scc-header cpl-u64-len) ())))))

(defthm fn-cpl-frame-len
  (implies (fn-cpl-payloadp p)
           (equal (len (fn-cpl-frame p)) (fn-cpl-frame-octets (len p))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cpl-frame-octets fn-cpl-payloadp cpl-frame-shape)
                           (fn-cpl-frame fn-scc-frames (fn-scc-header) (fn-scc-seal)))
           :use ((:instance cpl-seal-facts (h (fn-scc-header 0 1 (len p) 0)) (p p))))))

(local (defthm cpl-rr-gen
         (equal (revappend (revappend a b) c) (revappend b (append a c)))))
(local (defthm cpl-rr
         (implies (true-listp a) (equal (revappend (revappend a nil) nil) a))
         :hints (("Goal" :use ((:instance cpl-rr-gen (b nil) (c nil)))
                  :in-theory (disable cpl-rr-gen)))))

(local
 (defthm cpl-join-single
   (implies (and (fn-scc-octet-listp seg)
                 (equal (fn-scc-join (list seg) 0 1 q prev nil) (list :ok x)))
            (and (fn-scc-open-segment seg 0 1 q prev)
                 (equal (car (fn-scc-open-segment seg 0 1 q prev)) x)))
   :hints (("Goal" :expand ((fn-scc-join (list seg) 0 1 q prev nil))
            :use ((:instance fn-scc-open-segment-facts (index 0) (count 1) (sequence q)))
            :in-theory (disable fn-scc-open-segment fn-scc-open-segment-facts)))))

(local
 (defthm cpl-frame-octets-p
   (implies (fn-cpl-payloadp p) (fn-scc-octet-listp (fn-cpl-frame p)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-cpl-payloadp cpl-frame-shape)
                            (fn-cpl-frame fn-scc-frames (fn-scc-header) (fn-scc-seal)))
            :use ((:instance cpl-seal-facts (h (fn-scc-header 0 1 (len p) 0)) (p p))
                  (:instance cpl-octets-append
                             (a p)
                             (b (fn-scc-seal *fn-scc-genesis* (fn-scc-header 0 1 (len p) 0) p)))
                  (:instance cpl-octets-append
                             (a (fn-scc-header 0 1 (len p) 0))
                             (b (append p (fn-scc-seal *fn-scc-genesis*
                                                       (fn-scc-header 0 1 (len p) 0) p)))))))))

(local (defthm cpl-chunks-0 (equal (fn-scc-chunks p 0) (list p))
         :hints (("Goal" :in-theory (enable fn-scc-chunks)))))
(local (defthm cpl-frames-1
         (equal (fn-scc-frames (list p) 0 1 0 *fn-scc-genesis*) (list (fn-cpl-frame p)))
         :hints (("Goal" :in-theory (enable fn-cpl-frame fn-scc-frames)))))

(local
 (defthm cpl-frame-opens
   (implies (fn-cpl-payloadp p)
            (and (fn-scc-open-segment (fn-cpl-frame p) 0 1 0 *fn-scc-genesis*)
                 (equal (car (fn-scc-open-segment (fn-cpl-frame p) 0 1 0 *fn-scc-genesis*)) p)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-scc-join-of-chunks (seg 0) (q 0) (prev *fn-scc-genesis*))
                  (:instance cpl-join-single (seg (fn-cpl-frame p)) (q 0)
                             (prev *fn-scc-genesis*) (x p))
                  (:instance cpl-frame-octets-p))
            :in-theory (e/d (fn-cpl-payloadp cpl-chunks-0 cpl-frames-1)
                            (fn-cpl-frame fn-scc-frames fn-scc-open-segment
                             cpl-join-single cpl-frame-octets-p))))))

(local (defthm cpl-nthcdr-append (equal (nthcdr (len a) (append a b)) b)))
(local (defthm cpl-take-append
         (implies (and (true-listp a) (equal k (len a))) (equal (take k (append a b)) a))))
(local (defthm cpl-long-enough
         (implies (natp n) (equal (fn-scc-long-enoughp n xs) (<= n (len xs))))))

; The verified read of the frame appended at PRE.
(defthm fn-cpl-open-of-frame
  (implies (and (true-listp pre) (fn-cpl-payloadp p) (true-listp post))
           (equal (fn-cpl-open (list (+ 37 (len pre)) (len p))
                               (append pre (fn-cpl-frame p) post))
                  (list p)))
  :hints (("Goal" :do-not-induct t
           :expand ((fn-cpl-open (list (+ 37 (len pre)) (len p))
                                 (append pre (fn-cpl-frame p) post)))
           :use ((:instance fn-cpl-frame-len) (:instance cpl-frame-opens)
                 (:instance cpl-frame-octets-p)
                 (:instance cpl-take-append (a (fn-cpl-frame p)) (b post)
                            (k (fn-cpl-frame-octets (len p)))))
           :in-theory (e/d (fn-cpl-ref-start fn-cpl-ref-offset fn-cpl-ref-len
                                       cpl-long-enough)
                           (fn-cpl-frame fn-cpl-frame-len cpl-frame-opens cpl-frame-octets-p
                                         cpl-take-append fn-scc-open-segment
                                         (fn-cpl-frame-octets))))))

(local (defun cpl-ind (s x y c)
         (if (zp s) (list x y c) (cpl-ind (1- s) (cdr x) (cdr y) (1- c)))))
(local
 (defthm cpl-window
   (implies (and (natp s) (natp n) (natp c) (<= (+ s n) c)
                 (equal (take c x) (take c y)) (<= c (len x)) (<= c (len y)))
            (equal (take n (nthcdr s x)) (take n (nthcdr s y))))
   :hints (("Goal" :induct (cpl-ind s x y c)))))

(local (defun cpl-win (ref s n x)
         (and (fn-scc-long-enoughp n (nthcdr s x))
              (fn-cpl-open-seg ref (take n (nthcdr s x))))))
(local (defthm cpl-len-nthcdr
         (implies (natp s) (equal (len (nthcdr s x)) (nfix (- (len x) s))))
         :hints (("Goal" :induct (nthcdr s x)))))
(local
 (defthm cpl-win-equal
   (implies (and (natp s) (natp n) (natp c) (<= (+ s n) c)
                 (equal (take c x) (take c y)) (<= c (len x)) (<= c (len y)))
            (equal (cpl-win ref s n x) (cpl-win ref s n y)))
   :hints (("Goal" :do-not-induct t :use cpl-window
            :in-theory (e/d (cpl-long-enough) (cpl-window fn-cpl-open-seg))))))
(local
 (defthm cpl-open-as-win
   (equal (fn-cpl-open ref x)
          (and (<= 37 (fn-cpl-ref-offset ref))
               (cpl-win ref (fn-cpl-ref-start ref)
                        (fn-cpl-frame-octets (fn-cpl-ref-len ref)) x)))
   :hints (("Goal" :in-theory (e/d (fn-cpl-open cpl-win) (fn-cpl-open-seg))))))
(local
 (defthm cpl-end-bound
   (implies (<= 37 (fn-cpl-ref-offset ref))
            (equal (+ (fn-cpl-ref-start ref) (fn-cpl-frame-octets (fn-cpl-ref-len ref)))
                   (fn-cpl-ref-end ref)))
   :hints (("Goal" :in-theory (enable fn-cpl-ref-start fn-cpl-ref-end)))))

; A ref whose frame lies below C answers the same in any two files that agree
; on their first C octets (a shorter cut, a garbage or zero tail).
(defthm fn-cpl-open-ignores-the-tail
  (implies (and (natp c) (equal (take c x) (take c y)) (<= c (len x)) (<= c (len y))
                (<= (fn-cpl-ref-end ref) c))
           (equal (fn-cpl-open ref x) (fn-cpl-open ref y)))
  :hints (("Goal" :do-not-induct t
           :cases ((<= 37 (fn-cpl-ref-offset ref)))
           :use ((:instance cpl-win-equal (s (fn-cpl-ref-start ref))
                            (n (fn-cpl-frame-octets (fn-cpl-ref-len ref)))))
           :in-theory (disable cpl-win-equal fn-cpl-open fn-cpl-open-seg cpl-win
                               fn-cpl-ref-start fn-cpl-ref-end fn-cpl-ref-offset
                               fn-cpl-ref-len fn-cpl-frame-octets)))
  :rule-classes nil)

(defthm fn-cpl-committed-refs-ignore-the-tail
  (implies (and (natp c) (true-listp x) (true-listp y)
                (equal (take c x) (take c y))
                (<= c (len x)) (<= c (len y))
                (fn-cpl-refs-coveredp refs c))
           (equal (fn-cpl-open-all refs x) (fn-cpl-open-all refs y)))
  :hints (("Goal" :induct (fn-cpl-open-all refs x)
           :in-theory (disable fn-cpl-open cpl-open-as-win cpl-len-nthcdr cpl-end-bound))
          (and stable-under-simplificationp
               '(:use ((:instance fn-cpl-open-ignores-the-tail (ref (car refs))))))))

(local (in-theory (disable cpl-frame-shape cpl-frames-1 cpl-chunks-0 cpl-open-as-win
                           cpl-len-nthcdr cpl-end-bound cpl-long-enough
                           fn-cpl-open fn-cpl-frame)))

; -----------------------------------------------------------------------------
; 5. The append plan.

(defun fn-cpl-frames-ind (pre ps)
  (declare (xargs :verify-guards nil))
  (if (consp ps) (fn-cpl-frames-ind (append pre (fn-cpl-frame (car ps))) (cdr ps)) pre))

(local (defthm cpl-append-assoc (equal (append (append a b) c) (append a b c))))

(local
 (defthm cpl-frames-octets-p
   (implies (fn-cpl-payload-listp ps) (fn-scc-octet-listp (fn-cpl-frames ps)))))

(defthm fn-cpl-frames-len
  (implies (fn-cpl-payload-listp ps)
           (equal (len (fn-cpl-frames ps)) (fn-cpl-delta-octets ps))))

(local (defthm cpl-frame-tl
         (implies (fn-cpl-payloadp p) (true-listp (fn-cpl-frame p)))
         :hints (("Goal" :use cpl-frame-octets-p :in-theory (disable cpl-frame-octets-p)))))
(local (defthm cpl-frame-tl2
         (implies (and (fn-scc-octet-listp p) (< (+ 1 (len p)) 18446744073709551616))
                  (true-listp (fn-cpl-frame p)))
         :hints (("Goal" :use cpl-frame-tl :in-theory (enable fn-cpl-payloadp)))))
(local (defthm cpl-frames-tl
         (implies (fn-cpl-payload-listp ps) (true-listp (fn-cpl-frames ps)))
         :hints (("Goal" :use cpl-frames-octets-p :in-theory (disable cpl-frames-octets-p)))))
(local (defthm cpl-take-len (implies (true-listp x) (equal (take (len x) x) x))))
(local (defthm cpl-take-len-append
         (implies (true-listp f) (equal (take (len f) (append f z)) f))
         :hints (("Goal" :use ((:instance cpl-take-append (a f) (b z) (k (len f))))))))

(local
 (defthm cpl-resolves-step
   (implies (and (true-listp pre) (true-listp post) (fn-cpl-payloadp p)
                 (equal (fn-cpl-open-all (fn-cpl-refs (len (append pre (fn-cpl-frame p))) ps)
                                         (append (append pre (fn-cpl-frame p))
                                                 (fn-cpl-frames ps) post))
                        (fn-cpl-wrap ps)))
            (equal (fn-cpl-open-all (fn-cpl-refs (len pre) (cons p ps))
                                    (append pre (fn-cpl-frames (cons p ps)) post))
                   (fn-cpl-wrap (cons p ps))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-cpl-frames fn-cpl-refs fn-cpl-open-all fn-cpl-wrap cpl-len-append)
                            (fn-cpl-payloadp))
            :use ((:instance fn-cpl-open-of-frame (post (append (fn-cpl-frames ps) post)))
                  (:instance fn-cpl-frame-len))))))

(local
 (defthm cpl-resolves-gen
   (implies (and (true-listp pre) (true-listp post) (fn-cpl-payload-listp ps))
            (equal (fn-cpl-open-all (fn-cpl-refs (len pre) ps) (append pre (fn-cpl-frames ps) post))
                   (fn-cpl-wrap ps)))
   :hints (("Goal" :induct (fn-cpl-frames-ind pre ps)
            :do-not '(generalize eliminate-destructors))
           ("Subgoal *1/1"
            :use ((:instance cpl-resolves-step (p (car ps)) (ps (cdr ps)))
                  (:instance cpl-frame-tl2 (p (car ps))))
            :in-theory (disable cpl-resolves-step fn-cpl-open-of-frame fn-cpl-open-all
                                fn-cpl-refs fn-cpl-frames fn-cpl-wrap)))))

; CPL-1.  The plan is the delta's frames, O(delta): the bytes take no L, the
; length is the frames' (payload octets + 69 per payload), the refs lie wholly
; below L + delta.
(defthm fn-cpl-delta-is-lens-plus-overhead
  (implies (natp l)
           (equal (fn-cpl-delta-octets ps)
                  (+ (fn-cpl-ref-lens (fn-cpl-refs l ps)) (* 69 (len ps)))))
  :hints (("Goal" :induct (fn-cpl-refs l ps)))
  :rule-classes nil)

(defthm fn-cpl-refs-covered
  (implies (and (natp l) (natp c) (<= (+ l (fn-cpl-delta-octets ps)) c))
           (fn-cpl-refs-coveredp (fn-cpl-refs l ps) c))
  :hints (("Goal" :induct (fn-cpl-refs l ps))))

(defthm fn-cpl-append-plan-is-the-delta
  (implies (and (natp l) (fn-cpl-payload-listp ps))
           (and (equal (car (fn-cpl-append-plan l ps)) (fn-cpl-frames ps))
                (equal (len (car (fn-cpl-append-plan l ps))) (fn-cpl-delta-octets ps))
                (equal (fn-cpl-delta-octets ps)
                       (+ (fn-cpl-ref-lens (cadr (fn-cpl-append-plan l ps)))
                          (* (+ *fn-scc-segment-header-octets* *fn-frame-trailer-octets*)
                             (len ps))))
                (equal (cadr (fn-cpl-append-plan l ps)) (fn-cpl-refs l ps))
                (fn-cpl-refs-coveredp (cadr (fn-cpl-append-plan l ps))
                                      (+ l (fn-cpl-delta-octets ps)))))
  :hints (("Goal" :use ((:instance fn-cpl-delta-is-lens-plus-overhead)
                        (:instance fn-cpl-refs-covered (c (+ l (fn-cpl-delta-octets ps))))
                        fn-cpl-frames-len)
           :in-theory (disable fn-cpl-refs-covered fn-cpl-frames-len)))
  :rule-classes nil)

(defthm fn-cpl-append-plan-resolves
  (implies (and (true-listp f) (fn-cpl-payload-listp ps))
           (equal (fn-cpl-open-all (cadr (fn-cpl-append-plan (len f) ps))
                                   (append f (car (fn-cpl-append-plan (len f) ps))))
                  (fn-cpl-wrap ps)))
  :hints (("Goal" :use ((:instance cpl-resolves-gen (pre f) (post nil)))
           :in-theory (disable cpl-resolves-gen)))
  :rule-classes nil)

(local (defthm cpl-open-all-append
         (equal (fn-cpl-open-all (append a b) x)
                (append (fn-cpl-open-all a x) (fn-cpl-open-all b x)))))

; CPL-2.  Crash.
(local
 (defthm cpl-prefix-stable
   (implies (and (true-listp f) (true-listp z) (fn-cpl-refs-coveredp r (len f)))
            (equal (fn-cpl-open-all r (append f z)) (fn-cpl-open-all r f)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-cpl-committed-refs-ignore-the-tail
                             (c (len f)) (x (append f z)) (y f) (refs r)))
            :in-theory (disable fn-cpl-committed-refs-ignore-the-tail)))))

(defthm fn-cpl-crash-keeps-the-old-root
  (implies (and (true-listp f) (fn-cpl-payload-listp ps)
                (fn-cpl-refs-coveredp r0 (len f))
                (natp k) (<= k (fn-cpl-delta-octets ps)))
           (equal (fn-cpl-open-all r0 (append f (take k (car (fn-cpl-append-plan (len f) ps)))))
                  (fn-cpl-open-all r0 f)))
  :hints (("Goal" :use ((:instance cpl-prefix-stable (z (take k (fn-cpl-frames ps))) (r r0)))
           :in-theory (disable cpl-prefix-stable)))
  :rule-classes nil)

(defthm fn-cpl-crash-new-root-after-durable-append
  (implies (and (true-listp f) (fn-cpl-payload-listp ps)
                (fn-cpl-refs-coveredp r0 (len f)))
           (equal (fn-cpl-open-all (append r0 (cadr (fn-cpl-append-plan (len f) ps)))
                                   (append f (car (fn-cpl-append-plan (len f) ps))))
                  (append (fn-cpl-open-all r0 f) (fn-cpl-wrap ps))))
  :hints (("Goal" :use ((:instance cpl-prefix-stable (z (fn-cpl-frames ps)) (r r0))
                        fn-cpl-append-plan-resolves)
           :in-theory (disable cpl-prefix-stable)))
  :rule-classes nil)
