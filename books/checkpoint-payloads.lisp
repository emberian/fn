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
; payload, index 0 of count 1, sequence 0, with an EMPTY chain (prev = nil): its trailer is the frame digest of
; header ++ payload, the log entry's own frame check (fn-frame-digest of the
; protected prefix), so the extent path verifies it unchanged; it
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
; FACT, not defect: the reclaim plan copies a payload once per live REF; records
; do not share payloads today, and sharing (dedup) is CPL-DEDUP if ever wanted.
; The frame costs 69 octets (37 header + 32 trailer), so the compacted file is
; the live payload octets plus 69 per live ref.
;
;   `fn-cpl-compact file refs': the reclaim plan: the live payloads' frames in
;     a fresh file, and the ref map.

(in-package "ACL2")
(include-book "store-checkpoint-codec")
(include-book "checkpoint-payload-ref")
(include-book "store-checkpoint-buffer")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; 1. The frame, the ref, the open.

(defun fn-cpl-frame (payload)
  (declare (xargs :guard (true-listp payload) :verify-guards nil))
  (car (fn-scc-frames (list payload) 0 1 0 nil)))

; (fn-cpl-frame-octets n) is books/checkpoint-payload-ref.lisp's: 37 + n + 32.

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
; sequence 0, empty chain (its trailer verifies), and
; carries LEN octets.
(defun fn-cpl-open-seg (ref seg)
  (declare (xargs :guard (and (true-listp ref) (true-listp seg)) :verify-guards nil))
  (let ((o (fn-scc-open-segment seg 0 1 0 nil)))
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

; The frame's 32-octet trailer: the digest over the header
; and the payload.  A function of the payload alone (index 0 of 1, sequence 0).
(defun fn-cpl-trailer (p)
  (declare (xargs :guard (true-listp p) :verify-guards nil))
  (fn-scc-seal nil (fn-scc-header 0 1 (len p) 0) p))

(defun fn-cpl-trailers (ps)
  (declare (xargs :guard (true-list-listp ps) :verify-guards nil))
  (if (consp ps) (cons (fn-cpl-trailer (car ps)) (fn-cpl-trailers (cdr ps))) nil))

; Each trailer is the last 32 octets of its ref's frame in FILE.
(defun fn-cpl-trailers-at (refs trs file)
  (declare (xargs :guard (and (true-list-listp refs) (true-listp file)) :verify-guards nil))
  (if (consp refs)
      (and (consp trs)
           (equal (take 32 (nthcdr (- (fn-cpl-ref-end (car refs)) 32) file)) (car trs))
           (fn-cpl-trailers-at (cdr refs) (cdr trs) file))
    (null trs)))

; (list bytes refs trailers): the octets to append at the committed length L,
; the refs they will have, and each frame's trailer octets (the tape row
; carries them so an arena extent can be sealed without reading the file).
(defun fn-cpl-append-plan (l ps)
  (declare (xargs :guard (and (natp l) (true-list-listp ps)) :verify-guards nil))
  (list (fn-cpl-frames ps) (fn-cpl-refs l ps) (fn-cpl-trailers ps)))

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

(local
 (defthm cpl-frame-shape
   (equal (fn-cpl-frame p)
          (let ((h (fn-scc-header 0 1 (len p) 0)))
            (append h p (fn-scc-seal nil h p))))
   :hints (("Goal" :in-theory (enable fn-cpl-frame fn-scc-frames)))))

; The frame's layout: the 37-octet fn-scc header, the payload, the 32-octet
; trailer (the frame digest of header ++ payload).
(defthm fn-cpl-frame-layout
  (equal (fn-cpl-frame p)
         (append (fn-scc-header 0 1 (len p) 0) p (fn-cpl-trailer p)))
  :hints (("Goal" :use cpl-frame-shape
           :in-theory (e/d (fn-cpl-trailer) (cpl-frame-shape fn-cpl-frame))))
  :rule-classes nil)

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
            (and (fn-scc-octet-listp (fn-scc-seal nil h p))
                 (equal (len (fn-scc-seal nil h p)) 32)))
   :hints (("Goal" :use ((:instance cpl-seal-facts-gen (q nil)))))))

(local (defthm cpl-u64-len (equal (len (fn-scc-u64 n k)) (nfix k))
         :hints (("Goal" :in-theory (enable fn-scc-u64)))))
(local (defthm cpl-len-append (equal (len (append a b)) (+ (len a) (len b)))))
(defthm cpl-header-len (equal (len (fn-scc-header 0 1 l 0)) 37)
  :hints (("Goal" :in-theory (e/d (fn-scc-header cpl-u64-len) ()))))

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
                             (b (fn-scc-seal nil (fn-scc-header 0 1 (len p) 0) p)))
                  (:instance cpl-octets-append
                             (a (fn-scc-header 0 1 (len p) 0))
                             (b (append p (fn-scc-seal nil
                                                       (fn-scc-header 0 1 (len p) 0) p)))))))))

(local (defthm cpl-chunks-0 (equal (fn-scc-chunks p 0) (list p))
         :hints (("Goal" :in-theory (enable fn-scc-chunks)))))
(local (defthm cpl-frames-1
         (equal (fn-scc-frames (list p) 0 1 0 nil) (list (fn-cpl-frame p)))
         :hints (("Goal" :in-theory (enable fn-cpl-frame fn-scc-frames)))))

(local
 (defthm cpl-frame-opens
   (implies (fn-cpl-payloadp p)
            (and (fn-scc-open-segment (fn-cpl-frame p) 0 1 0 nil)
                 (equal (car (fn-scc-open-segment (fn-cpl-frame p) 0 1 0 nil)) p)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-scc-join-of-chunks (seg 0) (q 0) (prev nil))
                  (:instance cpl-join-single (seg (fn-cpl-frame p)) (q 0)
                             (prev nil) (x p))
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

; -----------------------------------------------------------------------------
; 6. Reclaim (CPL-3).  Facts about a verified read.

; A file the reclaim plan reads: octets, and short enough that a payload's
; length fits a frame header (no real file is 2^64 octets).
(defun fn-cpl-filep (f)
  (declare (xargs :guard t))
  (and (fn-scc-octet-listp f) (< (+ 1 (len f)) *fn-scc-u64-bound*)))

(local
 (defthm cpl-take-octets
   (implies (and (fn-scc-octet-listp x) (natp n) (<= n (len x)))
            (fn-scc-octet-listp (take n x)))
   :hints (("Goal" :induct (take n x)
            :in-theory (e/d (take fn-scc-octet-listp) (fn-scc-octet-listp-facts))))))

(local
 (defthm cpl-open-seg-facts
   (implies (and (fn-scc-octet-listp seg) (fn-cpl-open-seg ref seg))
            (and (fn-scc-octet-listp (car (fn-cpl-open-seg ref seg)))
                 (equal (len (car (fn-cpl-open-seg ref seg))) (fn-cpl-ref-len ref))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-scc-open-segment-chunk-octets (index 0) (count 1)
                             (sequence 0) (prev nil)))
            :in-theory (e/d (fn-cpl-open-seg)
                            (fn-scc-open-segment fn-scc-open-segment-chunk-octets))))))

(local
 (defthm cpl-open-seg-list
   (implies (fn-cpl-open-seg ref seg)
            (equal (fn-cpl-open-seg ref seg) (list (car (fn-cpl-open-seg ref seg)))))
   :hints (("Goal" :in-theory (enable fn-cpl-open-seg)))))
(local (in-theory (disable cpl-open-seg-list)))

(local
 (defthm cpl-open-seg-nil
   (not (fn-cpl-open-seg ref nil))
   :hints (("Goal" :in-theory (enable fn-cpl-open-seg fn-scc-open-segment
                                      fn-scc-parse-header fn-scc-long-enoughp)))))

(local
 (defthm cpl-win-facts
   (implies (and (fn-scc-octet-listp f) (natp s) (natp n) (cpl-win ref s n f))
            (and (equal (cpl-win ref s n f) (list (car (cpl-win ref s n f))))
                 (fn-scc-octet-listp (car (cpl-win ref s n f)))
                 (equal (len (car (cpl-win ref s n f))) (fn-cpl-ref-len ref))
                 (<= (+ s n) (len f))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance cpl-open-seg-facts (seg (take n (nthcdr s f))))
                  (:instance cpl-take-octets (x (nthcdr s f)))
                  (:instance cpl-open-seg-list (seg (take n (nthcdr s f)))))
            :in-theory (e/d (cpl-win cpl-long-enough cpl-len-nthcdr)
                            (cpl-open-seg-facts cpl-take-octets fn-cpl-open-seg))))))

(local
 (defthm cpl-open-facts
   (implies (and (fn-scc-octet-listp f) (< (+ 1 (len f)) 18446744073709551616)
                 (fn-cpl-open ref f))
            (and (fn-cpl-payloadp (car (fn-cpl-open ref f)))
                 (equal (fn-cpl-open ref f) (list (car (fn-cpl-open ref f))))
                 (equal (len (car (fn-cpl-open ref f))) (fn-cpl-ref-len ref))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance cpl-win-facts (s (fn-cpl-ref-start ref))
                             (n (fn-cpl-frame-octets (fn-cpl-ref-len ref)))))
            :in-theory (e/d (cpl-open-as-win fn-cpl-payloadp fn-cpl-frame-octets)
                            (cpl-win-facts cpl-win fn-cpl-open))))))

(local
 (defthm cpl-payloads-ok
   (implies (and (fn-cpl-filep f) (fn-cpl-all-openp refs f))
            (fn-cpl-payload-listp (fn-cpl-payloads-of refs f)))
   :hints (("Goal" :induct (fn-cpl-all-openp refs f) :in-theory (disable cpl-open-facts))
           (and stable-under-simplificationp
                '(:use ((:instance cpl-open-facts (ref (car refs))))
                  :in-theory (e/d (fn-cpl-filep) (cpl-open-facts)))))))

(local
 (defthm cpl-open-all-is-wrap
   (implies (and (fn-cpl-filep f) (fn-cpl-all-openp refs f))
            (equal (fn-cpl-open-all refs f) (fn-cpl-wrap (fn-cpl-payloads-of refs f))))
   :hints (("Goal" :induct (fn-cpl-all-openp refs f) :in-theory (disable cpl-open-facts))
           (and stable-under-simplificationp
                '(:use ((:instance cpl-open-facts (ref (car refs))))
                  :in-theory (e/d (fn-cpl-filep) (cpl-open-facts)))))))

(local
 (defthm cpl-payloads-delta
   (implies (and (fn-cpl-filep f) (fn-cpl-all-openp refs f))
            (equal (fn-cpl-delta-octets (fn-cpl-payloads-of refs f))
                   (+ (fn-cpl-ref-lens refs) (* 69 (len refs)))))
   :hints (("Goal" :induct (fn-cpl-all-openp refs f) :in-theory (disable cpl-open-facts))
           (and stable-under-simplificationp
                '(:use ((:instance cpl-open-facts (ref (car refs))))
                  :in-theory (e/d (fn-cpl-filep) (cpl-open-facts)))))))

; With the root switched atomically from (F, REFS) to (the fresh file, the
; map), every live ref answers the same payload before and after.
(defthm fn-cpl-compact-preserves-every-live-ref
  (implies (and (fn-cpl-filep f) (fn-cpl-all-openp refs f))
           (equal (fn-cpl-open-all (cadr (fn-cpl-compact-plan f refs))
                                   (car (fn-cpl-compact-plan f refs)))
                  (fn-cpl-open-all refs f)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance cpl-resolves-gen (pre nil) (post nil)
                            (ps (fn-cpl-payloads-of refs f)))
                 cpl-payloads-ok cpl-open-all-is-wrap)
           :in-theory (disable cpl-resolves-gen cpl-payloads-ok cpl-open-all-is-wrap))))

; The fresh file is the live payloads plus 69 octets of frame per live ref.
(defthm fn-cpl-compact-size
  (implies (and (fn-cpl-filep f) (fn-cpl-all-openp refs f))
           (equal (len (car (fn-cpl-compact-plan f refs)))
                  (+ (fn-cpl-ref-lens refs)
                     (* (+ *fn-scc-segment-header-octets* *fn-frame-trailer-octets*)
                        (len refs)))))
  :hints (("Goal" :do-not-induct t
           :use (cpl-payloads-ok cpl-payloads-delta
                 (:instance fn-cpl-frames-len (ps (fn-cpl-payloads-of refs f))))
           :in-theory (disable cpl-payloads-ok cpl-payloads-delta fn-cpl-frames-len))))

; A delta appended to the fresh file while the compaction ran.
(defthm fn-cpl-compact-concurrent-delta
  (implies (and (fn-cpl-filep f) (fn-cpl-all-openp refs f) (fn-cpl-payload-listp ps))
           (let* ((cp (fn-cpl-compact-plan f refs))
                  (nf (car cp))
                  (ap (fn-cpl-append-plan (len nf) ps))
                  (g (append nf (car ap))))
             (and (equal (fn-cpl-open-all (append (cadr cp) (cadr ap)) g)
                         (append (fn-cpl-open-all refs f) (fn-cpl-wrap ps)))
                  (equal (len g)
                         (+ (fn-cpl-ref-lens refs) (fn-cpl-ref-lens (cadr ap))
                            (* (+ *fn-scc-segment-header-octets* *fn-frame-trailer-octets*)
                               (+ (len refs) (len ps))))))))
  :hints (("Goal" :do-not-induct t
           :use (cpl-payloads-ok cpl-payloads-delta fn-cpl-compact-preserves-every-live-ref
                 (:instance fn-cpl-frames-len (ps (fn-cpl-payloads-of refs f)))
                 (:instance fn-cpl-frames-len)
                 (:instance fn-cpl-crash-new-root-after-durable-append
                            (f (fn-cpl-frames (fn-cpl-payloads-of refs f)))
                            (r0 (fn-cpl-refs 0 (fn-cpl-payloads-of refs f))))
                 (:instance fn-cpl-refs-covered (l 0) (ps (fn-cpl-payloads-of refs f))
                            (c (fn-cpl-delta-octets (fn-cpl-payloads-of refs f))))
                 (:instance fn-cpl-append-plan-is-the-delta
                            (l (fn-cpl-delta-octets (fn-cpl-payloads-of refs f))))
                 (:instance cpl-frames-tl (ps (fn-cpl-payloads-of refs f))))
           :in-theory (disable cpl-payloads-ok cpl-payloads-delta fn-cpl-frames-len
                               fn-cpl-compact-preserves-every-live-ref fn-cpl-refs-covered
                               cpl-frames-tl)))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; 7. The trailer.

(defthm fn-cpl-trailer-shape
  (implies (fn-cpl-payloadp p)
           (and (fn-scc-octet-listp (fn-cpl-trailer p))
                (equal (len (fn-cpl-trailer p)) 32)))
  :hints (("Goal" :use ((:instance cpl-seal-facts (h (fn-scc-header 0 1 (len p) 0)) (p p)))
           :in-theory (e/d (fn-cpl-trailer fn-cpl-payloadp)
                           (cpl-seal-facts fn-scc-header fn-scc-seal)))))

(local
 (defthm cpl-frame-trailer-at
   (implies (fn-cpl-payloadp p)
            (equal (nthcdr (+ 37 (len p)) (fn-cpl-frame p)) (fn-cpl-trailer p)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance cpl-frame-shape)
                  (:instance cpl-nthcdr-append (a (append (fn-scc-header 0 1 (len p) 0) p))
                             (b (fn-cpl-trailer p))))
            :in-theory (e/d (fn-cpl-trailer)
                            (cpl-nthcdr-append cpl-frame-shape fn-scc-header fn-scc-seal))))))

(local (defthm cpl-nthcdr-sum
         (implies (and (natp a) (natp b))
                  (equal (nthcdr (+ a b) x) (nthcdr b (nthcdr a x))))
         :hints (("Goal" :induct (nthcdr a x)))))
(local (defthm cpl-nthcdr-app
         (implies (and (natp k) (<= k (len a)))
                  (equal (nthcdr k (append a b)) (append (nthcdr k a) b)))
         :hints (("Goal" :induct (nthcdr k a)))))

; The frame's last 32 octets, wherever the frame sits in a file.
(defthm fn-cpl-trailer-in-file
   (implies (and (true-listp pre) (true-listp post) (fn-cpl-payloadp p))
            (equal (take 32 (nthcdr (+ (len pre) 37 (len p))
                                    (append pre (fn-cpl-frame p) post)))
                   (fn-cpl-trailer p)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance cpl-nthcdr-sum (a (len pre)) (b (+ 37 (len p)))
                             (x (append pre (fn-cpl-frame p) post)))
                  (:instance cpl-nthcdr-app (k (+ 37 (len p))) (a (fn-cpl-frame p)) (b post))
                  cpl-frame-trailer-at fn-cpl-trailer-shape fn-cpl-frame-len
                  (:instance cpl-take-len-append (f (fn-cpl-trailer p)) (z post)))
            :in-theory (e/d (fn-cpl-frame-octets)
                            (cpl-nthcdr-sum cpl-nthcdr-app cpl-frame-trailer-at
                                            fn-cpl-trailer-shape fn-cpl-frame-len
                                            cpl-take-len-append cpl-take-append)))))

(local
 (defthm cpl-trailers-step
   (implies (and (true-listp pre) (true-listp post) (fn-cpl-payloadp p)
                 (fn-cpl-trailers-at (fn-cpl-refs (len (append pre (fn-cpl-frame p))) ps)
                                     (fn-cpl-trailers ps)
                                     (append (append pre (fn-cpl-frame p))
                                             (fn-cpl-frames ps) post)))
            (fn-cpl-trailers-at (fn-cpl-refs (len pre) (cons p ps))
                                (fn-cpl-trailers (cons p ps))
                                (append pre (fn-cpl-frames (cons p ps)) post)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-cpl-frames fn-cpl-refs fn-cpl-trailers fn-cpl-trailers-at
                                           cpl-len-append fn-cpl-ref-end fn-cpl-ref-offset
                                           fn-cpl-ref-len)
                            (fn-cpl-payloadp))
            :use ((:instance fn-cpl-trailer-in-file (post (append (fn-cpl-frames ps) post)))
                  (:instance fn-cpl-frame-len))))))

(local
 (defthm cpl-trailers-gen
   (implies (and (true-listp pre) (true-listp post) (fn-cpl-payload-listp ps))
            (fn-cpl-trailers-at (fn-cpl-refs (len pre) ps) (fn-cpl-trailers ps)
                                (append pre (fn-cpl-frames ps) post)))
   :hints (("Goal" :induct (fn-cpl-frames-ind pre ps)
            :do-not '(generalize eliminate-destructors))
           ("Subgoal *1/1"
            :use ((:instance cpl-trailers-step (p (car ps)) (ps (cdr ps)))
                  (:instance cpl-frame-tl2 (p (car ps))))
            :in-theory (disable cpl-trailers-step fn-cpl-trailer-in-file fn-cpl-refs
                                fn-cpl-frames fn-cpl-trailers fn-cpl-trailers-at)))))

; The plan's trailers are the last 32 octets of each frame in the file after
; the append.
(defthm fn-cpl-append-plan-trailers
  (implies (and (true-listp f) (fn-cpl-payload-listp ps))
           (fn-cpl-trailers-at (cadr (fn-cpl-append-plan (len f) ps))
                               (caddr (fn-cpl-append-plan (len f) ps))
                               (append f (car (fn-cpl-append-plan (len f) ps)))))
  :hints (("Goal" :use ((:instance cpl-trailers-gen (pre f) (post nil)))
           :in-theory (disable cpl-trailers-gen))))

; -----------------------------------------------------------------------------
; 8. The trailer as four u64 words, big-endian (the tape row's form).
; Word i is octets [8i, 8i+8) of the trailer, most significant octet first.

(defun fn-cpl-trailer-word-count () (declare (xargs :guard t)) 4)

(defun fn-cpl-be-fold (xs acc)
  (declare (xargs :guard (and (true-listp xs) (natp acc))))
  (if (consp xs)
      (fn-cpl-be-fold (cdr xs) (+ (* 256 (nfix acc)) (nfix (car xs))))
    (nfix acc)))

(defun fn-cpl-be-octets (w n)
  (declare (xargs :guard (and (natp w) (natp n))))
  (if (zp n)
      nil
    (append (fn-cpl-be-octets (floor (nfix w) 256) (1- n)) (list (mod (nfix w) 256)))))

(defun fn-cpl-pack-words (tr n)
  (declare (xargs :guard (and (true-listp tr) (natp n))))
  (if (zp n)
      nil
    (cons (fn-cpl-be-fold (take 8 tr) 0) (fn-cpl-pack-words (nthcdr 8 tr) (1- n)))))

(defun fn-cpl-unpack-words (ws)
  (declare (xargs :guard (true-listp ws)))
  (if (consp ws)
      (append (fn-cpl-be-octets (nfix (car ws)) 8) (fn-cpl-unpack-words (cdr ws)))
    nil))

(defun fn-cpl-trailer-words-impl (p)
  (declare (xargs :guard (fn-cpl-payloadp p) :verify-guards nil))
  (fn-cpl-pack-words (fn-cpl-trailer p) (fn-cpl-trailer-word-count)))

(defun fn-cpl-ub64-listp (ws)
  (declare (xargs :guard t))
  (if (consp ws)
      (and (unsigned-byte-p 64 (car ws)) (fn-cpl-ub64-listp (cdr ws)))
    (null ws)))

(local
 (defthm cpl-be-octets-snoc
   (implies (and (natp v) (natp x) (< x 256) (natp n))
            (equal (fn-cpl-be-octets (+ (* 256 v) x) (+ 1 n))
                   (append (fn-cpl-be-octets v n) (list x))))
   :hints (("Goal" :expand ((fn-cpl-be-octets (+ (* 256 v) x) (+ 1 n)))))))

(local (defun cpl-ind3 (xs acc k)
         (declare (xargs :verify-guards nil))
         (if (consp xs)
             (cpl-ind3 (cdr xs) (+ (* 256 (nfix acc)) (nfix (car xs))) (+ 1 (nfix k)))
           (list acc k))))

(local
 (defthm cpl-be-fold-roundtrip
   (implies (and (fn-scc-octet-listp xs) (natp acc) (natp k))
            (equal (fn-cpl-be-octets (fn-cpl-be-fold xs acc) (+ k (len xs)))
                   (append (fn-cpl-be-octets acc k) xs)))
   :hints (("Goal" :induct (cpl-ind3 xs acc k)
            :in-theory (e/d (fn-scc-octet-listp fn-scc-octetp)
                            (fn-cpl-be-octets fn-scc-octet-listp-facts)))
           (and stable-under-simplificationp
                '(:use ((:instance cpl-be-octets-snoc (v acc) (x (car xs)) (n k))))))))

(local (defun cpl-ind5 (xs acc b)
         (declare (xargs :verify-guards nil))
         (if (consp xs)
             (cpl-ind5 (cdr xs) (+ (* 256 (nfix acc)) (nfix (car xs))) (* 256 (nfix b)))
           (list acc b))))

(local
 (defthm cpl-be-fold-bound
   (implies (and (fn-scc-octet-listp xs) (natp acc) (posp b) (< acc b))
            (< (fn-cpl-be-fold xs acc) (* b (expt 256 (len xs)))))
   :hints (("Goal" :induct (cpl-ind5 xs acc b)
            :in-theory (e/d (fn-scc-octet-listp fn-scc-octetp) (fn-scc-octet-listp-facts))))))

(local
 (defthm cpl-slice
   (implies (and (fn-scc-octet-listp xs) (equal (len xs) 8))
            (equal (fn-cpl-be-octets (fn-cpl-be-fold xs 0) 8) xs))
   :hints (("Goal" :use ((:instance cpl-be-fold-roundtrip (acc 0) (k 0)))
            :in-theory (disable cpl-be-fold-roundtrip)))))

(local (defthm cpl-append-take-nthcdr
         (implies (and (natp n) (<= n (len x))) (equal (append (take n x) (nthcdr n x)) x))))
(local (defthm cpl-nthcdr-octets
         (implies (fn-scc-octet-listp x) (fn-scc-octet-listp (nthcdr n x)))))
(local (defthm cpl-len-nthcdr2
         (implies (natp k) (equal (len (nthcdr k x)) (nfix (- (len x) k))))
         :hints (("Goal" :induct (nthcdr k x)))))
(local (defthm cpl-len-take (implies (and (natp n) (<= n (len x))) (equal (len (take n x)) n))))

(local
 (defthm cpl-slice-at
   (implies (and (fn-scc-octet-listp tr) (natp k) (<= (+ k 8) (len tr)))
            (equal (fn-cpl-be-octets (fn-cpl-be-fold (take 8 (nthcdr k tr)) 0) 8)
                   (take 8 (nthcdr k tr))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance cpl-slice (xs (take 8 (nthcdr k tr))))
                  (:instance cpl-take-octets (x (nthcdr k tr)) (n 8))
                  (:instance cpl-nthcdr-octets (x tr) (n k))
                  (:instance cpl-len-nthcdr2 (x tr))
                  (:instance cpl-len-take (n 8) (x (nthcdr k tr))))
            :in-theory (disable cpl-slice cpl-take-octets cpl-len-nthcdr2 cpl-nthcdr-octets
                                cpl-len-take)))))

(local
 (defthm cpl-len0
   (implies (and (fn-scc-octet-listp tr) (equal (len tr) 0)) (equal tr nil))
   :hints (("Goal" :in-theory (enable fn-scc-octet-listp)))
   :rule-classes nil))

(local
 (defthm cpl-pack-unpack
   (implies (and (fn-scc-octet-listp tr) (natp n) (equal (len tr) (* 8 n)))
            (equal (fn-cpl-unpack-words (fn-cpl-pack-words tr n)) tr))
   :hints (("Goal" :induct (fn-cpl-pack-words tr n) :in-theory (disable cpl-slice-at))
           (and stable-under-simplificationp
                '(:use ((:instance cpl-slice-at (k 0))
                        (:instance cpl-append-take-nthcdr (n 8) (x tr))
                        (:instance cpl-nthcdr-octets (x tr) (n 8))
                        (:instance cpl-len-nthcdr2 (x tr) (k 8))
                        (:instance cpl-len0))
                  :in-theory (disable cpl-slice-at cpl-append-take-nthcdr cpl-nthcdr-octets
                                      cpl-len-nthcdr2))))))

(local
 (defthm cpl-pack-ub64
   (implies (and (fn-scc-octet-listp tr) (natp n) (equal (len tr) (* 8 n)))
            (and (fn-cpl-ub64-listp (fn-cpl-pack-words tr n))
                 (equal (len (fn-cpl-pack-words tr n)) n)))
   :hints (("Goal" :induct (fn-cpl-pack-words tr n) :in-theory (disable cpl-be-fold-bound))
           (and stable-under-simplificationp
                '(:use ((:instance cpl-be-fold-bound (xs (take 8 tr)) (acc 0) (b 1))
                        (:instance cpl-take-octets (x tr) (n 8))
                        (:instance cpl-nthcdr-octets (x tr) (n 8))
                        (:instance cpl-len-nthcdr2 (x tr) (k 8))
                        (:instance cpl-len-take (x tr) (n 8)))
                  :in-theory (e/d (unsigned-byte-p integer-range-p)
                                  (cpl-be-fold-bound cpl-take-octets cpl-nthcdr-octets
                                                     cpl-len-nthcdr2 cpl-len-take)))))))

; Unpacking the words gives the trailer.
(defthm fn-cpl-trailer-words-pack
  (implies (fn-cpl-payloadp p)
           (equal (fn-cpl-unpack-words (fn-cpl-trailer-words-impl p)) (fn-cpl-trailer p)))
  :hints (("Goal" :use (fn-cpl-trailer-shape
                        (:instance cpl-pack-unpack (tr (fn-cpl-trailer p))
                                   (n (fn-cpl-trailer-word-count))))
           :in-theory (e/d (fn-cpl-trailer-word-count fn-cpl-trailer-words-impl)
                           (cpl-pack-unpack fn-cpl-trailer-shape fn-cpl-trailer
                                            fn-cpl-pack-words fn-cpl-unpack-words)))))

; The constraints of books/checkpoint-payload-ref.lisp's encapsulated
; fn-cpl-trailer-words (fn-cpl-trailer-words-shape), instanced at the
; implementation.
(defthm fn-cpl-trailer-words-impl-shape
  (implies (fn-cpl-payloadp p)
           (and (true-listp (fn-cpl-trailer-words-impl p))
                (consp (fn-cpl-trailer-words-impl p))
                (equal (len (fn-cpl-trailer-words-impl p)) 4)
                (unsigned-byte-p 64 (car (fn-cpl-trailer-words-impl p)))
                (unsigned-byte-p 64 (cadr (fn-cpl-trailer-words-impl p)))
                (unsigned-byte-p 64 (caddr (fn-cpl-trailer-words-impl p)))
                (unsigned-byte-p 64 (cadddr (fn-cpl-trailer-words-impl p)))))
  :hints (("Goal" :use (fn-cpl-trailer-shape
                        (:instance cpl-pack-ub64 (tr (fn-cpl-trailer p))
                                   (n (fn-cpl-trailer-word-count))))
           :in-theory (e/d (fn-cpl-trailer-word-count fn-cpl-trailer-words-impl fn-cpl-ub64-listp)
                           (cpl-pack-ub64 fn-cpl-trailer-shape fn-cpl-trailer
                                          fn-cpl-pack-words)))))

; -----------------------------------------------------------------------------
; 9. The executable: the frames written through the buffer.  No octet list is
; built for the file: the header (37 octets) and the trailer (32) are the small
; lists, the payload is appended as given (the arena-to-buffer copy without a
; transient list waits on the arena's inner-octet read, as
; fn-scka-append-src does).

(verify-guards fn-cpl-trailer)
(verify-guards fn-cpl-trailers)

(defun fn-cpl-write-frame (p fn-octets)
  (declare (xargs :stobjs fn-octets :guard (fn-cpl-payloadp p) :verify-guards nil))
  (let* ((fn-octets (fn-sccb-append-list (fn-scc-header 0 1 (len p) 0) fn-octets))
         (fn-octets (fn-sccb-append-list p fn-octets))
         (fn-octets (fn-sccb-append-list (fn-cpl-trailer p) fn-octets)))
    fn-octets))

(defun fn-cpl-write-frames (ps fn-octets)
  (declare (xargs :stobjs fn-octets :guard (fn-cpl-payload-listp ps) :verify-guards nil))
  (if (consp ps)
      (let ((fn-octets (fn-cpl-write-frame (car ps) fn-octets)))
        (fn-cpl-write-frames (cdr ps) fn-octets))
    fn-octets))

(verify-guards fn-cpl-write-frame
  :hints (("Goal" :use (fn-cpl-trailer-shape cpl-header-octets)
           :in-theory (disable fn-cpl-trailer-shape cpl-header-octets))))
(verify-guards fn-cpl-write-frames)

(defthm fn-cpl-write-frame-is-the-frame
  (implies (fn-cpl-payloadp p)
           (equal (fn-cpl-write-frame p fn-octets)
                  (append fn-octets (fn-cpl-frame p))))
  :hints (("Goal" :in-theory (e/d (fn-cpl-write-frame fn-cpl-trailer cpl-frame-shape)
                                  (fn-cpl-frame fn-scc-header fn-scc-seal)))))

(local (defthm cpl-tl-append (equal (true-listp (append a b)) (true-listp b))))

(local
 (defthm cpl-wf-step
   (implies (and (true-listp fn-octets) (fn-cpl-payloadp p)
                 (equal (fn-cpl-write-frames ps (append fn-octets (fn-cpl-frame p)))
                        (append fn-octets (fn-cpl-frame p) (fn-cpl-frames ps))))
            (equal (fn-cpl-write-frames (cons p ps) fn-octets)
                   (append fn-octets (fn-cpl-frames (cons p ps)))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-cpl-write-frames fn-cpl-frames)
                            (fn-cpl-write-frame fn-cpl-frame fn-cpl-payloadp))
            :use ((:instance fn-cpl-write-frame-is-the-frame))))))

(local
 (defthm cpl-wf-frames
   (implies (and (fn-cpl-payload-listp ps) (true-listp fn-octets))
            (equal (fn-cpl-write-frames ps fn-octets)
                   (append fn-octets (fn-cpl-frames ps))))
   :hints (("Goal" :induct (fn-cpl-write-frames ps fn-octets)
            :do-not '(generalize eliminate-destructors)
            :in-theory (disable fn-cpl-write-frame fn-cpl-payloadp))
           ("Subgoal *1/1"
            :use ((:instance cpl-wf-step (p (car ps)) (ps (cdr ps))))
            :in-theory (e/d (fn-cpl-payload-listp)
                            (cpl-wf-step fn-cpl-write-frame fn-cpl-frame fn-cpl-payloadp))))))

; The buffer after the writer is the buffer followed by the plan's bytes.
(defthm fn-cpl-write-frames-is-the-plan
  (implies (and (natp l) (fn-cpl-payload-listp ps) (true-listp fn-octets))
           (equal (fn-cpl-write-frames ps fn-octets)
                  (append fn-octets (car (fn-cpl-append-plan l ps)))))
  :hints (("Goal" :use cpl-wf-frames :in-theory (disable cpl-wf-frames))))

(verify-guards fn-cpl-trailer-words-impl
  :hints (("Goal" :use (fn-cpl-trailer-shape)
           :in-theory (e/d (fn-cpl-trailer-word-count) (fn-cpl-trailer-shape fn-cpl-trailer)))))

; -----------------------------------------------------------------------------
; 10. The read bridge: a frame in the payload file is a log-entry frame the
; extent path verifies unchanged.
;
; The extent realizer (host/native/extent.lisp fnn-extent-entry) reads the
; entry's protected prefix [EOFF, EOFF+ELEN) into a buffer and the 32 octets
; after it, and decides fn-arx-entry-verdict-buffer: :ok exactly when the
; frame digest of the prefix is the trailer read and the trailer is the
; descriptor's commitment.  A payload frame is that entry: the prefix is
; header ++ payload (EOFF = ref offset - 37, ELEN = 37 + len, POFF = 37,
; PLEN = len) and the trailer is the frame digest of the prefix, because the
; chain is empty.

(defun fn-cpl-prefix (p)
  (declare (xargs :guard (true-listp p) :verify-guards nil))
  (append (fn-scc-header 0 1 (len p) 0) p))

(defthm fn-cpl-trailer-is-the-frame-digest
  (implies (fn-cpl-payloadp p)
           (equal (fn-cpl-trailer p) (fn-frame-digest (fn-cpl-prefix p))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance cpl-octets-append (a (fn-scc-header 0 1 (len p) 0)) (b p))
                 (:instance cpl-cbor-octets (x (append (fn-scc-header 0 1 (len p) 0) p)))
                 (:instance fn-frame-trailer-of-octets
                            (octets (append (fn-scc-header 0 1 (len p) 0) p))))
           :in-theory (e/d (fn-cpl-trailer fn-cpl-prefix fn-cpl-payloadp fn-scc-seal)
                           (cpl-octets-append cpl-cbor-octets fn-frame-trailer-of-octets
                                              fn-scc-header)))))

(defthm fn-cpl-prefix-in-file
  (implies (and (true-listp pre) (true-listp post) (fn-cpl-payloadp p))
           (equal (take (+ 37 (len p))
                        (nthcdr (len pre) (append pre (fn-cpl-frame p) post)))
                  (fn-cpl-prefix p)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance cpl-take-append (a (fn-cpl-prefix p))
                            (b (append (fn-scc-seal nil (fn-scc-header 0 1 (len p) 0) p) post))
                            (k (+ 37 (len p)))))
           :in-theory (e/d (fn-cpl-prefix cpl-frame-shape)
                           (cpl-take-append fn-scc-header fn-scc-seal
                                            fn-cpl-trailer-is-the-frame-digest)))))

