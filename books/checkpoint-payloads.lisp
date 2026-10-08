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

; The payload at REF in FILE, as (list octets), or NIL: the frame lies wholly
; in FILE, parses at index 0 of 1, carries LEN octets, and its trailer verifies.
(defun fn-cpl-open (ref file)
  (declare (xargs :guard (and (true-listp ref) (true-listp file)) :verify-guards nil))
  (let* ((n (fn-cpl-frame-octets (fn-cpl-ref-len ref)))
         (rest (nthcdr (fn-cpl-ref-start ref) file))
         (o (and (<= *fn-scc-segment-header-octets* (fn-cpl-ref-offset ref))
                 (fn-scc-long-enoughp n rest)
                 (fn-scc-open-segment (take n rest) 0 1 0 *fn-scc-genesis*))))
    (and o (equal (len (car o)) (fn-cpl-ref-len ref))
         (list (car o)))))

; A payload the file can hold: an octet list whose length fits a frame header.
(defun fn-cpl-payloadp (p)
  (declare (xargs :guard t))
  (and (true-listp p) (fn-scc-octet-listp p) (< (len p) *fn-scc-u64-bound*)))

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
