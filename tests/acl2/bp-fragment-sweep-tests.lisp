; Teeth of books/bp-fragment-sweep.lisp (PRF-121): the uncapped reassembler
; `fn-bpfw-reassemble`, the one the node's family query calls.  Witnesses
; above both old caps (a 70000-octet ADU, 100 fragments), out of order and
; overlapping; each outcome (:ok, :conflict, :missing, :invalid) against the
; index-wise spec; and, for the one keystone with hypotheses
; (fn-bpfw-exact-canvas-reassembles), a witness per hypothesis that keeps
; the other true, makes that one false, and falsifies the conclusion.
(in-package "ACL2")
(include-book "../../books/bp-fragment-sweep")
(include-book "std/testing/must-fail" :dir :system)

(defun bpfwt-payload (n acc)
  (declare (xargs :guard (and (natp n) (true-listp acc))))
  (if (zp n) acc (bpfwt-payload (1- n) (cons (mod n 251) acc))))

; Fragments of CHUNK octets from OFF, most recent first (so the list is in
; descending offset order: the sweep's sort is exercised).
(defun bpfwt-frags (payload off chunk total acc)
  (declare (xargs :guard (and (true-listp payload) (natp off) (posp chunk)
                              (natp total) (true-listp acc))
                  :measure (len payload)))
  (if (or (endp payload) (not (posp chunk)))
      acc
    (bpfwt-frags (nthcdr chunk payload) (+ off chunk) chunk total
                 (cons (fn-bpf-make off (take (min chunk (len payload)) payload)
                                    total)
                       acc))))

(defconst *bpfwt-big* (bpfwt-payload 70000 nil))
(defconst *bpfwt-big-frags* (bpfwt-frags *bpfwt-big* 0 700 70000 nil))
(defun bpfwt-big-canvas ()
  (declare (xargs :guard t :verify-guards nil))
  (with-guard-checking :none (fn-bpf-canvas *bpfwt-big-frags* 0 70000)))

; Above both caps: 70000 > 65538 octets, 100 > 64 fragments.
(assert-event (equal (len *bpfwt-big-frags*) 100))
(assert-event (fn-bpfw-inputsp *bpfwt-big-frags* 70000))
(assert-event (not (fn-bpf-inputsp *bpfwt-big-frags* 70000)))

; fn-bpfw-reassemble-is-spec and fn-bpf-reassemble-is-capped-spec: the
; executed reassembler answers the exact payload, the capped reference
; refuses the same family.
(assert-event (equal (fn-bpfw-reassemble *bpfwt-big-frags* 70000)
                     (list :ok *bpfwt-big*)))
(assert-event (equal (fn-bpf-reassemble *bpfwt-big-frags* 70000)
                     '(:invalid :bounds)))

; Overlap: every fragment twice, and a second cut at a different chunk
; size, all interleaved.  Identical overlap merges.
(defconst *bpfwt-overlap*
  (append *bpfwt-big-frags*
          (bpfwt-frags *bpfwt-big* 0 997 70000 nil)
          (reverse *bpfwt-big-frags*)))
(assert-event (equal (fn-bpfw-reassemble *bpfwt-overlap* 70000)
                     (list :ok *bpfwt-big*)))

; The small families, against the spec itself (the spec is logic mode and
; index-wise; it executes on these sizes).
(defconst *bpfwt-p* '(10 20 30 40 50 60 70 80))
(defconst *bpfwt-cut*
  (list '(:fn-bp-fragment 5 (60 70 80) 8)
        '(:fn-bp-fragment 0 (10 20 30) 8)
        '(:fn-bp-fragment 3 (40 50) 8)))
(defconst *bpfwt-conflict*
  (list '(:fn-bp-fragment 0 (10 20 30 40 50) 8)
        '(:fn-bp-fragment 4 (51 60 70 80) 8)))
(defconst *bpfwt-gap*
  (list '(:fn-bp-fragment 5 (60 70 80) 8)
        '(:fn-bp-fragment 0 (10 20 30) 8)))
; A conflict after a gap: the conflict is reported, as in the reference.
(defconst *bpfwt-both*
  (list '(:fn-bp-fragment 0 (10 20) 8)
        '(:fn-bp-fragment 5 (60 70 80) 8)
        '(:fn-bp-fragment 6 (71) 8)))
(defconst *bpfwt-wrong-total*
  (list '(:fn-bp-fragment 0 (10 20 30) 8)
        '(:fn-bp-fragment 3 (40 50 60 70 80) 9)))

(assert-event (equal (fn-bpfw-reassemble *bpfwt-cut* 8) (list :ok *bpfwt-p*)))
(assert-event (equal (fn-bpfw-reassemble *bpfwt-conflict* 8) '(:conflict 4)))
(assert-event (equal (fn-bpfw-reassemble *bpfwt-gap* 8) '(:missing 3 5)))
(assert-event (equal (fn-bpfw-reassemble *bpfwt-both* 8) '(:conflict 6)))
(assert-event (equal (fn-bpfw-reassemble *bpfwt-wrong-total* 8)
                     '(:invalid :bounds)))
(assert-event (equal (fn-bpfw-reassemble nil 8) '(:invalid :bounds)))
(assert-event (equal (fn-bpfw-reassemble *bpfwt-cut* 0) '(:invalid :bounds)))
(assert-event
 (and (equal (fn-bpfw-reassemble *bpfwt-cut* 8) (fn-bpfw-spec *bpfwt-cut* 8))
      (equal (fn-bpfw-reassemble *bpfwt-conflict* 8)
             (fn-bpfw-spec *bpfwt-conflict* 8))
      (equal (fn-bpfw-reassemble *bpfwt-gap* 8) (fn-bpfw-spec *bpfwt-gap* 8))
      (equal (fn-bpfw-reassemble *bpfwt-both* 8) (fn-bpfw-spec *bpfwt-both* 8))
      (equal (fn-bpfw-reassemble *bpfwt-wrong-total* 8)
             (fn-bpfw-spec *bpfwt-wrong-total* 8))))
; Within the caps the two references agree.
(assert-event (equal (fn-bpf-reassemble *bpfwt-cut* 8)
                     (fn-bpfw-spec *bpfwt-cut* 8)))
(must-fail (assert-event (equal (fn-bpfw-reassemble *bpfwt-gap* 8)
                                (list :ok *bpfwt-p*))))

; -----------------------------------------------------------------------------
; fn-bpfw-exact-canvas-reassembles
;
; Positive: both hypotheses hold and so does the conclusion (above the caps;
; the index-wise canvas runs in logic mode, its capped guard unchecked).
(assert-event
 (and (fn-bpfw-inputsp *bpfwt-big-frags* 70000)
      (fn-cbor-octet-listp (bpfwt-big-canvas))
      (equal (fn-bpfw-reassemble *bpfwt-big-frags* 70000)
             (list :ok (bpfwt-big-canvas)))))

; Without fn-bpfw-inputsp: total 0 gives an empty (octet) canvas, and the
; answer is a refusal, not (:ok nil).
(assert-event
 (and (not (fn-bpfw-inputsp *bpfwt-cut* 0))
      (fn-cbor-octet-listp (fn-bpf-canvas *bpfwt-cut* 0 0))
      (not (equal (fn-bpfw-reassemble *bpfwt-cut* 0)
                  (list :ok (fn-bpf-canvas *bpfwt-cut* 0 0))))))

; Without the octet canvas: a gapped family is well-formed input, and the
; answer is :missing, not (:ok canvas).
(assert-event
 (and (fn-bpfw-inputsp *bpfwt-gap* 8)
      (not (fn-cbor-octet-listp (fn-bpf-canvas *bpfwt-gap* 0 8)))
      (not (equal (fn-bpfw-reassemble *bpfwt-gap* 8)
                  (list :ok (fn-bpf-canvas *bpfwt-gap* 0 8))))))
