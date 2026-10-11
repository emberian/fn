; fn: witnesses for books/runtime-contract-host-send.lisp (the host lease's send range, the
; in-place render as the contract's :write request, and no write under an outstanding send).
;
; What this book is evidence FOR.  The three keystones are not vacuous and have teeth, on a
; layer state the contract's invariant holds of (`*rths-s*': one connection slot live at
; incarnation 1, pool buffer 0 its workspace holding "AB", pool buffer 1 :out-leased to its
; outstanding :send of the three octets "HIJ"), with `*rths-c*' the concrete stobj (one octet
; array, buffer h at base(h)) that the abstract state is the abstraction of:
;  - HL1 fn-rtc-host-send-range-is-the-lease: the array range the host writes for the send is
;    the lease's octets; a removal per hypothesis (a concrete array that does not correspond,
;    a use past the buffer's fill the invariant refuses, a use the table does not hold, an
;    :in use whose window runs past the fill) and a mutation (a range that ignores the offset).
;  - HL1b fn-hl-splice-keeps-out-use-bytes: a splice into the workspace leaves the sent buffer;
;    a removal per hypothesis (a send naming a workspace the invariant refuses, a use the table
;    does not hold, an :in use whose buffer a landing splices) and a mutation (the spliced
;    buffer itself).
;  - HL3 fn-rtc-puts-is-the-write-request: putting a window octet by octet into the workspace
;    is the :write request's state; a removal per hypothesis and a mutation (the puts leave
;    the state).
; The invariant is evaluated through this book's concrete copy of the layer's contract
; functions (`rths-model-invp', the copy `fn-rtc-layer-copies' makes for a constant,
; non-committing machine), as tests/acl2/runtime-contract-landing-tests.lisp does; the
; keystones' fn-rtc-invp is the copy's functional instance.
;
; The seeded counterexample search over random scenes is build/vertical-runs/host-lease/
; search.lsp in the lane; its counts are in that file's header.

(in-package "ACL2")
(include-book "../../books/runtime-contract-host-send")
(include-book "../../books/runtime-contract-layer")
; HL4 carries its teeth in its own book; this root certifies it.
(include-book "../../books/runtime-contract-host-pool")
(include-book "std/testing/assert-bang" :dir :system)

(defun rths-init () (declare (xargs :guard t)) nil)
(defun rths-static-init (j) (declare (xargs :guard t) (ignore j)) nil)
(defun rths-step (m ev pool q) (declare (xargs :guard t) (ignore m ev pool q)) (mv nil nil 0))
(defun rths-committedp (m) (declare (xargs :guard t) (ignore m)) nil)
(defun rths-c () (declare (xargs :guard t)) 0)
(defun rths-max-reqs () (declare (xargs :guard t)) 0)
(defun rths-max-state () (declare (xargs :guard t)) 1)
(make-event
 (let* ((machine '((fn-rtc-m-init . rths-init) (fn-rtc-m-static-init . rths-static-init)
                   (fn-rtc-m-step . rths-step) (fn-rtc-m-committedp . rths-committedp)
                   (fn-rtc-m-c . rths-c) (fn-rtc-m-max-reqs . rths-max-reqs)
                   (fn-rtc-m-max-state . rths-max-state)))
        (copies (fn-rtc-layer-alist 'rths-model *fn-rtc-layer-spec-fns*))
        (alist (append machine copies)))
   (cons 'progn (fn-rtc-layer-copies *fn-rtc-layer-spec-fns* :spec alist (w state)))))

; ---------------------------------------------------------------------------
; The scenes.  Configuration: 2 slots, 2 buffers, no home buffers, a pool of two
; 8-octet buffers (base 0 and 8 in the array).
(defconst *rths-cfg* '(2 2 8 0 0 2 8))

(defun rths-scene (b1-owner b0 b1 uses nop)
  (declare (xargs :guard t))
  (list *rths-cfg* '((0 :live nil) (1 :live 5))
        (list (list 3 '(:workspace 1 1) b0) (list 4 b1-owner b1))
        uses '(nil nil) nop))

(defun rths-pad (l n)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil (cons (if (consp l) (car l) 0) (rths-pad (if (consp l) (cdr l) nil) (- n 1)))))

; The concrete stobj the scene is the abstraction of: the array holds each buffer's octets at
; its base, zero beyond its fill.
(defun rths-concrete (s)
  (declare (xargs :guard t :verify-guards nil))
  (let ((p (fn-rtc-pool s)))
    (list (fn-rtc-config s) (fn-rtc-slots s) (fn-rtc-mstates s)
          (list (list (fn-rtc-get 0 (nth 0 p)) (fn-rtc-get 1 (nth 0 p)) (len (fn-rtc-get 2 (nth 0 p))))
                (list (fn-rtc-get 0 (nth 1 p)) (fn-rtc-get 1 (nth 1 p)) (len (fn-rtc-get 2 (nth 1 p)))))
          (append (rths-pad (fn-rtc-get 2 (nth 0 p)) 8) (rths-pad (fn-rtc-get 2 (nth 1 p)) 8))
          (fn-rtc-uses s) (fn-rtc-next-op s))))

(defconst *rths-send* '(:send 1 1 1 (1 4 0 3)))
(defconst *rths-s* (rths-scene '(:leased 1 1 :out) '(65 66) '(72 73 74) (list *rths-send*) 2))
(defconst *rths-c* (rths-concrete *rths-s*))
; the send of the two octets at offset 1
(defconst *rths-send-1* '(:send 1 1 1 (1 4 1 2)))
(defconst *rths-s-1* (rths-scene '(:leased 1 1 :out) '(65 66) '(72 73 74) (list *rths-send-1*) 2))
; a send whose window runs past the buffer's fill
(defconst *rths-send-past* '(:send 1 1 1 (1 4 0 5)))
(defconst *rths-s-past* (rths-scene '(:leased 1 1 :out) '(65 66) '(72 73 74) (list *rths-send-past*) 2))
; buffer 1 :in-leased to an outstanding receive into [0, 5)
(defconst *rths-recv* '(:recv 1 1 1 (1 4 0 5)))
(defconst *rths-r* (rths-scene '(:leased 1 1 :in) '(65 66) '(72 73 74) (list *rths-recv*) 2))
; buffer 1 a workspace while a send names it
(defconst *rths-s-ws* (rths-scene '(:workspace 1 1) '(65 66) '(72 73 74) (list *rths-send*) 2))

(assert! (rths-model-invp *rths-s*))
(assert! (rths-model-invp *rths-s-1*))
(assert! (rths-model-invp *rths-r*))
(assert! (not (rths-model-invp *rths-s-past*)))
(assert! (not (rths-model-invp *rths-s-ws*)))
(assert! (fn-rtc-st$corr *rths-c* *rths-s*))

; ---------------------------------------------------------------------------
; HL1: fn-rtc-host-send-range-is-the-lease.
(defun rths-hl1-concl (c s u)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((hd (fn-rtc-u-hd u)) (h (fn-rtc-h-buf hd)))
    (equal (fn-rtc-c-octets (+ (fn-rtc-buf-base h (fn-rtc-config s)) (fn-rtc-h-off hd))
                            (fn-rtc-h-len hd) (nth *fn-rtc-c-bytesi* c))
           (take (fn-rtc-h-len hd) (nthcdr (fn-rtc-h-off hd) (fn-rtc-b-bytes (fn-rtc-buffer h s)))))))
(defun rths-hl1-hyps (c s u)
  (declare (xargs :guard t :verify-guards nil))
  (list (fn-rtc-st$corr c s) (rths-model-invp s) (and (member-equal u (fn-rtc-uses s)) t)
        (and (member-eq (fn-rtc-get 0 u) *fn-rtc-out-kinds*) t)))

; positive: every hypothesis, and the range is "HIJ"
(assert! (and (equal (rths-hl1-hyps *rths-c* *rths-s* *rths-send*) '(t t t t))
              (rths-hl1-concl *rths-c* *rths-s* *rths-send*)
              (equal (fn-rtc-c-octets 8 3 (nth *fn-rtc-c-bytesi* *rths-c*)) '(72 73 74))))
; corr removed: an array whose octet at base(1) is not the buffer's
(defconst *rths-c-bad* (update-nth *fn-rtc-c-bytesi*
                                   (update-nth 8 0 (nth *fn-rtc-c-bytesi* *rths-c*)) *rths-c*))
(assert! (and (equal (rths-hl1-hyps *rths-c-bad* *rths-s* *rths-send*) '(nil t t t))
              (not (rths-hl1-concl *rths-c-bad* *rths-s* *rths-send*))))
; invp removed: a send past the fill sends the array's zeros, not the lease's octets
(assert! (and (equal (rths-hl1-hyps (rths-concrete *rths-s-past*) *rths-s-past* *rths-send-past*)
                     '(t nil t t))
              (not (rths-hl1-concl (rths-concrete *rths-s-past*) *rths-s-past* *rths-send-past*))))
; member removed: a send the table does not hold, past the fill
(assert! (and (equal (rths-hl1-hyps *rths-c* *rths-s* '(:send 1 1 9 (1 4 1 5))) '(t t nil t))
              (not (rths-hl1-concl *rths-c* *rths-s* '(:send 1 1 9 (1 4 1 5))))))
; out-kind removed: an outstanding receive's window runs past the fill
(assert! (and (equal (rths-hl1-hyps (rths-concrete *rths-r*) *rths-r* *rths-recv*) '(t t t nil))
              (not (rths-hl1-concl (rths-concrete *rths-r*) *rths-r* *rths-recv*))))
; mutation: a range that starts at the buffer's base, ignoring the offset, is not the lease's
(assert! (let* ((c (rths-concrete *rths-s-1*)) (hd (fn-rtc-u-hd *rths-send-1*)))
           (and (equal (rths-hl1-hyps c *rths-s-1* *rths-send-1*) '(t t t t))
                (rths-hl1-concl c *rths-s-1* *rths-send-1*)
                (not (equal (fn-rtc-c-octets (fn-rtc-buf-base 1 *rths-cfg*) (fn-rtc-h-len hd)
                                             (nth *fn-rtc-c-bytesi* c))
                            (take (fn-rtc-h-len hd) (nthcdr (fn-rtc-h-off hd) '(72 73 74))))))))

; ---------------------------------------------------------------------------
; HL1b: fn-hl-splice-keeps-out-use-bytes.
(defun rths-hl1b-concl (s u h2 off data)
  (declare (xargs :guard t))
  (equal (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) (fn-rtc-st$a-splice h2 off data s))
         (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s)))
(defun rths-hl1b-hyps (s u)
  (declare (xargs :guard t :verify-guards nil))
  (list (rths-model-invp s) (and (member-equal u (fn-rtc-uses s)) t)
        (and (member-eq (fn-rtc-get 0 u) *fn-rtc-out-kinds*) t)))

; positive: a render into the workspace lands and the sent buffer is unchanged
(assert! (and (equal (rths-hl1b-hyps *rths-s* *rths-send*) '(t t t))
              (rths-hl1b-concl *rths-s* *rths-send* 0 2 '(67))
              (equal (fn-rtc-buffer 0 (fn-rtc-st$a-splice 0 2 '(67) *rths-s*)) '(3 (:workspace 1 1) (65 66 67)))))
; invp removed: a send naming a workspace; a render into it moves the sent octets
(assert! (and (equal (rths-hl1b-hyps *rths-s-ws* *rths-send*) '(nil t t))
              (not (rths-hl1b-concl *rths-s-ws* *rths-send* 1 0 '(9)))))
; member removed: a send the table does not hold, naming the workspace
(assert! (and (equal (rths-hl1b-hyps *rths-s* '(:send 1 1 9 (0 3 0 2))) '(t nil t))
              (not (rths-hl1b-concl *rths-s* '(:send 1 1 9 (0 3 0 2)) 0 1 '(9)))))
; out-kind removed: the landing of a receive changes its own buffer
(assert! (and (equal (rths-hl1b-hyps *rths-r* *rths-recv*) '(t t nil))
              (not (rths-hl1b-concl *rths-r* *rths-recv* 1 3 '(9)))))
; mutation: the spliced buffer's own bytes change
(assert! (not (equal (fn-rtc-buffer 0 (fn-rtc-st$a-splice 0 2 '(67) *rths-s*)) (fn-rtc-buffer 0 *rths-s*))))

; ---------------------------------------------------------------------------
; HL3: fn-rtc-puts-is-the-write-request.
(defun rths-hl3-concl (h off w s id inc g)
  (declare (xargs :guard t))
  (mv-let (s2 acts refused cost) (fn-rtc-req-write (list :write h g off w) id inc s)
    (declare (ignore acts refused cost))
    (equal (fn-rtc-st$a-puts h off w s) s2)))
(defun rths-hl3-hyps (h off w s id inc g)
  (declare (xargs :guard t))
  (let ((b (fn-rtc-buffer h s)))
    (list (consp w) (equal (fn-rtc-b-owner b) (list :workspace id inc))
          (natp g) (equal (fn-rtc-get 0 b) g) (natp off) (fn-cbor-octet-listp w)
          (<= (+ (rfix off) (len w)) (fn-rtc-buf-cap h (fn-rtc-config s))))))
(defconst *rths-hl3-all* '(t t t t t t t))

; positive: "CD" rendered at offset 2 of the workspace is the :write request's state
(assert! (and (equal (rths-hl3-hyps 0 2 '(67 68) *rths-s* 1 1 3) *rths-hl3-all*)
              (rths-hl3-concl 0 2 '(67 68) *rths-s* 1 1 3)
              (equal (fn-rtc-buffer 0 (fn-rtc-st$a-puts 0 2 '(67 68) *rths-s*))
                     '(3 (:workspace 1 1) (65 66 67 68)))))
; consp removed: the empty window over a buffer record that is not three fields; the
; request rebuilds the record, the puts leave it
(defconst *rths-s-4* (list *rths-cfg* '((0 :live nil) (1 :live 5))
                           '((3 (:workspace 1 1) (65 66) :extra) (4 (:leased 1 1 :out) (72 73 74)))
                           (list *rths-send*) '(nil nil) 2))
(assert! (and (equal (rths-hl3-hyps 0 2 nil *rths-s-4* 1 1 3) '(nil t t t t t t))
              (not (rths-hl3-concl 0 2 nil *rths-s-4* 1 1 3))))
; owner removed: another instance's workspace takes the puts, the request is refused
(assert! (and (equal (rths-hl3-hyps 0 2 '(67) *rths-s* 2 1 3) '(t nil t t t t t))
              (not (rths-hl3-concl 0 2 '(67) *rths-s* 2 1 3))))
; natp g removed: a generation that is no natural; the request compares the fixed one
(defconst *rths-s-g* (list *rths-cfg* '((0 :live nil) (1 :live 5))
                           '((:x (:workspace 1 1) (65 66)) (4 (:leased 1 1 :out) (72 73 74)))
                           (list *rths-send*) '(nil nil) 2))
(assert! (and (equal (rths-hl3-hyps 0 2 '(67) *rths-s-g* 1 1 :x) '(t t nil t t t t))
              (not (rths-hl3-concl 0 2 '(67) *rths-s-g* 1 1 :x))))
; generation removed: a stale generation; the request is refused
(assert! (and (equal (rths-hl3-hyps 0 2 '(67) *rths-s* 1 1 7) '(t t t nil t t t))
              (not (rths-hl3-concl 0 2 '(67) *rths-s* 1 1 7))))
; natp off removed: the first put is refused and the rest land from offset 1
(assert! (and (equal (rths-hl3-hyps 0 -1 '(67 68) *rths-s* 1 1 3) '(t t t t nil t t))
              (not (rths-hl3-concl 0 -1 '(67 68) *rths-s* 1 1 3))))
; octet list removed: the octets before a non-octet land
(assert! (and (equal (rths-hl3-hyps 0 2 '(67 300) *rths-s* 1 1 3) '(t t t t t nil t))
              (not (rths-hl3-concl 0 2 '(67 300) *rths-s* 1 1 3))))
; capacity removed: the octets within the capacity land
(assert! (and (equal (rths-hl3-hyps 0 2 '(1 2 3 4 5 6 7) *rths-s* 1 1 3) '(t t t t t t nil))
              (not (rths-hl3-concl 0 2 '(1 2 3 4 5 6 7) *rths-s* 1 1 3))))
; mutation: the puts leave the state
(assert! (not (equal (fn-rtc-st$a-puts 0 2 '(67 68) *rths-s*) *rths-s*)))
