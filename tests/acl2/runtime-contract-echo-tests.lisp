; fn: the multi-instance exercise of the runtime contract's echo instance
; (books/runtime-contract-echo.lisp), run in ACL2.
;
; What this book is evidence FOR.  Two interleaved connections over one
; layer (3 slots, three reserved 64-octet buffers per connection): pending read and send on the same
; connection, a held receive while a send is outstanding, a close with a send
; still outstanding (the slot drains), the late completion that retires the
; draining slot, a duplicate of it, slot reuse at the next incarnation with
; the reused buffer at a later generation, a stale completion naming the old
; incarnation, a short send, a failed receive and a close.  After every step
; the contract's invariant holds of the state read back, every outstanding
; :out use's octets are unchanged, and the two stale completions are
; discarded (state and actions unchanged).  The script is the book's
; (`fn-rce-exercise'); the extraction gate's step 2b runs the same variants
; through the developer image and fn-core (`--fn rtc-exercise run 0|1').
;
; Teeth: a host that writes into an :out-leased buffer is reported :moved
; (the injected overwrite keeps length and ownership), also when the
; same item then completes that send; a host that frees a buffer under an
; outstanding lease is reported :invp-violated.

(in-package "ACL2")
(include-book "../../books/runtime-contract-echo")
(include-book "../../books/runtime-contract-opened")
(include-book "std/testing/assert-bang" :dir :system)

(defun rce-run-variant (variant)
  (declare (xargs :guard t))
  (with-local-stobj fn-rtc-st
    (mv-let (fn-rtc-st obs) (fn-rce-exercise variant fn-rtc-st)
      obs)))

(defun rce-all-sound (obs)
  (declare (xargs :guard t))
  (if (atom obs) t
    (and (equal (fn-rtc-get 4 (car obs)) :invp)
         (equal (fn-rtc-get 5 (car obs)) :stable)
         (not (equal (fn-rtc-get 6 (car obs)) :unmatched-changed))
         (rce-all-sound (cdr obs)))))

(defconst *rce-obs* (rce-run-variant 0))

(assert! (equal (len *rce-obs*) 17))
(assert! (rce-all-sound *rce-obs*))
; the duplicate late completion and the stale completion of the old
; incarnation are discarded
(assert! (equal (fn-rtc-get 6 (nth 10 *rce-obs*)) :discarded))
(assert! (equal (fn-rtc-get 6 (nth 12 *rce-obs*)) :discarded))
; pending read and send: step 3 emits a send of the received octets and a
; new receive in another buffer
(assert! (equal (fn-rtc-get 2 (nth 3 *rce-obs*))
                '((:send 1 1 4 ((0 2 0 5) 7)) (:recv 1 1 5 ((1 1 0 64) 7)))))
; the close with a send outstanding drains; that send's completion retires
; the slot and re-arms admission
(assert! (equal (fn-rtc-get 2 (nth 9 *rce-obs*)) '((:accept 0 0 11 (nil)))))
; slot 2 reused at incarnation 2, receiving into its own buffer 3 at generation 4
(assert! (equal (fn-rtc-get 2 (nth 11 *rce-obs*)) '((:recv 2 2 12 ((3 4 0 64) 9)))))

; Teeth.  Writing into buffer 0 while connection 1's send (op 4) holds it
; :out-leased moves its octets.
(defconst *rce-moved* (rce-run-variant 1))
(assert! (equal (fn-rtc-get 5 (nth 4 *rce-moved*)) :moved))
(assert! (equal (fn-rtc-get 4 (nth 4 *rce-moved*)) :invp))
; Freeing buffer 0 under that lease breaks the invariant.
(defconst *rce-freed* (rce-run-variant 2))
(assert! (equal (fn-rtc-get 4 (nth 4 *rce-freed*)) :invp-violated))
; A host write into that buffer followed by the send's own completion is
; still reported: the host's half is checked before the step.
(defconst *rce-moved-then-completed* (rce-run-variant 3))
(assert! (equal (fn-rtc-get 5 (nth 4 *rce-moved-then-completed*)) :moved))
; The short send (step 13) resends the rest of the buffer.
(assert! (equal (fn-rtc-get 2 (nth 13 *rce-obs*)) '((:send 1 1 13 ((1 3 2 2) 7)))))
; The close with the resent rest outstanding drains slot 1; that send's
; completion retires it and re-arms admission.
(assert! (equal (fn-rtc-get 2 (nth 16 *rce-obs*)) '((:accept 0 0 15 (nil)))))
; Redirecting that buffer's lease to another instance violates the use
; owner check and is not a landing: reported :invp-violated and :moved.
(defconst *rce-redirected* (rce-run-variant 4))
(assert! (equal (fn-rtc-get 5 (nth 4 *rce-redirected*)) :moved))
(assert! (equal (fn-rtc-get 4 (nth 4 *rce-redirected*)) :invp-violated))

; Initialization also uses the instance's static initializer: this executes
; without an attachment for the contract's constrained static machine.
(defun rce-static-scene1 (fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :guard t))
  (mv-let (fn-rtc-st acts) (fn-rcl-x-init '(3 2 64 1 1 0 64) fn-rtc-st)
    (declare (ignore acts))
    (mv fn-rtc-st (fn-rtc-x-state fn-rtc-st))))
(defun rce-static-scene ()
  (declare (xargs :guard t))
  (with-local-stobj fn-rtc-st
    (mv-let (fn-rtc-st s) (rce-static-scene1 fn-rtc-st)
      s)))
(assert! (let ((s (rce-static-scene)))
           (and (fn-rcl-invp s)
                (equal (fn-rtc-slot 1 s) *fn-rtc-static-slot*)
                (equal (fn-rtc-mstate 1 s) (fn-rce-static-init 1)))))

; ---------------------------------------------------------------------------
; Contract v2.2: the :extend request (KX1, KX1r, KX2) and the layer-armed
; :opened completion (KO1, KO1b, KO2, KO3), on the echo layer with one static
; owner (slot 1) and one connection slot.  The echo machine never asks for an
; extent and does not know :opened; it answers the unknown event with a
; (:close) request, which the layer refuses for a static instance -- that
; refusal is the witness that the owner's machine was stepped.

(defconst *rce-open-cfg* '(3 2 64 1 1 0 64))
(defconst *rce-open-data* (list (list 0 nil 0 1 0) 7 (list 1 40 4)))

(defun rce-open-run1 (items fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (mv-let (fn-rtc-st obs) (fn-rce-run *rce-open-cfg* items fn-rtc-st)
    (mv fn-rtc-st obs (fn-rtc-x-state fn-rtc-st))))
(defun rce-open-run (items)
  (declare (xargs :guard t))
  (with-local-stobj fn-rtc-st
    (mv-let (fn-rtc-st obs s) (rce-open-run1 items fn-rtc-st)
      (mv obs s))))

(defconst *rce-open-e* (list :opened 1 1 0 '(:done 0) *rce-open-data*))

; KO1: the initial state arms the owner's :opened, and only the owner's -- the
; connection slot and the listener hold none -- and its action is in the
; initial action list.
(defconst *rce-open-0* (mv-let (obs s) (rce-open-run nil) (list obs s)))
(assert! (let ((obs (car *rce-open-0*)) (s (cadr *rce-open-0*)))
           (and (member-equal '(:opened 1 1 0 (0)) (fn-rtc-get 2 (nth 0 obs)))
                (fn-rtc-kind-out-p :opened 1 1 (fn-rtc-uses s))
                (not (fn-rtc-kind-out-p :opened 2 1 (fn-rtc-uses s)))
                (not (fn-rtc-kind-out-p :opened 0 1 (fn-rtc-uses s)))
                (not (fn-rtc-kind-out-p :opened 1 2 (fn-rtc-uses s)))
                (fn-rcl-invp s))))

; KO2 and KO3: the owner's (:done 0) :opened acts -- matched, the invariant
; and the stability checks hold, the owner's machine answered (refused
; (:close)) -- and delivered again it is discarded, changing nothing.
(defconst *rce-open-1*
  (mv-let (obs s) (rce-open-run (list (list :complete *rce-open-e*) (list :complete *rce-open-e*)))
    (list obs s)))
(assert! (let ((obs (car *rce-open-1*)) (s (cadr *rce-open-1*)))
           (and (equal (fn-rtc-get 6 (nth 1 obs)) :matched)
                (equal (fn-rtc-get 4 (nth 1 obs)) :invp)
                (equal (fn-rtc-get 5 (nth 1 obs)) :stable)
                (equal (fn-rtc-get 3 (nth 1 obs)) '((:close)))
                (equal (fn-rtc-get 6 (nth 2 obs)) :discarded)
                (null (fn-rtc-get 2 (nth 2 obs)))
                (not (fn-rtc-kind-out-p :opened 1 1 (fn-rtc-uses s)))
                (equal (fn-rtc-slot 1 s) *fn-rtc-static-slot*))))

; Teeth.  A completion that does not name the armed action is not the owner's
; :opened: another slot, another incarnation, another operation, another kind
; are each discarded, and the owner's own still acts afterwards.
(defconst *rce-open-2*
  (mv-let (obs s)
    (rce-open-run (list (list :complete (list :opened 2 1 0 '(:done 0) *rce-open-data*))
                        (list :complete (list :opened 1 2 0 '(:done 0) *rce-open-data*))
                        (list :complete (list :opened 1 1 9 '(:done 0) *rce-open-data*))
                        (list :complete (list :timer 1 1 0 '(:done 0)))
                        (list :complete *rce-open-e*)))
    (list obs s)))
(assert! (let ((obs (car *rce-open-2*)))
           (and (equal (fn-rtc-get 6 (nth 1 obs)) :discarded)
                (equal (fn-rtc-get 6 (nth 2 obs)) :discarded)
                (equal (fn-rtc-get 6 (nth 3 obs)) :discarded)
                (equal (fn-rtc-get 6 (nth 4 obs)) :discarded)
                (equal (fn-rtc-get 6 (nth 5 obs)) :matched))))

; KO3's (:done 0) hypothesis: the outcome the owner is told of any other
; outcome is a malformed failure (or the host's own failure), never DATA.
(assert! (equal (fn-rtc-delivered-outcome '(:opened 1 1 0 nil) '(:opened 1 1 0 (:done 3)))
                '(:failed :malformed-completion)))
(assert! (equal (fn-rtc-delivered-outcome '(:opened 1 1 0 nil) '(:opened 1 1 0 (:short 0)))
                '(:failed :malformed-completion)))
(assert! (equal (fn-rtc-delivered-outcome '(:opened 1 1 0 nil) '(:opened 1 1 0 (:done 0))) '(:done 0)))

(defun rce-sub (r id inc s)
  (declare (xargs :guard t))
  (mv-let (s2 acts refused cost) (fn-rtc-req-submit r id inc s)
    (declare (ignore cost))
    (list s2 acts refused)))

; KX1, KX1r: on the opened state the owner's extent request is exactly the
; action (:extend 1 1 OP (RES FILE FROM TO)), FROM < TO below 2^64, no handle;
; every other request is refused and changes nothing.
(defconst *rce-ext-r* '(:submit :extend nil (7 10 20)))
(defconst *rce-ext-s* (cadr *rce-open-1*))
(assert! (let ((res (rce-sub *rce-ext-r* 1 1 *rce-ext-s*)))
           (and (null (mv-nth 2 res))
                (equal (mv-nth 1 res)
                       (list (list :extend 1 1 (fn-rtc-next-op *rce-ext-s*)
                                   (cons (fn-rtc-s-res (fn-rtc-slot 1 *rce-ext-s*)) '(7 10 20)))))
                (fn-rtc-kind-out-p :extend 1 1 (fn-rtc-uses (mv-nth 0 res))))))
(assert! (let ((res (rce-sub '(:submit :extend nil (7 10 10)) 1 1 *rce-ext-s*)))
           (and (mv-nth 2 res) (equal (mv-nth 0 res) *rce-ext-s*) (null (mv-nth 1 res)))))
(assert! (mv-nth 2 (rce-sub '(:submit :extend nil (7 20 10)) 1 1 *rce-ext-s*)))
(assert! (mv-nth 2 (rce-sub '(:submit :extend nil (7 10)) 1 1 *rce-ext-s*)))
(assert! (mv-nth 2 (rce-sub (list :submit :extend '(0 1 0 0) '(7 10 20)) 1 1 *rce-ext-s*)))
(assert! (mv-nth 2 (rce-sub (list :submit :extend nil (list 7 10 (expt 2 64))) 1 1 *rce-ext-s*)))
; one extent outstanding per instance: a second is refused
(assert! (mv-nth 2 (rce-sub *rce-ext-r* 1 1 (mv-nth 0 (rce-sub *rce-ext-r* 1 1 *rce-ext-s*)))))

; KX2: what the instance is told of its extent.
(assert! (equal (fn-rtc-delivered-outcome '(:extend 1 1 5 nil) '(:extend 1 1 5 (:done 0))) '(:done 0)))
(assert! (equal (fn-rtc-delivered-outcome '(:extend 1 1 5 nil) '(:extend 1 1 5 (:cancelled))) '(:cancelled)))
(assert! (equal (fn-rtc-delivered-outcome '(:extend 1 1 5 nil) '(:extend 1 1 5 (:failed :enospc))) '(:failed :enospc)))
(assert! (equal (fn-rtc-delivered-outcome '(:extend 1 1 5 nil) '(:extend 1 1 5 (:done 1))) '(:failed :malformed-completion)))
(assert! (equal (fn-rtc-delivered-outcome '(:extend 1 1 5 nil) '(:extend 1 1 5 (:short 0))) '(:failed :malformed-completion)))

; A failed :opened still steps the owner and consumes the use (only the DATA
; delivery is gated on (:done 0)): the echo answers the unknown event with
; its (:close) request, refused for a static instance, and a later (:done 0)
; :opened for the same slot incarnation is discarded -- also after a run of
; other events (the listener's accept completes and a stale timer is dropped).
(defconst *rce-open-failed* (list :opened 1 1 0 '(:failed :eio)))
(defconst *rce-open-3*
  (mv-let (obs s)
    (rce-open-run (list (list :complete *rce-open-failed*)
                        (list :complete *rce-open-e*)))
    (list obs s)))
(assert! (let ((obs (car *rce-open-3*)) (s (cadr *rce-open-3*)))
           (and (equal (fn-rtc-get 6 (nth 1 obs)) :matched)
                (equal (fn-rtc-get 3 (nth 1 obs)) '((:close)))
                (equal (fn-rtc-get 4 (nth 1 obs)) :invp)
                (equal (fn-rtc-get 6 (nth 2 obs)) :discarded)
                (null (fn-rtc-get 2 (nth 2 obs)))
                (not (fn-rtc-kind-out-p :opened 1 1 (fn-rtc-uses s))))))
(defconst *rce-open-4*
  (mv-let (obs s)
    (rce-open-run (list (list :complete *rce-open-failed*)
                        (list :complete '(:accept 0 0 1 (:done 7)))
                        (list :complete '(:timer 1 1 0 (:done 0)))
                        (list :complete *rce-open-e*)))
    (list obs s)))
(assert! (let ((obs (car *rce-open-4*)))
           (and (equal (fn-rtc-get 6 (nth 1 obs)) :matched)
                (equal (fn-rtc-get 6 (nth 2 obs)) :matched)
                (equal (fn-rtc-get 6 (nth 3 obs)) :discarded)
                (equal (fn-rtc-get 6 (nth 4 obs)) :discarded)
                (null (fn-rtc-get 2 (nth 4 obs))))))
