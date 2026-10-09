; fn: the multi-instance exercise of the runtime contract's echo instance
; (books/runtime-contract-echo.lisp), run in ACL2.
;
; What this book is evidence FOR.  Two interleaved connections over one
; layer (3 slots, 6 buffers of 64 octets): pending read and send on the same
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
; (the invariant still holds: `fn-rtc-splice-keeps-invp'); a host that frees
; a buffer under an outstanding lease is reported :invp-violated.

(in-package "ACL2")
(include-book "../../books/runtime-contract-echo")
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

(assert! (equal (len *rce-obs*) 16))
(assert! (rce-all-sound *rce-obs*))
; the duplicate late completion and the stale completion of the old
; incarnation are discarded
(assert! (equal (fn-rtc-get 6 (nth 10 *rce-obs*)) :discarded))
(assert! (equal (fn-rtc-get 6 (nth 12 *rce-obs*)) :discarded))
; pending read and send: step 3 emits a send of the received octets and a
; new receive in another buffer
(assert! (equal (fn-rtc-get 2 (nth 3 *rce-obs*))
                '((:send 1 1 4 ((0 2 0 5) 7)) (:recv 1 1 5 ((2 1 0 64) 7)))))
; the close with a send outstanding drains; that send's completion retires
; the slot and re-arms admission
(assert! (equal (fn-rtc-get 2 (nth 9 *rce-obs*)) '((:accept 0 0 11 (nil)))))
; slot 2 reused at incarnation 2, receiving into buffer 0 at generation 4
(assert! (equal (fn-rtc-get 2 (nth 11 *rce-obs*)) '((:recv 2 2 12 ((0 4 0 64) 9)))))

; Teeth.  Writing into buffer 0 while connection 1's send (op 4) holds it
; :out-leased moves its octets.
(defconst *rce-moved* (rce-run-variant 1))
(assert! (equal (fn-rtc-get 5 (nth 4 *rce-moved*)) :moved))
(assert! (equal (fn-rtc-get 4 (nth 4 *rce-moved*)) :invp))
; Freeing buffer 0 under that lease breaks the invariant.
(defconst *rce-freed* (rce-run-variant 2))
(assert! (equal (fn-rtc-get 4 (nth 4 *rce-freed*)) :invp-violated))
