; Teeth of books/bp-fragment-send.lisp (PKT-061, PRF-114): the witnesses of
; the four keystones over real encoded bundles, and one must-fail for each
; hypothesis, showing the conclusion fails without it.  Every value that
; encodes a bundle is a zero-argument function (the CRC is computed when
; the function runs, never inside a defconst).
(in-package "ACL2")
(include-book "../../books/bp-fragment-send")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bpfst-a* (cons :dtn '(47 47 102 110 45 97 47)))   ; dtn://fn-a/
(defconst *bpfst-b* (cons :dtn '(47 47 102 110 45 98 47)))   ; dtn://fn-b/

(defun bpfst-payload (n acc)
  (declare (xargs :guard (and (natp n) (true-listp acc))))
  (if (zp n) acc (bpfst-payload (1- n) (cons (mod n 251) acc))))

; A whole bundle (FLAGS 0, or 4: must not be fragmented) carrying N octets,
; with a hop count and a bundle age block (both replicated in every
; fragment).
(defun bpfst-bundle (flags n)
  (fn-bpb-make-bundle
   (fn-bpp-make-block flags 1 *bpfst-b* *bpfst-a* *bpfst-a*
                      1000 7 3600000 nil nil)
   (list (fn-bpb-hop-count-block 2 0 1 (fn-bpp-make-hop-count 32 0))
         (fn-bpb-bundle-age-block 3 0 1 0))
   (fn-bpb-payload-block 1 (bpfst-payload n nil))))

; A fragment parent: ADU offset 500 of a 3000-octet ADU, carrying N octets.
(defun bpfst-fragment-parent (n)
  (fn-bpb-make-bundle
   (fn-bpp-make-block 1 1 *bpfst-b* *bpfst-a* *bpfst-a*
                      1000 7 3600000 500 3000)
   nil
   (fn-bpb-payload-block 1 (bpfst-payload n nil))))

(defun bpfst-wire (flags n) (fn-bpb-encode (bpfst-bundle flags n)))
(defun bpfst-plan (n mru) (fn-bpfs-plan (bpfst-wire 0 n) mru))
(defun bpfst-max-len (wires)
  (if (atom wires) 0 (max (len (car wires)) (bpfst-max-len (cdr wires)))))

; -----------------------------------------------------------------------------
; fn-bpfs-plan-fragments-fit-mru

; A bundle that fits is sent whole.
(assert-event (equal (bpfst-plan 1000 (len (bpfst-wire 0 1000))) '(:whole)))

; At MRU 300 the 1000-octet ADU is cut into more than one fragment, each at
; most 300 octets, the largest within 10 of the MRU (not a degenerate cut).
(assert-event
 (let ((p (bpfst-plan 1000 300)))
   (and (equal (car p) :fragments)
        (< 1 (len (cdr p)))
        (fn-bpfs-all-at-most (cdr p) 300)
        (<= 290 (bpfst-max-len (cdr p))))))

; The 8 octets the plan reserves are the byte-string head's growth: cut at
; MRU minus the overhead alone, a 313-octet chunk's head is 3 octets where
; the empty payload's was 1.  The first fragment (offset 0, a 1-octet head
; where the overhead's offset 1000 took 3) is exactly 400; the second
; (offset 313) is 402 and exceeds the MRU.
(assert-event
 (let* ((b (bpfst-bundle 0 1000))
        (chunk (- 400 (fn-bpfs-overhead b))))
   (and (equal (fn-bpfs-chunk b 400) (- chunk 8))
        (fn-bpfs-all-at-most (cdr (bpfst-plan 1000 400)) 400))))
(must-fail
 (assert-event
  (let* ((b (bpfst-bundle 0 1000))
         (chunk (- 400 (fn-bpfs-overhead b))))
    (fn-bpfs-all-at-most (fn-bpfs-cut b (fn-bpb-payload b) 0 chunk) 400))))

; The refusals.
(assert-event (equal (fn-bpfs-plan (bpfst-wire 4 1000) 300) '(:refused :no-fragment)))
(assert-event (equal (bpfst-plan 1000 40) '(:refused :mru-too-small)))
(assert-event (equal (fn-bpfs-plan (bpfst-wire 0 0) 10) '(:refused :mru-too-small)))
(assert-event (equal (fn-bpfs-plan '(1 2 3 4 5) 2) '(:refused :malformed)))

; -----------------------------------------------------------------------------
; fn-bpfs-plan-fragments-reassemble-exactly

(defun bpfst-canvas (wire mru)
  (let* ((parent (fn-bpfs-parent wire))
         (p (fn-bpb-bundle-primary parent)))
    (fn-bpf-canvas (fn-bpfs-views (cdr (fn-bpfs-plan wire mru)))
                   (fn-bpfs-base p) (len (fn-bpb-payload parent)))))

(assert-event (equal (bpfst-canvas (bpfst-wire 0 1000) 300) (bpfst-payload 1000 nil)))

; A fragment parent is cut in ADU coordinates: its pieces draw its payload
; at offset 500 and keep the total 3000.
(defun bpfst-fparent-wire () (fn-bpb-encode (bpfst-fragment-parent 1000)))
(assert-event
 (let ((p (fn-bpfs-plan (bpfst-fparent-wire) 300)))
   (and (equal (car p) :fragments)
        (equal (cadr (car (fn-bpfs-views (cdr p)))) 500)
        (fn-bpf-same-total (fn-bpfs-views (cdr p)) 3000)
        (equal (bpfst-canvas (bpfst-fparent-wire) 300) (bpfst-payload 1000 nil)))))

; Without :fragments the conclusion fails: a whole answer carries no views,
; and the canvas is all gaps.
(must-fail
 (assert-event (equal (bpfst-canvas (bpfst-wire 0 100) 100000) (bpfst-payload 100 nil))))

; -----------------------------------------------------------------------------
; fn-bpfs-plan-fragments-restore-parent

(assert-event (fn-bpfs-restoresp (cdr (bpfst-plan 1000 300)) (bpfst-bundle 0 1000)))
(assert-event (fn-bpfs-restoresp (cdr (fn-bpfs-plan (bpfst-fparent-wire) 300))
                                 (bpfst-fragment-parent 1000)))
; Every fragment decodes to the parent's blocks and unfragments to it.
(assert-event
 (let ((ws (cdr (bpfst-plan 1000 300))))
   (equal (fn-bpf-unfragment-block
           (fn-bpb-bundle-primary (fn-bpfs-parent (car (last ws)))))
          (fn-bpb-bundle-primary (bpfst-bundle 0 1000)))))
; Without :fragments: at MRU 5000 the answer is (:whole) and what goes on
; the wire is the parent itself, which carries no fragment flag.
(assert-event (equal (bpfst-plan 1000 5000) '(:whole)))
(must-fail
 (assert-event (fn-bpfs-restoresp (list (bpfst-wire 0 1000)) (bpfst-bundle 0 1000))))

; -----------------------------------------------------------------------------
; fn-bpfs-plan-fragments-reassemble-within-caps

(assert-event
 (equal (fn-bpf-reassemble (fn-bpfs-views (cdr (bpfst-plan 1000 300))) 1000)
        (list :ok (bpfst-payload 1000 nil))))
; A missing fragment is a gap, never (:ok ...).
(assert-event
 (equal (car (fn-bpf-reassemble (cdr (fn-bpfs-views (cdr (bpfst-plan 1000 300)))) 1000))
        :missing))

; Hypothesis :fragments: a whole answer has no views, and the reassembler
; refuses.
(must-fail
 (assert-event
  (equal (fn-bpf-reassemble (fn-bpfs-views (cdr (bpfst-plan 100 100000))) 100)
         (list :ok (bpfst-payload 100 nil)))))
; Hypothesis whole parent: a fragment parent's pieces carry its total 3000,
; not its payload length.
(must-fail
 (assert-event
  (equal (fn-bpf-reassemble (fn-bpfs-views (cdr (fn-bpfs-plan (bpfst-fparent-wire) 300)))
                            1000)
         (list :ok (bpfst-payload 1000 nil)))))
; Hypothesis at most *fn-bpf-max-fragments*: a 10-octet chunk cuts the
; 1000-octet ADU into 100 fragments, beyond the receiver's 64.
(defun bpfst-small-mru () (+ (fn-bpfs-overhead (bpfst-bundle 0 1000)) 8 10))
(assert-event
 (let ((p (bpfst-plan 1000 (bpfst-small-mru))))
   (and (equal (car p) :fragments) (equal (len (cdr p)) 100)
        (fn-bpfs-all-at-most (cdr p) (bpfst-small-mru)))))
(must-fail
 (assert-event
  (equal (fn-bpf-reassemble (fn-bpfs-views (cdr (bpfst-plan 1000 (bpfst-small-mru)))) 1000)
         (list :ok (bpfst-payload 1000 nil)))))
; Hypothesis at most *fn-bpf-max-length*: a 70000-octet ADU is cut exactly
; (its two views are consecutive extents whose bytes are its payload; the
; executable canvas's guard is the capped fragment recognizer, so the
; witness reads the views directly) but the receiver's reassembler refuses
; it.
(defun bpfst-concat (views)
  (if (atom views) nil (append (fn-bpf-bytes (car views)) (bpfst-concat (cdr views)))))
(defun bpfst-big-plan () (bpfst-plan 70000 40000))
(assert-event
 (let* ((p (bpfst-big-plan)) (vs (fn-bpfs-views (cdr p))))
   (and (equal (car p) :fragments) (equal (len (cdr p)) 2)
        (fn-bpfs-all-at-most (cdr p) 40000)
        (equal (fn-bpf-offset (car vs)) 0)
        (equal (fn-bpf-offset (cadr vs)) (len (fn-bpf-bytes (car vs))))
        (equal (fn-bpf-total (car vs)) 70000)
        (equal (fn-bpf-total (cadr vs)) 70000)
        (equal (bpfst-concat vs) (bpfst-payload 70000 nil)))))
(must-fail
 (assert-event
  (equal (fn-bpf-reassemble (fn-bpfs-views (cdr (bpfst-big-plan))) 70000)
         (list :ok (bpfst-payload 70000 nil)))))

;; -----------------------------------------------------------------------------
;; fn-bpfs-plan-fragments-reassemble-uncapped (PRF-121): the uncapped
;; reassembler answers the payload for exactly the two families the capped
;; one refuses above: 100 fragments, and a 70000-octet ADU.
(assert-event
 (equal (fn-bpfw-reassemble (fn-bpfs-views (cdr (bpfst-plan 1000 (bpfst-small-mru)))) 1000)
        (list :ok (bpfst-payload 1000 nil))))
(assert-event
 (equal (fn-bpfw-reassemble (fn-bpfs-views (cdr (bpfst-big-plan))) 70000)
        (list :ok (bpfst-payload 70000 nil))))
(assert-event
 (equal (fn-bpfw-reassemble (fn-bpfs-views (cdr (bpfst-plan 1000 300))) 1000)
        (list :ok (bpfst-payload 1000 nil))))
;; Hypothesis :fragments: a whole answer has no views; refused.
(assert-event (not (equal (car (bpfst-plan 100 100000)) :fragments)))
(must-fail
 (assert-event
  (equal (fn-bpfw-reassemble (fn-bpfs-views (cdr (bpfst-plan 100 100000))) 100)
         (list :ok (bpfst-payload 100 nil)))))
;; Hypothesis whole parent: the plan is :fragments, the parent is a
;; fragment, and its pieces carry the total 3000, not the payload length.
(assert-event
 (and (equal (car (fn-bpfs-plan (bpfst-fparent-wire) 300)) :fragments)
      (fn-bpp-fragmentp
       (fn-bpp-flags (fn-bpb-bundle-primary (fn-bpfs-parent (bpfst-fparent-wire)))))))
(must-fail
 (assert-event
  (equal (fn-bpfw-reassemble (fn-bpfs-views (cdr (fn-bpfs-plan (bpfst-fparent-wire) 300)))
                             1000)
         (list :ok (bpfst-payload 1000 nil)))))

; -----------------------------------------------------------------------------
; fn-bpfs-fragment-outcome: the first fragment's :failed stays :failed (the
; job was certainly not sent); a later one is :uncertain.
(assert-event (equal (fn-bpfs-fragment-outcome 1 :failed) :failed))
(assert-event (equal (fn-bpfs-fragment-outcome 2 :failed) :uncertain))
(assert-event (equal (fn-bpfs-fragment-outcome 3 :refused) :refused))
(must-fail (assert-event (equal (fn-bpfs-fragment-outcome 2 :failed) :failed)))
