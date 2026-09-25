; Witnesses for books/bp-fragment-send (spike/bp).  Every value that encodes
; a bundle is a zero-argument function: CRC and digest attachments are not
; used while ACL2 evaluates a defconst.
(in-package "ACL2")
(include-book "../../books/bp-fragment-send")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bpfst-a* (cons :dtn '(47 47 102 110 45 97 47)))   ; dtn://fn-a/
(defconst *bpfst-b* (cons :dtn '(47 47 102 110 45 98 47)))   ; dtn://fn-b/

(defun bpfst-payload (n acc)
  (declare (xargs :mode :program))
  (if (zp n) acc (bpfst-payload (1- n) (cons (mod n 251) acc))))

(defun bpfst-bundle (flags)
  (declare (xargs :mode :program))
  (fn-bpb-make-bundle
   (fn-bpp-make-block flags 1 *bpfst-b* *bpfst-a* *bpfst-a*
                      1000 7 3600000 nil nil)
   (list (fn-bpb-hop-count-block 2 0 1 (fn-bpp-make-hop-count 32 0))
         (fn-bpb-bundle-age-block 3 0 1 0))
   (fn-bpb-payload-block 1 (bpfst-payload 1000 nil))))

(defun bpfst-wire () (declare (xargs :mode :program)) (fn-bpb-encode (bpfst-bundle 0)))
(defun bpfst-plan (mru) (declare (xargs :mode :program)) (fn-bpfs-plan (bpfst-wire) mru))
(defun bpfst-frags (mru) (declare (xargs :mode :program)) (cdr (bpfst-plan mru)))

; A bundle that fits is sent whole.
(assert-event (equal (bpfst-plan (len (bpfst-wire))) '(:whole)))

; At MRU 300 the 1000-octet ADU is cut: every fragment fits, there is more
; than one, and the offsets reassemble EXACTLY to the parent payload.
(assert-event
 (let ((fs (bpfst-frags 300)))
   (and (equal (car (bpfst-plan 300)) :fragments)
        (< 1 (len fs))
        (<= (fn-bpfs-max-len fs) 300)
        (equal (fn-bpf-reassemble (fn-bpfs-views fs) 1000)
               (list :ok (bpfst-payload 1000 nil))))))

; Each fragment is a valid bundle with the parent's identity and the
; fragment flag, and unfragments to the parent's primary block.
(defun bpfst-all-unfragment (fs parent)
  (declare (xargs :mode :program))
  (or (atom fs)
      (let* ((r (fn-bpb-decode (car fs) (len (car fs))))
             (b (fn-cbor-result-value r)))
        (and (fn-cbor-result-okp r)
             (fn-bpp-fragmentp (fn-bpp-flags (fn-bpb-bundle-primary b)))
             (equal (fn-bpf-unfragment-block (fn-bpb-bundle-primary b)) parent)
             (equal (fn-bpb-bundle-blocks b)
                    (fn-bpb-bundle-blocks (bpfst-bundle 0)))
             (bpfst-all-unfragment (cdr fs) parent)))))
(assert-event
 (bpfst-all-unfragment (bpfst-frags 300)
                       (fn-bpb-bundle-primary (bpfst-bundle 0))))

; Teeth: a missing fragment is a gap, never :ok (held, not delivered).
(assert-event
 (equal (car (fn-bpf-reassemble (cdr (fn-bpfs-views (bpfst-frags 300))) 1000))
        :missing))
(must-fail
 (assert-event
  (equal (car (fn-bpf-reassemble (cdr (fn-bpfs-views (bpfst-frags 300))) 1000))
         :ok)))

; "Must not be fragmented" (flag 4) is refused, never cut.
(defun bpfst-nofrag-plan ()
  (declare (xargs :mode :program))
  (fn-bpfs-plan (fn-bpb-encode (bpfst-bundle 4)) 300))
(assert-event (equal (bpfst-nofrag-plan) '(:refused :no-fragment)))

; An MRU below the overhead is refused.
(assert-event (equal (bpfst-plan 40) '(:refused :mru-too-small)))
