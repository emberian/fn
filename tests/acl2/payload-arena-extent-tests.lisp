; Tests for books/payload-arena-extent.lisp and the generic's extent seal
; (lane arena-offheap-2, PRF-294).
;
; 1. Every exec function of the extent arena is guard-verified.
; 2. The extent arena run directly (not attached): resident seals, an extent
;    seal between them, a clear and a reseal; every read of a RESIDENT
;    handle answers its own octets after the extent seal, and the extent
;    handle's count and length are answered without a realizer call (the
;    certification world has no realizer: a read of an extent handle's
;    octets is the host's, host/native/extent.lisp).
; 3. The keystone's teeth: a ground positive witness per conjunct, and a
;    must-fail per hypothesis.

(in-package "ACL2")
(include-book "../../books/payload-arena-extent")
(include-book "../../books/payload-arena")
(include-book "must-fail-checked")

(assert-event
 (and (eq (symbol-class 'fn-arena$x-count (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arena$x-payload-len (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arena$x-get (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arena$x-payload (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arena$x-seal-list (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arena$x-seal-buffer (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arena$x-seal-range (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arena$x-clear (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arena$x-seal-extent (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arx-mark (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arena$l-seal-extent (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arena$x-reseat-extent (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arena$x-release (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arx-stage-write (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arx-page-copy (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arx-stage-payload (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arena$l-reseat-extent (w state)) :common-lisp-compliant)))

; The run: seal (1 2 3); seal the extent (file 7, entry [100, 200), payload
; [120, 140), trailer 99) as handle 1; seal (4 5); read everything a
; realizer-free process can read.
(defun paxt-run (fn-arena-extent)
  (declare (xargs :stobjs fn-arena-extent))
  (let* ((fn-arena-extent (fn-arena-extent-clear fn-arena-extent))
         (fn-arena-extent (fn-arena-extent-seal-list '(1 2 3) fn-arena-extent))
         (fn-arena-extent (fn-arena-extent-seal-extent 7 100 100 120 20 99 fn-arena-extent))
         (fn-arena-extent (fn-arena-extent-seal-list '(4 5) fn-arena-extent)))
    (mv (list (fn-arena-extent-count fn-arena-extent)
              (fn-arena-extent-payload-len 0 fn-arena-extent)
              (fn-arena-extent-payload-len 1 fn-arena-extent)
              (fn-arena-extent-payload-len 2 fn-arena-extent)
              (fn-arena-extent-payload 0 fn-arena-extent)
              (fn-arena-extent-payload 2 fn-arena-extent)
              (fn-arena-extent-get 2 1 fn-arena-extent))
        fn-arena-extent)))

(assert-event (mv-let (r fn-arena-extent) (paxt-run fn-arena-extent)
                (mv (equal r '(3 3 20 2 (1 2 3) (4 5) 5)) fn-arena-extent))
              :stobjs-out '(nil fn-arena-extent))

; Many extent seals grow EXT past its first 64 entries; a clear releases
; them and a reseal starts at handle 0.
(defun paxt-many (n fn-arena-extent)
  (declare (xargs :stobjs fn-arena-extent :guard (natp n)))
  (if (zp n)
      fn-arena-extent
    (let ((fn-arena-extent (fn-arena-extent-seal-extent 1 (* 64 n) 64 (+ 8 (* 64 n)) 50 n
                                                        fn-arena-extent)))
      (paxt-many (1- n) fn-arena-extent))))

(assert-event (let* ((fn-arena-extent (fn-arena-extent-clear fn-arena-extent))
                     (fn-arena-extent (paxt-many 150 fn-arena-extent))
                     (c (fn-arena-extent-count fn-arena-extent))
                     (l (fn-arena-extent-payload-len 149 fn-arena-extent))
                     (fn-arena-extent (fn-arena-extent-clear fn-arena-extent))
                     (fn-arena-extent (fn-arena-extent-seal-list '(9) fn-arena-extent)))
                (mv (and (equal c 150) (equal l 50)
                         (equal (fn-arena-extent-count fn-arena-extent) 1)
                         (equal (fn-arena-extent-payload 0 fn-arena-extent) '(9)))
                    fn-arena-extent))
              :stobjs-out '(nil fn-arena-extent))

; --- The keystone's teeth (books/payload-arena.lisp fn-arena-seal-extent-payload).
; Positive witness, every conjunct at a ground arena: the new handle 2 is the
; durable octets; handle 1, below the count, keeps (4 5); the count is 3.
(defthm paxt-keystone-witness
  (let ((a2 (fn-arena-seal-extent 7 100 100 120 20 99 '((1 2 3) (4 5)))))
    (and (equal (fn-arena-count '((1 2 3) (4 5))) 2)
         (equal (fn-arena-payload 2 a2) (fn-durable-octets 7 120 20))
         (< 1 (fn-arena-count '((1 2 3) (4 5))))
         (equal (fn-arena-payload 1 a2) '(4 5))
         (equal (fn-arena-payload 1 a2) (fn-arena-payload 1 '((1 2 3) (4 5))))
         (equal (fn-arena-count a2) 3)))
  :rule-classes nil)

; Without (< h count): handle h = count is the NEW handle, whose payload is
; the durable octets, not the old arena's (absent: nil).
(local
 (must-fail-checked
  (with-prover-step-limit 50000 (defthm paxt-keystone-without-below-count
    (implies (natp h)
             (equal (fn-arena-payload h (fn-arena-seal-extent file eoff elen poff plen trailer
                                                              fn-arena))
                    (fn-arena-payload h fn-arena)))))))

; Without (natp h): h = -1 on the empty arena is below the count 0 is false,
; but h = -1 on a one-payload arena reads position 0 of both; the failing
; case is the empty arena with h = -1 < 0 = count: nth -1 of the sealed
; arena is the durable octets, of the empty arena nil.  The ground instance:
(defthm paxt-keystone-natp-counterexample
  (and (< -1 (fn-arena-count nil))
       (equal (fn-arena-payload -1 (fn-arena-seal-extent 7 100 100 120 20 99 nil))
              (fn-durable-octets 7 120 20))
       (equal (fn-arena-payload -1 nil) nil)
       (consp (fn-durable-octets 7 120 20)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-durable-octets-len (file 7) (off 120) (len 20)))
           :in-theory (e/d (nth) (fn-durable-octets-len)))))

(local
 (must-fail-checked
  (with-prover-step-limit 50000 (defthm paxt-keystone-without-natp
    (implies (< h (fn-arena-count fn-arena))
             (equal (fn-arena-payload h (fn-arena-seal-extent file eoff elen poff plen trailer
                                                              fn-arena))
                    (fn-arena-payload h fn-arena)))))))

; The durable octets of an extent are its length (the assumption's
; constraint), which is what makes the handle's length the extent's.
(defthm paxt-extent-len
  (equal (fn-arena-payload-len 2 (fn-arena-seal-extent 7 100 100 120 20 99 '((1 2 3) (4 5))))
         20)
  :rule-classes nil)

; The whole-payload realizer is the durable octets (A-DURABLE-EXTENT's
; constraint: the read of an extent handle's payload, one call).
(defthm paxt-realize-witness
  (equal (fn-durable-realize-octets 7 100 100 120 20 99)
         (fn-durable-octets 7 120 20))
  :rule-classes nil)

; --- The stage (lane arena-offheap-3, PRF-309).  A buffer seal stages its
; copy: handle 1 reads (1 2 3 4) from its stage slot; a release of a STAGED
; handle keeps the copy; the reseat re-points handle 1 at an extent (its
; length is then the extent's, 4) and the release frees the slot; handle 0
; (resident) and handle 2 (still staged) read their own octets throughout.
(defun paxt-stage-run (fn-octets fn-arena-extent)
  (declare (xargs :stobjs (fn-octets fn-arena-extent)))
  (let* ((fn-octets (fn-octets-clear fn-octets))
         (fn-octets (fn-octets-append-list '(1 2 3 4) fn-octets))
         (fn-arena-extent (fn-arena-extent-clear fn-arena-extent))
         (fn-arena-extent (fn-arena-extent-seal-list '(9) fn-arena-extent))
         (fn-arena-extent (fn-arena-extent-seal-buffer fn-octets fn-arena-extent))
         (fn-arena-extent (fn-arena-extent-seal-buffer fn-octets fn-arena-extent))
         (r1 (list (fn-arena-extent-payload 1 fn-arena-extent)
                   (fn-arena-extent-payload-len 1 fn-arena-extent)
                   (fn-arena-extent-get 1 2 fn-arena-extent)))
         (fn-arena-extent (fn-arena-extent-release 1 fn-arena-extent))
         (r2 (fn-arena-extent-payload 1 fn-arena-extent))
         (fn-arena-extent (fn-arena-extent-reseat-extent 1 7 100 100 120 4 99 fn-arena-extent))
         (fn-arena-extent (fn-arena-extent-release 1 fn-arena-extent))
         (r3 (list (fn-arena-extent-count fn-arena-extent)
                   (fn-arena-extent-payload-len 1 fn-arena-extent)
                   (fn-arena-extent-payload 2 fn-arena-extent)
                   (fn-arena-extent-payload 0 fn-arena-extent))))
    (mv (list r1 r2 r3) fn-octets fn-arena-extent)))

(assert-event (mv-let (r fn-octets fn-arena-extent) (paxt-stage-run fn-octets fn-arena-extent)
                (mv (equal r '(((1 2 3 4) 4 3) (1 2 3 4) (3 4 (1 2 3 4) (9))))
                    fn-octets fn-arena-extent))
              :stobjs-out '(nil fn-octets fn-arena-extent))

; --- The reseat's keystones (books/payload-arena.lisp).
; fn-arena-reseat-extent-payload, every conjunct at a ground arena: handle 1
; is the extent's durable octets, handle 0 keeps (1 2 3), the count stays 2.
(defthm paxt-reseat-witness
  (let ((a2 (fn-arena-reseat-extent 1 7 100 100 120 20 99 '((1 2 3) (4 5)))))
    (and (fn-arena-p '((1 2 3) (4 5)))
         (< 1 (fn-arena-count '((1 2 3) (4 5))))
         (equal (fn-arena-payload 1 a2) (fn-durable-octets 7 120 20))
         (equal (fn-arena-payload 0 a2) '(1 2 3))
         (equal (fn-arena-count a2) 2)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-arena-reseat-extent-payload
                                   (h 1) (k 0) (file 7) (eoff 100) (elen 100) (poff 120) (plen 20)
                                   (trailer 99) (fn-arena '((1 2 3) (4 5)))))
           :in-theory (disable (:e fn-arena-reseat-extent) fn-arena-reseat-extent-payload))))

(local
 (must-fail-checked
  (with-prover-step-limit 50000 (defthm paxt-reseat-without-below-count
    (implies (and (fn-arena-p fn-arena) (natp h))
             (equal (fn-arena-payload h (fn-arena-reseat-extent h file eoff elen poff plen trailer
                                                                fn-arena))
                    (fn-durable-octets file poff plen)))))))

; fn-arena-reseat-extent-keeps-a-faithful-arena: at a ground arena whose
; handle 1 the file holds (the hypothesis), the reseat is the identity.
(defthm paxt-faithful-witness
  (implies (equal (fn-durable-octets 7 120 2) '(4 5))
           (and (fn-arena-p '((1 2 3) (4 5)))
                (< 1 (fn-arena-count '((1 2 3) (4 5))))
                (equal (fn-durable-octets 7 120 2) (fn-arena-payload 1 '((1 2 3) (4 5))))
                (equal (fn-arena-reseat-extent 1 7 100 100 120 2 99 '((1 2 3) (4 5)))
                       '((1 2 3) (4 5)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-arena-reseat-extent-keeps-a-faithful-arena
                                   (h 1) (file 7) (eoff 100) (elen 100) (poff 120) (plen 2)
                                   (trailer 99) (fn-arena '((1 2 3) (4 5)))))
           :in-theory (disable (:e fn-arena-reseat-extent)
                               fn-arena-reseat-extent-keeps-a-faithful-arena))))

(local
 (must-fail-checked
  (with-prover-step-limit 50000 (defthm paxt-faithful-without-faithful
    (implies (and (fn-arena-p fn-arena) (natp h) (< h (fn-arena-count fn-arena)))
             (equal (fn-arena-reseat-extent h file eoff elen poff plen trailer fn-arena)
                    fn-arena))))))

(local
 (must-fail-checked
  (with-prover-step-limit 50000 (defthm paxt-faithful-without-below-count
    (implies (and (fn-arena-p fn-arena) (natp h)
                  (equal (fn-durable-octets file poff plen) (fn-arena-payload h fn-arena)))
             (equal (fn-arena-reseat-extent h file eoff elen poff plen trailer fn-arena)
                    fn-arena))))))

(local
 (must-fail-checked
  (with-prover-step-limit 50000 (defthm paxt-faithful-without-arena-p
    (implies (and (natp h) (< h (fn-arena-count fn-arena))
                  (equal (fn-durable-octets file poff plen) (fn-arena-payload h fn-arena)))
             (equal (fn-arena-reseat-extent h file eoff elen poff plen trailer fn-arena)
                    fn-arena))))))
