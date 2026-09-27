; Tests for books/payload-extent.lisp (lane arena-offheap-2, PRF-281).
;
; 1. The exec functions the host calls are guard-verified.
; 2. The codec's place of the payload is right on a real record: a record
;    encoded by the store's codec (fn-record-encode-impl), placed at an entry
;    start, yields a verified extent whose slice of the record octets is the
;    payload; a record whose octets do not hold the payload there yields nil.
; 3. Teeth: positive witnesses and must-fails for the keystones.

(in-package "ACL2")
(include-book "../../books/payload-extent")
(include-book "std/testing/must-fail" :dir :system)

(assert-event
 (and (eq (symbol-class 'fn-arx-positions (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arx-extent-of (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arx-intern-event (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arx-intern-events (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arx-intern-step (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arx-cat-intern-extent (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arx-entry-ok (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arx-read-cache-entries (w state)) :common-lisp-compliant)))

(defconst *pxt-payload*
  (append (fn-record-string-octets "Subject: a") '(13 10 13 10)
          (fn-record-string-octets "body line") '(13 10)))

(defconst *pxt-w*
  (fn-record-make 7 7 1 "<x@fn.invalid>" *pxt-payload* '("fn.test") "o" "s" "e" 4 5))

(defconst *pxt-r* (fn-record-encode-impl *pxt-w*))

; The entry at start 4096 of file 3, frame length 42 + |r| + 32, trailer 77.
(defconst *pxt-pos* (list 4096 (+ 42 (len *pxt-r*) 32) 77))

(assert-event (consp *pxt-r*))

(assert-event
 (let ((x (fn-arx-extent-of 3 *pxt-pos* *pxt-r* *pxt-w*)))
   (and (fn-arn-extentp x)
        (equal (nth 0 x) 3)
        (equal (nth 1 x) 4096)
        (equal (nth 2 x) (+ 42 (len *pxt-r*)))
        (equal (nth 4 x) (len *pxt-payload*))
        (equal (nth 5 x) 77)
        ; the payload's place inside the record octets is where the payload is
        (equal (take (nth 4 x) (nthcdr (- (nth 3 x) (+ 4096 42)) *pxt-r*)) *pxt-payload*))))

; A frame length that does not match the record, or octets that do not hold
; the payload at the codec's place, give no extent (the record stays resident).
(assert-event (null (fn-arx-extent-of 3 (list 4096 (+ 43 (len *pxt-r*) 32) 77) *pxt-r* *pxt-w*)))
(assert-event (null (fn-arx-extent-of 3 *pxt-pos* (cons 0 (butlast *pxt-r* 1)) *pxt-w*)))

; --- Teeth.
; fn-arx-extent-of-denotes-payload: positive witness at the real record, the
; faithful read as the hypothesis (a ground instance of every hypothesis).
(defthm pxt-denotes-witness
  (implies (equal (fn-durable-octets 3 (+ 4096 42) (len *pxt-r*)) *pxt-r*)
           (and (fn-arx-extent-of 3 *pxt-pos* *pxt-r* *pxt-w*)
                (true-listp (fn-record-payload *pxt-w*))
                (equal (fn-durable-octets (nth 0 (fn-arx-extent-of 3 *pxt-pos* *pxt-r* *pxt-w*))
                                          (nth 3 (fn-arx-extent-of 3 *pxt-pos* *pxt-r* *pxt-w*))
                                          (nth 4 (fn-arx-extent-of 3 *pxt-pos* *pxt-r* *pxt-w*)))
                       *pxt-payload*)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-arx-extent-of-denotes-payload
                                   (file 3) (position *pxt-pos*) (r *pxt-r*) (w *pxt-w*))))))

; Without the faithful read the extent's durable octets are unconstrained.
(local
 (must-fail
  (with-prover-step-limit 50000 (defthm pxt-denotes-without-faithful
    (implies (fn-arx-extent-of 3 *pxt-pos* *pxt-r* *pxt-w*)
             (equal (fn-durable-octets 3 (nth 3 (fn-arx-extent-of 3 *pxt-pos* *pxt-r* *pxt-w*))
                                       (len *pxt-payload*))
                    *pxt-payload*))))))

; fn-arx-intern-step-refines: without the faithful read, or on a value that
; is not an arena, the two steps are not provably equal.
(local
 (must-fail
  (with-prover-step-limit 50000 (defthm pxt-refines-without-faithful
    (implies (fn-arena-p fn-arena)
             (equal (fn-arx-intern-step acc ws rs ps fn-arena)
                    (fn-srs-intern-step acc ws fn-arena)))))))

(local
 (must-fail
  (with-prover-step-limit 50000 (defthm pxt-refines-without-arena-p
    (implies (fn-arx-faithful-p rs ps)
             (equal (fn-arx-intern-step acc ws rs ps fn-arena)
                    (fn-srs-intern-step acc ws fn-arena)))))))

; Positive witness of the keystone: an empty chunk (every hypothesis true,
; both sides the accumulator and the arena unchanged).
(defthm pxt-refines-witness
  (and (fn-arena-p '((1 2)))
       (fn-arx-faithful-p nil nil)
       (equal (fn-arx-intern-step '(r0) nil nil nil '((1 2)))
              (fn-srs-intern-step '(r0) nil '((1 2))))
       (equal (fn-arx-intern-step '(r0) nil nil nil '((1 2))) (mv '(r0) '((1 2)))))
  :rule-classes nil)

; fn-arx-entry-ok-of-durable: without the recorded trailer being the digest,
; a read is not provably accepted; with it, it is.
(local
 (must-fail
  (with-prover-step-limit 50000 (defthm pxt-entry-ok-without-trailer
    (fn-arx-entry-ok (fn-durable-octets file eoff elen) trailer)))))

(defthm pxt-entry-ok-witness
  (fn-arx-entry-ok '(1 2 3) (fn-arx-octets-nat (fn-sha256 '(1 2 3)) 0))
  :rule-classes nil)

(assert-event (not (fn-arx-entry-ok '(1 2 3) 0)))
