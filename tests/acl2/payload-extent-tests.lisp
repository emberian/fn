; Tests for books/payload-extent.lisp (lane arena-offheap-2, PRF-294).
;
; 1. The exec functions the host calls are guard-verified.
; 2. The codec's place of the payload is right on a real record: a record
;    encoded by the store's codec (fn-record-encode-impl), placed at an entry
;    start, yields a verified extent whose slice of the record octets is the
;    payload; a record whose octets do not hold the payload there yields nil.
; 3. Teeth: positive witnesses and must-fails for the keystones.

(in-package "ACL2")
(include-book "../../books/payload-extent")
; The attached frame digest, so the log's own encoder (fn-lg-log) executes.
(include-book "../../books/crypto-attach")
(include-book "must-fail-checked")

(assert-event
 (and (eq (symbol-class 'fn-arx-list-places (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arx-extent-of (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arx-intern-event (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arx-intern-events (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arx-intern-step (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arx-cat-intern-extent (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arx-entry-ok (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arx-read-cache-entries (w state)) :common-lisp-compliant)))

; The chunk fold of the keystone is a model of the host's loop, not executed.
(assert-event (eq (symbol-class 'fn-arx-steps (w state)) :ideal))

(defconst *pxt-payload*
  (append (fn-record-string-octets "Subject: a") '(13 10 13 10)
          (fn-record-string-octets "body line") '(13 10)))

(defconst *pxt-w*
  (fn-record-make 7 7 1 "<x@fn.invalid>" *pxt-payload* '("fn.test") "o" "s" "e" 4 5))

(defconst *pxt-r* (fn-record-encode-impl *pxt-w*))

; The record's place: a one-record entry at start 4096 of file 3, frame
; length 42 + |r| + 32, the record at 4096 + 42, |r| octets.
(defconst *pxt-pos* (list 4096 (+ 42 (len *pxt-r*) 32) (+ 4096 42) (len *pxt-r*)))

(assert-event (consp *pxt-r*))

(assert-event
 (let ((x (fn-arx-extent-of 3 *pxt-pos* *pxt-r* *pxt-w*)))
   (and (fn-arn-extentp x)
        (equal (nth 0 x) 3)
        (equal (nth 1 x) 4096)
        (equal (nth 2 x) (+ 42 (len *pxt-r*)))
        (equal (nth 4 x) (len *pxt-payload*))
        (equal (nth 5 x) 0)
        ; the payload's place inside the record octets is where the payload is
        (equal (take (nth 4 x) (nthcdr (- (nth 3 x) (+ 4096 42)) *pxt-r*)) *pxt-payload*))))

; A frame length that does not match the record, or octets that do not hold
; the payload at the codec's place, give no extent (the record stays resident).
(assert-event (null (fn-arx-extent-of 3 (list 4096 (+ 42 (len *pxt-r*) 32) (+ 4096 42) (1+ (len *pxt-r*)))
                                      *pxt-r* *pxt-w*)))
(assert-event (null (fn-arx-extent-of 3 (list 4096 (+ 41 (len *pxt-r*) 32) (+ 4096 42) (len *pxt-r*))
                                      *pxt-r* *pxt-w*)))
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
 (must-fail-checked
  (with-prover-step-limit 50000 (defthm pxt-denotes-without-faithful
    (implies (fn-arx-extent-of 3 *pxt-pos* *pxt-r* *pxt-w*)
             (equal (fn-durable-octets 3 (nth 3 (fn-arx-extent-of 3 *pxt-pos* *pxt-r* *pxt-w*))
                                       (len *pxt-payload*))
                    *pxt-payload*))))))

; fn-arx-intern-step-refines still needs faithful bytes.  Arena validity,
; however, is unnecessary, as the strengthened event fold proves.
(local
 (must-fail-checked
  (with-prover-step-limit 50000 (defthm pxt-refines-without-faithful
    (implies (fn-arena-p fn-arena)
             (equal (fn-arx-intern-step acc ws rs ps fn-arena)
                    (fn-srs-intern-step acc ws fn-arena)))))))

(defthm pxt-refines-without-arena-p
  (implies (fn-arx-faithful-p rs ps)
           (equal (fn-arx-intern-step acc ws rs ps fn-arena)
                  (fn-srs-intern-step acc ws fn-arena)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-arx-intern-events fn-intern-events))))

; Positive witness of the keystone: an empty chunk (every hypothesis true,
; both sides the accumulator and the arena unchanged).
(defthm pxt-refines-witness
  (and (fn-arena-p '((1 2)))
       (fn-arx-faithful-p nil nil)
       (equal (fn-arx-intern-step '(r0) nil nil nil '((1 2)))
              (fn-srs-intern-step '(r0) nil '((1 2))))
       (equal (fn-arx-intern-step '(r0) nil nil nil '((1 2))) (mv '(r0) '((1 2)))))
  :rule-classes nil)

;; KEYSTONE fn-arx-steps-are-one-step-of-the-concatenation (the chunk
;; stream).  Positive witness: a chunk of one record R with no place (the
;; faithful condition holds by computation), every hypothesis asserted with
;; the conclusion.  (The record decode is not executable in this world --
;; fn-record-decode-exact is attached in the image -- so the witness is
;; symbolic in R and the arena.)
(defthm pxt-chunks-witness
  (implies (fn-arena-p fn-arena)
           (and (fn-srs-chunksp (list (list r)))
                (fn-arx-faithful-chunks-p (list (list r)) (list (list nil)))
                (let ((steps (fn-arx-steps (list (list r)) (list (list nil)) acc fn-arena))
                      (one (fn-srs-step acc (fn-srs-concat (list (list r))) fn-arena)))
                  (and (iff (eq (mv-nth 0 steps) :bad) (eq (mv-nth 0 one) :bad))
                       (implies (not (eq (mv-nth 0 one) :bad))
                                (equal steps one))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-arx-steps-are-one-step-of-the-concatenation
                                   (chunks (list (list r))) (placess (list (list nil)))))
           :in-theory (union-theories '(fn-srs-chunksp fn-arx-faithful-chunks-p fn-arx-faithful-p
                                        true-listp iff car-cons cdr-cons (:e consp) (:e atom))
                                      (theory 'minimal-theory)))))

;; Hypothesis-removal must-fails (bounded search: a failed search, not a
;; counterexample).
(local
 (must-fail-checked
  (with-prover-step-limit 50000 (defthm pxt-chunks-without-faithful
    (implies (and (fn-arena-p fn-arena) (fn-srs-chunksp chunks))
             (equal (fn-arx-steps chunks placess acc fn-arena)
                    (fn-srs-steps chunks acc fn-arena)))))))

(local
 (must-fail-checked
  (with-prover-step-limit 50000 (defthm pxt-chunks-without-arena-p
    (implies (and (fn-srs-chunksp chunks) (fn-arx-faithful-chunks-p chunks placess))
             (equal (fn-arx-steps chunks placess acc fn-arena)
                    (fn-srs-steps chunks acc fn-arena)))))))

(local
 (must-fail-checked
  (with-prover-step-limit 50000 (defthm pxt-chunks-without-chunksp
    (implies (and (fn-arena-p fn-arena) (fn-arx-faithful-chunks-p chunks placess))
             (let ((steps (fn-arx-steps chunks placess acc fn-arena))
                   (one (fn-srs-step acc (fn-srs-concat chunks) fn-arena)))
               (implies (not (eq (mv-nth 0 one) :bad))
                        (equal steps one))))))))

;; A record with no place needs no faithful read (fn-arx-intern-event-without-place).
(defthm pxt-without-place-witness
  (equal (fn-arx-intern-event w r nil 7 nil 0 fn-arena)
         (fn-intern-event w nil 0 fn-arena))
  :rule-classes nil)

; fn-arx-entry-ok-of-durable: without the file holding the prefix's digest
; after it, a read is not provably accepted; with it, it is.
(local
 (must-fail-checked
  (with-prover-step-limit 50000 (defthm pxt-entry-ok-without-trailer
    (implies (natp elen)
             (fn-arx-entry-ok (append (fn-durable-octets file eoff elen)
                                      (fn-durable-octets file (+ eoff elen) 32))
                              elen))))))

(defthm pxt-entry-ok-witness
  (fn-arx-entry-ok (append '(1 2 3) (fn-blake3 '(1 2 3))) 3)
  :rule-classes nil)

; A torn trailer (zeros) and a short read are refused.
(assert-event (not (fn-arx-entry-ok (append '(1 2 3) (make-list 32 :initial-element 0)) 3)))
(assert-event (not (fn-arx-entry-ok (append '(1 2) (fn-blake3 '(1 2 3))) 3)))

;; The places, against the log's OWN encoder: two batches written as
;; fn-lg-log writes them (the second chained from the first's last trailer),
;; the first of three small records (one kind-2 chunk entry: their u32
;; lengths packed), the second of one record (a kind-1 entry).  Every place
;; the walker answers holds its record, over the whole written octets (the
;; commit's) and over each entry alone at its offset (the open's stream).
(defconst *pxt-b1* (list (make-list 5 :initial-element 1) (make-list 7 :initial-element 2)
                         (make-list 300 :initial-element 3)))
(defconst *pxt-b2* (list (make-list 900 :initial-element 4)))
; (Macros, not constants: the frame digest runs through its attachment,
; which a defconst may not call.)
(defmacro pxt-log1 () '(fn-lg-log *pxt-b1* *fn-lg-genesis* 4096))
(defmacro pxt-log ()
  '(append (pxt-log1)
           (fn-lg-log *pxt-b2* (fn-lg-last-trailer *pxt-b1* *fn-lg-genesis*) 4096)))

(defun pxt-places-hold (places records octets)
  (if (atom records)
      (atom places)
    (and (consp places)
         (equal (nth 3 (car places)) (len (car records)))
         (equal (take (len (car records)) (nthcdr (nth 2 (car places)) octets)) (car records))
         (pxt-places-hold (cdr places) (cdr records) octets))))

(assert-event
 (let ((ps (fn-arx-list-places (pxt-log) 0 4 4096 0 0 nil 0 0 nil)))
   (and (equal (len ps) 4)
        (pxt-places-hold ps (append *pxt-b1* *pxt-b2*) (pxt-log))
        ; the three small records share one entry (kind 2), the fourth has its own
        (equal (nth 0 (nth 0 ps)) 0) (equal (nth 0 (nth 2 ps)) 0)
        (equal (nth 0 (nth 3 ps)) 4096))))

;; Each entry alone at its offset, as the stream reads it: the first entry
;; (the three-record chunk, 398 octets) at 0, the second at 4096.
(assert-event
 (and (equal (fn-arx-list-places (take 398 (pxt-log)) 0 3 4096 0 0 nil 0 0 nil)
             (take 3 (fn-arx-list-places (pxt-log) 0 4 4096 0 0 nil 0 0 nil)))
      (equal (fn-arx-list-places (nthcdr 4096 (pxt-log)) 4096 1 4096 0 0 nil 0 0 nil)
             (nthcdr 3 (fn-arx-list-places (pxt-log) 0 4 4096 0 0 nil 0 0 nil)))))

; More records than the entries hold, or a count of zero entries' worth past
; the end: nil (every record stays resident).
(assert-event (null (fn-arx-list-places (pxt-log) 0 5 4096 0 0 nil 0 0 nil)))
(assert-event (null (fn-arx-list-places (pxt-log1) 0 4 4096 0 0 nil 0 0 nil)))

; The event fold's teeth.  The arena premise was proved unnecessary in
; payload-extent: both logical seals use the same snoc on arbitrary values.
; A changed payload byte provides a ground counterexample to the remaining
; faithful-bytes premise and to the conclusion together.
(include-book "teeth-ground-lemma")

; A closed logical fixture: one well-typed event, one placed nonempty
; durable slice, and a one-octet payload at the codec's suffix-relative
; position.  These are ground terms over the existing durable seam, not
; an attachment or a claim that a particular physical file exists.  The
; event fold does not decode the record; decoding is the caller's job.
(defmacro pxt-teeth-w ()
  '(fn-record-make 7 7 1 "<x@fn.invalid>" (fn-durable-octets 3 42 1)
                   '("fn.test") "o" "s" "e" 4 5))
(defconst *pxt-teeth-size* (+ 1 (fn-arx-record-suffix-len *pxt-w*)))
(defmacro pxt-teeth-r () '(fn-durable-octets 3 42 *pxt-teeth-size*))
(defconst *pxt-teeth-position*
  (list 0 (+ 42 *pxt-teeth-size* 32) 42 *pxt-teeth-size*))

; Assert validity of the initial arena and that the placed branch really
; seals a one-byte extent, rather than taking the no-place resident path.
(defthm pxt-teeth-placed
  (and (fn-arena-p nil)
       (fn-record-p (pxt-teeth-w))
       (equal (fn-arx-extent-of 3 *pxt-teeth-position* (pxt-teeth-r) (pxt-teeth-w))
              (list 3 0 (+ 42 *pxt-teeth-size*) 42 1 0)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-durable-octets-unfold
                            (file 3) (off 42) (len *pxt-teeth-size*)))
           :in-theory (enable fn-arena-p fn-record-p fn-record-payloadp
                              fn-arx-extent-of fn-durable-octets-unfold))))

(defthm pxt-one-event-has-row
  (implies (fn-record-p w)
           (consp (mv-nth 0 (fn-intern-events (list w) nil 0 fn-arena))))
  :hints (("Goal" :in-theory
           (e/d (fn-intern-events fn-intern-event fn-cat-intern-list)
                (fn-record-p fn-held-facts-of fn-held-context-of
                 fn-arena-seal-list)))))

(defconst *pxt-events-claim*
  '(((faithful (fn-arx-faithful-p rs ps)))
    (equal (fn-arx-intern-events ws rs ps keyring generation arena-value)
           (fn-intern-events ws keyring generation arena-value))))

(teeth-ground-lemma pxt-events-positive *pxt-events-claim*
  ((ws (list (pxt-teeth-w))) (rs (list (pxt-teeth-r)))
   (ps (list (cons 3 *pxt-teeth-position*)))
   (keyring nil) (generation 0) (arena-value nil))
  :hints (("Goal" :in-theory (disable fn-arx-intern-events fn-intern-events))))

(teeth-ground-lemma pxt-events-dropped-row *pxt-events-claim*
  ((ws (list (pxt-teeth-w))) (rs (list (pxt-teeth-r)))
   (ps (list (cons 3 *pxt-teeth-position*)))
   (keyring nil) (generation 0) (arena-value nil))
  :mutation (:conclusion
             (equal (mv-nth 0 (fn-arx-intern-events ws rs ps keyring generation arena-value)) nil))
  :hints (("Goal" :use (pxt-teeth-placed
                       (:instance pxt-one-event-has-row (w (pxt-teeth-w)) (fn-arena nil)))
           :in-theory (disable fn-arx-intern-events fn-intern-events fn-record-p
                               fn-arx-extent-of))))

; Flip the durable byte between zero and nonzero, preserving the octet
; guard.  The presented record contains the changed byte; its extent still
; denotes the original durable byte.  Both faithfulness and equality fail.
(defmacro pxt-teeth-other-byte ()
  '(if (equal (fn-durable-octet 3 42) 0) 1 0))
(defmacro pxt-teeth-bad-w ()
  '(fn-record-make 7 7 1 "<x@fn.invalid>" (list (pxt-teeth-other-byte))
                   '("fn.test") "o" "s" "e" 4 5))
(defmacro pxt-teeth-bad-r ()
  '(cons (pxt-teeth-other-byte) (cdr (pxt-teeth-r))))
(defthm pxt-teeth-bad-placed
  (and (fn-record-p (pxt-teeth-bad-w))
       (equal (fn-arx-extent-of 3 *pxt-teeth-position* (pxt-teeth-bad-r) (pxt-teeth-bad-w))
              (list 3 0 (+ 42 *pxt-teeth-size*) 42 1 0)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-durable-octets-unfold
                            (file 3) (off 42) (len *pxt-teeth-size*)))
           :in-theory (enable fn-record-p fn-record-payloadp
                              fn-arx-extent-of fn-durable-octets-unfold))))
(teeth-ground-lemma pxt-events-without-faithful *pxt-events-claim*
  ((ws (list (pxt-teeth-bad-w))) (rs (list (pxt-teeth-bad-r)))
   (ps (list (cons 3 *pxt-teeth-position*)))
   (keyring nil) (generation 0) (arena-value nil))
  :without faithful
  :hints (("Goal"
           :use (pxt-teeth-bad-placed
                 (:instance fn-durable-octets-unfold
                            (file 3) (off 42) (len *pxt-teeth-size*)))
           :in-theory
           (e/d (fn-arx-intern-events fn-intern-events fn-arx-intern-event
                 fn-intern-event fn-arx-cat-intern-extent fn-cat-intern-list
                 fn-arena-seal-extent fn-arena-seal-list fn-durable-octets-unfold)
                (fn-record-p fn-held-facts-of fn-held-context-of fn-arx-extent-of)))))

(defteeth fn-arx-intern-events-refines
  :claim (((faithful (fn-arx-faithful-p rs ps)))
          (equal (fn-arx-intern-events ws rs ps keyring generation arena-value)
                 (fn-intern-events ws keyring generation arena-value)))
  :subject fn-arx-intern-events
  :witness ((ws (list (pxt-teeth-w))) (rs (list (pxt-teeth-r)))
            (ps (list (cons 3 *pxt-teeth-position*)))
            (keyring nil) (generation 0) (arena-value nil))
  :witness-lemma pxt-events-positive
  :breaks ((faithful
            ((ws (list (pxt-teeth-bad-w))) (rs (list (pxt-teeth-bad-r)))
             (ps (list (cons 3 *pxt-teeth-position*)))
             (keyring nil) (generation 0) (arena-value nil))
            :lemma pxt-events-without-faithful))
  :mutations ((dropped-row
               (:conclusion
                (equal (mv-nth 0 (fn-arx-intern-events ws rs ps keyring generation arena-value)) nil))
               ((ws (list (pxt-teeth-w))) (rs (list (pxt-teeth-r)))
                (ps (list (cons 3 *pxt-teeth-position*)))
                (keyring nil) (generation 0) (arena-value nil))
               :fault "the extent fold seals the payload but drops the returned row"
               :lemma pxt-events-dropped-row)))
