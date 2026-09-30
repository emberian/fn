; Witnesses and teeth for books/payload-lz-record (the compressed record
; frame, lane compression-extents, PRF-326).
;
; The witness is codec-c1's real held-out 1993 Usenet article (alt.atheism,
; 750 octets, sha256 47eb37f1...2cba) and the streams zlib 9 wrote for
; it without and with a 2,749-octet dictionary; the article and dictionary come from
; planning/evidence/codec-c1-2026-09-27/witness.py, the two streams from
; planning/evidence/compress-2026-09-28/pz_witness.py.
(in-package "ACL2")
(include-book "../../books/payload-lz-replay")
; The codec attached to its seam, so the record's encoding and decoding execute.
(include-book "../../books/records-attach")
(include-book "must-fail-checked")


(include-book "payload-deflate-vectors")

; -----------------------------------------------------------------------------
; The frame books' functions are guard-verified; the payload witnesses
; above are zlib's streams (the stream written against the dictionary is
; 122 octets shorter than the one without).

(assert-event
 (and (eq (symbol-class 'fn-lzr-seal (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-lzr-expand (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-lzr-want-p (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-lzr-extent-of (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-lzr-read (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-lzr-dicts-add (w state)) :common-lisp-compliant)))

; -----------------------------------------------------------------------------
; The article as a record, its payload span, the tables.

(defconst *plr-w*
  (fn-record-make 7 7 1 "<30069@ursa.bear.com>" *plz-article* '("alt.atheism")
                  "o" "s" "e" 4 5))

(defconst *plr-r* (fn-record-encode-impl *plr-w*))

; The attached encoder is the codec: the same octets.
(assert-event (equal (fn-record-encode *plr-w*) *plr-r*))

; The payload span: the codec's place (books/payload-extent.lisp
; fn-arx-record-suffix-len: the payload item is followed by the suffix).
(defconst *plr-k* (- (len *plr-r*) (+ (fn-arx-record-suffix-len *plr-w*) 750)))

(defconst *plr-dicts* (list (cons 1 *plz-dict*) (cons 0 nil)))

(assert-event
 (and (fn-record-p *plr-w*)
      (fn-cbor-octet-listp *plr-r*)
      (natp *plr-k*)
      (equal (take 750 (nthcdr *plr-k* *plr-r*)) *plz-article*)
      (fn-lzr-dictsp *plr-dicts*)
      (not (fn-lzr-magicp *plr-r*))))

; -----------------------------------------------------------------------------
; The seal: the real block frames the record, without and with the
; dictionary; the frame is shorter than the record.

(defconst *plr-z0* (fn-lzr-seal nil 0 64 *plr-r* *plr-k* 750 *plz-block*))
(defconst *plr-z1* (fn-lzr-seal *plz-dict* 1 64 *plr-r* *plr-k* 750 *plz-dict-block*))

(assert-event
 (and (fn-lzr-magicp *plr-z0*)
      (fn-lzr-magicp *plr-z1*)
      (equal (len *plr-z0*) (+ (- (len *plr-r*) 750) 455 21))
      (equal (len *plr-z1*) (+ (- (len *plr-r*) 750) 333 21))
      (< (len *plr-z1*) (len *plr-z0*))
      (< (len *plr-z0*) (len *plr-r*))
      (equal (fn-lzr-expand *plr-dicts* *plr-z0*) (list :ok *plr-r*))
      (equal (fn-lzr-expand *plr-dicts* *plr-z1*) (list :ok *plr-r*))))

; The decision keeps the record: threshold 0 (off), a threshold above the
; span, a candidate that decodes to other octets, a candidate that does not
; shrink the record (the literal block), a span past the record.
(assert-event
 (and (equal (fn-lzr-seal nil 0 0 *plr-r* *plr-k* 750 *plz-block*) *plr-r*)
      (equal (fn-lzr-seal nil 0 751 *plr-r* *plr-k* 750 *plz-block*) *plr-r*)
      (equal (fn-lzr-seal nil 0 64 *plr-r* (1+ *plr-k*) 750 *plz-block*) *plr-r*)
      (equal (fn-lzr-seal nil 0 64 *plr-r* *plr-k* 750 (fn-pzd-stored *plz-article*))
             *plr-r*)
      (equal (fn-lzr-seal nil 0 64 *plr-r* (len *plr-r*) 750 *plz-block*) *plr-r*)
      ; the dictionary block against the empty dictionary: refused by the seal
      (equal (fn-lzr-seal nil 0 64 *plr-r* *plr-k* 750 *plz-dict-block*) *plr-r*)
      (fn-lzr-want-p 64 750)
      (not (fn-lzr-want-p 0 750))
      (not (fn-lzr-want-p 64 21))))

; The expansion refuses by name: an unknown dictionary, the wrong
; dictionary under the frame's id, a damaged frame.
(assert-event
 (and (equal (fn-lzr-expand (list (cons 0 nil)) *plr-z1*) (list :refused :lz-dictionary))
      (equal (fn-lzr-expand (list (cons 1 nil)) *plr-z1*) (list :refused :lz-decode))
      (equal (fn-lzr-expand *plr-dicts* (take 30 *plr-z0*)) (list :refused :lz-frame))))

; A record that begins with the frame's head is framed with an empty span
; (the escape), and expands to itself.
(defconst *plr-odd* (append *fn-lzr-magic* '(1 2 3)))
(assert-event
 (let ((z (fn-lzr-seal nil 0 64 *plr-odd* 0 0 nil)))
   (and (fn-lzr-magicp *plr-odd*)
        (not (equal z *plr-odd*))
        (equal (fn-lzr-expand *plr-dicts* z) (list :ok *plr-odd*)))))

; -----------------------------------------------------------------------------
; Teeth: fn-lzr-expand-of-seal.

; Reachable witness at the real record and block, every hypothesis and the
; conclusion affirmed on the :lz arm.
(defthm plr-expand-of-seal-witness
  (and (equal (assoc-equal 1 *plr-dicts*) (cons 1 *plz-dict*))
       (fn-lzr-u32p 1)
       (fn-lzr-u32p (len *plr-r*))
       (fn-cbor-octet-listp *plr-r*)
       (not (equal *plr-z1* *plr-r*))
       (equal (fn-lzr-expand *plr-dicts* *plr-z1*) (list :ok *plr-r*)))
  :rule-classes nil)

; Without the dictionary binding: the frame names id 1, the table binds 1
; to other octets (every other hypothesis holds); the conclusion fails.
(defthm plr-expand-of-seal-without-the-binding
  (let ((dicts (list (cons 1 nil))))
    (and (not (equal (assoc-equal 1 dicts) (cons 1 *plz-dict*)))
         (fn-lzr-u32p 1) (fn-lzr-u32p (len *plr-r*)) (fn-cbor-octet-listp *plr-r*)
         (not (equal (fn-lzr-expand dicts *plr-z1*) (list :ok *plr-r*)))))
  :rule-classes nil)

(must-fail-checked
 (defthm plr-expand-of-seal-no-binding
   (implies (and (fn-lzr-u32p dict-id) (fn-lzr-u32p (len r)) (fn-cbor-octet-listp r))
            (equal (fn-lzr-expand dicts (fn-lzr-seal dict dict-id min r k n candidate))
                   (list :ok r)))
   :hints (("Goal" :do-not-induct t))))

; Without a u32 dictionary id: a record that begins with the frame's head
; cannot be escaped under id 2^32, is kept, and expands to something else.
(defthm plr-expand-of-seal-without-u32-id
  (let ((dicts (list (cons 4294967296 nil))))
    (and (equal (assoc-equal 4294967296 dicts) (cons 4294967296 nil))
         (not (fn-lzr-u32p 4294967296))
         (fn-lzr-u32p (len *plr-odd*)) (fn-cbor-octet-listp *plr-odd*)
         (not (equal (fn-lzr-expand dicts (fn-lzr-seal nil 4294967296 64 *plr-odd* 0 0 nil))
                     (list :ok *plr-odd*)))))
  :rule-classes nil)

(must-fail-checked
 (defthm plr-expand-of-seal-no-u32-id
   (implies (and (equal (assoc-equal dict-id dicts) (cons dict-id dict))
                 (fn-lzr-u32p (len r)) (fn-cbor-octet-listp r))
            (equal (fn-lzr-expand dicts (fn-lzr-seal dict dict-id min r k n candidate))
                   (list :ok r)))
   :hints (("Goal" :do-not-induct t))))

; Without octets (a true list): an improper list that begins with the head.
(defconst *plr-improper* (list* 68 102 110 45 122 7))
(defthm plr-expand-of-seal-without-octets
  (let ((dicts (list (cons 0 nil))))
    (and (equal (assoc-equal 0 dicts) (cons 0 nil))
         (fn-lzr-u32p 0) (fn-lzr-u32p (len *plr-improper*))
         (not (fn-cbor-octet-listp *plr-improper*))
         (not (equal (fn-lzr-expand dicts (fn-lzr-seal nil 0 64 *plr-improper* 0 0 nil))
                     (list :ok *plr-improper*)))))
  :rule-classes nil)

(must-fail-checked
 (defthm plr-expand-of-seal-no-octets
   (implies (and (equal (assoc-equal dict-id dicts) (cons dict-id dict))
                 (fn-lzr-u32p dict-id) (fn-lzr-u32p (len r)))
            (equal (fn-lzr-expand dicts (fn-lzr-seal dict dict-id min r k n candidate))
                   (list :ok r)))
   :hints (("Goal" :do-not-induct t))))

; Without a u32 length: no ground record of 2^32 octets is built here; the
; theorem without the hypothesis is not proved (an escape frame's length
; field cannot hold such a record).
(must-fail-checked
 (defthm plr-expand-of-seal-no-u32-len
   (implies (and (equal (assoc-equal dict-id dicts) (cons dict-id dict))
                 (fn-lzr-u32p dict-id) (fn-cbor-octet-listp r))
            (equal (fn-lzr-expand dicts (fn-lzr-seal dict dict-id min r k n candidate))
                   (list :ok r)))
   :hints (("Goal" :do-not-induct t))))

; -----------------------------------------------------------------------------
; Teeth: fn-lzr-replay-reads-the-sealed-record.

;; The replay, executed through the attached codec: the frame expands to the
;; record's octets and they decode to the record, payload the article.
(assert-event
 (let ((x (fn-lzr-expand *plr-dicts* *plr-z1*)))
   (and (equal (car x) :ok)
        (equal (fn-record-decode-exact (cadr x)) (list :ok *plr-w*))
        (equal (fn-record-payload *plr-w*) *plz-article*))))

; The keystone at the reachable witness: every hypothesis holds of the real
; record, id and table.
(defthm plr-replay-witness
  (and (fn-record-p *plr-w*)
       (equal (assoc-equal 1 *plr-dicts*) (cons 1 *plz-dict*))
       (fn-lzr-u32p 1)
       (let ((x (fn-lzr-expand *plr-dicts* (fn-lzr-seal *plz-dict* 1 64 (fn-record-encode *plr-w*)
                                                        *plr-k* 750 *plz-dict-block*))))
         (and (equal (car x) :ok)
              (equal (fn-record-decode-exact (cadr x)) (list :ok *plr-w*)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-lzr-replay-reads-the-sealed-record
                                   (w *plr-w*) (dict-id 1) (dicts *plr-dicts*) (dict *plz-dict*)
                                   (min 64) (k *plr-k*) (n 750) (candidate *plz-dict-block*)))
           :in-theory (disable fn-lzr-replay-reads-the-sealed-record fn-lzr-expand fn-lzr-seal))))

(must-fail-checked
 (defthm plr-replay-no-record
   (implies (and (equal (assoc-equal dict-id dicts) (cons dict-id dict))
                 (fn-lzr-u32p dict-id))
            (let ((x (fn-lzr-expand dicts (fn-lzr-seal dict dict-id min (fn-record-encode w)
                                                       k n candidate))))
              (and (equal (car x) :ok)
                   (equal (fn-record-decode-exact (cadr x)) (list :ok w)))))
   :hints (("Goal" :do-not-induct t))))

; -----------------------------------------------------------------------------
; The compressed extent: Z at a one-record entry at 4096 of file 3.

(defconst *plr-pos* (list 4096 (+ 42 (len *plr-z1*) 32) (+ 4096 42) (len *plr-z1*)))
(defconst *plr-e* (fn-lzr-extent-of 3 *plr-pos* *plr-z1* *plz-article* *plr-dicts*))

(assert-event
 (and (fn-lzr-extentp *plr-e*)
      (equal (nth 0 *plr-e*) 3)
      (equal (nth 1 *plr-e*) 4096)
      (equal (nth 4 *plr-e*) 333)
      (equal (nth 6 *plr-e*) 750)
      (equal (nth 7 *plr-e*) 1)
      ; C sits at the extent's place in the frame
      (equal (take 333 (nthcdr (- (nth 3 *plr-e*) (+ 4096 42)) *plr-z1*)) *plz-dict-block*)
      (equal (fn-lzr-read *plz-dict* *plz-dict-block* 750) (list :ok *plz-article*))
      (equal (fn-lzr-read nil *plz-dict-block* 750) (list :refused :lz-decode))))

; No extent: a place of another length, a payload C does not decode to, an
; unknown dictionary, a record that is not a frame.
(assert-event
 (and (null (fn-lzr-extent-of 3 (list 4096 (+ 42 (len *plr-z1*) 32) (+ 4096 42) (1+ (len *plr-z1*)))
                              *plr-z1* *plz-article* *plr-dicts*))
      (null (fn-lzr-extent-of 3 *plr-pos* *plr-z1* (cdr *plz-article*) *plr-dicts*))
      (null (fn-lzr-extent-of 3 *plr-pos* *plr-z1* *plz-article* (list (cons 0 nil))))
      (null (fn-lzr-extent-of 3 *plr-pos* *plr-r* *plz-article* *plr-dicts*))))

; Teeth: fn-lzr-extent-read-denotes.  The positive witness takes the
; faithful read as its hypothesis (fn-durable-octets is the constrained
; file); every other antecedent is affirmed at the real frame.
(defthm plr-extent-read-witness
  (implies (equal (fn-durable-octets 3 (+ 4096 42) (len *plr-z1*)) *plr-z1*)
           (and *plr-e*
                (true-listp *plr-z1*)
                (equal (fn-lzr-read (cdr (assoc-equal (nth 7 *plr-e*) *plr-dicts*))
                                    (fn-durable-octets (nth 0 *plr-e*) (nth 3 *plr-e*) (nth 4 *plr-e*))
                                    (nth 6 *plr-e*))
                       (list :ok *plz-article*))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-lzr-extent-read-denotes
                                   (file 3) (position *plr-pos*) (z *plr-z1*)
                                   (payload *plz-article*) (dicts *plr-dicts*)))
           :in-theory (disable fn-lzr-extent-read-denotes fn-lzr-read fn-lzr-extent-of))))

; Without the faithful read the durable octets are unconstrained.
(must-fail-checked
 (defthm plr-extent-read-no-faithful
   (let ((e (fn-lzr-extent-of file position z payload dicts)))
     (implies (and e (true-listp z))
              (equal (fn-lzr-read (cdr (assoc-equal (nth 7 e) dicts))
                                  (fn-durable-octets (nth 0 e) (nth 3 e) (nth 4 e))
                                  (nth 6 e))
                     (list :ok payload))))
   :hints (("Goal" :do-not-induct t))))

; Without the extent: nothing ties the read to the payload.
(must-fail-checked
 (defthm plr-extent-read-no-extent
   (let ((e (fn-lzr-extent-of file position z payload dicts)))
     (implies (and (equal (fn-durable-octets (nfix file) (nfix (nth 2 position)) (len z)) z)
                   (true-listp z))
              (equal (fn-lzr-read (cdr (assoc-equal (nth 7 e) dicts))
                                  (fn-durable-octets (nth 0 e) (nth 3 e) (nth 4 e))
                                  (nth 6 e))
                     (list :ok payload))))
   :hints (("Goal" :do-not-induct t))))

; Ground: with no extent (a payload C does not decode to) the read of the
; frame's C is not that payload.
(defthm plr-extent-read-without-extent
  (and (null (fn-lzr-extent-of 3 *plr-pos* *plr-z1* (cdr *plz-article*) *plr-dicts*))
       (not (equal (fn-lzr-read *plz-dict* *plz-dict-block* 750) (list :ok (cdr *plz-article*)))))
  :rule-classes nil)

; Dictionaries are immutable once named.
(assert-event
 (and (equal (fn-lzr-dicts-add *plr-dicts* 1 *plz-dict*) (list :ok *plr-dicts*))
      (equal (fn-lzr-dicts-add *plr-dicts* 1 nil) (list :refused :lz-dictionary-rebound))
      (equal (fn-lzr-dicts-add *plr-dicts* 2 (make-list 65537 :initial-element 0))
             (list :refused :lz-dictionary-format))
      (equal (car (fn-lzr-dicts-add *plr-dicts* 2 '(1 2 3))) :ok)))

; -----------------------------------------------------------------------------
; The arena's compressed exports (books/payload-arena.lisp).

(defconst *plr-arena* (list *plz-article*))

; fn-arena-seal-lz-extent-payload has no hypothesis: the witness is its
; instance at the real extent over a one-payload arena.
(defthm plr-seal-lz-witness
  (and (equal (fn-arena-payload 1 (fn-arena-seal-lz-extent 3 4096 (nth 2 *plr-e*) (nth 3 *plr-e*) 333
                                                           0 750 *plz-dict* *plr-arena*))
              (fn-lzr-lz-value *plz-dict* (fn-durable-octets 3 (nth 3 *plr-e*) 333) 750))
       (equal (fn-arena-payload 0 (fn-arena-seal-lz-extent 3 4096 (nth 2 *plr-e*) (nth 3 *plr-e*) 333
                                                           0 750 *plz-dict* *plr-arena*))
              *plz-article*))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-arena-seal-lz-extent-payload
                                   (file 3) (eoff 4096) (elen (nth 2 *plr-e*)) (poff (nth 3 *plr-e*))
                                   (plen 333) (trailer 0) (n 750) (dict *plz-dict*)
                                   (fn-arena *plr-arena*) (h 0)))
           :in-theory (disable fn-arena-seal-lz-extent-payload))))

; fn-arena-reseat-lz-extent-keeps-a-faithful-arena: the positive witness
; under the faithful write (the block the log holds at the extent is the real
; block), every other hypothesis affirmed at the ground arena.
(defthm plr-reseat-lz-witness
  (implies (equal (fn-durable-octets 3 (nth 3 *plr-e*) 333) *plz-dict-block*)
           (and (fn-arena-p *plr-arena*)
                (< 0 (fn-arena-count *plr-arena*))
                (equal (fn-lzr-lz-value *plz-dict* (fn-durable-octets 3 (nth 3 *plr-e*) 333) 750)
                       (fn-arena-payload 0 *plr-arena*))
                (equal (fn-arena-reseat-lz-extent 0 3 4096 (nth 2 *plr-e*) (nth 3 *plr-e*) 333 0 750
                                                  *plz-dict* *plr-arena*)
                       *plr-arena*)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-arena-reseat-lz-extent-keeps-a-faithful-arena)
           :use ((:instance fn-arena-reseat-lz-extent-keeps-a-faithful-arena
                            (fn-arena *plr-arena*) (h 0) (file 3) (eoff 4096)
                            (elen (nth 2 *plr-e*)) (poff (nth 3 *plr-e*)) (plen 333) (trailer 0)
                            (n 750) (dict *plz-dict*))
                 (:instance fn-lzr-lz-value-of-decode
                            (dict *plz-dict*) (c *plz-dict-block*) (n 750)
                            (payload *plz-article*))))))

; Without the value hypothesis: the value the block decodes to need not be
; the handle's payload.
(must-fail-checked
 (defthm plr-reseat-lz-no-value
   (implies (and (fn-arena-p fn-arena) (natp h) (< h (fn-arena-count fn-arena)))
            (equal (fn-arena-reseat-lz-extent h file eoff elen poff plen trailer n dict fn-arena)
                   fn-arena))
   :hints (("Goal" :do-not-induct t))))

; Ground: the other dictionary's value is not the article.
(assert-event
 (not (equal (fn-lzr-lz-value nil *plz-dict-block* 750) *plz-article*)))

; -----------------------------------------------------------------------------
; The replay's intern and the commit's reseat with compressed records.

; The intern step: under the faithful place of the frame, the step with
; compressed extents is the resident step (the witness is the keystone's
; instance at the real frame, place and table).
(defthm plr-intern-step-witness
  (implies (equal (fn-durable-octets 3 (+ 4096 42) (len *plr-z1*)) *plr-z1*)
           (and (fn-arena-p *plr-arena*)
                (fn-arx-faithful-p (list *plr-z1*) (list (cons 3 *plr-pos*)))
                (equal (fn-lzr-intern-step nil (list *plr-w*) (list *plr-z1*)
                                           (list (cons 3 *plr-pos*)) *plr-dicts* *plr-arena*)
                       (fn-srs-intern-step nil (list *plr-w*) *plr-arena*))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-lzr-intern-step-refines fn-lzr-intern-step
                                      fn-srs-intern-step)
           :use ((:instance fn-lzr-intern-step-refines
                            (acc nil) (ws (list *plr-w*)) (zs (list *plr-z1*))
                            (ps (list (cons 3 *plr-pos*))) (dicts *plr-dicts*)
                            (fn-arena *plr-arena*))))))

(must-fail-checked
 (defthm plr-intern-step-no-faithful
   (implies (fn-arena-p fn-arena)
            (equal (fn-lzr-intern-step acc ws zs ps dicts fn-arena)
                   (fn-srs-intern-step acc ws fn-arena)))
   :hints (("Goal" :do-not-induct t))))

; The commit's reseat: a fenced member (handle 0, file 3, the frame's place)
; under the faithful write leaves the arena.
(defthm plr-commit-reseats-witness
  (implies (equal (fn-durable-octets 3 (+ 4096 42) (len *plr-z1*)) *plr-z1*)
           (and (fn-arena-p *plr-arena*)
                (fn-arx-commit-faithful-p (list (list 0 3 *plr-pos* *plr-z1*)))
                (equal (fn-lzr-commit-reseats (list (list 0 3 *plr-pos* *plr-z1*)) *plr-dicts*
                                              *plr-arena*)
                       *plr-arena*)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-lzr-commit-reseats-keep-the-arena fn-lzr-commit-reseats)
           :use ((:instance fn-lzr-commit-reseats-keep-the-arena
                            (members (list (list 0 3 *plr-pos* *plr-z1*))) (dicts *plr-dicts*)
                            (fn-arena *plr-arena*))))))

(must-fail-checked
 (defthm plr-commit-reseats-no-faithful
   (implies (fn-arena-p fn-arena)
            (equal (fn-lzr-commit-reseats members dicts fn-arena) fn-arena))
   :hints (("Goal" :do-not-induct t))))

; The host's realizer runs fn-lzr-lz-read: the real block reads as the
; article; the block against the empty dictionary is refused by name.
(assert-event
 (and (equal (fn-lzr-lz-read *plz-dict* *plz-dict-block* 750) (list :ok *plz-article*))
      (equal (fn-lzr-lz-read nil *plz-dict-block* 750) (list :refused :lz-decode))
      (equal (fn-lzr-lz-read *plz-dict* *plz-dict-block* 749) (list :refused :lz-decode))))

; The chunk expansion: a frame and a plain record expand; a frame under an
; unknown dictionary makes the chunk :bad (the open refuses it).
(assert-event
 (and (equal (fn-lzr-expand-chunk *plr-dicts* (list *plr-z1* *plr-r*)) (list *plr-r* *plr-r*))
      (equal (fn-lzr-expand-chunk (list (cons 0 nil)) (list *plr-z1*)) :bad)))
