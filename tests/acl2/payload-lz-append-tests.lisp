; Witnesses and teeth for books/payload-lz-append (the append of a compressed
; record, lane compression-extents-2).
;
; The witness is the predecessor's: codec-c1's real held-out 1993 article
; (750 octets) as a record through the attached codec, and the blocks
; zlib 9 wrote for it (tests/acl2/payload-lz-record-tests.lisp, whose
; constants this book includes: *plr-r* the record, *plr-k* its payload
; span, *plz-block* the block alone, *plz-dict-block* the block against the
; 2,749-octet dictionary *plz-dict*, *plr-z0* the seal with *plz-block*).
(in-package "ACL2")
(include-book "../../books/payload-lz-append")
(include-book "payload-lz-record-tests")

(assert-event
 (and (eq (symbol-class 'fn-lzr-append-plan (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-lzr-append-decide (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-lzr-record-span (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-lzr-read-refusal-text (w state)) :common-lisp-compliant)))

(defconst *pla-dicts* (fn-lzr-dicts-initial))   ; ID 0, the empty dictionary

; -----------------------------------------------------------------------------
; The plan: ACL2's span of the real record; off at 0, above the span, and
; for anything that is not a record (a frame, junk).

(assert-event
 (and (equal (fn-lzr-record-span *plr-r*) (cons *plr-k* 750))
      (equal (fn-lzr-append-plan 64 *plr-r*) (cons *plr-k* 750))
      (equal (fn-lzr-append-plan 750 *plr-r*) (cons *plr-k* 750))
      (equal (fn-lzr-append-plan 0 *plr-r*) nil)
      (equal (fn-lzr-append-plan 751 *plr-r*) nil)
      (equal (fn-lzr-append-plan 64 *plr-z0*) nil)
      (equal (fn-lzr-append-plan 64 '(1 2 3)) nil)
      (equal (fn-lzr-candidate-cap 750) 728)
      (equal (fn-lzr-candidate-cap 22) 0)))

; -----------------------------------------------------------------------------
; The decision, each outcome on the real record.

(defconst *pla-framed* (fn-lzr-append-decide nil 0 64 *plr-r* *plr-k* 750 *plz-block*))

(assert-event
 (and (equal *pla-framed* (list :framed *plr-z0*))
      (equal (fn-lzr-append-octets *pla-framed* *plr-r*) *plr-z0*)
      (equal (fn-lzr-expand *pla-dicts* *plr-z0*) (list :ok *plr-r*))
      (< (len *plr-z0*) (len *plr-r*))
      ; the encoder found no block within the cap: the policy keeps R
      (equal (fn-lzr-append-decide nil 0 64 *plr-r* *plr-k* 750 :none) (list :kept :lz-no-gain))
      ; a candidate that decodes to the span but does not shrink it (the literal block)
      (equal (fn-lzr-append-decide nil 0 64 *plr-r* *plr-k* 750
                                   (fn-pzd-stored *plz-article*))
             (list :kept :lz-no-gain))
      (equal (fn-lzr-append-octets (list :kept :lz-no-gain) *plr-r*) *plr-r*)
      ; a span past the record
      (equal (fn-lzr-append-decide nil 0 64 *plr-r* (len *plr-r*) 750 *plz-block*)
             (list :kept :lz-span))
      ; the dictionary block against the empty dictionary: refused by name
      (equal (fn-lzr-append-decide nil 0 64 *plr-r* *plr-k* 750 *plz-dict-block*)
             (list :refused :lz-candidate))
      ; the right block for the wrong span: refused by name
      (equal (fn-lzr-append-decide nil 0 64 *plr-r* (1+ *plr-k*) 750 *plz-block*)
             (list :refused :lz-candidate))
      ; a damaged block (one octet flipped): refused by name
      (equal (fn-lzr-append-decide nil 0 64 *plr-r* *plr-k* 750
                                   (update-nth 40 (logxor 1 (nth 40 *plz-block*)) *plz-block*))
             (list :refused :lz-candidate))
      (stringp (fn-lzr-append-refusal-text (list :refused :lz-candidate)))
      (equal (fn-lzr-append-refusal-text *pla-framed*) nil)
      ; the read refusals carry lines
      (stringp (fn-lzr-read-refusal-text (list :refused :lz-frame)))
      (stringp (fn-lzr-read-refusal-text (list :refused :lz-dictionary)))
      (stringp (fn-lzr-read-refusal-text (list :refused :lz-decode)))
      (equal (fn-lzr-read-refusal-text (list :ok *plr-r*)) nil)))

; -----------------------------------------------------------------------------
; KEYSTONE fn-lzr-append-decide-framed-expands.

(defthm pla-framed-expands-witness
  (and (equal (car (fn-lzr-append-decide nil 0 64 *plr-r* *plr-k* 750 *plz-block*)) :framed)
       (equal (assoc-equal 0 *pla-dicts*) (cons 0 nil))
       (equal (fn-lzr-expand *pla-dicts*
                             (cadr (fn-lzr-append-decide nil 0 64 *plr-r* *plr-k* 750 *plz-block*)))
              (list :ok *plr-r*)))
  :rule-classes nil)

; Without the framed outcome: a refused decision's second element is its
; name, which is not R.
(defthm pla-framed-expands-without-framed
  (let ((d (fn-lzr-append-decide nil 0 64 *plr-r* *plr-k* 750 *plz-dict-block*)))
    (and (not (equal (car d) :framed))
         (equal (assoc-equal 0 *pla-dicts*) (cons 0 nil))
         (not (equal (fn-lzr-expand *pla-dicts* (cadr d)) (list :ok *plr-r*)))))
  :rule-classes nil)

(must-fail-checked
 (defthm pla-framed-expands-no-framed
   (implies (equal (assoc-equal dict-id dicts) (cons dict-id dict))
            (equal (fn-lzr-expand dicts (cadr (fn-lzr-append-decide dict dict-id min r k n
                                                                    candidate)))
                   (list :ok r)))
   :hints (("Goal" :do-not-induct t))))

; Without the binding: the table binds no dictionary 0.
(defthm pla-framed-expands-without-the-binding
  (let ((d (fn-lzr-append-decide nil 0 64 *plr-r* *plr-k* 750 *plz-block*)))
    (and (equal (car d) :framed)
         (not (equal (assoc-equal 0 nil) (cons 0 nil)))
         (equal (fn-lzr-expand nil (cadr d)) (list :refused :lz-dictionary))))
  :rule-classes nil)

(must-fail-checked
 (defthm pla-framed-expands-no-binding
   (implies (equal (car (fn-lzr-append-decide dict dict-id min r k n candidate)) :framed)
            (equal (fn-lzr-expand dicts (cadr (fn-lzr-append-decide dict dict-id min r k n
                                                                    candidate)))
                   (list :ok r)))
   :hints (("Goal" :do-not-induct t))))

; -----------------------------------------------------------------------------
; fn-lzr-append-decide-refuses-exactly-a-bad-candidate: both directions at
; the real record (the right-hand side holds for the dictionary block, fails
; for the real block and for :none).

(defthm pla-refuses-exactly-witness
  (and (equal (fn-lzr-append-decide nil 0 64 *plr-r* *plr-k* 750 *plz-dict-block*)
              (list :refused :lz-candidate))
       (fn-lzr-span-okp *plr-r* *plr-k* 750) (fn-lzr-u32p 0)
       (not (eq *plz-dict-block* :none))
       (not (equal (fn-pzd-decode nil *plz-dict-block* 750)
                   (list :ok (take 750 (nthcdr *plr-k* *plr-r*)))))
       (not (equal (fn-lzr-append-decide nil 0 64 *plr-r* *plr-k* 750 *plz-block*)
                   (list :refused :lz-candidate)))
       (equal (fn-pzd-decode nil *plz-block* 750) (list :ok (take 750 (nthcdr *plr-k* *plr-r*))))
       (not (equal (fn-lzr-append-decide nil 0 64 *plr-r* *plr-k* 750 :none)
                   (list :refused :lz-candidate))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; fn-lzr-append-decide-framed-is-shorter and -is-the-seal.

(defthm pla-framed-is-shorter-witness
  (let ((d (fn-lzr-append-decide nil 0 64 *plr-r* *plr-k* 750 *plz-block*)))
    (and (equal (car d) :framed)
         (equal (cadr d) (fn-lzr-seal nil 0 64 *plr-r* *plr-k* 750 *plz-block*))
         (fn-lzr-compress-p 64 750 (len *plz-block*))
         (< (len (cadr d)) (len *plr-r*))))
  :rule-classes nil)

(must-fail-checked
 (defthm pla-shorter-no-framed
   (< (len (fn-lzr-append-octets (fn-lzr-append-decide dict dict-id min r k n candidate) r))
      (len r))
   :hints (("Goal" :do-not-induct t))))

; -----------------------------------------------------------------------------
; fn-lzr-record-is-not-a-frame.

; pla-record-is-not-a-frame-witness (evaluated: the codec is the attached one)
(assert-event
  (and (fn-record-result-okp (fn-record-decode-exact *plr-r*))
       (not (fn-lzr-magicp *plr-r*))
       (equal (fn-lzr-expand *pla-dicts* *plr-r*) (list :ok *plr-r*))))

; Without a record: the frame is no record, and it is a frame.
; pla-record-is-not-a-frame-without-a-record (evaluated: the codec is the attached one)
(assert-event
  (and (not (fn-record-result-okp (fn-record-decode-exact *plr-z0*)))
       (fn-lzr-magicp *plr-z0*)
       (not (equal (fn-lzr-expand *pla-dicts* *plr-z0*) (list :ok *plr-z0*)))))

(must-fail-checked
 (defthm pla-not-a-frame-no-record
   (not (fn-lzr-magicp r))
   :hints (("Goal" :do-not-induct t))))

; -----------------------------------------------------------------------------
; fn-lzr-append-replay-reads-the-record (the digests are over the original
; octets): framed and kept, the log's octets read back as R, which decodes
; to the sealed record.

; pla-replay-reads-the-record-witness (evaluated: the codec is the attached one)
(assert-event
  (let ((d (fn-lzr-append-decide nil 0 64 *plr-r* *plr-k* 750 *plz-block*))
        (kept (fn-lzr-append-decide nil 0 64 *plr-r* *plr-k* 750 :none)))
    (and (fn-record-result-okp (fn-record-decode-exact *plr-r*))
         (equal (assoc-equal 0 *pla-dicts*) (cons 0 nil))
         (equal (car d) :framed)
         (equal (fn-lzr-expand *pla-dicts* (fn-lzr-append-octets d *plr-r*)) (list :ok *plr-r*))
         (equal (fn-record-decode-exact *plr-r*) (list :ok *plr-w*))
         (equal (car kept) :kept)
         (equal (fn-lzr-expand *pla-dicts* (fn-lzr-append-octets kept *plr-r*))
                (list :ok *plr-r*)))))

; Without the record: a frame-headed input is expanded, not passed through.
; (The theorem had a third hypothesis, that the decision is not refused; the
; weakened theorem was proved first and the hypothesis removed.)
; pla-replay-without-a-record (evaluated: the codec is the attached one)
(assert-event
  (let ((junk (append *fn-lzr-magic* '(0 0 0 0))))
    (and (not (fn-record-result-okp (fn-record-decode-exact junk)))
         (equal (car (fn-lzr-append-decide nil 0 64 junk 0 0 :none)) :kept)
         (not (equal (fn-lzr-expand *pla-dicts* (fn-lzr-append-octets
                                                (fn-lzr-append-decide nil 0 64 junk 0 0 :none)
                                                junk))
                     (list :ok junk))))))

(must-fail-checked
 (defthm pla-replay-no-record
   (implies (equal (assoc-equal dict-id dicts) (cons dict-id dict))
            (equal (car (fn-lzr-expand dicts (fn-lzr-append-octets
                                              (fn-lzr-append-decide dict dict-id min r k n
                                                                    candidate)
                                              r)))
                   :ok))
   :hints (("Goal" :do-not-induct t))))

; Without the binding: the framed record under an empty table.
; pla-replay-without-the-binding (evaluated: the codec is the attached one)
(assert-event
  (let ((d (fn-lzr-append-decide nil 0 64 *plr-r* *plr-k* 750 *plz-block*)))
    (and (fn-record-result-okp (fn-record-decode-exact *plr-r*))
         (not (equal (assoc-equal 0 nil) (cons 0 nil)))
         (not (equal (car (fn-lzr-expand nil (fn-lzr-append-octets d *plr-r*))) :ok)))))

(must-fail-checked
 (defthm pla-replay-no-binding
   (implies (fn-record-result-okp (fn-record-decode-exact r))
            (equal (car (fn-lzr-expand dicts (fn-lzr-append-octets
                                              (fn-lzr-append-decide dict dict-id min r k n
                                                                    candidate)
                                              r)))
                   :ok))
   :hints (("Goal" :do-not-induct t))))

; -----------------------------------------------------------------------------
; fn-lzr-append-plan-off.

; pla-plan-off-witness (evaluated: the codec is the attached one)
(assert-event
  (and (zp 0) (equal (fn-lzr-append-plan 0 *plr-r*) nil)
       (equal (fn-lzr-append-plan 64 *plr-r*) (cons *plr-k* 750))))

(must-fail-checked
 (defthm pla-plan-off-any-min
   (equal (fn-lzr-append-plan min r) nil)
   :hints (("Goal" :do-not-induct t))))

; -----------------------------------------------------------------------------
; The read step and the store's report: a frame and a plain record read
; through fn-lzr-read-step; the tally counts both, the frame's stored octets
; and its expansion, and dictionary 0 in use.

(assert-event
 (mv-let (x1 t1) (fn-lzr-read-step (fn-lzr-tally-empty) *pla-dicts* *plr-z0*)
   (mv-let (x2 t2) (fn-lzr-read-step t1 *pla-dicts* *plr-r*)
     (and (equal x1 (list :ok *plr-r*))
          (equal x2 (list :ok *plr-r*))
          (equal t2 (list 2 1 (+ (len *plr-z0*) (len *plr-r*)) (* 2 (len *plr-r*)) (list 0)))
          (equal (fn-lzr-tally-text 0 (fn-lzr-tally-empty))
                 "compression: compress-min-octets=0 (off) records=0 compressed-records=0 stored-octets=0 uncompressed-octets=0 dictionaries=none")
          (equal (fn-lzr-tally-text 64 (list 2 1 1500 1600 (list 0)))
                 "compression: compress-min-octets=64 records=2 compressed-records=1 stored-octets=1500 uncompressed-octets=1600 dictionaries=0")))))

; A refused read leaves the tally, and names its line.
(assert-event
 (mv-let (x tl) (fn-lzr-read-step (fn-lzr-tally-empty) nil *plr-z0*)
   (and (equal x (list :refused :lz-dictionary))
        (equal tl (fn-lzr-tally-empty))
        (stringp (fn-lzr-read-refusal-text x)))))

; -----------------------------------------------------------------------------
; The switch is a configuration row (fn-lzr-config-min): no row is off, the
; row's N is the threshold, and 0 is off.
(defconst *pla-cfg-on*
  (fn-cfg-apply (fn-cfg-empty-value) 1 0 (list (fn-cfg-set-limit "compress-min-octets" 64))))
(defconst *pla-cfg-off*
  (fn-cfg-apply (fn-cfg-empty-value) 1 0 (list (fn-cfg-set-limit "compress-min-octets" 0))))
(assert-event (equal (fn-lzr-config-min (fn-cfg-empty-value)) 0))
(assert-event (equal (fn-lzr-config-min *pla-cfg-on*) 64))
(assert-event (equal (fn-lzr-config-min *pla-cfg-off*) 0))
(assert-event (equal (fn-lzr-append-plan (fn-lzr-config-min *pla-cfg-on*) *plr-r*)
                     (cons *plr-k* 750)))
(assert-event (equal (fn-lzr-append-plan (fn-lzr-config-min (fn-cfg-empty-value)) *plr-r*) nil))

; fn-lzr-config-min-without-a-row-is-off: the witness (the empty value has
; no row; off), and with the row the conclusion fails.
(assert-event (and (not (consp (fn-cfg-row-lookup (fn-cfg-limits (fn-cfg-empty-value))
                                                  "compress-min-octets")))
                   (equal (fn-lzr-config-min (fn-cfg-empty-value)) 0)))
(assert-event (and (consp (fn-cfg-row-lookup (fn-cfg-limits *pla-cfg-on*) "compress-min-octets"))
                   (not (equal (fn-lzr-config-min *pla-cfg-on*) 0))))
(must-fail-checked
 (defthm pla-config-min-any-row
   (equal (fn-lzr-config-min v) 0)
   :hints (("Goal" :do-not-induct t))))

; Teeth for the two refusal-line keystones (PRF-952).  Append: a block that
; does not decode to the span is refused with the line (positive witness);
; the encoder's :none and the real frame have no line (hypothesis removal:
; the candidate, the decode).  Read: no dictionary held for the real frame is
; refused with a line (positive witness); the frame with its dictionary, and
; the plain record, expand and have none (hypothesis removal: the
; dictionary; the magic).
(assert-event
 (let ((d (fn-lzr-append-decide nil 0 64 *plr-r* *plr-k* 750 '(1 2 3))))
   (and (equal d (list :refused :lz-candidate))
        (stringp (fn-lzr-append-refusal-text d))
        (not (equal (fn-lz-decode nil '(1 2 3) 750)
                    (list :ok (take 750 (nthcdr *plr-k* *plr-r*))))))))
(assert-event
 (and (null (fn-lzr-append-refusal-text
             (fn-lzr-append-decide nil 0 64 *plr-r* *plr-k* 750 :none)))
      (null (fn-lzr-append-refusal-text *pla-framed*))))
(assert-event
 (let ((x (fn-lzr-expand nil *plr-z0*)))
   (and (fn-lzr-magicp *plr-z0*)
        (equal x (list :refused :lz-dictionary))
        (stringp (fn-lzr-read-refusal-text x)))))
(assert-event
 (and (null (fn-lzr-read-refusal-text (fn-lzr-expand *pla-dicts* *plr-z0*)))
      (not (fn-lzr-magicp *plr-r*))
      (null (fn-lzr-read-refusal-text (fn-lzr-expand *pla-dicts* *plr-r*)))))
