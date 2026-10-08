; Witnesses and teeth for books/checkpoint-payloads.lisp (lane s-cpl).
;
; Ground store: a 10-octet file F (committed length L = 10), a delta of three
; payloads (one empty).  (Attachments evaluate in assert-event: the seal is
; fn-blake3's.)  Each keystone has a reachable positive witness asserting the
; whole antecedent and conclusion; each tooth names the omitted hypothesis,
; checks the retained ones, the failure of the omitted one and of the
; conclusion.  Corrupted-state witnesses are labelled.

(in-package "ACL2")
(include-book "must-fail-checked")
(include-book "../../books/checkpoint-payloads")
(include-book "../../books/checkpoint-payloads-extent")
(include-book "std/testing/assert-bang" :dir :system)

(defconst *cpl-f* '(9 9 9 9 9 9 9 9 9 9))
(defconst *cpl-ps* '((1 2 3) (4 5) ()))
(defconst *cpl-plan* (fn-cpl-append-plan (len *cpl-f*) *cpl-ps*))
(defconst *cpl-bytes* (car *cpl-plan*))
(defconst *cpl-refs* (cadr *cpl-plan*))
(defconst *cpl-full* (append *cpl-f* *cpl-bytes*))

; CPL-1 positive: premises hold, the plan is the delta's frames, O(delta), the
; refs resolve to the delta's payloads in the file after the append.
(assert-event
 (and (true-listp *cpl-f*) (fn-cpl-payload-listp *cpl-ps*)
      (equal *cpl-bytes* (fn-cpl-frames *cpl-ps*))
      (equal (len *cpl-bytes*) (fn-cpl-delta-octets *cpl-ps*))
      (equal (fn-cpl-delta-octets *cpl-ps*) (+ 5 (* 69 3)))
      (equal *cpl-refs* '((47 3) (119 2) (190 0)))
      (equal (fn-cpl-open-all *cpl-refs* *cpl-full*) (fn-cpl-wrap *cpl-ps*))))

; CPL-1 MUTATION witness (the expression changes; the removal witnesses are
; below): refs planned at offset 0 instead of the committed length L
; (the hypothesis (equal l (len f)) omitted): premises hold, l /= (len f), the
; refs do not resolve.
(assert-event
 (let ((bad (fn-cpl-refs 0 *cpl-ps*)))
   (and (true-listp *cpl-f*) (fn-cpl-payload-listp *cpl-ps*)
        (not (equal 0 (len *cpl-f*)))
        (not (equal (fn-cpl-open-all bad *cpl-full*) (fn-cpl-wrap *cpl-ps*))))))

; CPL-2 positive: a root of committed length C = 82 (F and the first frame)
; resolves its refs identically in the full file and in the file cut at C with
; ANY tail (here zeros, as a filesystem may expose after a crash).
(assert-event
 (let* ((c 82) (root-refs (list (car *cpl-refs*)))
        (cut (append (take c *cpl-full*) '(0 0 0 0 0 0 0 0 0 0 0 0))))
   (and (<= c (len *cpl-full*)) (<= c (len cut))
        (equal (take c cut) (take c *cpl-full*))
        (fn-cpl-refs-coveredp root-refs c)
        (fn-cpl-durable-rootp c root-refs cut)
        (equal (fn-cpl-open-all root-refs cut) (fn-cpl-open-all root-refs *cpl-full*))
        (equal (fn-cpl-open-all root-refs cut) '(((1 2 3)))))))

; CPL-2 tooth: a root whose committed length counts frames not yet durable
; (C = the full length, the file cut after the first frame).  The retained
; hypotheses hold (the refs are covered by C, the cut agrees with the full file
; on its own length); the omitted one, C <= (len cut), fails, and so does the
; conclusion: the second and third refs do not resolve in the cut.
(assert-event
 (let* ((c (len *cpl-full*)) (cut (take 82 *cpl-full*)))
   (and (fn-cpl-refs-coveredp *cpl-refs* c)
        (equal cut (take (len cut) *cpl-full*))
        (not (<= c (len cut)))
        (not (fn-cpl-durable-rootp c *cpl-refs* cut))
        (not (equal (fn-cpl-open-all *cpl-refs* cut)
                    (fn-cpl-open-all *cpl-refs* *cpl-full*))))))

; CPL-2 tooth: the coverage hypothesis omitted.  A ref past C resolves in the
; full file and not in the cut that agrees with it below C.
(assert-event
 (let* ((c 82) (cut (take c *cpl-full*)))
   (and (<= c (len cut)) (equal (take c cut) (take c *cpl-full*))
        (not (fn-cpl-refs-coveredp (list (cadr *cpl-refs*)) c))
        (not (equal (fn-cpl-open-all (list (cadr *cpl-refs*)) cut)
                    (fn-cpl-open-all (list (cadr *cpl-refs*)) *cpl-full*))))))

; The verified read agrees with the interface's resolve (books/checkpoint-payload-ref).
(assert-event
 (and (equal (fn-cpl-open (car *cpl-refs*) *cpl-full*)
             (list (fn-cpl-resolve (car *cpl-refs*) *cpl-full*)))
      (equal (fn-cpl-resolve (cadr *cpl-refs*) *cpl-full*) '(4 5))
      (eq (fn-cpl-resolve (cadr *cpl-refs*) (take 100 *cpl-full*)) :absent)))

; CPL-2 labelled corrupted-state witness: one flipped payload octet inside a
; committed frame is refused by the trailer, not returned.
(assert-event
 (let ((bad (update-nth 48 77 *cpl-full*)))
   (and (equal (fn-cpl-open (car *cpl-refs*) *cpl-full*) '((1 2 3)))
        (equal (fn-cpl-open (car *cpl-refs*) bad) nil))))

; CPL-3 positive: compaction of the live refs {first, third} into a fresh file.
(assert-event
 (let* ((live (list (car *cpl-refs*) (caddr *cpl-refs*)))
        (cp (fn-cpl-compact-plan *cpl-full* live))
        (nf (car cp)) (m (cadr cp)))
   (and (fn-cpl-all-openp live *cpl-full*)
        (equal (fn-cpl-open-all m nf) (fn-cpl-open-all live *cpl-full*))
        (equal (len nf) (+ (fn-cpl-ref-lens live) (* 69 (len live))))
        (< (len nf) (len *cpl-full*))
        (equal m '((37 3) (109 0))))))

; CPL-3 concurrent delta: the compacted file followed by one delta append.
(assert-event
 (let* ((live (list (car *cpl-refs*) (caddr *cpl-refs*)))
        (cp (fn-cpl-compact-plan *cpl-full* live))
        (nf (car cp)) (ap (fn-cpl-append-plan (len nf) '((7))))
        (g (append nf (car ap))))
   (equal (fn-cpl-open-all (append (cadr cp) (cadr ap)) g)
          '(((1 2 3)) (NIL) ((7))))))

; CPL-3 tooth: the all-open hypothesis omitted.  A dead ref (past the end of
; the file) is among the refs: the premises hold, the hypothesis fails, and the
; map does not give the same answers before and after.
(assert-event
 (let* ((dead '(500 4))
        (refs (list (car *cpl-refs*) dead))
        (cp (fn-cpl-compact-plan *cpl-full* refs)))
   (and (true-listp *cpl-full*) (true-list-listp refs)
        (not (fn-cpl-all-openp refs *cpl-full*))
        (not (equal (fn-cpl-open-all (cadr cp) (car cp))
                    (fn-cpl-open-all refs *cpl-full*))))))

; -----------------------------------------------------------------------------
; The trailer, its words, the writer and the extent bridge.

; CPL-4 positive: each returned trailer is the last 32 octets of its frame in
; the file after the append (third plan component), and is a function of the
; payload alone (the same payload at another offset has the same trailer).
(assert-event
 (let ((trs (caddr *cpl-plan*)))
   (and (fn-cpl-payload-listp *cpl-ps*)
        (equal trs (fn-cpl-trailers *cpl-ps*))
        (fn-cpl-trailers-at *cpl-refs* trs *cpl-full*)
        (equal (len (car trs)) 32)
        (equal (fn-cpl-trailer '(1 2 3))
               (fn-cpl-trailer (car (fn-cpl-payloads-of (list (car *cpl-refs*)) *cpl-full*)))))))

; CPL-4 MUTATION witness (the expression changes; the removal witness for
; fn-cpl-append-plan-trailers is below): a trailer taken one octet off the frame's end is not the
; frame's last 32 octets.
(assert-event
 (let ((trs (caddr *cpl-plan*)))
   (and (fn-cpl-trailers-at *cpl-refs* trs *cpl-full*)
        (not (fn-cpl-trailers-at (list (cons (+ 1 (car (car *cpl-refs*))) (cdr (car *cpl-refs*))))
                                 (list (car trs)) *cpl-full*)))))

; Words: the pack theorem on the ground payloads, and the shape constraint.
(assert-event
 (and (fn-cpl-payloadp '(1 2 3))
      (equal (fn-cpl-unpack-words (fn-cpl-trailer-words-impl '(1 2 3)))
             (fn-cpl-trailer '(1 2 3)))
      (equal (len (fn-cpl-trailer-words-impl '(1 2 3))) 4)
      (unsigned-byte-p 64 (car (fn-cpl-trailer-words-impl '(1 2 3))))
      (unsigned-byte-p 64 (cadddr (fn-cpl-trailer-words-impl '(1 2 3))))
      ;; big-endian, 8 octets to a word: word 0 is octets 0..7
      (equal (fn-cpl-be-octets (car (fn-cpl-trailer-words-impl '(1 2 3))) 8)
             (take 8 (fn-cpl-trailer '(1 2 3))))))

; Words MUTATION witness (the expression changes; the removal witness for
; fn-cpl-trailer-words-pack is below): little-endian packing of the same octets is a different word
; (the pack theorem is about the big-endian one).
(assert-event
 (let ((tr (fn-cpl-trailer '(1 2 3))))
   (not (equal (fn-cpl-be-fold (reverse (take 8 tr)) 0)
               (car (fn-cpl-trailer-words-impl '(1 2 3)))))))

; The writer: the octets it appends are the plan's bytes.
(defun cpl-test-write (f ps)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (r fn-octets)
      (let* ((fn-octets (fn-octets-from-list f fn-octets))
             (fn-octets (fn-cpl-write-frames ps fn-octets)))
        (mv (fn-octets-list fn-octets) fn-octets))
      r)))
(assert-event (equal (cpl-test-write *cpl-f* *cpl-ps*) *cpl-full*))

; The extent bridge: the realizer's verdict on a frame in the file is :ok; a
; trailer of another payload is refused (:trailer: not the commitment), and a
; damaged prefix is refused (:digest).
(defun cpl-test-verdict (commit read prefix)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (r fn-octets)
      (let* ((fn-octets (fn-octets-from-list prefix fn-octets)))
        (mv (fn-arx-entry-verdict-buffer commit read fn-octets) fn-octets))
      r)))
(assert-event
 (let* ((p '(4 5)) (pre *cpl-f*)
        (file (append pre (fn-cpl-frame p) '(7 7)))
        (prefix (take (+ 37 (len p)) (nthcdr (len pre) file)))
        (read (take 32 (nthcdr (+ (len pre) 37 (len p)) file)))
        (commit (fn-arx-trailer-nat (fn-cpl-trailer p))))
   (and (equal read (fn-cpl-trailer p))
        (equal (cpl-test-verdict commit read prefix) :ok)
        (equal (cpl-test-verdict (fn-arx-trailer-nat (fn-cpl-trailer '(1 2 3))) read prefix)
               :trailer)
        (equal (cpl-test-verdict commit read (update-nth 38 77 prefix)) :digest))))

; The descriptor the open seals for a ref: absolute offsets, the prefix is
; header ++ payload (the trailer is read after it), the commitment packs the
; trailer.  The guard of fn-arena-seal-extent holds; the RELATIVE reading
; (poff 37) names a different, wrong extent for a frame that does not start at 0.
(assert-event
 (let* ((ref (cadr *cpl-refs*)) (tr (cadr (caddr *cpl-plan*)))
        (e (fn-cpl-extent 1 ref tr)))
   (and (equal ref '(119 2))
        (equal (subseq e 0 5) '(1 82 39 119 2))
        (equal (nth 5 e) (fn-arx-trailer-nat tr))
        (fn-arn-extent-guardp (nth 0 e) (nth 1 e) (nth 2 e) (nth 3 e) (nth 4 e) (nth 5 e))
        ;; the extent [eoff, eoff+elen) of the file is header ++ payload, and the
        ;; 32 octets after it are the trailer
        (equal (take 39 (nthcdr 82 *cpl-full*)) (fn-cpl-prefix '(4 5)))
        (equal (take 32 (nthcdr 121 *cpl-full*)) tr)
        (equal (take 2 (nthcdr 119 *cpl-full*)) '(4 5))
        (not (equal (take 2 (nthcdr 37 *cpl-full*)) '(4 5))))))

; -----------------------------------------------------------------------------
; Teeth for the train-28 statement audit (rows 24-35; lane s-teeth28).
;
; Each keystone below has (a) a positive witness asserting the WHOLE antecedent
; (every hypothesis, including fn-cpl-filep / fn-cpl-all-openp / fn-cpl-holdsp
; where the theorem has it) and the WHOLE conclusion, and (b) a
; hypothesis-removal witness: exactly one hypothesis dropped, every retained
; hypothesis asserted, the omitted hypothesis shown false, and the conclusion
; shown false.  The antecedent and conclusion are the literal text of the
; theorem, as a function of its variables.  The earlier witnesses above that
; change the EXPRESSION (the hard-coded offset, the substituted refs, the
; little-endian packing) stay, as mutation witnesses; they are not removal
; witnesses.  Values outside a guard are evaluated with guard checking off:
; the hypothesis removed is the guard.
;
; No removal witness for fn-cpl-write-frames-is-the-plan: the live fn-octets stobj refuses
; a non-octet payload before the conclusion can be evaluated (its executable guard IS
; the hypothesis), so only the positive witness is ground-checkable.
;
; Hypotheses with no ground failure: fn-cpl-append-plan-is-the-delta's
; (natp l) (the conclusion also holds at l = -100), fn-cpl-crash-keeps-the-old-root's
; (natp k) and (<= k delta) (a covered root never reads the tail), fn-cpl-write-frames-is-the-plan's
; (natp l) (l is not in the conclusion) and every fn-cpl-filep (it bounds the file
; below 2^64 octets, which no ground file reaches).  Those are not removed here;
; removing one needs the weakened theorem proved first.

; A longer ground store: the first 82 octets of *cpl-full* (10 octets, then the
; first frame, 72 octets), and the delta that follows it.
(defconst *cpl-f82* (take 82 *cpl-full*))
(defconst *cpl-ps2* '((4 5) ()))
(defconst *cpl-bad-ps* '((300)))          ; 300 is not an octet

; --- fn-cpl-append-plan-is-the-delta
(defun cpl-ante-delta (l ps) (declare (xargs :guard t :verify-guards nil))
  (and (natp l) (fn-cpl-payload-listp ps)))
(defun cpl-concl-delta (l ps) (declare (xargs :guard t :verify-guards nil))
  (and (equal (car (fn-cpl-append-plan l ps)) (fn-cpl-frames ps))
       (equal (len (car (fn-cpl-append-plan l ps))) (fn-cpl-delta-octets ps))
       (equal (fn-cpl-delta-octets ps)
              (+ (fn-cpl-ref-lens (cadr (fn-cpl-append-plan l ps)))
                 (* (+ *fn-scc-segment-header-octets* *fn-frame-trailer-octets*)
                    (len ps))))
       (equal (cadr (fn-cpl-append-plan l ps)) (fn-cpl-refs l ps))
       (fn-cpl-refs-coveredp (cadr (fn-cpl-append-plan l ps))
                             (+ l (fn-cpl-delta-octets ps)))))
(assert-event (with-guard-checking :none
                (and (cpl-ante-delta 10 *cpl-ps*) (cpl-concl-delta 10 *cpl-ps*))))
; removal of (fn-cpl-payload-listp ps): the plan's length is not the delta's.
(assert-event (with-guard-checking :none
                (and (natp 10) (not (fn-cpl-payload-listp *cpl-bad-ps*))
                     (not (cpl-concl-delta 10 *cpl-bad-ps*)))))

; --- fn-cpl-append-plan-resolves
(defun cpl-ante-resolves (f ps) (declare (xargs :guard t :verify-guards nil))
  (and (true-listp f) (fn-cpl-payload-listp ps)))
(defun cpl-concl-resolves (f ps) (declare (xargs :guard t :verify-guards nil))
  (equal (fn-cpl-open-all (cadr (fn-cpl-append-plan (len f) ps))
                          (append f (car (fn-cpl-append-plan (len f) ps))))
         (fn-cpl-wrap ps)))
(assert-event (with-guard-checking :none
                (and (cpl-ante-resolves *cpl-f* *cpl-ps*) (cpl-concl-resolves *cpl-f* *cpl-ps*)
                     (not (member nil (fn-cpl-open-all *cpl-refs* *cpl-full*))))))
; removal of (fn-cpl-payload-listp ps)
(assert-event (with-guard-checking :none
                (and (true-listp *cpl-f*) (not (fn-cpl-payload-listp *cpl-bad-ps*))
                     (not (cpl-concl-resolves *cpl-f* *cpl-bad-ps*)))))

; --- fn-cpl-crash-keeps-the-old-root
(defun cpl-ante-keeps (f ps r0 k) (declare (xargs :guard t :verify-guards nil))
  (and (true-listp f) (fn-cpl-payload-listp ps)
       (fn-cpl-refs-coveredp r0 (len f))
       (natp k) (<= k (fn-cpl-delta-octets ps))))
(defun cpl-concl-keeps (f ps r0 k) (declare (xargs :guard t :verify-guards nil))
  (equal (fn-cpl-open-all r0 (append f (take k (car (fn-cpl-append-plan (len f) ps)))))
         (fn-cpl-open-all r0 f)))
(assert-event (with-guard-checking :none
                (let ((r0 (list (car *cpl-refs*))))
                  (and (cpl-ante-keeps *cpl-f82* *cpl-ps2* r0 50)
                       (cpl-concl-keeps *cpl-f82* *cpl-ps2* r0 50)
                       (equal (fn-cpl-open-all r0 *cpl-f82*) '(((1 2 3))))))))
; removal of (fn-cpl-refs-coveredp r0 (len f)): the root's ref lies in the
; delta, durable only after the whole delta is.
(assert-event (with-guard-checking :none
                (let ((r0 (list (cadr *cpl-refs*))))
                  (and (true-listp *cpl-f82*) (fn-cpl-payload-listp *cpl-ps2*)
                       (natp 140) (<= 140 (fn-cpl-delta-octets *cpl-ps2*))
                       (not (fn-cpl-refs-coveredp r0 (len *cpl-f82*)))
                       (not (cpl-concl-keeps *cpl-f82* *cpl-ps2* r0 140))))))

; --- fn-cpl-crash-new-root-after-durable-append
(defun cpl-ante-newroot (f ps r0) (declare (xargs :guard t :verify-guards nil))
  (and (true-listp f) (fn-cpl-payload-listp ps)
       (fn-cpl-refs-coveredp r0 (len f))))
(defun cpl-concl-newroot (f ps r0) (declare (xargs :guard t :verify-guards nil))
  (equal (fn-cpl-open-all (append r0 (cadr (fn-cpl-append-plan (len f) ps)))
                          (append f (car (fn-cpl-append-plan (len f) ps))))
         (append (fn-cpl-open-all r0 f) (fn-cpl-wrap ps))))
(assert-event (with-guard-checking :none
                (let ((r0 (list (car *cpl-refs*))))
                  (and (cpl-ante-newroot *cpl-f82* *cpl-ps2* r0)
                       (cpl-concl-newroot *cpl-f82* *cpl-ps2* r0)
                       (equal (fn-cpl-open-all r0 *cpl-f82*) '(((1 2 3))))))))
; removal of coveredp: the old root's ref is in the delta
(assert-event (with-guard-checking :none
                (let ((r0 (list (cadr *cpl-refs*))))
                  (and (true-listp *cpl-f82*) (fn-cpl-payload-listp *cpl-ps2*)
                       (not (fn-cpl-refs-coveredp r0 (len *cpl-f82*)))
                       (not (cpl-concl-newroot *cpl-f82* *cpl-ps2* r0))))))

; --- the three compaction keystones (live refs: the first and third payloads)
(defconst *cpl-live* (list (car *cpl-refs*) (caddr *cpl-refs*)))
(defconst *cpl-dead* '(500 4))

(defun cpl-ante-compact (f refs) (declare (xargs :guard t :verify-guards nil))
  (and (fn-cpl-filep f) (fn-cpl-all-openp refs f)))
(defun cpl-concl-preserves (f refs) (declare (xargs :guard t :verify-guards nil))
  (equal (fn-cpl-open-all (cadr (fn-cpl-compact-plan f refs))
                          (car (fn-cpl-compact-plan f refs)))
         (fn-cpl-open-all refs f)))
(defun cpl-concl-size (f refs) (declare (xargs :guard t :verify-guards nil))
  (equal (len (car (fn-cpl-compact-plan f refs)))
         (+ (fn-cpl-ref-lens refs)
            (* (+ *fn-scc-segment-header-octets* *fn-frame-trailer-octets*)
               (len refs)))))
(assert-event (with-guard-checking :none
                (and (cpl-ante-compact *cpl-full* *cpl-live*)
                     (cpl-concl-preserves *cpl-full* *cpl-live*)
                     (cpl-concl-size *cpl-full* *cpl-live*)
                     (equal (fn-cpl-open-all *cpl-live* *cpl-full*) '(((1 2 3)) (nil))))))
; fn-cpl-compact-preserves-every-live-ref, removal of (fn-cpl-all-openp refs f)
(assert-event (with-guard-checking :none
                (let ((refs (list (car *cpl-refs*) *cpl-dead*)))
                  (and (fn-cpl-filep *cpl-full*)
                       (not (fn-cpl-all-openp refs *cpl-full*))
                       (not (cpl-concl-preserves *cpl-full* refs))))))
; fn-cpl-compact-size, removal of (fn-cpl-all-openp refs f)
(assert-event (with-guard-checking :none
                (let ((refs (list (car *cpl-refs*) *cpl-dead*)))
                  (and (fn-cpl-filep *cpl-full*)
                       (not (fn-cpl-all-openp refs *cpl-full*))
                       (not (cpl-concl-size *cpl-full* refs))))))

; --- fn-cpl-compact-concurrent-delta
(defun cpl-ante-conc (f refs ps) (declare (xargs :guard t :verify-guards nil))
  (and (fn-cpl-filep f) (fn-cpl-all-openp refs f) (fn-cpl-payload-listp ps)))
(defun cpl-concl-conc (f refs ps) (declare (xargs :guard t :verify-guards nil))
  (let* ((cp (fn-cpl-compact-plan f refs))
         (nf (car cp))
         (ap (fn-cpl-append-plan (len nf) ps))
         (g (append nf (car ap))))
    (and (equal (fn-cpl-open-all (append (cadr cp) (cadr ap)) g)
                (append (fn-cpl-open-all refs f) (fn-cpl-wrap ps)))
         (equal (len g)
                (+ (fn-cpl-ref-lens refs) (fn-cpl-ref-lens (cadr ap))
                   (* (+ *fn-scc-segment-header-octets* *fn-frame-trailer-octets*)
                      (+ (len refs) (len ps))))))))
(assert-event (with-guard-checking :none
                (and (cpl-ante-conc *cpl-full* *cpl-live* '((7)))
                     (cpl-concl-conc *cpl-full* *cpl-live* '((7)))
                     (equal (len (car (fn-cpl-compact-plan *cpl-full* *cpl-live*))) 141))))
; removal of (fn-cpl-all-openp refs f)
(assert-event (with-guard-checking :none
                (let ((refs (list (car *cpl-refs*) *cpl-dead*)))
                  (and (fn-cpl-filep *cpl-full*) (fn-cpl-payload-listp '((7)))
                       (not (fn-cpl-all-openp refs *cpl-full*))
                       (not (cpl-concl-conc *cpl-full* refs '((7))))))))
; removal of (fn-cpl-payload-listp ps)
(assert-event (with-guard-checking :none
                (and (fn-cpl-filep *cpl-full*) (fn-cpl-all-openp *cpl-live* *cpl-full*)
                     (not (fn-cpl-payload-listp *cpl-bad-ps*))
                     (not (cpl-concl-conc *cpl-full* *cpl-live* *cpl-bad-ps*)))))

; --- fn-cpl-append-plan-trailers
(defun cpl-ante-trs (f ps) (declare (xargs :guard t :verify-guards nil))
  (and (true-listp f) (fn-cpl-payload-listp ps)))
(defun cpl-concl-trs (f ps) (declare (xargs :guard t :verify-guards nil))
  (fn-cpl-trailers-at (cadr (fn-cpl-append-plan (len f) ps))
                      (caddr (fn-cpl-append-plan (len f) ps))
                      (append f (car (fn-cpl-append-plan (len f) ps)))))
(assert-event (with-guard-checking :none
                (and (cpl-ante-trs *cpl-f* *cpl-ps*) (cpl-concl-trs *cpl-f* *cpl-ps*))))
; removal of (fn-cpl-payload-listp ps)
(assert-event (with-guard-checking :none
                (and (true-listp *cpl-f*) (not (fn-cpl-payload-listp *cpl-bad-ps*))
                     (not (cpl-concl-trs *cpl-f* *cpl-bad-ps*)))))

; --- fn-cpl-trailer-words-pack
(defun cpl-concl-pack (p) (declare (xargs :guard t :verify-guards nil))
  (equal (fn-cpl-unpack-words (fn-cpl-trailer-words-impl p)) (fn-cpl-trailer p)))
(assert-event (with-guard-checking :none
                (and (fn-cpl-payloadp '(1 2 3)) (cpl-concl-pack '(1 2 3)))))
; removal of (fn-cpl-payloadp p)
(assert-event (with-guard-checking :none
                (and (not (fn-cpl-payloadp '(300))) (not (cpl-concl-pack '(300))))))

; --- fn-cpl-write-frames-is-the-plan
(defun cpl-ante-wf (l ps f) (declare (xargs :guard t :verify-guards nil))
  (and (natp l) (fn-cpl-payload-listp ps) (true-listp f)))
(defun cpl-concl-wf (l ps f) (declare (xargs :guard t :verify-guards nil))
  (equal (cpl-test-write f ps) (append f (car (fn-cpl-append-plan l ps)))))
(assert-event (with-guard-checking :none
                (and (cpl-ante-wf 10 *cpl-ps* *cpl-f*) (cpl-concl-wf 10 *cpl-ps* *cpl-f*))))

; --- fn-cpl-ref-passes-the-extent-realizer
(defun cpl-ante-realizer (pre post p fo) (declare (xargs :guard t :verify-guards nil))
  (and (true-listp pre) (true-listp post) (fn-cpl-payloadp p)
       (equal fo (take (+ 37 (len p))
                       (nthcdr (len pre) (append pre (fn-cpl-frame p) post))))))
(defun cpl-concl-realizer (pre post p fo) (declare (xargs :guard t :verify-guards nil))
  (equal (cpl-test-verdict (fn-arx-trailer-nat (fn-cpl-trailer p))
                           (take 32 (nthcdr (+ (len pre) 37 (len p))
                                            (append pre (fn-cpl-frame p) post)))
                           fo)
         :ok))
(defconst *cpl-pfx* (take 39 (nthcdr 10 (append *cpl-f* (fn-cpl-frame '(4 5)) '(7 7)))))
(assert-event (with-guard-checking :none
                (and (cpl-ante-realizer *cpl-f* '(7 7) '(4 5) *cpl-pfx*)
                     (cpl-concl-realizer *cpl-f* '(7 7) '(4 5) *cpl-pfx*))))
; removal of (equal fn-octets (take ...)): the buffer holds a damaged prefix
; (the realizer answers :digest).
(assert-event (with-guard-checking :none
                (let ((bad (update-nth 38 77 *cpl-pfx*)))
                  (and (true-listp *cpl-f*) (true-listp '(7 7)) (fn-cpl-payloadp '(4 5))
                       (not (cpl-ante-realizer *cpl-f* '(7 7) '(4 5) bad))
                       (not (cpl-concl-realizer *cpl-f* '(7 7) '(4 5) bad))))))

; --- fn-cpl-seal-reads-back-the-payload: inhabitation in a model of
; A-DURABLE-EXTENT.  The constrained fn-durable-* cannot be defattach'ed (they
; are ancestors of the abstract stobj fn-arena), so the witness is a MODEL of the
; assumption: concrete cpl-t-* that satisfy each A-DURABLE-EXTENT constraint
; (proved below), under which fn-cpl-holdsp's analogue holds for a non-empty
; durable file (file 3, the 222 octets of *cpl-full*: a 10-octet prefix and three
; real frames) and the keystone's conclusion, which fn-arena-seal-extent-payload
; reduces to the durable octets of the extent, is the payload.
(defun cpl-t-octet (file pos)
  (declare (xargs :guard t))
  (if (equal file 3)
      (let ((x (nth (nfix pos) *cpl-full*))) (if (fn-cbor-octetp x) x 0))
    0))
(defun cpl-t-octets (file off len)
  (declare (xargs :guard t :verify-guards nil))
  (if (zp len) nil (cons (cpl-t-octet file off) (cpl-t-octets file (+ 1 (nfix off)) (1- len)))))
(defun cpl-t-realize-octet (file eoff elen poff plen trailer i)
  (declare (ignore eoff elen trailer))
  (nth i (cpl-t-octets file poff plen)))
(defun cpl-t-realize-octets (file eoff elen poff plen trailer)
  (declare (ignore eoff elen trailer))
  (cpl-t-octets file poff plen))
; the model satisfies A-DURABLE-EXTENT's constraints (books/assumptions-durable.lisp)
(defthm cpl-t-model-octet-is-octet (fn-cbor-octetp (cpl-t-octet file pos))
  :hints (("Goal" :in-theory (disable nth))))
(defthm cpl-t-model-unfold
  (equal (cpl-t-octets file off len)
         (if (zp len) nil
           (cons (cpl-t-octet file off) (cpl-t-octets file (+ 1 (nfix off)) (1- len))))))
(defthm cpl-t-model-realize-octet-is-durable
  (equal (cpl-t-realize-octet file eoff elen poff plen trailer i)
         (nth i (cpl-t-octets file poff plen))))
(defthm cpl-t-model-realize-octets-is-durable
  (equal (cpl-t-realize-octets file eoff elen poff plen trailer)
         (cpl-t-octets file poff plen)))

(defun cpl-t-holdsp (file f i) (declare (xargs :guard (natp i)))
  (if (consp f)
      (and (equal (cpl-t-octet file i) (car f)) (cpl-t-holdsp file (cdr f) (+ 1 (nfix i))))
    t))
(defun cpl-ante-seal (pre post p file) (declare (xargs :guard t :verify-guards nil))
  (and (true-listp pre) (true-listp post) (fn-cpl-payloadp p) (natp file)
       (cpl-t-holdsp file (append pre (fn-cpl-frame p) post) 0)))
(defun cpl-concl-seal (pre post p file) (declare (xargs :guard t :verify-guards nil))
  (declare (ignorable post))
  (let ((e (fn-cpl-extent file (list (+ 37 (len pre)) (len p)) (fn-cpl-trailer p))))
    (and (fn-arn-extent-guardp (nth 0 e) (nth 1 e) (nth 2 e) (nth 3 e) (nth 4 e) (nth 5 e))
         (equal (cpl-t-octets (nth 0 e) (nth 3 e) (nth 4 e)) p))))
(assert-event (with-guard-checking :none
                (let ((pre *cpl-f82*) (post (fn-cpl-frame nil)))
                  (and (consp (append pre (fn-cpl-frame '(4 5)) post))
                       (equal (append pre (fn-cpl-frame '(4 5)) post) *cpl-full*)
                       (cpl-ante-seal pre post '(4 5) 3)
                       (cpl-concl-seal pre post '(4 5) 3)))))
; removal of (fn-cpl-holdsp file ...): file 4 holds zeros, not the frames
(assert-event (with-guard-checking :none
                (let ((pre *cpl-f82*) (post (fn-cpl-frame nil)))
                  (and (true-listp pre) (true-listp post) (fn-cpl-payloadp '(4 5)) (natp 4)
                       (not (cpl-t-holdsp 4 (append pre (fn-cpl-frame '(4 5)) post) 0))
                       (not (cpl-concl-seal pre post '(4 5) 4))))))

; The tape row's four words unpack to the frame digest of header ++ payload
; (fn-cpl-trailer-words-are-the-frame-digest): the one implementation, no seam.
(assert-event
 (and (fn-cpl-payloadp '(1 2 3))
      (equal (fn-cpl-unpack-words (fn-cpl-trailer-words-impl '(1 2 3)))
             (fn-frame-digest (fn-cpl-prefix '(1 2 3))))))
