; fn: witnesses and teeth for books/store-recover-stream.lisp (lane
; recover-memory, PKT-823): the chunked full replay the host runs
; (host/native/io.lisp fnn-bridge-recover: per chunk fn-store-decode-records,
; which is fn-srs-decode, then fn-srs-intern-step; the two calls of
; fn-srs-step's body; then fn-srs-rows into fn-store-sn-recover-rows).
;
; The history is three real journal records (fn-rcon-record-encode-impl of
; records the codec decodes back exactly); the arena is a local one.
(in-package "ACL2")
(include-book "../../books/store-recover-stream")
; The codecs' attachments, as the host image evaluates them.
(include-book "../../books/records-attach-concrete")
(include-book "../../books/statement-attach")

(defconst *srst-groups* '("fn.test"))
(defconst *srst-records*
  (list (fn-record-make 0 0 0 "<r0@example>" '(65 66 67) *srst-groups*
                        "p0" "c0" "e0" 2 841000000)
        (fn-record-make 1 1 0 "<r1@example>" '(68 69) *srst-groups*
                        "p1" "c1" "e1" 2 841000001)
        (fn-record-make 2 2 0 "<r2@example>" '(70) *srst-groups*
                        "p2" "c2" "e2" 2 841000002)))
(assert-event (and (fn-record-p (nth 0 *srst-records*))
                   (fn-record-p (nth 1 *srst-records*))
                   (fn-record-p (nth 2 *srst-records*))))
(defconst *srst-r0* (fn-rcon-record-encode-impl (nth 0 *srst-records*)))
(defconst *srst-r1* (fn-rcon-record-encode-impl (nth 1 *srst-records*)))
(defconst *srst-r2* (fn-rcon-record-encode-impl (nth 2 *srst-records*)))
(defconst *srst-history* (list *srst-r0* *srst-r1* *srst-r2*))
; The records decode back exactly (what the journal replay reads).
(assert-event (equal (fn-srs-decode *srst-history*) *srst-records*))

; The fold and the one step, each over a fresh local arena; the answer is the
; rows (newest first, or :bad) and the arena's payloads.
(defun srst-arena-list (i fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil
                  :measure (nfix (- (fn-arena-count fn-arena) (nfix i)))))
  (if (and (natp i) (< i (fn-arena-count fn-arena)))
      (cons (fn-arena-payload i fn-arena) (srst-arena-list (1+ i) fn-arena))
    nil))
(defun srst-steps-in (chunks fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (acc fn-arena)
    (fn-srs-steps chunks nil fn-arena)
    (mv (list acc (srst-arena-list 0 fn-arena)) fn-arena)))
(defun srst-one-in (chunks fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (acc fn-arena)
    (fn-srs-step nil (fn-srs-concat chunks) fn-arena)
    (mv (list acc (srst-arena-list 0 fn-arena)) fn-arena)))
(defun srst-intern-of-decode-in (octet-records fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (rows fn-arena)
    (fn-intern-events (fn-srs-decode octet-records) nil 0 fn-arena)
    (mv (list rows (srst-arena-list 0 fn-arena)) fn-arena)))
(defun srst-steps (chunks)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (out fn-arena) (srst-steps-in chunks fn-arena) out)))
(defun srst-one (chunks)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (out fn-arena) (srst-one-in chunks fn-arena) out)))
(defun srst-intern-of-decode (octet-records)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (out fn-arena) (srst-intern-of-decode-in octet-records fn-arena) out)))

; The keystone's conclusion over its answers (fn-srs-same's reading).
(defun srst-conclusion (steps one)
  (declare (xargs :verify-guards nil))
  (and (iff (eq (car steps) :bad) (eq (car one) :bad))
       (implies (not (eq (car one) :bad)) (equal steps one))))

; -----------------------------------------------------------------------------
; Reachable positive witnesses: the host's chunkings of a real history.
; Antecedent: every chunk a true list.  Conclusion: the same rows and arena
; as one step; not :bad; the rows oldest first are the intern of the decode
; and the arena holds the three payloads in order.

(defconst *srst-chunkings*
  (list (list *srst-history*)
        (list (list *srst-r0* *srst-r1*) (list *srst-r2*))
        (list (list *srst-r0*) (list *srst-r1*) (list *srst-r2*))
        (list nil (list *srst-r0*) nil (list *srst-r1* *srst-r2*))))

(defun srst-all-hold (cs)
  (declare (xargs :verify-guards nil))
  (if (atom cs)
      t
    (let ((chunks (car cs)))
      (and (fn-srs-chunksp chunks)
           (equal (fn-srs-concat chunks) *srst-history*)
           (not (eq (car (srst-one chunks)) :bad))
           (srst-conclusion (srst-steps chunks) (srst-one chunks))
           (srst-all-hold (cdr cs))))))
(assert-event (srst-all-hold *srst-chunkings*))

(assert-event
 (let ((one (srst-one (list *srst-history*)))
       (ref (srst-intern-of-decode *srst-history*)))
   (and (equal (fn-srs-rows (car one)) (car ref))
        (equal (cadr one) (cadr ref))
        (equal (cadr one) '((65 66 67) (68 69) (70)))
        (equal (len (car one)) 3))))

; A refused history: the second chunk's record does not decode (one octet
; flipped).  Antecedent holds; both answers are :bad (conclusion holds).
(defconst *srst-corrupt* (cons (logxor 1 (car *srst-r1*)) (cdr *srst-r1*)))
(assert-event (equal (fn-srs-decode (list *srst-corrupt*)) :bad))
(assert-event
 (let ((chunks (list (list *srst-r0*) (list *srst-corrupt* *srst-r2*))))
   (and (fn-srs-chunksp chunks)
        (eq (car (srst-steps chunks)) :bad)
        (eq (car (srst-one chunks)) :bad)
        (srst-conclusion (srst-steps chunks) (srst-one chunks)))))

; -----------------------------------------------------------------------------
; Hypothesis removal (fn-srs-chunksp): a chunk that is not a true list.  The
; hypothesis fails; the fold refuses the dotted chunk while one step over the
; concatenation (which normalizes each chunk) opens: the conclusion fails.
(assert-event
 (let ((chunks (list (cons *srst-r0* 5) (list *srst-r1* *srst-r2*))))
   (and (not (fn-srs-chunksp chunks))
        (eq (car (srst-steps chunks)) :bad)
        (not (eq (car (srst-one chunks)) :bad))
        (not (srst-conclusion (srst-steps chunks) (srst-one chunks))))))

; The quantum: a chunk closes at 1 MiB of record octets, and a record above
; it is a chunk by itself (the host's loop takes one record before asking).
(assert-event (and (not (fn-srs-chunk-fullp 0))
                   (not (fn-srs-chunk-fullp 1048575))
                   (fn-srs-chunk-fullp 1048576)
                   (fn-srs-chunk-fullp 10485760)))

; -----------------------------------------------------------------------------
; The numbered chunk (section 5; host/native/io.lisp fnn-recover-file-chunks
; answers fn-srs-checked-decode of ((FILE-NUMBER . RECORD) ...)).

(defconst *srst-numbered* (list (cons 0 *srst-r0*) (cons 1 *srst-r1*) (cons 2 *srst-r2*)))

; The per-file check's function reads each record's sequence.
(assert-event (and (equal (fn-srs-record-sequence *srst-r0*) 0)
                   (equal (fn-srs-record-sequence *srst-r1*) 1)
                   (equal (fn-srs-record-sequence *srst-r2*) 2)
                   (equal (fn-srs-record-sequence *srst-corrupt*) -1)))

; Reachable positive witness of fn-srs-checked-decode-is-the-per-file-check:
; a numbered chunk whose records decode and whose numbers are their
; sequences.  Antecedent (no hypothesis) and conclusion: the checked decode
; is the right-hand side's decode arm, and it is the unchecked decode.
(assert-event
 (let ((ws (fn-srs-decode (fn-srs-pair-octets *srst-numbered*))))
   (and (equal (fn-srs-pair-octets *srst-numbered*) *srst-history*)
        (not (equal ws :bad))
        (fn-srs-numberedp *srst-numbered*)
        (equal (fn-srs-checked-decode *srst-numbered*) ws)
        (equal (fn-srs-checked-decode *srst-numbered*) *srst-records*))))

; A file whose number is not its record's sequence (records 1 and 2 swapped
; between files 1 and 2): the records decode, the per-file check fails, and
; the checked decode answers :sequence -- the arm the host faults on
; ("record sequence does not match immutable filename").
(defconst *srst-misnumbered* (list (cons 0 *srst-r0*) (cons 1 *srst-r2*) (cons 2 *srst-r1*)))
(assert-event
 (and (not (equal (fn-srs-decode (fn-srs-pair-octets *srst-misnumbered*)) :bad))
      (not (fn-srs-numberedp *srst-misnumbered*))
      (equal (fn-srs-checked-decode *srst-misnumbered*) :sequence)))

; A record that does not decode: :bad, whatever the numbers (the decode arm
; comes first, as the open's refusal of the history).
(assert-event
 (and (equal (fn-srs-checked-decode (list (cons 0 *srst-r0*) (cons 1 *srst-corrupt*))) :bad)
      (equal (fn-srs-checked-decode (list (cons 7 *srst-corrupt*))) :bad)))

; fn-srs-checked-step-is-the-step, reachable: the host's two calls over each
; numbered chunk fold to the unchecked fold over the chunks' records, which
; the fold keystone equates with one step over the history.
(defun srst-checked-steps-in (numbered-chunks acc fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (if (atom numbered-chunks)
      (mv (list acc (srst-arena-list 0 fn-arena)) fn-arena)
    (mv-let (acc fn-arena)
      (fn-srs-intern-step acc (fn-srs-checked-decode (car numbered-chunks)) fn-arena)
      (srst-checked-steps-in (cdr numbered-chunks) acc fn-arena))))
(defun srst-checked-steps (numbered-chunks)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (out fn-arena) (srst-checked-steps-in numbered-chunks nil fn-arena) out)))
(assert-event
 (let ((numbered (list (list (cons 0 *srst-r0*) (cons 1 *srst-r1*)) (list (cons 2 *srst-r2*)))))
   (and (not (equal (fn-srs-checked-decode (car numbered)) :sequence))
        (not (equal (fn-srs-checked-decode (cadr numbered)) :sequence))
        (equal (srst-checked-steps numbered)
               (srst-steps (list (list *srst-r0* *srst-r1*) (list *srst-r2*))))
        (equal (srst-checked-steps numbered) (srst-one (list *srst-history*))))))

; Hypothesis removal (fn-srs-checked-step-is-the-step's "not :sequence"): a
; misnumbered chunk.  The hypothesis fails; the intern step of :sequence is
; not the step over the chunk's records (which opens them): the conclusion
; fails, which is why the host faults on :sequence before any intern.
(assert-event
 (and (equal (fn-srs-checked-decode *srst-misnumbered*) :sequence)
      (not (eq (car (srst-one (list (fn-srs-pair-octets *srst-misnumbered*)))) :bad))
      (not (equal (car (srst-checked-steps (list *srst-misnumbered*)))
                  (car (srst-one (list (fn-srs-pair-octets *srst-misnumbered*))))))))

; -----------------------------------------------------------------------------
; The unframe without a payload copy (section 6; host/native/io.lisp
; fnn-unframe-list sends a transaction file as its protected prefix and its
; trailer, host/store-host.lisp fn-store-unframe-split).  The keystone
; fn-srs-unframe-is-the-frame-decode has no hypothesis; the witnesses below
; are theorems because the digest is an attachment (fn-frame-digest, SHA-256)
; that an event may not call: each holds for whatever the digest is.

; A real journal frame of record r0 with its own trailer: the fast arm opens
; it and the payload is the record (the frame decode's answer, by the keystone).
(defconst *srst-prefix*
  (fn-frame-protected *fn-frame-magic-store* *fn-frame-version* *fn-frame-store-kind* *srst-r0*))
(defthm srst-unframe-opens-a-real-frame
  (let ((fast (fn-srs-unframe *srst-prefix* (fn-frame-trailer *srst-prefix*))))
    (and (fn-frame-result-okp fast)
         (equal (fn-frame-result-payload fast) *srst-r0*)
         (equal fast (fn-frame-store-decode (append *srst-prefix* (fn-frame-trailer *srst-prefix*))
                                            (fn-frame-trailer *srst-prefix*)))))
  :hints (("Goal" :use ((:instance fn-srs-unframe-is-the-frame-decode
                                   (prefix *srst-prefix*) (trailer (fn-frame-trailer *srst-prefix*))))
           :in-theory (e/d (fn-srs-unframe)
                           (fn-srs-unframe-is-the-frame-decode fn-frame-store-decode))))
  :rule-classes nil)

; A trailer of the right length that is not the prefix's digest: :integrity.
(defthm srst-unframe-refuses-a-wrong-trailer
  (implies (and (fn-cbor-octet-listp trailer) (equal (len trailer) 32)
                (not (equal trailer (fn-frame-trailer *srst-prefix*))))
           (equal (fn-srs-unframe *srst-prefix* trailer) (fn-frame-error :integrity)))
  :hints (("Goal" :in-theory (e/d (fn-srs-unframe)
                                  (fn-srs-unframe-is-the-frame-decode fn-frame-store-decode))))
  :rule-classes nil)

; A prefix that is not octets: the fast arm does not apply and the answer is
; the frame decode's refusal (evaluated: the digest of non-octets is :bad
; with no attachment called).
(assert-event
 (let ((prefix (cons 256 (cdr *srst-prefix*))) (trailer (make-list 32 :initial-element 0)))
   (and (not (fn-frame-result-okp (fn-srs-unframe prefix trailer)))
        (equal (fn-srs-unframe prefix trailer)
               (fn-frame-store-decode (append prefix trailer) (fn-frame-trailer prefix))))))
