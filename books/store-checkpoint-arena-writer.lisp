; fn: the state checkpoint's WRITER under the records flip: the arena run
; written from the live store (rows and arena) through the publication
; buffer, one batch of whole payloads per step (lane checkpoint-arena-2,
; 2026-09-27; D27, D33).
;
; The file is the arena run A (books/store-checkpoint-arena.lisp
; fn-scka-run-segments) followed by the four tables of the capture of the
; CANONICAL rows (fn-scka-canon-rows: alpha of each live row interned at
; the canonical handle), written by the table pipeline unchanged
; (books/owner-checkpoint-writer.lisp fn-ockp-step).  This book holds the A
; run's steps:
;
;   `fn-scka-write-setup' (rows seg): the payload count N and the batches KS
;     (fn-scka-batches of each canonical payload's length, whole payloads
;     while a chunk stays within SEG octets, at least one per batch), read
;     one row at a time (`fn-scka-canon-lens');
;   `fn-scka-write-step': step 0 writes the head chunk (the tag and N),
;     step k the next (nth (k - 1) KS) canonical payloads, each its length
;     and its octets (`fn-scka-append-batch': alpha of one row at a time,
;     never the history as wire records), then frames the buffer as segment
;     k of 1 + (len KS), chained, and admits the frame by the reader's own
;     rule (fn-ockp-admit-frames) before the host writes it.
;
; KEYSTONE `fn-scka-write-run-is-run-segments': the octets of every step's
; frames, in order, are exactly the arena run of the canonical payloads
; (fn-scka-canon-payloads, which is fn-scka-payloads of alpha of the rows:
; fn-scka-canon-payloads-is-payloads-of-alpha), for ANY buffer contents
; before the first step.  With books/store-checkpoint-arena-load.lisp
; fn-scka-load-of-written-file the file loads to the tables and exactly
; these payloads as the arena.

(in-package "ACL2")
(include-book "store-checkpoint-arena")
(include-book "owner-checkpoint-writer")
(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (disable fn-cp-idp fn-cp-idp-true-listp
                           fn-sccr-scc-octet-listp-is-cbor-octet-listp
                           fn-sccr-cbor-octet-listp-is-scc-octet-listp
                           fn-row-wire-of fn-scka-sealsp fn-scka-payload-of
                           fn-scka-canon-payloads-is-payloads-of-alpha)))

; -----------------------------------------------------------------------------
; 1. One row's canonical payload, and the lengths.

(defun fn-scka-canon-lens (rows fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (if (atom rows)
      nil
    (let ((w (fn-row-wire-of (car rows) fn-arena)))
      (if (fn-scka-sealsp w)
          (cons (len (fn-scka-payload-of w)) (fn-scka-canon-lens (cdr rows) fn-arena))
        (fn-scka-canon-lens (cdr rows) fn-arena)))))

(defthm fn-scka-canon-lens-is-lens
  (equal (fn-scka-canon-lens rows fn-arena)
         (fn-scka-lens (fn-scka-canon-payloads rows fn-arena))))

; (list N KS COUNT): the payload count, the batches, the run's segments.
(defun fn-scka-write-setup (rows seg fn-arena)
  (declare (xargs :stobjs fn-arena :guard (natp seg) :verify-guards nil))
  (let* ((lens (fn-scka-canon-lens rows fn-arena))
         (ks (fn-scka-batches lens seg)))
    (list (len lens) ks (+ 1 (len ks)))))

(defthm fn-scka-write-setup-facts
  (let ((su (fn-scka-write-setup rows seg fn-arena))
        (ps (fn-scka-canon-payloads rows fn-arena)))
    (and (equal (nth 0 su) (len ps))
         (equal (fn-scka-sum (nth 1 su)) (len ps))
         (equal (nth 2 su) (+ 1 (len (nth 1 su))))))
  :hints (("Goal" :in-theory (disable fn-scka-batches fn-scka-lens))))

; -----------------------------------------------------------------------------
; 2. The batch: the next K canonical payloads appended to the buffer, each
; its length and its octets; the rows after the K-th sealing row.
; (mv ROWS' fn-octets)

(defun fn-scka-append-batch (rows k fn-arena fn-octets)
  (declare (xargs :stobjs (fn-arena fn-octets) :guard (natp k) :verify-guards nil
                  :measure (len rows)))
  (if (or (atom rows) (zp k))
      (mv rows fn-octets)
    (let ((w (fn-row-wire-of (car rows) fn-arena)))
      (if (fn-scka-sealsp w)
          (let ((fn-octets (fn-octets-append-list
                            (fn-scka-payload-octets (fn-scka-payload-of w)) fn-octets)))
            (fn-scka-append-batch (cdr rows) (1- k) fn-arena fn-octets))
        (fn-scka-append-batch (cdr rows) k fn-arena fn-octets)))))

; A sealed event's payload is an octet list (the record's payload field).
(local
 (defthm fn-scka-payloadp-octets
   (implies (fn-record-payloadp p)
            (and (fn-cbor-octet-listp p) (true-listp p)))
   :hints (("Goal" :in-theory (enable fn-record-payloadp)))))

(local
 (defthm fn-scka-record-payloadp
   (implies (fn-record-p x) (fn-record-payloadp (fn-record-payload x)))
   :hints (("Goal" :in-theory '(fn-record-p)))))

(defthm fn-scka-payload-of-octets
  (implies (fn-scka-sealsp w)
           (and (fn-cbor-octet-listp (fn-scka-payload-of w))
                (true-listp (fn-scka-payload-of w))))
  :hints (("Goal" :in-theory (e/d (fn-scka-sealsp fn-scka-payload-of)
                                  (fn-record-p fn-replay-composite-record fn-stxa-p
                                   fn-record-payloadp)))))

(local
 (defthm fn-scka-record-payloadp-bound
   (implies (fn-scka-sealsp w)
            (<= (len (fn-scka-payload-of w)) *fn-record-max-payload*))
   :hints (("Goal" :in-theory (e/d (fn-scka-sealsp fn-scka-payload-of fn-record-payloadp)
                                   (fn-record-p fn-replay-composite-record fn-stxa-p))
            :use ((:instance fn-scka-record-payloadp (x w))
                  (:instance fn-scka-record-payloadp (x (fn-replay-composite-record w))))))))

(local
 (defthm fn-scka-len-le-digits-bound
   (implies (and (natp n) (natp k) (< n (expt 256 k)))
            (<= (len (fn-scc-le-digits n)) k))
   :hints (("Goal" :induct (fn-scc-u64 n k)))))

; A payload's length is written in at most eight octets.
(defthm fn-scka-payload-of-digits
  (implies (fn-scka-sealsp w)
           (<= (len (fn-scc-le-digits (len (fn-scka-payload-of w)))) 8))
  :hints (("Goal" :use ((:instance fn-scka-len-le-digits-bound
                                   (n (len (fn-scka-payload-of w))) (k 8))
                        (:instance fn-scka-record-payloadp-bound))
           :in-theory (disable fn-scka-len-le-digits-bound fn-scka-record-payloadp-bound))))

(local
 (defthm fn-scka-payload-octets-cbor
   (implies (and (fn-cbor-octet-listp p) (< (len (fn-scc-le-digits (len p))) 256))
            (fn-cbor-octet-listp (fn-scka-payload-octets p)))
   :hints (("Goal" :use ((:instance fn-sccr-scc-octet-listp-is-cbor-octet-listp
                                    (x (fn-scc-le-digits (len p)))))
            :in-theory (e/d (fn-scka-payload-octets fn-scc-nat-octets)
                            (fn-scc-le-digits))))))

(local
 (defthm fn-scka-head-cbor
   (implies (fn-scc-nat-encodablep n)
            (fn-cbor-octet-listp (fn-scka-head n)))
   :hints (("Goal" :use ((:instance fn-sccr-scc-octet-listp-is-cbor-octet-listp
                                    (x (fn-scc-le-digits n))))
            :in-theory (e/d (fn-scka-head fn-scc-nat-octets fn-scc-nat-encodablep)
                            (fn-scc-le-digits))))))

(local
 (defthm fn-scka-nat-listp-nthcdr
   (implies (nat-listp x) (nat-listp (nthcdr n x)))))

(local
 (defthm fn-scka-payload-octets-true-listp
   (implies (true-listp p) (true-listp (fn-scka-payload-octets p)))))

(local
 (defthm fn-scka-take-of-cons
   (implies (and (natp n) (< 0 n))
            (equal (take n (cons a x)) (cons a (take (- n 1) x))))))

(local
 (defthm fn-scka-nthcdr-of-cons
   (implies (and (natp n) (< 0 n))
            (equal (nthcdr n (cons a x)) (nthcdr (- n 1) x)))))

(local
 (defthm fn-scka-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(defthm fn-scka-append-batch-is-body
  (implies (and (natp k) (<= k (len (fn-scka-canon-payloads rows fn-arena)))
                (true-listp fn-octets))
           (let ((r (fn-scka-append-batch rows k fn-arena fn-octets)))
             (and (equal (mv-nth 1 r)
                         (append fn-octets
                                 (fn-scka-body (take k (fn-scka-canon-payloads rows fn-arena)))))
                  (equal (fn-scka-canon-payloads (mv-nth 0 r) fn-arena)
                         (nthcdr k (fn-scka-canon-payloads rows fn-arena))))))
  :hints (("Goal" :induct (fn-scka-append-batch rows k fn-arena fn-octets)
           :in-theory (e/d (fn-oct-append-list-is-append) (fn-scka-payload-octets)))))

(verify-guards fn-scka-payload-of)
(verify-guards fn-scka-canon-lens)
(verify-guards fn-scka-batches
  :hints (("Goal" :in-theory (disable fn-scka-batch-count))))
(verify-guards fn-scka-write-setup)
(verify-guards fn-scka-append-batch
  :hints (("Goal" :use ((:instance fn-scka-payload-of-digits
                                   (w (fn-row-wire-of (car rows) fn-arena)))
                        (:instance fn-scka-payload-of-octets
                                   (w (fn-row-wire-of (car rows) fn-arena))))
           :in-theory (disable fn-scka-payload-of-digits fn-scka-payload-of-octets
                               fn-scka-payload-octets))))

(defthm fn-scka-append-batch-octets-p
  (implies (fn-octets-p fn-octets)
           (fn-octets-p (mv-nth 1 (fn-scka-append-batch rows k fn-arena fn-octets))))
  :hints (("Goal" :induct (fn-scka-append-batch rows k fn-arena fn-octets)
           :in-theory (e/d (fn-oct-octets-p-is-octet-listp fn-oct-append-list-is-append)
                           (fn-scka-payload-octets)))
          ("Subgoal *1/2" :use ((:instance fn-scka-payload-octets-cbor
                                           (p (fn-scka-payload-of (fn-row-wire-of (car rows)
                                                                                  fn-arena))))
                                (:instance fn-scka-payload-of-digits
                                           (w (fn-row-wire-of (car rows) fn-arena)))
                                (:instance fn-scka-payload-of-octets
                                           (w (fn-row-wire-of (car rows) fn-arena))))
           :in-theory (e/d (fn-oct-octets-p-is-octet-listp fn-oct-append-list-is-append)
                           (fn-scka-payload-octets fn-scka-payload-octets-cbor
                            fn-scka-payload-of-digits fn-scka-payload-of-octets)))))

(local
 (defthm fn-scka-last-frame-true-list-listp
   (true-list-listp (fn-ockp-last-frame a index count s prev fn-octets))
   :hints (("Goal" :in-theory (enable fn-ockp-last-frame)))))

(local
 (defthm fn-scka-last-frame-car
   (true-listp (car (fn-ockp-last-frame a index count s prev fn-octets)))
   :hints (("Goal" :in-theory (enable fn-ockp-last-frame)))))

; -----------------------------------------------------------------------------
; 3. The step.  PST = (INDEX ROWS KS PREV TOTAL): the next segment's index,
; the rows not yet written, the batches not yet written, the chain's last
; trailer, the file octets admitted so far.  N the payload count, COUNT the
; run's segment count (1 + (len KS) at the start).
; (mv VERDICT FRAMES PST' fn-octets): VERDICT :ok, or (:refused REASON) when
; the frame is one the reader would refuse (the host abandons the staged
; file; nothing is written of it).

(defun fn-scka-initial-state (rows ks total)
  (declare (xargs :guard t))
  (list 0 rows ks *fn-scc-genesis* total))

(defun fn-scka-write-donep (pst count)
  (declare (xargs :guard t))
  (not (< (nfix (fn-sco-at 0 pst)) (nfix count))))

(defun fn-scka-write-step (pst n count s segment-bound file-bound fn-arena fn-octets)
  (declare (xargs :stobjs (fn-arena fn-octets) :verify-guards nil
                  :guard (and (true-listp pst) (natp n) (fn-scc-nat-encodablep n)
                              (natp count) (natp s))))
  (let* ((index (nfix (nth 0 pst))) (rows (nth 1 pst)) (ks (nth 2 pst))
         (prev (nth 3 pst)) (total (nfix (nth 4 pst)))
         (fn-octets (fn-octets-clear fn-octets)))
    (mv-let (rows ks fn-octets)
      (if (zp index)
          (let ((fn-octets (fn-octets-append-list (fn-scka-head n) fn-octets)))
            (mv rows ks fn-octets))
        (mv-let (rows fn-octets)
          (fn-scka-append-batch rows (if (consp ks) (nfix (car ks)) 0) fn-arena fn-octets)
          (mv rows (if (consp ks) (cdr ks) nil) fn-octets)))
      (let* ((frames (fn-ockp-last-frame 0 index count s prev fn-octets))
             (adm (fn-ockp-admit-frames frames total segment-bound file-bound)))
        (if (eq (car adm) :ok)
            (mv :ok frames (list (+ 1 index) rows ks (nth 3 (car frames)) (cadr adm))
                fn-octets)
          (mv adm nil pst fn-octets))))))

(verify-guards fn-scka-write-step
  :hints (("Goal" :in-theory (disable fn-scka-append-batch fn-ockp-last-frame
                                           fn-ockp-admit-frames fn-scka-head
                                           fn-scc-nat-encodablep))))

; The loop in the logic: the octets of every step's frames until the run's
; COUNT segments are written; FUEL bounds it and running out says so.
; (mv VERDICT OCTETS fn-octets)
(defun fn-scka-write-run (pst n count s segment-bound file-bound fuel fn-arena fn-octets)
  (declare (xargs :stobjs (fn-arena fn-octets) :measure (nfix fuel) :verify-guards nil))
  (if (fn-scka-write-donep pst count)
      (mv :ok nil fn-octets)
    (if (zp fuel)
        (mv :fuel nil fn-octets)
      (mv-let (verdict frames pst2 fn-octets)
        (fn-scka-write-step pst n count s segment-bound file-bound fn-arena fn-octets)
        (if (not (eq verdict :ok))
            (mv verdict nil fn-octets)
          (let ((octets (fn-sccb-plan-octets frames fn-octets)))
            (mv-let (verdict2 more fn-octets)
              (fn-scka-write-run pst2 n count s segment-bound file-bound (1- fuel)
                                 fn-arena fn-octets)
              (mv verdict2 (append octets more) fn-octets))))))))

; -----------------------------------------------------------------------------
; 4. The keystone.

; One frame over the whole buffer is the codec's frame of the buffer's list
; (books/owner-checkpoint-pipeline.lisp keeps its twin local).
(local
 (defthm fn-scka-take-len
   (implies (true-listp x) (equal (take (len x) x) x))))

(local
 (defthm fn-scka-last-frame-octets
   (implies (true-listp fn-octets)
            (equal (fn-sccb-plan-octets (fn-ockp-last-frame 0 index count s prev fn-octets)
                                        fn-octets)
                   (fn-scc-concat (fn-scc-frames (list fn-octets) index count s prev))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-ockp-last-frame fn-sccb-slice-acc-is-slice-list)
                                   (fn-scc-header fn-scc-seal take len))))))

(local
 (defthm fn-scka-last-frame-trailer
   (implies (true-listp fn-octets)
            (equal (nth 3 (car (fn-ockp-last-frame 0 index count s prev fn-octets)))
                   (fn-scc-seal prev (fn-scc-header index count (len fn-octets) s) fn-octets)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-ockp-last-frame fn-sccb-slice-acc-is-slice-list)
                            (fn-scc-header fn-scc-seal take len))))))

(local
 (defthm fn-scka-concat-of-cons-frames
   (implies
    (consp rest)
    (equal (fn-scc-concat (fn-scc-frames (cons c rest) index count s prev))
          (append (fn-scc-concat (fn-scc-frames (list c) index count s prev))
                  (fn-scc-concat (fn-scc-frames rest (+ 1 index) count s
                                                (fn-scc-seal prev
                                                             (fn-scc-header index count
                                                                            (len c) s)
                                                             c))))))
   :hints (("Goal" :in-theory (disable fn-scc-header fn-scc-seal)))))

; The step after the head: the batch's chunk framed at INDEX, the state
; advanced over it.
(defthm fn-scka-write-step-batch
  (let* ((r (fn-scka-write-step pst n count s segment-bound file-bound fn-arena fn-octets))
         (ps (fn-scka-canon-payloads (nth 1 pst) fn-arena))
         (k (nfix (car (nth 2 pst))))
         (c (fn-scka-body (take k ps))))
    (implies (and (posp (nth 0 pst)) (<= k (len ps))
                  (equal (mv-nth 0 r) :ok))
             (and (equal (fn-sccb-plan-octets (mv-nth 1 r) (mv-nth 3 r))
                         (fn-scc-concat (fn-scc-frames (list c) (nth 0 pst) count s (nth 3 pst))))
                  (consp (mv-nth 2 r))
                  (equal (nth 0 (mv-nth 2 r)) (+ 1 (nth 0 pst)))
                  (equal (fn-scka-canon-payloads (nth 1 (mv-nth 2 r)) fn-arena) (nthcdr k ps))
                  (equal (nth 2 (mv-nth 2 r)) (cdr (nth 2 pst)))
                  (equal (nth 3 (mv-nth 2 r))
                         (fn-scc-seal (nth 3 pst) (fn-scc-header (nth 0 pst) count (len c) s) c)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-scka-append-batch-is-body
                            (rows (nth 1 pst)) (k (nfix (car (nth 2 pst)))) (fn-octets nil)))
           :in-theory (e/d (fn-oct-append-list-is-append)
                           (fn-scka-append-batch-is-body fn-scka-append-batch fn-scka-body
                            fn-ockp-admit-frames fn-scc-header fn-scc-seal fn-scc-frames
                            fn-scka-canon-payloads fn-sccb-plan-octets)))))

; The head step: the tag and N framed at 0.
(defthm fn-scka-write-step-head
  (let ((r (fn-scka-write-step pst n count s segment-bound file-bound fn-arena fn-octets)))
    (implies (and (zp (nth 0 pst)) (equal (mv-nth 0 r) :ok))
             (and (equal (fn-sccb-plan-octets (mv-nth 1 r) (mv-nth 3 r))
                         (fn-scc-concat (fn-scc-frames (list (fn-scka-head n)) 0 count s
                                                       (nth 3 pst))))
                  (consp (mv-nth 2 r))
                  (equal (nth 0 (mv-nth 2 r)) 1)
                  (equal (nth 1 (mv-nth 2 r)) (nth 1 pst))
                  (equal (nth 2 (mv-nth 2 r)) (nth 2 pst))
                  (equal (nth 3 (mv-nth 2 r))
                         (fn-scc-seal (nth 3 pst)
                                      (fn-scc-header 0 count (len (fn-scka-head n)) s)
                                      (fn-scka-head n))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-oct-append-list-is-append)
                           (fn-scka-append-batch fn-scka-head
                            fn-ockp-admit-frames fn-scc-header fn-scc-seal fn-scc-frames
                            fn-sccb-plan-octets)))))

(local
 (defthm fn-scka-sum-bounds-car
   (implies (nat-listp ks)
            (<= (car ks) (fn-scka-sum ks)))
   :rule-classes :linear))

(local
 (defthm fn-scka-len-nthcdr
   (implies (and (natp n) (<= n (len xs)))
            (equal (len (nthcdr n xs)) (- (len xs) n)))))

(local
 (defthm fn-scka-chunks-of-cons
   (implies (consp ks)
            (equal (fn-scka-chunks ps ks)
                   (cons (fn-scka-body (take (nfix (car ks)) ps))
                         (fn-scka-chunks (nthcdr (nfix (car ks)) ps) (cdr ks)))))))

(local
 (defthm fn-scka-chunks-of-atom
   (implies (not (consp ks)) (equal (fn-scka-chunks ps ks) nil))))

(local
 (defthm fn-scka-len-zero-atom
   (equal (equal (len x) 0) (not (consp x)))))

; The batches after the head, by induction over the loop.
(defthm fn-scka-write-run-batches
  (let ((r (fn-scka-write-run pst n count s segment-bound file-bound fuel fn-arena fn-octets)))
    (implies (and (posp (nth 0 pst))
                  (equal count (+ (nth 0 pst) (len (nth 2 pst))))
                  (nat-listp (nth 2 pst))
                  (equal (fn-scka-sum (nth 2 pst))
                         (len (fn-scka-canon-payloads (nth 1 pst) fn-arena)))
                  (equal (mv-nth 0 r) :ok))
             (equal (mv-nth 1 r)
                    (fn-scc-concat
                     (fn-scc-frames (fn-scka-chunks (fn-scka-canon-payloads (nth 1 pst) fn-arena)
                                                    (nth 2 pst))
                                    (nth 0 pst) count s (nth 3 pst))))))
  :hints (("Goal" :induct (fn-scka-write-run pst n count s segment-bound file-bound fuel
                                             fn-arena fn-octets)
           :in-theory (e/d () (fn-scka-write-step fn-scka-body fn-scc-header fn-scc-seal
                               fn-scka-write-step-batch fn-scka-write-step-head
                               fn-scka-canon-payloads fn-sccb-plan-octets fn-scka-chunks)))
          ("Subgoal *1/4" :use ((:instance fn-scka-write-step-batch
                                           (count (+ (car pst) (len (nth 2 pst)))))))))

; KEYSTONE (the writer).  From the initial state over the live ROWS, the
; octets of every step's frames, in order, are the arena run of the rows'
; canonical payloads with the batches KS: exactly the segments
; books/store-checkpoint-arena-load.lisp `fn-scka-load-of-written-file'
; loads to those payloads.  Any buffer contents before the first step.
; The hypotheses are what `fn-scka-write-setup' establishes
; (fn-scka-write-setup-facts: N, the sum of KS, COUNT); a step the reader
; would refuse ends the loop with its reason, which is not :ok.
(defthm fn-scka-write-run-is-run-segments
  (let* ((ps (fn-scka-canon-payloads rows fn-arena))
         (r (fn-scka-write-run (fn-scka-initial-state rows ks total) (len ps) (+ 1 (len ks))
                               s segment-bound file-bound fuel fn-arena fn-octets)))
    (implies (and (nat-listp ks) (equal (fn-scka-sum ks) (len ps))
                  (equal (mv-nth 0 r) :ok))
             (equal (mv-nth 1 r) (fn-scc-concat (fn-scka-run-segments ps ks s)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-scka-write-step-head
                            (pst (fn-scka-initial-state rows ks total))
                            (n (len (fn-scka-canon-payloads rows fn-arena)))
                            (count (+ 1 (len ks))))
                 (:instance fn-scka-write-run-batches
                            (pst (mv-nth 2 (fn-scka-write-step
                                            (fn-scka-initial-state rows ks total)
                                            (len (fn-scka-canon-payloads rows fn-arena))
                                            (+ 1 (len ks)) s segment-bound file-bound
                                            fn-arena fn-octets)))
                            (n (len (fn-scka-canon-payloads rows fn-arena)))
                            (count (+ 1 (len ks))) (fuel (1- fuel))
                            (fn-octets (mv-nth 3 (fn-scka-write-step
                                                  (fn-scka-initial-state rows ks total)
                                                  (len (fn-scka-canon-payloads rows fn-arena))
                                                  (+ 1 (len ks)) s segment-bound file-bound
                                                  fn-arena fn-octets)))))
           :in-theory (e/d (fn-scka-run-segments fn-scka-run-chunks)
                           (fn-scka-write-step-head fn-scka-write-run-batches
                            fn-scka-write-step-batch fn-scka-write-step
                            fn-scka-body fn-scc-header fn-scc-seal fn-scka-head
                            fn-scka-canon-payloads fn-sccb-plan-octets fn-scka-chunks)))))
