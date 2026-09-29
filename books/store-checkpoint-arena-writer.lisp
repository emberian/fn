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

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
;; Its work is proof time no prover step counts (docs/proof-style.md
;; 9.1); planning/evidence/tau-cost-*.json has this book's figures.
(local (in-theory (disable (tau-system))))

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-scc-frames)
                          (:definition fn-scc-le-digits)
                          (:definition fn-scc-nat-encodablep)
                          (:definition fn-scc-nat-octets)
                          (:definition fn-scc-seal)
                          (:definition fn-sccb-frame-octets)
                          (:rewrite fn-bs-natural-head-is-no-other-wire-event)
                          (:rewrite fn-stxa-is-no-other-wire-event))))

(local (in-theory (disable fn-cp-idp fn-cp-idp-true-listp
                           fn-sccr-scc-octet-listp-is-cbor-octet-listp
                           fn-sccr-cbor-octet-listp-is-scc-octet-listp
                           fn-row-wire-of fn-scka-sealsp fn-scka-payload-of
                           fn-scka-canon-payloads-is-payloads-of-alpha
                           ; imported rules that backchain from (true-listp x) into an
                           ; unrelated recognizer (the NNTP response text, the NOV line)
                           ; or open the octet recognizers on every list
                           fn-nntp-response-text-true-listp fn-nntp-clean-line-is-response-text
                           fn-scc-octet-listp-facts fn-sccb-scc-octetp-is-cbor-octetp)))

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

; The run's octets, from the payloads' lengths and its segment count: every
; segment its header and its trailer, the head chunk (the tag and N), and
; each payload its length's octets and its own.
; Executes by a loop (PKT-876, lane open-depth): one frame per payload of the
; checkpoint.  The :logic is the recursion, unchanged; equal by the guard proof.
(defun fn-scka-enc-lens-sum-acc (lens acc)
  (declare (xargs :guard (and (nat-listp lens) (acl2-numberp acc))))
  (if (atom lens)
      acc
    (fn-scka-enc-lens-sum-acc (cdr lens) (+ acc (fn-scka-enc-len (nfix (car lens)))))))

(defun fn-scka-enc-lens-sum (lens)
  (declare (xargs :guard (nat-listp lens) :verify-guards nil))
  (mbe :logic
       (if (atom lens)
           0
         (+ (fn-scka-enc-len (nfix (car lens))) (fn-scka-enc-lens-sum (cdr lens))))
       :exec (fn-scka-enc-lens-sum-acc lens 0)))

(encapsulate ()
  (local
   (defthm fn-scka-enc-lens-sum-acc-is-plus
     (implies (acl2-numberp acc)
              (equal (fn-scka-enc-lens-sum-acc lens acc)
                     (+ acc (fn-scka-enc-lens-sum lens))))
     :hints (("Goal" :in-theory (disable fn-scka-enc-len)))))
  (verify-guards fn-scka-enc-lens-sum
    :hints (("Goal" :in-theory (disable fn-scka-enc-len)))))

(defun fn-scka-run-octets (lens count)
  (declare (xargs :guard (and (nat-listp lens) (natp count))))
  (+ (* (nfix count) (+ *fn-scc-segment-header-octets* *fn-frame-trailer-octets*))
     (len (fn-scka-head (len lens)))
     (fn-scka-enc-lens-sum lens)))

; (list N KS COUNT OCTETS): the payload count, the batches, the run's
; segments and the run's octets.
(defun fn-scka-lens-setup (lens seg)
  (declare (xargs :guard (and (nat-listp lens) (natp seg)) :verify-guards nil))
  (let ((ks (fn-scka-batches lens seg)))
    (list (len lens) ks (+ 1 (len ks)) (fn-scka-run-octets lens (+ 1 (len ks))))))

(defun fn-scka-write-setup (rows seg fn-arena)
  (declare (xargs :stobjs fn-arena :guard (natp seg) :verify-guards nil))
  (fn-scka-lens-setup (fn-scka-canon-lens rows fn-arena) seg))

(defthm fn-scka-write-setup-facts
  (let ((su (fn-scka-write-setup rows seg fn-arena))
        (ps (fn-scka-canon-payloads rows fn-arena)))
    (and (equal (nth 0 su) (len ps))
         (equal (fn-scka-sum (nth 1 su)) (len ps))
         (equal (nth 2 su) (+ 1 (len (nth 1 su))))))
  :hints (("Goal" :in-theory (disable fn-scka-batches fn-scka-lens))))

; -----------------------------------------------------------------------------
; 1b. Each canonical payload's SOURCE (lane checkpoint-arena-3): where the
; writer copies it from.  A held row's payload is its handle in the live
; arena (when the handle is sealed; else no octets), any other sealing
; row's is the octet list its wire event carries (a composite's article).
; The writer copies a handle's octets straight from the arena, one
; fn-arena-get per octet (`fn-scka-append-src'), so the arena run is written
; without alpha: the history is never materialized as wire records to write
; it.  One walk of the rows (`fn-scka-srcs-n', in bounded steps) gives the
; lengths and the sources together.

(defun fn-scka-src-of (row w fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (if (and (fn-held-p row) (fn-record-p w))
      (let ((h (fn-record-payload row)))
        (if (and (natp h) (< h (fn-arena-count fn-arena))) h nil))
    (fn-scka-payload-of w)))

(defun fn-scka-canon-srcs (rows fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (if (atom rows)
      nil
    (let ((w (fn-row-wire-of (car rows) fn-arena)))
      (if (fn-scka-sealsp w)
          (cons (fn-scka-src-of (car rows) w fn-arena) (fn-scka-canon-srcs (cdr rows) fn-arena))
        (fn-scka-canon-srcs (cdr rows) fn-arena)))))

; (A true list whatever the value: the writer's step theorems need no
; hypothesis about the arena; true-list-fix of a true list is the list, one
; walk and no allocation.)
(defun fn-scka-src-payload (s fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (true-list-fix
   (if (natp s)
       (if (< s (fn-arena-count fn-arena)) (fn-arena-payload s fn-arena) nil)
     s)))

(defun fn-scka-src-payloads (srcs fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (atom srcs)
      nil
    (cons (fn-scka-src-payload (car srcs) fn-arena)
          (fn-scka-src-payloads (cdr srcs) fn-arena))))

; -----------------------------------------------------------------------------
; 2. The batch: the next K canonical payloads appended to the buffer, each
; its length and its octets; the rows after the K-th sealing row.
; (mv ROWS' fn-octets)

; A source the writer can copy: a sealed handle, or an octet list; either
; way a length the run's length field encodes (at most 255 digits).
(defun fn-scka-src-okp (s fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (natp s)
      (and (< s (fn-arena-count fn-arena))
           (fn-scc-nat-encodablep (fn-arena-payload-len s fn-arena)))
    (and (fn-cbor-octet-listp s) (true-listp s)
         (fn-scc-nat-encodablep (len s)))))

(defun fn-scka-srcs-okp (srcs fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (atom srcs)
      t
    (and (fn-scka-src-okp (car srcs) fn-arena)
         (fn-scka-srcs-okp (cdr srcs) fn-arena))))

; One source's length field and octets, in one bulk append (the payload's
; octets read from the arena as one list, never through alpha).
(defun fn-scka-append-src (s fn-arena fn-octets)
  (declare (xargs :stobjs (fn-arena fn-octets) :verify-guards nil
                  :guard (fn-scka-src-okp s fn-arena)))
  (fn-octets-append-list (fn-scka-payload-octets (fn-scka-src-payload s fn-arena)) fn-octets))

(defun fn-scka-append-batch (srcs k fn-arena fn-octets)
  (declare (xargs :stobjs (fn-arena fn-octets) :verify-guards nil
                  :guard (and (natp k) (fn-scka-srcs-okp srcs fn-arena))
                  :measure (len srcs)))
  (if (or (atom srcs) (zp k))
      (mv srcs fn-octets)
    (let ((fn-octets (fn-scka-append-src (car srcs) fn-arena fn-octets)))
      (fn-scka-append-batch (cdr srcs) (1- k) fn-arena fn-octets))))

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

(local
 (defthm fn-scka-payload-listp-nth
   (implies (fn-arn-payload-listp xs)
            (and (fn-cbor-octet-listp (nth h xs)) (true-listp (nth h xs))))
   :hints (("Goal" :in-theory (enable nth fn-cbor-octet-listp)))))

; An admissible source reads back an octet list whose length encodes.
(defthm fn-scka-src-okp-payload
  (implies (and (fn-arena-p fn-arena) (fn-scka-src-okp s fn-arena))
           (let ((p (fn-scka-src-payload s fn-arena)))
             (and (fn-cbor-octet-listp p) (true-listp p)
                  (fn-scc-nat-encodablep (len p)))))
  :hints (("Goal" :in-theory (e/d (fn-arena-p-is-payload-listp) (fn-scc-nat-encodablep)))))

(local (in-theory (enable (tau-system)))) ; tau-cost: this form needs tau
(defthm fn-scka-append-batch-is-body
  (implies (and (natp k) (<= k (len srcs)) (true-listp fn-octets))
           (let ((r (fn-scka-append-batch srcs k fn-arena fn-octets)))
             (and (equal (mv-nth 1 r)
                         (append fn-octets
                                 (fn-scka-body (take k (fn-scka-src-payloads srcs fn-arena)))))
                  (equal (mv-nth 0 r) (nthcdr k srcs)))))
  :hints (("Goal" :induct (fn-scka-append-batch srcs k fn-arena fn-octets)
           :in-theory (e/d (fn-oct-append-list-is-append) (fn-scka-payload-octets
                                                           fn-scka-src-payload
                                                           fn-scka-src-okp)))))
(local (in-theory (disable (tau-system))))

(defthm fn-scka-len-src-payloads
  (equal (len (fn-scka-src-payloads srcs fn-arena)) (len srcs)))

(local (defthm fn-scka-nthcdr-nil (equal (nthcdr n nil) nil)))

(defthm fn-scka-src-payloads-nthcdr
  (equal (fn-scka-src-payloads (nthcdr k srcs) fn-arena)
         (nthcdr k (fn-scka-src-payloads srcs fn-arena)))
  :hints (("Goal" :in-theory (disable fn-scka-src-payload))))

(verify-guards fn-scka-payload-of)
(verify-guards fn-scka-canon-lens)
(verify-guards fn-scka-batches
  :hints (("Goal" :in-theory (disable fn-scka-batch-count))))
(local
 (defthm fn-scka-canon-lens-nat-listp
   (nat-listp (fn-scka-canon-lens rows fn-arena))))

; (Section 1b, continued: the sources read back the canonical payloads.)
(local
 (defthm fn-scka-record-payload-of-held-wire
   (equal (fn-record-payload (fn-held-wire h p)) p)
   :hints (("Goal" :in-theory (enable fn-held-wire)))))

(local
 (defthm fn-scka-payload-of-not-natp
   (implies (fn-scka-sealsp w)
            (not (natp (fn-scka-payload-of w))))
   :hints (("Goal" :use ((:instance fn-scka-payload-of-octets))
            :in-theory (disable fn-scka-payload-of-octets fn-scka-payload-of fn-scka-sealsp)))))

(local
 (defthm fn-scka-payload-of-record
   (implies (fn-record-p w) (equal (fn-scka-payload-of w) (fn-record-payload w)))
   :hints (("Goal" :in-theory (enable fn-scka-payload-of)))))

; A sealing row's source reads back its canonical payload.
(defthm fn-scka-src-payload-of-src-of
  (implies (fn-scka-sealsp (fn-row-wire-of row fn-arena))
           (equal (fn-scka-src-payload (fn-scka-src-of row (fn-row-wire-of row fn-arena) fn-arena)
                                       fn-arena)
                  (fn-scka-payload-of (fn-row-wire-of row fn-arena))))
  :hints (("Goal" :cases ((and (fn-held-p row) (fn-record-p (fn-row-wire-of row fn-arena))))
           :in-theory (e/d (fn-scka-src-of fn-scka-src-payload)
                           (fn-scka-sealsp fn-scka-payload-of fn-record-p fn-row-wire-of)))
          ("Subgoal 1" :use ((:instance fn-scka-payload-of-octets
                                        (w (fn-row-wire-of row fn-arena))))
           :in-theory (e/d (fn-scka-src-of fn-scka-src-payload fn-row-wire-of
                                        fn-row-bytes)
                                       (fn-scka-sealsp fn-scka-payload-of fn-record-p
                                        fn-held-wire fn-scka-payload-of-octets)))))

(defthm fn-scka-src-payloads-of-canon-srcs
  (equal (fn-scka-src-payloads (fn-scka-canon-srcs rows fn-arena) fn-arena)
         (fn-scka-canon-payloads rows fn-arena))
  :hints (("Goal" :induct (fn-scka-canon-srcs rows fn-arena)
           :in-theory (disable fn-scka-src-of fn-scka-src-payload fn-row-wire-of
                               fn-scka-sealsp fn-scka-payload-of))))

; The walk: up to N rows per call, the lengths and the sources consed onto
; LACC and SACC (reversed).  (list ROWS' LACC' SACC').
(defun fn-scka-srcs-n (rows n lacc sacc fn-arena)
  (declare (xargs :stobjs fn-arena :guard (natp n) :verify-guards nil
                  :measure (nfix n)))
  (if (or (atom rows) (zp n))
      (list rows lacc sacc)
    (let ((w (fn-row-wire-of (car rows) fn-arena)))
      (if (fn-scka-sealsp w)
          (fn-scka-srcs-n (cdr rows) (1- n)
                          (cons (len (fn-scka-payload-of w)) lacc)
                          (cons (fn-scka-src-of (car rows) w fn-arena) sacc)
                          fn-arena)
        (fn-scka-srcs-n (cdr rows) (1- n) lacc sacc fn-arena)))))

; The host's bounded calls are one walk (the state after A rows, walked B
; more, is the walk of A + B rows).
(defthm fn-scka-srcs-n-compose
  (implies (and (natp a) (natp b))
           (equal (let ((st (fn-scka-srcs-n rows a lacc sacc fn-arena)))
                    (fn-scka-srcs-n (nth 0 st) b (nth 1 st) (nth 2 st) fn-arena))
                  (fn-scka-srcs-n rows (+ a b) lacc sacc fn-arena)))
  :hints (("Goal" :induct (fn-scka-srcs-n rows a lacc sacc fn-arena)
           :in-theory (disable fn-scka-src-of fn-row-wire-of fn-scka-sealsp fn-scka-payload-of))))

; The whole walk is the lengths and the sources, reversed onto the
; accumulators; the rows are consumed.
(defthm fn-scka-srcs-n-complete
  (implies (and (true-listp rows) (<= (len rows) (nfix n)))
           (equal (fn-scka-srcs-n rows n lacc sacc fn-arena)
                  (list nil
                        (revappend (fn-scka-canon-lens rows fn-arena) lacc)
                        (revappend (fn-scka-canon-srcs rows fn-arena) sacc))))
  :hints (("Goal" :induct (fn-scka-srcs-n rows n lacc sacc fn-arena)
           :in-theory (disable fn-scka-src-of fn-row-wire-of fn-scka-sealsp fn-scka-payload-of))))

(verify-guards fn-scka-lens-setup)
(verify-guards fn-scka-write-setup)
(verify-guards fn-scka-src-of)
(verify-guards fn-scka-canon-srcs)
(verify-guards fn-scka-srcs-n)

; The lengths are naturals (the host hands the walk's lengths to
; fn-scka-lens-setup).
(defthm fn-scka-srcs-n-lens-nat-listp
  (implies (nat-listp lacc)
           (nat-listp (nth 1 (fn-scka-srcs-n rows n lacc sacc fn-arena))))
  :hints (("Goal" :in-theory (disable fn-scka-src-of fn-row-wire-of fn-scka-sealsp
                                      fn-scka-payload-of))))

; Every source of a sealing row is one the writer can copy.
(local
 (defthm fn-scka-held-wire-payloadp
   (implies (fn-record-p (fn-held-wire row bytes))
            (fn-record-payloadp bytes))
   :hints (("Goal" :use ((:instance fn-scka-record-payloadp (x (fn-held-wire row bytes))))
            :in-theory (disable fn-scka-record-payloadp fn-held-wire fn-record-p)))))

(local
 (defthm fn-scka-payloadp-encodable
   (implies (fn-record-payloadp p)
            (fn-scc-nat-encodablep (len p)))
   :hints (("Goal" :use ((:instance fn-scka-len-le-digits-bound (n (len p)) (k 8)))
            :in-theory (e/d (fn-record-payloadp fn-scc-nat-encodablep)
                            (fn-scka-len-le-digits-bound))))))

(defthm fn-scka-src-okp-of-src-of
  (implies (fn-scka-sealsp (fn-row-wire-of row fn-arena))
           (fn-scka-src-okp (fn-scka-src-of row (fn-row-wire-of row fn-arena) fn-arena) fn-arena))
  :hints (("Goal" :use ((:instance fn-scka-payload-of-octets (w (fn-row-wire-of row fn-arena)))
                        (:instance fn-scka-record-payloadp-bound (w (fn-row-wire-of row fn-arena))))
           :in-theory (e/d (fn-row-wire-of fn-row-bytes fn-scka-sealsp fn-scka-payload-of)
                           (fn-scka-payload-of-octets fn-scka-record-payloadp-bound
                            fn-held-wire fn-record-p fn-stxa-p fn-replay-composite-record)))))

(defthm fn-scka-srcs-okp-of-canon-srcs
  (fn-scka-srcs-okp (fn-scka-canon-srcs rows fn-arena) fn-arena)
  :hints (("Goal" :induct (fn-scka-canon-srcs rows fn-arena)
           :in-theory (disable fn-scka-src-of fn-scka-src-okp fn-row-wire-of fn-scka-sealsp))))

; The publication's setup: the table pipeline's (books/owner-checkpoint-
; writer.lisp fn-ockp-setup: the tables of NEXT, their estimate, the
; encodability check), with the decision taken by name, before anything is
; allocated, over the WHOLE file's octets: the arena run's (ALEN, from
; fn-scka-write-setup) and the tables'.  (list VERDICT TABLES COUNTS MTRIE
; INDEX N ESTIMATE), ESTIMATE the whole file's.
(defun fn-scka-publication-setup (next frontier revision log seg budget free alen)
  (declare (xargs :guard (and (natp seg) (natp budget) (natp alen))
                  :guard-hints (("Goal" :in-theory (disable fn-ockp-setup fn-ockp-decide)))))
  (let ((setup (fn-ockp-setup next frontier revision log seg budget free)))
    (if (eq (car setup) :unencodable)
        setup
      (let ((estimate (+ alen (nfix (fn-sco-at 6 setup)))))
        (update-nth 6 estimate
                    (update-nth 0 (fn-ockp-decide estimate budget free) setup))))))
;; PRF-129's disk half: the publication's space check.  KEYSTONE: the setup
; the host calls before it allocates anything (host/owner-host.lisp
; fn-owner-sco-prepare, the owner's automatic and `store compact' /
; `store reclaim' checkpoint through host/native/owner.lisp
; fnn-owner-publish-captured; host/store-node-host.lisp
; fn-store-sco-publish-setup, the offline writer) answers a plan exactly when
; the whole file's estimate -- the arena run's ALEN plus the tables' octets,
; which are the octets the table pipeline writes (fn-ockp-estimate-is-len-
; file-octets) -- is within the budget and within the observed free octets
; less the maintenance reservation (fn-ockp-space: free less
; fn-smr-reserve-octets, PRF-129's reservation); the plan names that
; estimate.  Otherwise it defers by name (fn-ockp-decide-defers-by-the-
; estimate) and nothing is written.  Scope: ALEN is the arena run's octets
; computed from the payload lengths (fn-scka-run-octets); that it is the
; length of what fn-scka-write-run writes is not proved here.
(defthm fn-scka-publication-setup-plans-within-the-disk
  (let* ((setup (fn-scka-publication-setup next frontier revision log seg budget free alen))
         (estimate (nth 6 setup)))
    (implies (not (equal (car setup) :unencodable))
             (and (equal estimate
                         (+ alen (len (fn-sct-file-octets
                                       (fn-sct-table-programs (nth 1 setup) (nth 4 setup))
                                       seg s))))
                  (iff (equal (car (car setup)) :plan)
                       (and (<= estimate budget)
                            (natp free)
                            (<= estimate (fn-ockp-space free))))
                  (implies (equal (car (car setup)) :plan)
                           (equal (car setup) (list :plan estimate))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-scka-publication-setup fn-ockp-setup fn-ockp-space fn-ockp-decide)
                           (fn-sct-file-octets
                            fn-sct-table-programs fn-ockp-counts fn-ockp-tables-encodablep))
           :use ((:instance fn-ockp-estimate-is-len-file-octets
                            (tables (fn-sct-tables-of-capture next frontier revision log))
                            (index (fn-sco-event-index next)))))))

(verify-guards fn-scka-append-src
  :hints (("Goal" :use ((:instance fn-scka-src-okp-payload))
           :in-theory (e/d (fn-scc-nat-encodablep)
                           (fn-scka-src-okp-payload fn-scka-payload-octets fn-scka-src-payload
                            fn-scka-src-okp)))))

(verify-guards fn-scka-append-batch
  :hints (("Goal" :in-theory (disable fn-scka-append-src fn-scka-src-okp))))

(defthm fn-scka-append-src-octets-p
  (implies (and (fn-arena-p fn-arena) (fn-scka-src-okp s fn-arena) (fn-octets-p fn-octets))
           (fn-octets-p (fn-scka-append-src s fn-arena fn-octets)))
  :hints (("Goal" :use ((:instance fn-scka-src-okp-payload)
                        (:instance fn-scka-payload-octets-cbor
                                   (p (fn-scka-src-payload s fn-arena))))
           :in-theory (e/d (fn-oct-octets-p-is-octet-listp fn-oct-append-list-is-append
                            fn-scc-nat-encodablep)
                           (fn-scka-src-okp-payload fn-scka-payload-octets-cbor
                            fn-scka-payload-octets fn-scka-src-payload fn-scka-src-okp)))))

(defthm fn-scka-append-batch-octets-p
  (implies (and (fn-arena-p fn-arena) (fn-scka-srcs-okp srcs fn-arena) (fn-octets-p fn-octets))
           (fn-octets-p (mv-nth 1 (fn-scka-append-batch srcs k fn-arena fn-octets))))
  :hints (("Goal" :induct (fn-scka-append-batch srcs k fn-arena fn-octets)
           :in-theory (disable fn-scka-append-src fn-scka-src-okp))))

(defthm fn-scka-srcs-okp-nthcdr
  (implies (fn-scka-srcs-okp srcs fn-arena)
           (fn-scka-srcs-okp (nthcdr k srcs) fn-arena))
  :hints (("Goal" :in-theory (disable fn-scka-src-okp))))

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
                              (natp count) (natp s)
                              (fn-scka-srcs-okp (nth 1 pst) fn-arena))))
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
         (ps (fn-scka-src-payloads (nth 1 pst) fn-arena))
         (k (nfix (car (nth 2 pst))))
         (c (fn-scka-body (take k ps))))
    (implies (and (posp (nth 0 pst)) (<= k (len ps))
                  (equal (mv-nth 0 r) :ok))
             (and (equal (fn-sccb-plan-octets (mv-nth 1 r) (mv-nth 3 r))
                         (fn-scc-concat (fn-scc-frames (list c) (nth 0 pst) count s (nth 3 pst))))
                  (consp (mv-nth 2 r))
                  (equal (nth 0 (mv-nth 2 r)) (+ 1 (nth 0 pst)))
                  (equal (nth 1 (mv-nth 2 r)) (nthcdr k (nth 1 pst)))
                  (equal (nth 2 (mv-nth 2 r)) (cdr (nth 2 pst)))
                  (equal (nth 3 (mv-nth 2 r))
                         (fn-scc-seal (nth 3 pst) (fn-scc-header (nth 0 pst) count (len c) s) c)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-scka-append-batch-is-body
                            (srcs (nth 1 pst)) (k (nfix (car (nth 2 pst)))) (fn-octets nil)))
           :in-theory (e/d (fn-oct-append-list-is-append)
                           (fn-scka-append-batch-is-body fn-scka-append-batch fn-scka-body
                            fn-scka-head fn-scc-le-digits fn-sccr-nth-is-cell
                            fn-ockp-admit-frames fn-scc-header fn-scc-seal fn-scc-frames
                            fn-scka-src-payloads fn-sccb-plan-octets fn-scka-srcs-okp)))))

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
   (implies (natp (car ks))
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
                  (equal (fn-scka-sum (nth 2 pst))
                         (len (fn-scka-src-payloads (nth 1 pst) fn-arena)))
                  (equal (mv-nth 0 r) :ok))
             (equal (mv-nth 1 r)
                    (fn-scc-concat
                     (fn-scc-frames (fn-scka-chunks (fn-scka-src-payloads (nth 1 pst) fn-arena)
                                                    (nth 2 pst))
                                    (nth 0 pst) count s (nth 3 pst))))))
  :hints (("Goal" :induct (fn-scka-write-run pst n count s segment-bound file-bound fuel
                                             fn-arena fn-octets)
           :in-theory (e/d () (fn-scka-write-step fn-scka-body fn-scc-header fn-scc-seal
                               fn-scka-write-step-batch fn-scka-write-step-head
                               fn-scka-src-payloads fn-sccb-plan-octets fn-scka-srcs-okp fn-scka-chunks
                               ; rules the octet buffer and the NNTP books export that
                               ; fire on every list here and never help
                               fn-nntp-article-idp-is-consp fn-oct-bufp-true-listp
                               fn-octets$c-bufp)))
          ("Subgoal *1/4" :use ((:instance fn-scka-write-step-batch
                                           (count (+ (car pst) (len (nth 2 pst)))))))))

; From the initial state over the sources SRCS, the octets of every step's
; frames, in order, are the arena run of the sources' payloads with the
; batches KS: exactly the segments
; books/store-checkpoint-arena-load.lisp `fn-scka-load-of-written-file'
; loads to those payloads.  Any buffer contents before the first step.
; The hypotheses are what `fn-scka-write-setup' establishes
; (fn-scka-write-setup-facts: N, the sum of KS, COUNT); a step the reader
; would refuse ends the loop with its reason, which is not :ok.
(defthm fn-scka-write-run-srcs-is-run-segments
  (let* ((ps (fn-scka-src-payloads srcs fn-arena))
         (r (fn-scka-write-run (fn-scka-initial-state srcs ks total) (len ps) (+ 1 (len ks))
                               s segment-bound file-bound fuel fn-arena fn-octets)))
    (implies (and (equal (fn-scka-sum ks) (len ps))
                  (equal (mv-nth 0 r) :ok))
             (equal (mv-nth 1 r) (fn-scc-concat (fn-scka-run-segments ps ks s)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-scka-write-step-head
                            (pst (fn-scka-initial-state srcs ks total))
                            (n (len (fn-scka-src-payloads srcs fn-arena)))
                            (count (+ 1 (len ks))))
                 (:instance fn-scka-write-run-batches
                            (pst (mv-nth 2 (fn-scka-write-step
                                            (fn-scka-initial-state srcs ks total)
                                            (len (fn-scka-src-payloads srcs fn-arena))
                                            (+ 1 (len ks)) s segment-bound file-bound
                                            fn-arena fn-octets)))
                            (n (len (fn-scka-src-payloads srcs fn-arena)))
                            (count (+ 1 (len ks))) (fuel (1- fuel))
                            (fn-octets (mv-nth 3 (fn-scka-write-step
                                                  (fn-scka-initial-state srcs ks total)
                                                  (len (fn-scka-src-payloads srcs fn-arena))
                                                  (+ 1 (len ks)) s segment-bound file-bound
                                                  fn-arena fn-octets)))))
           :in-theory (e/d (fn-scka-run-segments fn-scka-run-chunks)
                           (fn-scka-write-step-head fn-scka-write-run-batches
                            fn-scka-write-step-batch fn-scka-write-step
                            fn-scka-body fn-scc-header fn-scc-seal fn-scka-head
                            fn-scka-src-payloads fn-sccb-plan-octets fn-scka-srcs-okp fn-scka-chunks)))))

; -----------------------------------------------------------------------------

; KEYSTONE (the writer).  From the initial state over the SOURCES of the
; live ROWS (fn-scka-canon-srcs, which the host's bounded fn-scka-srcs-n
; calls produce: fn-scka-srcs-n-compose, fn-scka-srcs-n-complete), the
; octets of every step's frames, in order, are the arena run of the rows'
; canonical payloads with the batches KS: exactly the segments
; books/store-checkpoint-arena-load.lisp `fn-scka-load-of-written-file'
; loads to those payloads.  Any buffer contents before the first step.
(defthm fn-scka-write-run-is-run-segments
  (let* ((ps (fn-scka-canon-payloads rows fn-arena))
         (r (fn-scka-write-run (fn-scka-initial-state (fn-scka-canon-srcs rows fn-arena) ks total)
                               (len ps) (+ 1 (len ks))
                               s segment-bound file-bound fuel fn-arena fn-octets)))
    (implies (and (equal (fn-scka-sum ks) (len ps))
                  (equal (mv-nth 0 r) :ok))
             (equal (mv-nth 1 r) (fn-scc-concat (fn-scka-run-segments ps ks s)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-scka-write-run-srcs-is-run-segments
                            (srcs (fn-scka-canon-srcs rows fn-arena))))
           :in-theory (disable fn-scka-write-run-srcs-is-run-segments fn-scka-write-run
                               fn-scka-initial-state fn-scka-run-segments fn-scka-canon-srcs
                               fn-scka-canon-payloads))))

; 5. The owner's next checkpoint.  The owner publishes from its live rows
; while it serves: BASE is the checkpoint it last captured (at the open, the
; open's extended checkpoint E; after a publication, that publication's
; NEXT), the capture of the canonical rows of the first (len (fn-sco-records
; BASE)) live rows, and H0 their canonical payload count.  NEXT extends BASE
; over the canonical rows of the rows after them, whose handles continue
; from H0: the history is never canonicalized twice.  (NEXT, or :bad when a
; row's alpha does not intern.)  host/owner-host.lisp fn-owner-sco-prepare
; calls it off the owner mutex (it READS the arena: the handles it reads
; are below the count the capture saw, sealed before the capture and never
; rewritten).

(defun fn-scka-next-checkpoint (base h0 configs records fn-arena)
  (declare (xargs :stobjs fn-arena :guard (natp h0) :verify-guards nil))
  (let ((canon (fn-scka-canon-rows (nthcdr (len (fn-sco-records base)) records) fn-arena h0)))
    (if (equal canon :bad)
        :bad
      (fn-sco-extend base configs canon))))

(local
 (defthm fn-scka-sco-records-of-capture
   (implies (true-listp records)
            (equal (fn-sco-records (fn-sco-capture configs records)) records))
   :hints (("Goal" :in-theory (e/d (fn-sco-capture fn-sco-make fn-sco-records fn-sco-at)
                                   (fn-sco-cpr-prefix fn-replay-identity-loop
                                    fn-cpe-projection-replay fn-th-prefix-loop
                                    fn-cei-build-aux))))))

(local
 (defthm fn-scka-rows-wire-of-append
   (equal (fn-rows-wire-of (append a b) fn-arena)
          (append (fn-rows-wire-of a fn-arena) (fn-rows-wire-of b fn-arena)))))

(local
 (defthm fn-scka-len-intern-at
   (implies (not (equal (fn-scka-intern-at ws h) :bad))
            (equal (len (fn-scka-intern-at ws h)) (len ws)))
   :hints (("Goal" :in-theory (disable fn-scka-intern-one fn-scka-sealsp)))))

(local
 (defthm fn-scka-len-take
   (implies (natp n) (equal (len (take n x)) n))))

(local
 (defthm fn-scka-len-rows-wire-of
   (equal (len (fn-rows-wire-of rows fn-arena)) (len rows))))

(local
 (defthm fn-scka-append-take-nthcdr-all
   (implies (and (natp n) (<= n (len x)))
            (equal (append (take n x) (nthcdr n x)) x))))

; KEYSTONE (the owner's next): from a BASE that is the capture of the
; canonical rows of the first PLEN live rows, with H0 their canonical
; payload count, NEXT is the capture of the canonical rows of all of them:
; the file the publication writes is that of fn-store-sco-publish-setup's
; NEXT for the same rows, so the load and open keystones hold of it.
(defthm fn-scka-next-checkpoint-is-capture
  (implies (and (natp plen) (<= plen (len records))
                (equal base (fn-sco-capture configs
                                            (fn-scka-canon-rows (take plen records) fn-arena 0)))
                (equal h0 (len (fn-scka-canon-payloads (take plen records) fn-arena)))
                (not (equal (fn-scka-canon-rows records fn-arena 0) :bad)))
           (equal (fn-scka-next-checkpoint base h0 configs records fn-arena)
                  (fn-sco-capture configs (fn-scka-canon-rows records fn-arena 0))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-scka-append-take-nthcdr-all (n plen) (x records))
                 (:instance fn-scka-intern-at-of-append
                            (ws (fn-rows-wire-of (take plen records) fn-arena))
                            (vs (fn-rows-wire-of (nthcdr plen records) fn-arena)) (h 0))
                 (:instance fn-scka-intern-at-of-append-bad
                            (ws (fn-rows-wire-of (take plen records) fn-arena))
                            (vs (fn-rows-wire-of (nthcdr plen records) fn-arena)) (h 0))
                 (:instance fn-scka-intern-at-store-eventsp
                            (ws (fn-rows-wire-of (take plen records) fn-arena)))
                 (:instance fn-scka-intern-at-true-listp
                            (ws (fn-rows-wire-of (take plen records) fn-arena)) (h 0))
                 (:instance fn-scka-intern-at-true-listp
                            (ws (fn-rows-wire-of (nthcdr plen records) fn-arena))
                            (h (len (fn-scka-payloads (fn-rows-wire-of (take plen records)
                                                                        fn-arena)))))
                 (:instance fn-sco-extend-of-capture
                            (prefix (fn-scka-intern-at (fn-rows-wire-of (take plen records)
                                                                         fn-arena) 0))
                            (suffix (fn-scka-intern-at
                                     (fn-rows-wire-of (nthcdr plen records) fn-arena)
                                     (len (fn-scka-payloads (fn-rows-wire-of (take plen records)
                                                                              fn-arena)))))))
           :in-theory (e/d (fn-scka-canon-rows-is-intern-at-of-alpha
                            fn-scka-canon-payloads-is-payloads-of-alpha)
                           (fn-scka-append-take-nthcdr-all fn-scka-intern-at-of-append
                            fn-scka-intern-at-of-append-bad fn-scka-intern-at-store-eventsp
                            fn-scka-intern-at-true-listp fn-sco-extend-of-capture
                            fn-scka-intern-at fn-scka-payloads fn-rows-wire-of
                            fn-sco-extend fn-sco-capture fn-scka-canon-rows
                            fn-scka-canon-payloads)))))

; -----------------------------------------------------------------------------
; 6. The base the owner KEEPS between publications (lane checkpoint-arena-3;
; per-record-state PKT-PRS-2: a kept base's own event index was 0.68 KB per
; record, a second trie beside the store node's).  The owner keeps the base
; STRIPPED of its event index (`fn-scka-strip-base') and rebuilds it from the
; base's records when it publishes (`fn-scka-restore-base', the index
; fn-sco-capture builds), so between publications only the records and the
; four projections are retained.  host/owner-host.lisp: the base is stored
; stripped (fn-owner-install-extended, fn-owner-sco-publication-done) and
; restored in fn-owner-sco-prepare before fn-scka-next-checkpoint.

(defun fn-scka-strip-base (c)
  (declare (xargs :guard t))
  (fn-sco-make (fn-sco-records c) (fn-sco-cpr c) (fn-sco-identity c)
               (fn-sco-consumer c) (fn-sco-topic c) nil))

(defun fn-scka-restore-base (c)
  (declare (xargs :guard t))
  (fn-sco-make (fn-sco-records c) (fn-sco-cpr c) (fn-sco-identity c)
               (fn-sco-consumer c) (fn-sco-topic c)
               (fn-cei-build-aux (true-list-fix (fn-sco-records c)) 0 nil)))

(local
 (defthm fn-scka-true-list-fix-true-list-fix
   (equal (true-list-fix (true-list-fix x)) (true-list-fix x))))

; KEYSTONE (the kept base): restoring the stripped capture is the capture,
; so fn-scka-next-checkpoint-is-capture's BASE hypothesis holds of what the
; owner restores exactly when it held of what it stripped.
(defthm fn-scka-restore-base-of-strip-of-capture
  (equal (fn-scka-restore-base (fn-scka-strip-base (fn-sco-capture configs records)))
         (fn-sco-capture configs records))
  :hints (("Goal" :in-theory (e/d (fn-sco-capture fn-sco-make fn-sco-records fn-sco-cpr
                                   fn-sco-identity fn-sco-consumer fn-sco-topic
                                   fn-sco-event-index fn-sco-at)
                                  (fn-sco-cpr-prefix fn-replay-identity-loop
                                   fn-cpe-projection-replay fn-th-prefix-loop
                                   fn-cei-build-aux)))))

; The stripped base keeps what the owner reads of it between publications:
; its records (the covered count).
(defthm fn-scka-strip-base-keeps-the-records
  (equal (fn-sco-records (fn-scka-strip-base c)) (fn-sco-records c))
  :hints (("Goal" :in-theory (enable fn-sco-make fn-sco-records fn-sco-at))))
