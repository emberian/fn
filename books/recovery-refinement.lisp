; fn: THE RECOVERY-REFINEMENT THEOREM (design 2026-10-01 "pages are the
; state", stage 7, the crash part; specs/recovery-refinement.md).  Prefix fn-rr-.
;
; Argosy's shape (Chajed et al., PLDI 2019), stated as DFSCQ's tree sequence
; (Chen et al., SOSP 2017): the composed store has two layers with their own
; crash models, and their recoveries compose into ONE recovery refinement.
;
;   The LOG (books/store-log-kernel.lisp, the relation R = fn-lgk-relp): one
;   pending write at the frontier, one fence; every crash image scans to
;   COMMITTED followed by a PREFIX of the batch in flight
;   (fn-lgk-crash-of-related-state-is-a-prefix), or the first damaged entry
;   forges, which A-CRYPTO-TRAILER's premise fn-lg-platform-tears-p removes
;   (fn-lg-no-forgery-under-a-crypto-trailer).  Nothing in flight: the
;   segment is fenced and the image holds its durable content
;   (fn-bs-crash-keeps-fenced-content), which scans to exactly COMMITTED.
;   ACKED, the acknowledged prefix length of COMMITTED, is R's fourth
;   conjunct (the owner batch layer's fn-owb-acked members are exactly those
;   records: fn-owb-alignedp, fn-lgu-acknowledged-record-is-committed in
;   books/store-log-durable.lisp, the owner-layer corollary of section 5).
;
;   The IMAGE MEDIUM is any prefix cache the open may use.  Its interface
;   (section 3, the constrained functions fn-rr-medium-*) is PRF-083's
;   keystone and the selection's bound, stated as constraints: the open of
;   the capture of P over Q is the full open of P ++ Q
;   (fn-sn-recover-from-checkpoint-equals-full-recover), and a served
;   selection has S within the count (fn-sco-select-bounds-the-suffix).
;   The store's medium discharges it by functional instantiation
;   (books/recovery-refinement-store.lisp: fn-sco-capture, fn-sco-open,
;   fn-cpo-open-observed, fn-sco-select).  What an image on disk is at a
;   cut is the medium's own crash keystone: today the state checkpoint
;   file, OLD or NEW, never torn (fn-bs-scp-program-crash-is-old-or-new,
;   section 7); the design's target the page store's root
;   (pgs-open-after-crash, PRF-344).
;
; The TREE SEQUENCE is the list of abstract states the recovery may land on:
; the full open of COMMITTED ++ P for each prefix P of INFLIGHT.  Every
; element holds every acknowledged record.  Old-or-new per operation: a
; record in flight is present or absent, and the present ones are a prefix.
; Acknowledged => present.
;
; THE KEYSTONE fn-rr-recovery-refines-a-prefix-with-every-acknowledged-record:
; at every crash point of the log's served programs (a related state; every
; cut state of the append, the fence, the reserve, the order, the extension
; and the recovery is one: fn-lg-append-program-keeps-the-relation,
; fn-lg-fence-program-keeps-the-relation, fn-lg-reserve-program-keeps-the-
; relation, fn-lg-order-program-keeps-the-relation, fn-lg-extend-program-
; keeps-the-relation, fn-lg-recover-program-establishes-the-relation), for
; every admissible crash image, the records the log's recovery holds are one
; element of the tree sequence, the composed open over whatever image the
; medium holds (bound to a prefix of the committed records) is the full open
; of those records, and every acknowledged record is among them.
;
; MODEL-LEVEL (the Codex review of 2d1b10ed7, F1).  No host file calls
; fn-rr-open or the store instance's fn-rrs-open.  What the host runs
; (host/native/io.lisp fnn-recover-log): the log's recovery (fnn-log-recover:
; fn-lg-open-kernel, proved the recovered kernel by
; fn-lg-open-kernel-is-the-recovered-kernel), the record decode
; (fn-srs-decode, the octets of the log's records to the open's events, one
; per record or :bad: fn-srs-decode-of-append), then the checkpoint's
; selection and the open through fn-rii-sco-extend-open
; (books/replay-identity-index.lisp) or fn-sfi-extend-open
; (books/store-finalize-incremental.lisp), or the full replay.  `fn-rr-open'
; is that composition over the medium's interface; the decode is the
; identity on the interface's records here (the log's records ARE the
; medium's, see section 2's note) and the store instance states it over
; fn-srs-decode.  The claim becomes one about the served path only with the
; store instance admitted AND a named equation of its open to those
; host-called opens (PRF-1212's pending subject); until then the registry
; row says MODEL-LEVEL.  No ACL2 function the host calls composes the two
; layers (the open square is host code: the same gap PRF-344 names for the
; page store).
;
; NOT proved here, named as open obligations in planning/proofs.json:
;   PRF-1214  the crash point INSIDE a publication while a batch is in
;             flight: R names the segment's write as the ONLY pending
;             operation (its pending conjunct); a concurrent staged-
;             checkpoint write is outside R.  Section 7 is the sequential
;             half: the quiet store fn-bs-scp-inputp asks for.
;   PRF-1215  the page store as the medium (pgs-open-after-crash is the
;             same old-or-new premise over the model disk; no host path
;             opens the owner's state from a root yet).
;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(in-package "ACL2")
(include-book "store-log-programs")
(include-book "byte-store-state-checkpoint-program")
(local (include-book "byte-store-invariants"))

; -----------------------------------------------------------------------------
; 1. The tree sequence.

; RECOVERED is one element of the tree sequence over COMMITTED and
; INFLIGHT: COMMITTED followed by a prefix of INFLIGHT.
(defun fn-rr-tree-sequence-memberp (recovered committed inflight)
  (declare (xargs :guard t :verify-guards nil))
  (let ((p (nthcdr (len committed) recovered)))
    (and (fn-lg-prefixp p inflight)
         (equal recovered (append committed p)))))

; The records the log's recovery holds, read from a crash image's segment
; (host/native/io.lisp fnn-log-recover: fn-lg-open-kernel, which is
; fn-lgt-recover of the octets, fn-lg-open-kernel-is-the-recovered-kernel).
(defun fn-rr-recovered-records (image ino genesis unit max next-txid)
  (declare (xargs :guard t :verify-guards nil))
  (fn-lgk-committed
   (fn-lgk-recover (fn-bs-durable-content image ino) genesis unit max next-txid)))

; -----------------------------------------------------------------------------
; 2. List algebra (local).

(local
 (defthm fn-rr-append-take-nthcdr
   (implies (and (natp s) (<= s (len x)))
            (equal (append (take s x) (nthcdr s x)) x))
   :hints (("Goal" :induct (take s x)))))

(local
 (defthm fn-rr-take-of-append-within
   (implies (and (natp s) (<= s (len a)))
            (equal (take s (append a b)) (take s a)))
   :hints (("Goal" :induct (take s a)))))

(local
 (defthm fn-rr-member-of-append-left
   (implies (member-equal x a) (member-equal x (append a b)))))

(local
 (defthm fn-rr-member-of-take
   (implies (and (natp n) (<= n (len x)) (member-equal r (take n x)))
            (member-equal r x))
   :hints (("Goal" :induct (take n x)))))

(local
 (defthm fn-rr-nthcdr-len-of-append
   (implies (true-listp a)
            (equal (nthcdr (len a) (append a b)) b))))

(local
 (defthm fn-rr-recovered-kernel-holds-the-scan
   (equal (fn-lgk-committed (fn-lgk-recover c genesis unit max next-txid))
          (car (fn-lg-scan c genesis unit max)))
   :hints (("Goal" :in-theory (e/d (fn-lgk-recover)
                                   (fn-lg-scan fn-lg-scan-last fn-lgk-make fn-lgk-committed))))))

; -----------------------------------------------------------------------------
; 3. The image medium's interface: PRF-083's keystone and the selection's
;    bound as constraints.  The local witness is the medium that caches
;    nothing: the capture is its records, the open the full open of prefix
;    ++ suffix, the full open a tuple, the selection served exactly within
;    the count.  books/recovery-refinement-store.lisp instantiates it with
;    the store's fn-sco-capture, fn-sco-open, fn-cpo-open-observed and
;    fn-sco-select (the functions host/store-node-host.lisp calls).

(encapsulate
  (((fn-rr-medium-capture * *) => *)
   ((fn-rr-medium-open * * * *) => *)
   ((fn-rr-medium-full-open * * *) => *)
   ((fn-rr-medium-select * * * *) => *)
   ((fn-rr-medium-open-okp *) => *)
   ((fn-rr-medium-holds * *) => *))

  (local (defun fn-rr-medium-capture (configs records)
           (declare (ignore configs))
           records))
  (local (defun fn-rr-medium-full-open (configs frontier records)
           (list configs frontier records)))
  (local (defun fn-rr-medium-open (ckpt configs frontier suffix)
           (fn-rr-medium-full-open configs frontier (append ckpt suffix))))
  (local (defun fn-rr-medium-select (status s count k)
           (if (and (equal status :ok) (natp s) (natp count) (<= s count)
                    (natp k) (<= (- count s) k))
               (list :checkpoint s)
             (list :full-replay))))
  ; The witness's open always succeeds, and it holds a record when its
  ; records do.
  (local (defun fn-rr-medium-open-okp (st)
           (declare (ignore st))
           t))
  (local (defun fn-rr-medium-holds (st r)
           (member-equal r (car (cdr (cdr st))))))

  ; PRF-083's shape: the open of the capture of P over Q is the full open
  ; of P ++ Q, with no hypothesis.
  (defthm fn-rr-medium-open-of-capture-is-the-full-open
    (equal (fn-rr-medium-open (fn-rr-medium-capture configs prefix) configs frontier suffix)
           (fn-rr-medium-full-open configs frontier (append prefix suffix))))

  ; fn-sco-select-bounds-the-suffix's shape: a served selection has a
  ; natural S within the natural COUNT.
  (defthm fn-rr-medium-select-bounds-the-sequence
    (implies (equal (car (fn-rr-medium-select status s count k)) :checkpoint)
             (and (natp s) (natp count) (<= s count)))
    :rule-classes nil)

  ; An open that SUCCEEDED holds every record it was opened from (the Codex
  ; review of 2d1b10ed7, F2: without it the two constraints above admit an
  ; open that answers NIL, and "acknowledged => present" would be a fact
  ; about the recovered list alone, not about the opened store).  The
  ; store's full open refuses a bad history by name (fn-sn-open-error), so
  ; the constraint is over a successful open: refused stays refused, and
  ; conjunct (2) of the keystone carries the refusal through the composed
  ; open unchanged.  What holding means is the medium's: the store instance
  ; names it over the opened Store's replayed events.
  (defthm fn-rr-medium-full-open-holds-its-records
    (implies (and (member-equal r records)
                  (fn-rr-medium-open-okp (fn-rr-medium-full-open configs frontier records)))
             (fn-rr-medium-holds (fn-rr-medium-full-open configs frontier records) r))))

; The composed open after the log's recovery: the image's selection under
; K, then the open from the image over the suffix it leaves, or the full
; open.  STATUS and S are what the host decoded from the image it read.
(defun fn-rr-open (status s ckpt configs frontier records k)
  (declare (xargs :guard t :verify-guards nil))
  (if (equal (car (fn-rr-medium-select status s (len records) k)) :checkpoint)
      (fn-rr-medium-open ckpt configs frontier (nthcdr s records))
    (fn-rr-medium-full-open configs frontier records)))

; -----------------------------------------------------------------------------
; 4. The medium's half: the composed open is the full open of the recovered
;    records whenever the image is bound to a prefix of them.  No other
;    hypothesis: an image the selection refuses is the full open by
;    definition, and a served one is the open of its capture.

(defthm fn-rr-open-is-the-full-open-of-the-recovered-records
  (implies (equal ckpt (fn-rr-medium-capture configs (take s records)))
           (equal (fn-rr-open status s ckpt configs frontier records k)
                  (fn-rr-medium-full-open configs frontier records)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-rr-medium-select-bounds-the-sequence
                            (count (len records)))
                 (:instance fn-rr-medium-open-of-capture-is-the-full-open
                            (prefix (take s records)) (suffix (nthcdr s records)))
                 (:instance fn-rr-append-take-nthcdr (x records)))
           :in-theory (union-theories '(fn-rr-open car-cons cdr-cons)
                                      (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; 5. The log's half: the recovered records are one element of the tree
;    sequence at every crash image of a related state.

; A batch in flight: fn-lgk-crash-of-related-state-is-a-prefix, with the
; forgery disjunct removed by A-CRYPTO-TRAILER's premise.
(defthm fn-rr-log-crash-image-in-flight-recovers-a-tree-sequence-member
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (consp (fn-lgk-inflight ks))
                (fn-bs-crash-imagep bs image)
                (fn-lg-platform-tears-p
                 (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content image ino))
                 (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs)))
           (fn-rr-tree-sequence-memberp
            (fn-rr-recovered-records image ino genesis (fn-bs-unit bs) max next-txid)
            (fn-lgk-committed ks) (fn-lgk-inflight ks)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-lgk-crash-of-related-state-is-a-prefix)
                 (:instance fn-lg-no-forgery-under-a-crypto-trailer
                            (x (nthcdr (fn-lgk-frontier ks)
                                       (fn-bs-durable-content image ino)))
                            (batch (fn-lgk-inflight ks)) (prev (fn-lgk-last ks))
                            (unit (fn-bs-unit bs))))
           :in-theory (union-theories '(fn-rr-tree-sequence-memberp
                                        fn-rr-recovered-records
                                        fn-lg-crash-verdictp
                                        fn-rr-recovered-kernel-holds-the-scan)
                                      (theory 'minimal-theory)))))

; Nothing in flight: the segment is fenced, so the image holds the durable
; content, whose scan is exactly COMMITTED (the complete prefix, then the
; preallocated zeros).
(local
 (defthm fn-rr-bs-take-then-nthcdr
   (implies (and (natp n) (<= n (len x)) (true-listp x))
            (equal (append (fn-bs-take n x) (nthcdr n x)) x))
   :hints (("Goal" :induct (fn-bs-take n x)))))

(local
 (defthm fn-rr-quiet-related-content-scans-to-committed
   (implies (and (fn-lgk-relp bs ks ino genesis max)
                 (not (consp (fn-lgk-inflight ks))))
            (equal (car (fn-lg-scan (fn-bs-durable-content bs ino) genesis (fn-bs-unit bs) max))
                   (fn-lgk-committed ks)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-lg-scan-of-complete-append
                             (d (fn-bs-take (fn-lgk-frontier ks) (fn-bs-durable-content bs ino)))
                             (x (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content bs ino)))
                             (prev genesis) (unit (fn-bs-unit bs)))
                  (:instance fn-lg-scan-of-zeros
                             (z (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content bs ino)))
                             (prev (fn-lg-scan-last
                                    (fn-bs-take (fn-lgk-frontier ks) (fn-bs-durable-content bs ino))
                                    genesis (fn-bs-unit bs) max))
                             (unit (fn-bs-unit bs)))
                  (:instance fn-rr-bs-take-then-nthcdr
                             (n (fn-lgk-frontier ks)) (x (fn-bs-durable-content bs ino))))
            :in-theory (e/d (fn-lgk-relp fn-lgk-content-okp)
                            (fn-lg-scan fn-lg-scan-last fn-lg-log fn-lg-recordsp fn-bs-take
                             fn-lg-zerosp fn-frame-digestp fn-bs-durable-content
                             fn-lgk-committed fn-lgk-last fn-lgk-frontier fn-lgk-inflight
                             fn-lgk-batch fn-lgk-acked fn-lg-scan-of-complete-append
                             fn-lg-scan-of-zeros fn-rr-bs-take-then-nthcdr))))))

(defthm fn-rr-log-crash-image-quiet-recovers-committed
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (not (consp (fn-lgk-inflight ks)))
                (fn-bs-crash-imagep bs image))
           (equal (fn-rr-recovered-records image ino genesis (fn-bs-unit bs) max next-txid)
                  (fn-lgk-committed ks)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-rr-quiet-related-content-scans-to-committed)
                 (:instance fn-bs-crash-keeps-fenced-content (s bs)))
           :in-theory (union-theories '(fn-rr-recovered-records
                                        fn-rr-recovered-kernel-holds-the-scan
                                        fn-bs-fencedp fn-lgk-relp fn-bs-ops-for-ino)
                                      (theory 'minimal-theory)))))

(local
 (defthm fn-rr-relp-committed-true-listp
   (implies (fn-lgk-relp bs ks ino genesis max)
            (true-listp (fn-lgk-committed ks)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-lgk-relp fn-lgk-content-okp)
                                   (fn-lg-scan fn-lg-scan-last fn-lg-log fn-lg-recordsp fn-bs-take
                                    fn-lg-zerosp fn-frame-digestp fn-bs-durable-content
                                    fn-lgk-committed fn-lgk-last fn-lgk-frontier fn-lgk-inflight
                                    fn-lgk-batch fn-lgk-acked))))))
(local
 (defthm fn-rr-nthcdr-len-self
   (implies (true-listp x)
            (equal (nthcdr (len x) x) nil))
   :rule-classes nil))
(local
 (defthm fn-rr-append-nil
   (implies (true-listp x) (equal (append x nil) x))
   :rule-classes nil))
(defthm fn-rr-log-crash-image-recovers-a-tree-sequence-member
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (fn-bs-crash-imagep bs image)
                (fn-lg-platform-tears-p
                 (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content image ino))
                 (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs)))
           (fn-rr-tree-sequence-memberp
            (fn-rr-recovered-records image ino genesis (fn-bs-unit bs) max next-txid)
            (fn-lgk-committed ks) (fn-lgk-inflight ks)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :cases ((consp (fn-lgk-inflight ks)))
           :use ((:instance fn-rr-log-crash-image-in-flight-recovers-a-tree-sequence-member)
                 (:instance fn-rr-log-crash-image-quiet-recovers-committed)
                 (:instance fn-rr-relp-committed-true-listp)
                 (:instance fn-rr-nthcdr-len-self (x (fn-lgk-committed ks)))
                 (:instance fn-rr-append-nil (x (fn-lgk-committed ks))))
           :in-theory (union-theories '(fn-rr-tree-sequence-memberp fn-lg-prefixp)
                                      (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; 6. Acknowledged => present, in every element of the tree sequence.  The
;    kernel's word: the first ACKED of COMMITTED (R: ACKED <= len COMMITTED).

(defthm fn-rr-acknowledged-record-is-in-every-tree-sequence-member
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (member-equal r (take (fn-lgk-acked ks) (fn-lgk-committed ks)))
                (fn-rr-tree-sequence-memberp recovered (fn-lgk-committed ks) inflight))
           (member-equal r recovered))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-rr-member-of-take
                            (n (fn-lgk-acked ks)) (x (fn-lgk-committed ks)))
                 (:instance fn-rr-member-of-append-left
                            (x r)
                            (a (fn-lgk-committed ks))
                            (b (nthcdr (len (fn-lgk-committed ks)) recovered))))
           :in-theory (e/d (fn-rr-tree-sequence-memberp fn-lgk-relp fn-lgk-content-okp)
                           (fn-lg-scan fn-lg-scan-last fn-lg-log fn-lg-recordsp fn-bs-take
                            fn-lg-zerosp fn-frame-digestp fn-bs-durable-content
                            fn-lgk-committed fn-lgk-last fn-lgk-frontier fn-lgk-inflight
                            fn-lgk-batch fn-lgk-acked take member-equal)))))

; -----------------------------------------------------------------------------
; 7. THE KEYSTONE.

; Every crash point of the log's served programs is a related state (BS,
; KS).  For every admissible crash image of it, under A-CRYPTO-TRAILER's
; premise on what the tear left past the frontier, and for any image the
; medium holds that is bound to the capture of a prefix of the committed
; records (S records, S at most the committed count: the publication
; captures only fenced records):
;   (1) the records the log's recovery holds are COMMITTED followed by a
;       prefix of the batch in flight (one element of the tree sequence);
;   (2) the composed open over the image is the full open of those records;
;   (3) every acknowledged record (the first ACKED of COMMITTED) is among
;       them, and the opened state holds it.
(local
 (defthm fn-rr-holds-across-equal
   (implies (and (equal a (fn-rr-medium-full-open configs frontier records))
                 (member-equal r records)
                 (fn-rr-medium-open-okp a))
            (fn-rr-medium-holds a r))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-rr-medium-full-open-holds-its-records))))))
(defthm fn-rr-recovery-refines-a-prefix-with-every-acknowledged-record
  (let ((recovered (fn-rr-recovered-records image ino genesis (fn-bs-unit bs) max next-txid)))
    (implies (and (fn-lgk-relp bs ks ino genesis max)
                  (fn-bs-crash-imagep bs image)
                  (fn-lg-platform-tears-p
                   (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content image ino))
                   (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs))
                  (natp s)
                  (<= s (len (fn-lgk-committed ks)))
                  (equal ckpt (fn-rr-medium-capture configs (take s (fn-lgk-committed ks)))))
             (and (fn-rr-tree-sequence-memberp recovered (fn-lgk-committed ks)
                                               (fn-lgk-inflight ks))
                  (equal (fn-rr-open status s ckpt configs frontier recovered k)
                         (fn-rr-medium-full-open configs frontier recovered))
                  (implies (member-equal r (take (fn-lgk-acked ks) (fn-lgk-committed ks)))
                           (and (member-equal r recovered)
                                (implies (fn-rr-medium-open-okp
                                          (fn-rr-open status s ckpt configs frontier recovered k))
                                         (fn-rr-medium-holds
                                          (fn-rr-open status s ckpt configs frontier recovered k)
                                          r)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-rr-log-crash-image-recovers-a-tree-sequence-member)
                 (:instance fn-rr-acknowledged-record-is-in-every-tree-sequence-member
                            (recovered (fn-rr-recovered-records image ino genesis (fn-bs-unit bs)
                                                                max next-txid))
                            (inflight (fn-lgk-inflight ks)))
                 (:instance fn-rr-open-is-the-full-open-of-the-recovered-records
                            (records (fn-rr-recovered-records image ino genesis (fn-bs-unit bs)
                                                              max next-txid)))
                 (:instance fn-rr-holds-across-equal
                            (a (fn-rr-open status s ckpt configs frontier
                                           (fn-rr-recovered-records image ino genesis (fn-bs-unit bs)
                                                                    max next-txid)
                                           k))
                            (records (fn-rr-recovered-records image ino genesis (fn-bs-unit bs)
                                                              max next-txid)))
                 (:instance fn-rr-take-of-append-within
                            (a (fn-lgk-committed ks))
                            (b (nthcdr (len (fn-lgk-committed ks))
                                       (fn-rr-recovered-records image ino genesis (fn-bs-unit bs)
                                                                max next-txid)))))
           :in-theory (union-theories '(fn-rr-tree-sequence-memberp)
                                      (theory 'minimal-theory)))))

;; -----------------------------------------------------------------------------
; 8. The checkpoint program's crash points (the five state-checkpoint cuts
;    of tests/campaign/native_cuts.py STATE_CHECKPOINT_CUTS): from the quiet
;    store the publication asks for (fn-bs-scp-inputp: nothing pending, so
;    nothing in flight), the program never writes the segment, every crash
;    image of every cut recovers exactly COMMITTED, and the image it holds
;    is the OLD one or the NEW one (fn-bs-scp-program-crash-is-old-or-new).
;    The open over either is section 4's: the full open of COMMITTED.

; Every state of a run keeps the segment: fenced, its durable content and
; the unit unchanged.
(defun fn-rr-all-keep-segment (pairs bs ino)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp pairs)
      (and (fn-bs-fencedp (car (car pairs)) ino)
           (equal (fn-bs-durable-content (car (car pairs)) ino) (fn-bs-durable-content bs ino))
           (equal (fn-bs-unit (car (car pairs))) (fn-bs-unit bs))
           (fn-rr-all-keep-segment (cdr pairs) bs ino))
    t))

(local
 (defthm fn-rr-assoc-of-put-assoc-same
   (implies k
            (equal (assoc-equal k (fn-bs-put-assoc k v a)) (cons k v)))
   :hints (("Goal" :in-theory (enable fn-bs-put-assoc)))))
(local
 (defthm fn-rr-assoc-of-put-assoc-other
   (implies (not (equal k j))
            (equal (assoc-equal k (fn-bs-put-assoc j v a)) (assoc-equal k a)))
   :hints (("Goal" :in-theory (enable fn-bs-put-assoc)))))
(local
 (defthm fn-rr-scp-run-keeps-the-segment
   (implies (and (fn-bs-scp-inputp bs stage old-ino)
                 (natp ino) (< ino (fn-bs-next-ino bs)))
            (fn-rr-all-keep-segment (fn-bs-run bs ks (fn-bs-scp-program stage octets)
                                               nil groups capacity)
                                    bs ino))
   :hints (("Goal" :do-not-induct t
            :expand ((:free (b k s o) (fn-bs-run b k s o groups capacity)))
            :in-theory (e/d (fn-bs-scp-program fn-bs-scp-inputp fn-rr-all-keep-segment
                             fn-bs-step fn-bs-create fn-bs-write fn-bs-fsync-file
                             fn-bs-fsync-dir fn-bs-rename fn-bs-fence-file
                             fn-bs-fence-dir fn-bs-lookup fn-bs-view
                             fn-bs-durable-entry fn-bs-durable-content
                             fn-bs-fencedp fn-bs-ops-for-ino
                             fn-bs-apply-op fn-bs-apply-ops)
                            (fn-bs-splice fn-bs-put-assoc))))))

(local
 (defthm fn-rr-all-keep-segment-member
   (implies (and (fn-rr-all-keep-segment pairs bs ino) (member-equal p pairs))
            (and (fn-bs-fencedp (car p) ino)
                 (equal (fn-bs-durable-content (car p) ino) (fn-bs-durable-content bs ino))
                 (equal (fn-bs-unit (car p)) (fn-bs-unit bs))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-rr-all-keep-segment)
                                   (fn-bs-fencedp fn-bs-durable-content))))))
(defthm fn-rr-checkpoint-crash-point-recovers-committed-under-old-or-new
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (not (consp (fn-lgk-inflight ks)))
                (fn-bs-scp-inputp bs stage old-ino)
                (natp ino) (< ino (fn-bs-next-ino bs))
                (fn-cbor-octet-listp octets) (consp octets)
                (member-equal p (fn-bs-run bs ks2 (fn-bs-scp-program stage octets)
                                           nil groups capacity)))
           (let ((image (fn-bs-crash (car p) choices)))
             (and (equal (fn-rr-recovered-records image ino genesis (fn-bs-unit bs) max next-txid)
                         (fn-lgk-committed ks))
                  (fn-bs-scp-old-or-newp image bs old-ino octets))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-scp-program-crash-is-old-or-new (ks ks2))
                 (:instance fn-rr-scp-run-keeps-the-segment (ks ks2))
                 (:instance fn-rr-all-keep-segment-member
                            (pairs (fn-bs-run bs ks2 (fn-bs-scp-program stage octets)
                                              nil groups capacity)))
                 (:instance fn-bs-crash-with-choices-keeps-fenced-content (s (car p)))
                 (:instance fn-rr-quiet-related-content-scans-to-committed))
           :in-theory (union-theories '(fn-rr-recovered-records
                                        fn-rr-recovered-kernel-holds-the-scan)
                                      (theory 'minimal-theory)))))

(in-theory (disable fn-rr-tree-sequence-memberp fn-rr-recovered-records fn-rr-open
                    fn-rr-all-keep-segment))
