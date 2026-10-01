; Teeth for books/bp-receipt-log-crash (PKT-217 restated over the record
; log's crash model, coordinator decision 2026-10-01): the keystone
; fn-brlc-receipt-regenerated-after-log-crash on the live BP receiver trace of
; tests/acl2/bp-receiver-evolving-tests.lisp (a request accepted, a second
; article ingested with receiver steps interleaved), whose Store history is
; the two rows the log below holds as two encoded Store records.
;
; The log is the record log of books/store-log-kernel (the fixture shape of
; tests/acl2/recovery-refinement-tests.lisp, prefix brlct-): its records are
; the host's octets (fn-store-event-encode of each wire record), the open
; decodes and interns them (fn-srs-step from the empty arena), and opens over
; the rows through the host's fn-cpo-open-observed under a fresh store's one
; configuration record at txid 0.
;
; Crash images are fn-bs-crash under explicit choices with
; fn-bs-crash-choicesp asserted (fn-bs-crash-imagep is a defun-sk; its
; witness is fn-bs-crash-imagep-suff).  fn-brlc-rows and fn-brlc-decodedp are
; logical (defun-nx); their executable twins below run the same fn-srs-step
; on a local arena that starts empty (ARENA0 = the empty arena).
;
; Witnesses:
;   POSITIVE (reachable): the quiet log after recovery, both records
;     committed and acknowledged; the crash image of the fenced segment;
;     every hypothesis of the keystone and both conclusions.
;   REMOVAL of the acknowledged-prefix hypothesis: a quiet log that
;     acknowledged only r2; every other hypothesis holds; the receipt is
;     not regenerated.
;   REMOVAL of fn-brlc-decodedp: a third, undecodable record in flight lands
;     whole; every other hypothesis holds; the receipt is not regenerated.
;   MUTATION (labelled): a recovery that drops the receipted record r1 is no
;     tree-sequence member (no admissible crash image of a related state
;     yields it), and the host open refuses it.
(in-package "ACL2")
(include-book "../../books/bp-receipt-log-crash")
(include-book "bp-receiver-evolving-tests")
(include-book "must-fail-checked")

; -----------------------------------------------------------------------------
; The log's records: the host's octets of the live Store's two wire records.

(make-event `(defconst *brlct-octets*
               ',(list (fn-store-event-encode *bpr-record*)
                       (fn-store-event-encode *bpre-record2*))))
(defconst *brlct-r1* (car *brlct-octets*))
(defconst *brlct-r2* (cadr *brlct-octets*))
(defconst *brlct-garbage* '(1 2 7))

; The executable twins of fn-brlc-rows / fn-brlc-decodedp at the empty arena.
(defun brlct-step-a (octets fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (acc fn-arena) (fn-srs-step nil octets fn-arena)
    (mv (list (fn-srs-rows acc) (not (eq acc :bad))) fn-arena)))
(defun brlct-step-x (octets)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena (mv-let (r fn-arena) (brlct-step-a octets fn-arena) r)))
(defun brlct-rows (octets) (declare (xargs :verify-guards nil)) (car (brlct-step-x octets)))
(defun brlct-decodedp (octets) (declare (xargs :verify-guards nil)) (cadr (brlct-step-x octets)))

; The rows the open makes of the two records ARE the live Store's history.
(assert-event (equal (brlct-rows *brlct-octets*) (list *bpr-row* *bpre-row2*)))
(assert-event (equal (fn-bprv-history *bpre-final-store*) (list *bpr-row* *bpre-row2*)))
(assert-event (brlct-decodedp *brlct-octets*))
(assert-event (not (brlct-decodedp (list *brlct-r1* *brlct-r2* *brlct-garbage*))))

; -----------------------------------------------------------------------------
; The log fixture.

(defun brlct-unit () (declare (xargs :guard t)) 4)
(defun brlct-max () (declare (xargs :guard t)) 4096)
(defun brlct-genesis () (declare (xargs :guard t :verify-guards nil)) *fn-lg-genesis*)
(defun brlct-store (content pending)
  (declare (xargs :guard t))
  (fn-bs-make (brlct-unit) (list (cons 0 content)) nil pending 1))
(defun brlct-sels (count sel)
  (declare (xargs :guard t :verify-guards nil))
  (if (zp count) nil (cons sel (brlct-sels (1- count) sel))))
(defun brlct-content (records)
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-lg-log records (brlct-genesis) (brlct-unit)) (fn-bs-zeros 2048)))
(defun brlct-ks0 (records)
  (declare (xargs :guard t :verify-guards nil))
  (fn-lgk-recover (brlct-content records) (brlct-genesis) (brlct-unit) (brlct-max) 3))
(defun brlct-bs0 (records)
  (declare (xargs :guard t :verify-guards nil))
  (car (car (last (fn-lg-run (brlct-store (brlct-content records) nil) (brlct-ks0 records)
                             (fn-lg-recover-program) nil 0)))))
; RECORDS committed, then BATCH prepared and appended: the log-written state.
(defun brlct-prepare-all (ks batch)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp batch) (brlct-prepare-all (fn-lgk-prepare ks (car batch)) (cdr batch)) ks))
(defun brlct-appended (records batch)
  (declare (xargs :guard t :verify-guards nil))
  (car (last (fn-lg-run (brlct-bs0 records) (brlct-prepare-all (brlct-ks0 records) batch)
                        (fn-lg-append-program) nil 0))))

(defun brlct-image (bs choices) (declare (xargs :guard t :verify-guards nil)) (fn-bs-crash bs choices))
(defun brlct-recovered (bs choices)
  (declare (xargs :guard t :verify-guards nil))
  (fn-rr-recovered-records (brlct-image bs choices) 0 (brlct-genesis) (brlct-unit) (brlct-max) 0))
(defun brlct-tearsp (bs ks choices)
  (declare (xargs :guard t :verify-guards nil))
  (fn-lg-platform-tears-p
   (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content (brlct-image bs choices) 0))
   (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs)))

; The open, the barriers, the install: over rows of RECOVERED, frontier F.
(defconst *brlct-configs*
  (list (fn-cfg-record-make 0 0 1 (list (fn-cfg-create-group "fn.letters"
                                                             *fn-cfg-default-policy-id*)
                                        (fn-cfg-set-capacity 20))
                            *fn-cfg-default-stamp*)))
(defun brlct-opened (recovered f)
  (declare (xargs :verify-guards nil))
  (fn-cpo-open-observed *brlct-configs* f (brlct-rows recovered)))
(defun brlct-probe (recovered f)
  (declare (xargs :verify-guards nil))
  (fn-snrt-run (fn-sn-open-state (brlct-opened recovered f)) *bpre-barriers*))
(bpr-lift fn-bpr-live-install 2)
(defun brlct-installed (recovered f)
  (declare (xargs :verify-guards nil))
  (in-arena-fn-bpr-live-install *bpre-payloads* (brlct-probe recovered f) *bpre-journal*))
(defun brlct-regeneratedp (recovered f)
  (declare (xargs :verify-guards nil))
  (let ((installed (brlct-installed recovered f)))
    (and (equal (cadr installed) *bpre-final-state*)
         (equal (fn-bpr-receipt-adu (cadr installed) *bpr-request*)
                (fn-bpr-receipt-adu *bpre-final-state* *bpr-request*)))))

; Every hypothesis of the keystone but the image predicate (asserted below by
; its witness) and the receiver's own (asserted once: the live trace).
(defun brlct-log-hyps (bs ks choices)
  (declare (xargs :verify-guards nil))
  (and (fn-lgk-relp bs ks 0 (brlct-genesis) (brlct-max))
       (fn-bs-crash-choicesp choices (fn-bs-pending bs) (fn-bs-unit bs))
       (brlct-tearsp bs ks choices)))
(defun brlct-acked-prefixp (ks)
  (declare (xargs :verify-guards nil))
  (fn-sf-prefixp (fn-bprv-history *bpre-final-store*)
                 (brlct-rows (take (fn-lgk-acked ks) (fn-lgk-committed ks)))))
(defun brlct-open-hyps (recovered f)
  (declare (xargs :verify-guards nil))
  (and (brlct-decodedp recovered)
       (fn-sonb-configured-before-eventsp *brlct-configs*)
       (fn-sn-open-okp (brlct-opened recovered f))
       (equal (fn-bprv-phase (brlct-probe recovered f)) :ready)))

; The receiver's hypotheses, over the live trace's start.
(assert-event (fn-csi-full-relationp (car *bpre-live0*)))
(assert-event (equal (in-arena-fn-bprr-replay *bpre-payloads* (car *bpre-live0*) (caddr *bpre-live0*))
                     (list t (cadr *bpre-live0*))))

; -----------------------------------------------------------------------------
; POSITIVE (reachable): the recovered log, quiet, both records acknowledged.

(defconst *brlct-q-bs* (brlct-bs0 *brlct-octets*))
(defconst *brlct-q-ks* (brlct-ks0 *brlct-octets*))
(assert-event
 (and (brlct-log-hyps *brlct-q-bs* *brlct-q-ks* nil)
      (equal (fn-lgk-committed *brlct-q-ks*) *brlct-octets*)
      (equal (fn-lgk-acked *brlct-q-ks*) 2)
      (not (consp (fn-lgk-inflight *brlct-q-ks*)))
      (brlct-acked-prefixp *brlct-q-ks*)
      (equal (brlct-recovered *brlct-q-bs* nil) *brlct-octets*)
      (brlct-open-hyps (brlct-recovered *brlct-q-bs* nil) *bpre-frontier*)
      (brlct-regeneratedp (brlct-recovered *brlct-q-bs* nil) *bpre-frontier*)
      (equal (fn-bpr-receipt-adu (cadr (brlct-installed (brlct-recovered *brlct-q-bs* nil)
                                                        *bpre-frontier*))
                                 *bpr-request*)
             *bpr-receipt-adu*)))
; The image predicate, by its witness.
(defthm brlct-quiet-image-is-a-crash-image
  (fn-bs-crash-imagep *brlct-q-bs* (fn-bs-crash *brlct-q-bs* nil))
  :hints (("Goal" :use ((:instance fn-bs-crash-imagep-suff (s *brlct-q-bs*)
                                   (image (fn-bs-crash *brlct-q-bs* nil)) (choices nil)))
           :in-theory (union-theories '((:e fn-bs-crash-choicesp) (:e fn-bs-pending) (:e fn-bs-unit))
                                      (theory 'minimal-theory))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; REMOVAL of the acknowledged-prefix hypothesis: a quiet log that committed
; and acknowledged a different first article (the second ADU, prepared at
; sequence 0 against the empty Store), never r1, on which the receiver
; acted.  Every log hypothesis evaluates (nothing in flight), the decode and
; the open succeed and reach :ready, and the receipt is gone.  (A crash that
; loses an in-flight r1 is the same loss, but its image is a non-exact tear,
; where A-CRYPTO-TRAILER's premise is the constrained fn-assume-crash-tearp
; and cannot be evaluated: recovery-refinement-tests' note.  A log holding
; r2 alone does not open: its history starts at sequence 1.)

(make-event `(defconst *brlct-prepared2-first*
               ',(fn-bpi-ingress-prepare (bpr-reserve (fn-sn-initial *bpr-groups* 20))
                                         *bpre-policy2* *bpre-context2* *bpre-adu2* 0)))
(assert-event (equal (fn-bpi-result-kind *brlct-prepared2-first*) :prepared))
(make-event `(defconst *brlct-r2-first*
               ',(fn-store-event-encode (fn-bpi-result-wire *brlct-prepared2-first*))))
(defconst *brlct-p-bs* (brlct-bs0 (list *brlct-r2-first*)))
(defconst *brlct-p-ks* (brlct-ks0 (list *brlct-r2-first*)))
(defconst *brlct-p-recovered* (brlct-recovered *brlct-p-bs* nil))
(assert-event
 (and (brlct-log-hyps *brlct-p-bs* *brlct-p-ks* nil)
      (equal (fn-lgk-acked *brlct-p-ks*) 1)
      (equal *brlct-p-recovered* (list *brlct-r2-first*))
      (brlct-open-hyps *brlct-p-recovered* 1)))
(assert-event (not (brlct-acked-prefixp *brlct-p-ks*)))
(assert-event (not (brlct-regeneratedp *brlct-p-recovered* 1)))
; Acknowledging r1 alone suffices for THIS receipt (it is grounded in r1):
; the hypothesis asks for the whole live history, which is sufficient.
(assert-event (brlct-regeneratedp (list *brlct-r1*) 1))

; A batch in flight that lands whole (the exact tear, evaluable) recovers
; both rows and regenerates the receipt, though neither record was
; acknowledged: the hypothesis is sufficient, not claimed necessary for
; every image.
(defun brlct-batch-units (bs)
  (declare (xargs :guard t :verify-guards nil))
  (floor (len (nth 3 (car (fn-bs-pending bs)))) (brlct-unit)))
(defconst *brlct-f-pair* (brlct-appended nil *brlct-octets*))
(defconst *brlct-f-bs* (car *brlct-f-pair*))
(defconst *brlct-f-ks* (cdr *brlct-f-pair*))
(defconst *brlct-f-all* (list (brlct-sels (brlct-batch-units *brlct-f-bs*) :new)))
(assert-event
 (and (brlct-log-hyps *brlct-f-bs* *brlct-f-ks* *brlct-f-all*)
      (equal (fn-lgk-inflight *brlct-f-ks*) *brlct-octets*)
      (equal (brlct-recovered *brlct-f-bs* *brlct-f-all*) *brlct-octets*)
      (not (brlct-acked-prefixp *brlct-f-ks*))
      (brlct-regeneratedp (brlct-recovered *brlct-f-bs* *brlct-f-all*) *bpre-frontier*)))

; -----------------------------------------------------------------------------
; REMOVAL of fn-brlc-decodedp: r1 r2 committed and acknowledged, an
; undecodable record in flight lands whole.  The decode refuses, the rows are
; none, the open over them (frontier 0) reaches :ready, and the receipt is
; gone.

(defconst *brlct-g-pair* (brlct-appended *brlct-octets* (list *brlct-garbage*)))
(defconst *brlct-g-bs* (car *brlct-g-pair*))
(defconst *brlct-g-ks* (cdr *brlct-g-pair*))
(defconst *brlct-g-all* (list (brlct-sels (brlct-batch-units *brlct-g-bs*) :new)))
(defconst *brlct-g-recovered* (brlct-recovered *brlct-g-bs* *brlct-g-all*))
(assert-event
 (and (brlct-log-hyps *brlct-g-bs* *brlct-g-ks* *brlct-g-all*)
      (equal (fn-lgk-acked *brlct-g-ks*) 2)
      (brlct-acked-prefixp *brlct-g-ks*)
      (equal *brlct-g-recovered* (list *brlct-r1* *brlct-r2* *brlct-garbage*))
      (fn-sonb-configured-before-eventsp *brlct-configs*)
      (fn-sn-open-okp (brlct-opened *brlct-g-recovered* 0))
      (equal (fn-bprv-phase (brlct-probe *brlct-g-recovered* 0)) :ready)))
(assert-event (not (brlct-decodedp *brlct-g-recovered*)))
(assert-event (not (brlct-regeneratedp *brlct-g-recovered* 0)))

; -----------------------------------------------------------------------------
; MUTATION (a recovery that drops the receipted record r1).  It is no element
; of the tree sequence of the quiet log (every admissible crash image of a
; related state recovers one: fn-rr-log-crash-image-recovers-a-tree-sequence-
; member).

(defconst *brlct-dropped* (list *brlct-r2*))
(assert-event (not (fn-rr-tree-sequence-memberp *brlct-dropped*
                                                (fn-lgk-committed *brlct-q-ks*)
                                                (fn-lgk-inflight *brlct-q-ks*))))
(assert-event (fn-rr-tree-sequence-memberp (brlct-recovered *brlct-q-bs* nil)
                                           (fn-lgk-committed *brlct-q-ks*)
                                           (fn-lgk-inflight *brlct-q-ks*)))
; The store refuses the mutated history by name (its sequence starts at 1),
; so no restart over it serves the receipt.
(assert-event
 (and (brlct-decodedp *brlct-dropped*)
      (not (fn-sn-open-okp (brlct-opened *brlct-dropped* 1)))
      (not (fn-sn-open-okp (brlct-opened *brlct-dropped* 0)))))
