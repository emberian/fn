; Teeth for books/bp-receipt-log-crash (PKT-217 restated over the record
; log's crash model, coordinator decision 2026-10-01): the keystone
; fn-brlc-receipt-regenerated-after-log-crash on the live BP receiver trace of
; tests/acl2/bp-receiver-evolving-tests.lisp (a request accepted, a second
; article ingested with receiver steps interleaved), whose Store history is
; the two rows the log below holds as two encoded Store records.
;
; The log is the record log of books/store-log-kernel (the fixture shape of
; tests/acl2/recovery-refinement-tests.lisp, prefix brlct-): its records are
; the host's octets (fn-store-event-encode of each wire record), WRITTEN by
; the log's own programs from a fresh store's log (prepare, P-LOG-APPEND,
; P-LOG-FENCE, fn-lgk-finish-one).  The open runs the host's chain: the
; seeded fn-ssr-intern-step over fn-srs-decode (fn-brlc-rows), then
; fn-rii-sco-extend-open on the empty capture under a fresh store's one
; configuration record at txid 0 (fn-brlc-host-classified).
;
; Each witness asserts brlct-hyps, the keystone's hypotheses in order but
; the image predicate (fn-bs-crash-imagep, a defun-sk: asserted through
; fn-bs-crash-imagep-suff by fn-bs-crash-choicesp, refuted by a theorem),
; and brlct-concl, its conclusion.
;
; Witnesses:
;   POSITIVE (reachable, writer-built): r1 r2 written, fenced, acknowledged;
;     the crash image of the fenced segment; every hypothesis, both
;     conclusions.
;   REMOVALS: the replay agreement (CORRUPTED receiver state), fn-lgk-relp
;     (CORRUPTED kernel), fn-bs-crash-imagep, the phase :ready, the
;     acknowledged-prefix hypothesis.
;   fn-brlc-decodedp is no longer a hypothesis (fn-brlc-open-ok-implies-
;     decoded); its old scenario is kept as a check.
;   NOT WITNESSED (reasons below): fn-csi-full-relationp,
;     fn-lg-platform-tears-p, fn-sn-open-okp,
;     fn-sonb-configured-before-eventsp.
;   MUTATION (labelled): a recovery that drops the receipted record r1 is no
;     tree-sequence member, and the host's replay refuses it.
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

; The executable twins of fn-brlc-rows / fn-brlc-decodedp at the empty arena:
; the host's seeded statement-context replay (fn-ssr-intern-step :resident
; from fn-brlc-seed) over the decode, on a local arena that starts empty.
(defun brlct-step-a (octets fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (acc fn-arena)
    (fn-ssr-intern-step (fn-brlc-seed) (fn-srs-decode octets) nil nil :resident nil fn-arena)
    (mv (list (fn-ssr-rows acc) (not (eq acc :bad))) fn-arena)))
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

; RECORDS written through the log's own programs from a fresh store's log
; (init's genesis, recovered empty): BATCH prepared (fn-lgk-prepare), written
; (P-LOG-APPEND, cut log-written), fenced (P-LOG-FENCE, cut log-fenced), then
; ACKS of its records acknowledged in order (fn-lgk-finish-one, the owner's
; acknowledgement).  (bs . ks).
(defun brlct-fence (pair)
  (declare (xargs :guard t :verify-guards nil))
  (car (last (fn-lg-run (car pair) (cdr pair) (fn-lg-fence-program) nil 0))))
(defun brlct-finish (ks n)
  (declare (xargs :guard t :verify-guards nil :measure (nfix n)))
  (if (zp n) ks (brlct-finish (fn-lgk-finish-one ks) (1- n))))
(defun brlct-written (batch acks)
  (declare (xargs :guard t :verify-guards nil))
  (let ((f (brlct-fence (brlct-appended nil batch))))
    (cons (car f) (brlct-finish (cdr f) acks))))
; ... and then BATCH2 prepared and written, not yet fenced: in flight.
(defun brlct-written-then-appended (batch acks batch2)
  (declare (xargs :guard t :verify-guards nil))
  (let ((w (brlct-written batch acks)))
    (car (last (fn-lg-run (car w) (brlct-prepare-all (cdr w) batch2)
                          (fn-lg-append-program) nil 0)))))

; The host's open over the rows of RECOVERED at frontier F under CONFIGS
; (fn-store-sn-recover-rows: fn-rii-sco-extend-open on the empty capture; the
; installed value is the second element of the classified answer), the
; barriers, the install.
(defconst *brlct-configs*
  (list (fn-cfg-record-make 0 0 1 (list (fn-cfg-create-group "fn.letters"
                                                             *fn-cfg-default-policy-id*)
                                        (fn-cfg-set-capacity 20))
                            *fn-cfg-default-stamp*)))
(defun brlct-opened-c (configs recovered f)
  (declare (xargs :verify-guards nil))
  (cadr (cadr (fn-rii-sco-extend-open (fn-sco-capture configs nil) configs
                                      (brlct-rows recovered) f))))
(defun brlct-probe-c (configs recovered f barriers)
  (declare (xargs :verify-guards nil))
  (fn-snrt-run (fn-sn-open-state (brlct-opened-c configs recovered f)) barriers))
(bpr-lift fn-bpr-live-install 2)
(bpr-lift fn-bpr-live-run 2)
(bpr-lift fn-bprr-replay 2)
(defun brlct-final (live events)
  (declare (xargs :verify-guards nil))
  (in-arena-fn-bpr-live-run *bpre-payloads* live events))

; The recovered records of IMAGE, and the keystone's conclusion.
(defun brlct-recov (image)
  (declare (xargs :verify-guards nil))
  (fn-rr-recovered-records image 0 (brlct-genesis) (brlct-unit) (brlct-max) 0))
(defun brlct-concl (live events configs recovered f barriers)
  (declare (xargs :verify-guards nil))
  (let* ((final (brlct-final live events))
         (installed (in-arena-fn-bpr-live-install
                     *bpre-payloads* (brlct-probe-c configs recovered f barriers) (caddr final))))
    (and (equal (cadr installed) (cadr final))
         (equal (fn-bpr-receipt-adu (cadr installed) *bpr-request*)
                (fn-bpr-receipt-adu (cadr final) *bpr-request*)))))

; The keystone's hypotheses but the image predicate (fn-bs-crash-imagep, a
; defun-sk: asserted by its witness fn-bs-crash-imagep-suff where it holds,
; refuted by a theorem where it does not), each as T or NIL, in the
; statement's order.
(defun brlct-bool (x) (declare (xargs :guard t)) (if x t nil))
(defun brlct-hyps (live events bs ks image configs f barriers)
  (declare (xargs :verify-guards nil))
  (let ((recovered (brlct-recov image)))
    (list :csi (brlct-bool (fn-csi-full-relationp (car live)))
          :replay (equal (in-arena-fn-bprr-replay *bpre-payloads* (car live) (caddr live))
                         (list t (cadr live)))
          :relp (brlct-bool (fn-lgk-relp bs ks 0 (brlct-genesis) (brlct-max)))
          :tears (brlct-bool (fn-lg-platform-tears-p
                              (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content image 0))
                              (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs)))
          :acked (brlct-bool (fn-sf-prefixp (fn-bprv-history (car (brlct-final live events)))
                                            (brlct-rows (take (fn-lgk-acked ks)
                                                              (fn-lgk-committed ks)))))
          :configured (brlct-bool (fn-sonb-configured-before-eventsp configs))
          :open-ok (brlct-bool (fn-sn-open-okp (brlct-opened-c configs recovered f)))
          :ready (equal (fn-bprv-phase (brlct-probe-c configs recovered f barriers)) :ready))))
(defconst *brlct-all*
  '(:csi t :replay t :relp t :tears t :acked t :configured t :open-ok t :ready t))
(defun brlct-plist-off (key pl)
  (declare (xargs :guard t :verify-guards nil :measure (acl2-count pl)))
  (cond ((atom pl) nil)
        ((atom (cdr pl)) pl)
        ((eq (car pl) key) (list* key nil (cddr pl)))
        (t (list* (car pl) (cadr pl) (brlct-plist-off key (cddr pl))))))
(defun brlct-all-but (key)
  (declare (xargs :guard t :verify-guards nil))
  (brlct-plist-off key *brlct-all*))
(defun brlct-choicesp (bs choices)
  (declare (xargs :verify-guards nil))
  (fn-bs-crash-choicesp choices (fn-bs-pending bs) (fn-bs-unit bs)))

; The receiver's hypotheses, over the live trace's start.
(assert-event (fn-csi-full-relationp (car *bpre-live0*)))
(assert-event (equal (in-arena-fn-bprr-replay *bpre-payloads* (car *bpre-live0*) (caddr *bpre-live0*))
                     (list t (cadr *bpre-live0*))))

; -----------------------------------------------------------------------------
; POSITIVE (reachable, WRITER-BUILT): r1 r2 prepared, written, fenced and
; both acknowledged on a fresh store's log; the crash image of the fenced
; segment (nothing pending); every hypothesis of the keystone and both
; conclusions.

(defconst *brlct-w* (brlct-written *brlct-octets* 2))
(defconst *brlct-w-bs* (car *brlct-w*))
(defconst *brlct-w-ks* (cdr *brlct-w*))
(defconst *brlct-w-image* (fn-bs-crash *brlct-w-bs* nil))
(assert-event
 (and (equal (fn-lgk-committed *brlct-w-ks*) *brlct-octets*)
      (equal (fn-lgk-acked *brlct-w-ks*) 2)
      (not (consp (fn-lgk-inflight *brlct-w-ks*)))
      (not (consp (fn-bs-pending *brlct-w-bs*)))
      (brlct-choicesp *brlct-w-bs* nil)
      (equal (brlct-recov *brlct-w-image*) *brlct-octets*)
      (equal (brlct-hyps *bpre-live0* *bpre-events* *brlct-w-bs* *brlct-w-ks* *brlct-w-image*
                         *brlct-configs* *bpre-frontier* *bpre-barriers*)
             *brlct-all*)
      (brlct-concl *bpre-live0* *bpre-events* *brlct-configs* *brlct-octets* *bpre-frontier*
                   *bpre-barriers*)
      (equal (fn-bpr-receipt-adu (cadr (in-arena-fn-bpr-live-install
                                        *bpre-payloads*
                                        (brlct-probe-c *brlct-configs* *brlct-octets*
                                                       *bpre-frontier* *bpre-barriers*)
                                        *bpre-journal*))
                                 *bpr-request*)
             *bpr-receipt-adu*)))
; The chain's steps on the positive, each named.
; fn-brlc-host-open-is-the-observed-open: the host's open IS the observed
; open here (a Store).
(assert-event
 (and (fn-sn-open-okp (brlct-opened-c *brlct-configs* *brlct-octets* *bpre-frontier*))
      (equal (brlct-opened-c *brlct-configs* *brlct-octets* *bpre-frontier*)
             (fn-cpo-open-observed *brlct-configs* *bpre-frontier* (brlct-rows *brlct-octets*)))))
; fn-brlc-acknowledged-rows-are-a-prefix-of-the-recovered-rows (and its
; step on prefixes): r1's rows are a prefix of r1 r2's, and the
; acknowledged records' rows of the recovered rows.
(assert-event
 (and (brlct-decodedp (list *brlct-r1*))
      (fn-sf-prefixp (brlct-rows (list *brlct-r1*)) (brlct-rows *brlct-octets*))
      (fn-sf-prefixp (brlct-rows (take (fn-lgk-acked *brlct-w-ks*) (fn-lgk-committed *brlct-w-ks*)))
                     (brlct-rows (brlct-recov *brlct-w-image*)))))
; fn-brlc-rows-of-prefix-is-a-prefix, each hypothesis violated: an improper
; A (the whole decodes, A's rows are :bad), and a whole that does not
; decode.  (:logic evaluation: fn-sf-prefixp's guard asks for lists.)
(assert-event
 (with-guard-checking
  :none
  (and (not (true-listp (cons *brlct-r1* 5)))
      (brlct-decodedp (append (cons *brlct-r1* 5) (list *brlct-r2*)))
      (not (fn-sf-prefixp (brlct-rows (cons *brlct-r1* 5))
                          (brlct-rows (append (cons *brlct-r1* 5) (list *brlct-r2*))))))))
(assert-event
 (with-guard-checking
  :none
  (and (true-listp (list *brlct-r1*))
      (not (brlct-decodedp (list *brlct-r1* *brlct-garbage*)))
      (not (fn-sf-prefixp (brlct-rows (list *brlct-r1*))
                          (brlct-rows (list *brlct-r1* *brlct-garbage*)))))))
; fn-brlc-chunks-are-one-step: the host's two chunks (r1) (r2) give the rows
; of the one step over r1 r2.
(defun brlct-chunks-a (acc chunks fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (if (atom chunks)
      (mv acc fn-arena)
    (mv-let (acc fn-arena)
      (fn-ssr-intern-step acc (fn-srs-decode (car chunks)) nil nil :resident nil fn-arena)
      (brlct-chunks-a acc (cdr chunks) fn-arena))))
(defun brlct-chunk-rows (chunks)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (acc fn-arena) (brlct-chunks-a (fn-brlc-seed) chunks fn-arena) (fn-ssr-rows acc))))
(assert-event (equal (brlct-chunk-rows (list (list *brlct-r1*) (list *brlct-r2*)))
                     (brlct-rows *brlct-octets*)))
; The image predicate, by its witness.
(defthm brlct-written-image-is-a-crash-image
  (fn-bs-crash-imagep *brlct-w-bs* *brlct-w-image*)
  :hints (("Goal" :use ((:instance fn-bs-crash-imagep-suff (s *brlct-w-bs*)
                                   (image *brlct-w-image*) (choices nil)))
           :in-theory (union-theories '((:e fn-bs-crash-choicesp) (:e fn-bs-pending) (:e fn-bs-unit) (:e fn-bs-crash))
                                      (theory 'minimal-theory))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; Hypothesis removals.  Each: every other hypothesis holds (the vector), the
; omitted one fails, and the conclusion fails.

; The fresh store's log (nothing written): the image of its bytes recovers
; nothing.
(defconst *brlct-e* (brlct-written nil 0))
(defconst *brlct-e-image* (fn-bs-crash (car *brlct-e*) nil))
(assert-event (and (brlct-choicesp (car *brlct-e*) nil)
                   (equal (brlct-recov *brlct-e-image*) nil)))

; REMOVAL of the replay agreement (CORRUPTED receiver state): the receiver
; state is ahead of its journal (it holds the request context, the journal
; only the configuration), run over the trace after the request; the
; WRITER-BUILT log.  The install replays the journal and stays behind.
(defconst *brlct-ahead-events* (cdr *bpre-events*))
(assert-event
 (and (equal (brlct-hyps *bpre-ahead-live0* *brlct-ahead-events* *brlct-w-bs* *brlct-w-ks*
                         *brlct-w-image* *brlct-configs* *bpre-frontier* *bpre-barriers*)
             (brlct-all-but :replay))
      (not (brlct-concl *bpre-ahead-live0* *brlct-ahead-events* *brlct-configs* *brlct-octets*
                        *bpre-frontier* *bpre-barriers*))))

; REMOVAL of fn-lgk-relp (CORRUPTED kernel): the writer-built kernel (r1 r2
; committed and acknowledged) over the fresh store's bytes (no record
; written).  The image of those bytes recovers nothing; the open over no rows
; reaches :ready; the receipt is gone.
(assert-event
 (and (brlct-choicesp (car *brlct-e*) nil)
      (equal (brlct-hyps *bpre-live0* *bpre-events* (car *brlct-e*) *brlct-w-ks*
                         *brlct-e-image* *brlct-configs* 0 *bpre-barriers*)
             (brlct-all-but :relp))
      (not (brlct-concl *bpre-live0* *bpre-events* *brlct-configs* nil 0 *bpre-barriers*))))

; REMOVAL of fn-bs-crash-imagep: the writer-built related state with the
; fresh store's bytes as the "image".  Nothing is pending, so every crash
; image of the written state is its one durable image, and this is not it.
(assert-event
 (and (equal (brlct-hyps *bpre-live0* *bpre-events* *brlct-w-bs* *brlct-w-ks*
                         *brlct-e-image* *brlct-configs* 0 *bpre-barriers*)
             *brlct-all*)
      (not (equal *brlct-e-image* *brlct-w-image*))
      (not (brlct-concl *bpre-live0* *bpre-events* *brlct-configs* nil 0 *bpre-barriers*))))
(local
 (defthm brlct-crash-of-nothing-pending
   (implies (and (atom (fn-bs-pending s)) (fn-bs-crash-choicesp c (fn-bs-pending s) u))
            (equal (fn-bs-crash s c) (fn-bs-crash s nil)))
   :hints (("Goal" :in-theory (enable fn-bs-crash fn-bs-crash-select fn-bs-crash-choicesp)))))
(defthm brlct-fresh-bytes-are-no-crash-image-of-the-written-state
  (not (fn-bs-crash-imagep *brlct-w-bs* *brlct-e-image*))
  :hints (("Goal" :use ((:instance brlct-crash-of-nothing-pending
                                   (s *brlct-w-bs*) (u (fn-bs-unit *brlct-w-bs*))
                                   (c (fn-bs-crash-imagep-witness *brlct-w-bs* *brlct-e-image*))))
           :in-theory (e/d (fn-bs-crash-imagep) (fn-bs-crash fn-bs-crash-choicesp))))
  :rule-classes nil)

; REMOVAL of the phase :ready: no barriers run; the opened Store is
; :recovering, refuses the request context, and the replay stops.
(assert-event
 (and (equal (brlct-hyps *bpre-live0* *bpre-events* *brlct-w-bs* *brlct-w-ks* *brlct-w-image*
                         *brlct-configs* *bpre-frontier* nil)
             (brlct-all-but :ready))
      (not (brlct-concl *bpre-live0* *bpre-events* *brlct-configs* *brlct-octets*
                        *bpre-frontier* nil))))

; REMOVAL of the acknowledged-prefix hypothesis: a quiet log that committed
; and acknowledged a different first article (the second ADU, prepared at
; sequence 0 against the empty Store), never r1, on which the receiver
; acted; WRITER-BUILT.  (A crash that loses an in-flight r1 is the same
; loss, but its image is a non-exact tear, where A-CRYPTO-TRAILER's premise
; is the constrained fn-assume-crash-tearp and cannot be evaluated:
; recovery-refinement-tests' note.  A log holding r2 alone does not open:
; its history starts at sequence 1.)
(make-event `(defconst *brlct-prepared2-first*
               ',(fn-bpi-ingress-prepare (bpr-reserve (fn-sn-initial *bpr-groups* 20))
                                         *bpre-policy2* *bpre-context2* *bpre-adu2* 0)))
(assert-event (equal (fn-bpi-result-kind *brlct-prepared2-first*) :prepared))
(make-event `(defconst *brlct-r2-first*
               ',(fn-store-event-encode (fn-bpi-result-wire *brlct-prepared2-first*))))
(defconst *brlct-p* (brlct-written (list *brlct-r2-first*) 1))
(defconst *brlct-p-image* (fn-bs-crash (car *brlct-p*) nil))
(assert-event
 (and (brlct-choicesp (car *brlct-p*) nil)
      (equal (fn-lgk-acked (cdr *brlct-p*)) 1)
      (equal (brlct-recov *brlct-p-image*) (list *brlct-r2-first*))
      (equal (brlct-hyps *bpre-live0* *bpre-events* (car *brlct-p*) (cdr *brlct-p*) *brlct-p-image*
                         *brlct-configs* 1 *bpre-barriers*)
             (brlct-all-but :acked))
      (not (brlct-concl *bpre-live0* *bpre-events* *brlct-configs* (list *brlct-r2-first*) 1
                        *bpre-barriers*))))
; Acknowledging r1 alone suffices for THIS receipt (it is grounded in r1):
; the hypothesis asks for the whole live history, which is sufficient.
(assert-event (brlct-concl *bpre-live0* *bpre-events* *brlct-configs* (list *brlct-r1*) 1
                           *bpre-barriers*))
; Written and fenced but NOT acknowledged: the acknowledged prefix is empty,
; the hypothesis fails, and this image still regenerates the receipt (the
; hypothesis is sufficient, not claimed necessary for every image).
(defconst *brlct-u* (brlct-written *brlct-octets* 0))
(assert-event
 (and (equal (fn-lgk-acked (cdr *brlct-u*)) 0)
      (equal (brlct-hyps *bpre-live0* *bpre-events* (car *brlct-u*) (cdr *brlct-u*)
                         (fn-bs-crash (car *brlct-u*) nil) *brlct-configs* *bpre-frontier*
                         *bpre-barriers*)
             (brlct-all-but :acked))
      (brlct-concl *bpre-live0* *bpre-events* *brlct-configs* *brlct-octets* *bpre-frontier*
                   *bpre-barriers*)))

; NOT A HYPOTHESIS: fn-brlc-decodedp.  It was one;
; fn-brlc-open-ok-implies-decoded proves an :ok open implies it, and the
; keystone no longer carries it.  The scenario that witnessed its removal, run here: r1 r2 written,
; fenced, acknowledged; an undecodable record in flight lands whole (the
; exact tear, evaluable).  The decode refuses, and the host's open over the
; :bad rows is no Store (the host faults earlier still: fnn-bridge-recover-
; step answers NIL on :bad).
(defun brlct-batch-units (bs)
  (declare (xargs :guard t :verify-guards nil))
  (floor (len (nth 3 (car (fn-bs-pending bs)))) (brlct-unit)))
(defconst *brlct-g* (brlct-written-then-appended *brlct-octets* 2 (list *brlct-garbage*)))
(defconst *brlct-g-all* (list (brlct-sels (brlct-batch-units (car *brlct-g*)) :new)))
(defconst *brlct-g-image* (fn-bs-crash (car *brlct-g*) *brlct-g-all*))
(defconst *brlct-g-recovered* (brlct-recov *brlct-g-image*))
(assert-event
 (and (brlct-choicesp (car *brlct-g*) *brlct-g-all*)
      (equal *brlct-g-recovered* (list *brlct-r1* *brlct-r2* *brlct-garbage*))
      (not (brlct-decodedp *brlct-g-recovered*))
      (not (fn-sn-open-okp (brlct-opened-c *brlct-configs* *brlct-g-recovered* 0)))))

; -----------------------------------------------------------------------------
; NOT WITNESSED, with the reason (no false removal is claimed):
;   fn-csi-full-relationp: the receipt reads no consumer or identity
;     conjunct; its fn-snt-relation conjunct does its work in
;     fn-bpr-live-step-extends-history and is refuted there
;     (bp-receiver-evolving-tests bpre-teeth-live-extension-without-relation:
;     an untyped Store is no prefix of itself, so the acknowledged-prefix
;     hypothesis fails with it).
;   fn-lg-platform-tears-p: T whenever nothing is in flight; with a batch in
;     flight its failure is a non-exact tear outside A-CRYPTO-TRAILER's
;     constrained fn-assume-crash-tearp, which no evaluation exhibits.
;   fn-sn-open-okp: a refused open leaves no Store for the barriers to bring
;     to :ready; no refused open reaching :ready was found.
;   fn-sonb-configured-before-eventsp: the open PKT-217 follow-up (the
;     receipt over fn-cst-relation).  It is not shown necessary: a log
;     reconfigured after an event (fn.letters removed at txid 2) opens,
;     reaches :ready and regenerates the receipt.
(defconst *brlct-late-configs*
  (list (car *brlct-configs*)
        (fn-cfg-record-make 1 2 2 (list (fn-cfg-remove-group "fn.letters"))
                            *fn-cfg-default-stamp*)))
(assert-event
 (and (equal (brlct-hyps *bpre-live0* *bpre-events* *brlct-w-bs* *brlct-w-ks* *brlct-w-image*
                         *brlct-late-configs* *bpre-frontier* *bpre-barriers*)
             (brlct-all-but :configured))
      (brlct-concl *bpre-live0* *bpre-events* *brlct-late-configs* *brlct-octets*
                   *bpre-frontier* *bpre-barriers*)))

; -----------------------------------------------------------------------------
; MUTATION (a recovery that drops the receipted record r1).  It is no element
; of the tree sequence of the written log (every admissible crash image of a
; related state recovers one: fn-rr-log-crash-image-recovers-a-tree-sequence-
; member).

(defconst *brlct-dropped* (list *brlct-r2*))
(assert-event (not (fn-rr-tree-sequence-memberp *brlct-dropped*
                                                (fn-lgk-committed *brlct-w-ks*)
                                                (fn-lgk-inflight *brlct-w-ks*))))
(assert-event (fn-rr-tree-sequence-memberp (brlct-recov *brlct-w-image*)
                                           (fn-lgk-committed *brlct-w-ks*)
                                           (fn-lgk-inflight *brlct-w-ks*)))
; The host's replay refuses the mutated history (its sequence starts at 1:
; fn-ssr-intern-step's identity step answers :bad), and no open over it is a
; Store, so no restart over it serves the receipt.
(assert-event
 (and (not (brlct-decodedp *brlct-dropped*))
      (not (fn-sn-open-okp (brlct-opened-c *brlct-configs* *brlct-dropped* 1)))
      (not (fn-sn-open-okp (brlct-opened-c *brlct-configs* *brlct-dropped* 0)))))
