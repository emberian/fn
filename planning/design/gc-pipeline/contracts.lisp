; Draft vocabulary, not a book or a second commit machine.  No state transition
; is reimplemented here: readouts compose the existing host-called functions.
; statements.lisp contains the unproved obligations; witnesses.lisp does not
; load those obligations as axioms/theorems.  See TRACE.md for missing wiring.
(in-package "ACL2")
(include-book "../../../books/owner-reader-view")
(include-book "../../../books/owner-queued-work")
(include-book "../../../books/store-log-durable")

; H is the logical record history, M the existing OCVM count abstraction,
; KS the existing log kernel. C counts COMPLETED records, D fenced records.
; D is a RECORD prefix length, never a txid or fn-lgk-frontier's byte offset.
; The receipt coupling is essential: a successful barrier observation must
; cover its captured batch. It must be established by the composed transition
; under fn-lgk-relp/A-DURABLE, not checked by walking H on the served path.
(defun fn-ocp-gc-linkedp (h m ks s event phase word)
  (declare (xargs :guard t :verify-guards nil))
  (let ((c (fn-ocvm-c m)) (a (fn-ocvm-a m))
        (d (len (fn-lgk-committed ks))))
    (and (true-listp h) (true-listp ks)
         (true-listp (fn-lgk-committed ks))
         (fn-olr-linkp h ks) (fn-ocvm-inv m)
         (equal (fn-ocvm-w m) (len h))
         (<= c d) (<= d (+ c a))
         (implies (equal (mv-nth 0 (fn-ocp-commit-event s event)) :complete)
                  (and (equal (fn-lgk-phase ks) :fenced) (equal d (+ c a))))
         (implies (or (equal phase :resolutions)
                      (equal (fn-oqw-step :batch phase word) :resolutions))
                  (and (equal (fn-lgk-phase ks) :fenced) (equal d (+ c a)))))))

; These are dependency-prefix bounds, NOT fabricated wire renderers. Each
; record-derived octet (including a derived field, not merely copied payload)
; must be rendered solely from the selected prefix. Protocol literals,
; incoming bytes, intent frames and pre-attempt refusals are not stored-record
; reveals. The renderer/refusal dependency bridges are separate obligations.
; Equation to current calls, by construction:
;  reader: fn-ocv-reader-view (fn-ocfg-at-reader-view wraps it)
;  reply/log: fn-ocp-commit-event -> :complete, fn-ocs-member-releases
;  feed: fn-oqw-step :batch :fence :ok -> :resolutions.
; The host callsites for this equation are listed in TRACE.md.
(defun fn-ocp-gc-cuts (m s event phase word)
  (declare (xargs :guard t))
  (let ((end (+ (fn-ocvm-c m) (fn-ocvm-a m)))
        (action (mv-nth 0 (fn-ocp-commit-event s event))))
    (list (fn-ocv-reader-view (fn-ocvm-views m) (fn-ocvm-w m))
          (if (or (equal phase :resolutions)
                  (equal (fn-oqw-step :batch phase word) :resolutions)) end 0)
          (if (equal action :complete) end 0)
          (if (equal action :complete) end 0))))

; The named equation is intentionally a definition lemma, not an event
; keystone and not a claimed proof of native host control flow.
(defthm fn-ocp-gc-cuts-by-definition
  (equal (fn-ocp-gc-cuts m s event phase word)
         (list (fn-ocv-reader-view (fn-ocvm-views m) (fn-ocvm-w m))
               (if (or (equal phase :resolutions)
                       (equal (fn-oqw-step :batch phase word) :resolutions))
                   (+ (fn-ocvm-c m) (fn-ocvm-a m)) 0)
               (if (equal (mv-nth 0 (fn-ocp-commit-event s event)) :complete)
                   (+ (fn-ocvm-c m) (fn-ocvm-a m)) 0)
               (if (equal (mv-nth 0 (fn-ocp-commit-event s event)) :complete)
                   (+ (fn-ocvm-c m) (fn-ocvm-a m)) 0))))

(defun fn-ocv-gc-prefix-durablep (h ks cut)
  (declare (xargs :guard t :verify-guards nil))
  (and (natp cut) (<= cut (len (fn-lgk-committed ks)))
       (fn-lg-prefixp (take cut h) (fn-lgk-committed ks))))

(defun fn-ocp-gc-reveals-okp (h ks cuts)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp cuts)
      (and (fn-ocv-gc-prefix-durablep h ks (car cuts))
           (fn-ocp-gc-reveals-okp h ks (cdr cuts)))
    t))

; Failure contract uses the actual concrete acknowledgement fold the host
; calls. Arbitrary N includes any subsequent attempted acknowledgements;
; old committed but unacknowledged records may still be counted, never the
; failed suffix. No recovery/new incarnation is in this quantification.
; Native fnn-store-fenced := t and stop(exit 3) remain required effects of
; :stop, not a property silently inferred from the scheduler alone.
(defun fn-ocp-gc-failure-hyp (s ks a b)
  (declare (xargs :guard t :verify-guards nil))
  (and (true-listp ks)
       (<= (fn-lgk-acked ks) (len (fn-lgk-committed ks)))
       (member-eq (fn-ocs-phase (fn-ocp-ocs s)) '(:staged :failed))
       (true-listp a) (true-listp b)
       (equal (len a) (len (fn-lgk-inflight ks)))
       (equal (len b) (len (fn-lgk-batch ks)))))

(defun fn-ocp-gc-failure-okp (s ks a b n)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((action (mv-nth 0 (fn-ocp-commit-event s :failed)))
         (failed (fn-lgc-fence-failed (fn-lgc-of ks)))
         (later (fn-lgu-acknowledge failed (nfix n)))
         (releases (fn-ocs-member-releases action (append a b))))
    (and (equal action :stop)
         (equal (fn-lgc-phase later) :fault)
         (equal (fn-lgc-count later) (len (fn-lgk-committed ks)))
         (<= (fn-lgc-acked later) (len (fn-lgk-committed ks)))
         (equal (len releases) (+ (len a) (len b)))
         (subsetp-equal releases '(:own-uncertain :uncertain-reply :close)))))

; Membership is ORDERED, at the barrier's captured write cut, not its return
; time. The open batch contains history after the preceding seal; the
; in-flight batch contains sealed records after the durable prefix. Keeping
; both equalities prevents assigning the next batch to the current receipt.
; OMAX in this target is actual encoded log octets, including framing and
; padding. Today's fn-olr-take counts packed record bytes (4+len) instead.
; PROFILE-FITS is the proposed additional ACL2 preflight, before consuming
; the submission. Configuration must accommodate one maximal legal record;
; full work yields/resumes, never an inline barrier or silent truncation.
(defun fn-olr-gc-profile-fitp (ks record bmax omax unit)
  (declare (xargs :guard t :verify-guards nil))
  (and (posp bmax) (natp omax) (posp unit)
       (<= (fn-lgc-append-len (fn-lgc-of (fn-lgk-prepare ks record)) unit) omax)))

(defun fn-olr-gc-membership-hyp (h ks record txid count octets bmax omax unit)
  (declare (xargs :guard t :verify-guards nil))
  (and (true-listp h) (true-listp ks)
       (true-listp (fn-lgk-batch ks)) (fn-olr-linkp h ks)
       (equal count (len (fn-lgk-batch ks)))
       (equal octets (fn-lg-pack-len (fn-lgk-batch ks)))
       (fn-olr-gc-profile-fitp ks record bmax omax unit)
       (equal (car (fn-olr-take ks record txid count octets bmax omax unit)) :taken)))

(defun fn-olr-gc-membership-okp (h ks record txid count octets bmax omax unit)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((after (cadr (fn-olr-take ks record txid count octets bmax omax unit)))
         (d (len (fn-lgk-committed ks)))
         (seal (+ d (len (fn-lgk-inflight ks))))
         (h2 (append h (list record))))
    (and (equal (fn-lgk-inflight after) (fn-lgk-inflight ks))
         (equal (fn-lgk-batch after) (nthcdr seal h2))
         (equal (append (true-list-fix (fn-lgk-inflight after))
                        (fn-lgk-batch after)) (nthcdr d h2))
         (<= (len (fn-lgk-batch after)) bmax)
         (<= (fn-lgc-append-len (fn-lgc-of after) unit) omax))))
