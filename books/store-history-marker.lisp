; M5: the committed-history boundary (review 2026-09-24, finding 3 of
; planning/evidence/m5-compact-verb-2026-09-24.md).
;
; The open's namespace gate admits a history and every proper prefix of it
; (fn-cverb-open-history-gate-admits-a-lost-suffix), and the allocation
; frontier cannot tell a lost newest record from a burned reservation: both
; leave the frontier above the last record's txid.  This book is the witness
; the review asks for.  A marker file, committed-history.json in the store
; root, holds a committed-record COUNT.  The host writes it after a record's
; transaction-directory barrier and before fn-sn-finish, and never on any
; other path (a reservation, an abort, a refusal, a recovery), so
;
;   * every record the node ever acknowledged is below a durable marker,
;   * the marker is never above the number of durable records, and
;   * a burned allocation writes nothing the marker reads.
;
; What it does not detect: loss of the marker file together with the files
; it covers (an absent marker is admitted as :unmarked, which is how every
; store written before this book opens), a marker write that fails (the
; transaction is then uncertain and never acknowledged), replacement of the
; whole store by an older valid copy (that needs a freshness anchor outside
; the store, D14), or the configuration history and the BP stores, which
; have namespaces of their own.
;
; Host subjects: host/native/io.lisp fnn-mark-committed calls
; fn-hm-after-commit; fnn-check-history-marker (called by fnn-recover, every
; open) calls fn-hm-open-verdict.  fn-hm-marker-cut-names is the developer
; cut selector's table.
(in-package "ACL2")
(include-book "byte-store-frame")

; FNSM kind 3.  The FNSM family (books/byte-store-frame) has config (1) and
; the allocation frontier (2); a distinct kind keeps a copied frontier file
; from reading as a marker.
(defconst *fn-hm-kind* 3)

(defun fn-hm-countp (n)
  (declare (xargs :guard t))
  (and (natp n) (<= n *fn-cbor-max-uint*)))

(defun fn-hm-encode (n)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-hm-countp n))
      nil
    (fn-frame-seal *fn-bs-meta-magic* *fn-bs-meta-version* *fn-hm-kind*
                   (fn-cbor-encode (cons :uint n)))))

(defun fn-hm-decode (octets)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-cbor-octet-listp octets))
      nil
    (let ((frame (fn-frame-open octets *fn-bs-meta-max-frontier-payload*)))
      (if (not (fn-bs-meta-frame-okp frame *fn-hm-kind*
                                      (fn-frame-result-payload frame)
                                      *fn-bs-meta-max-frontier-payload*))
          nil
        (let ((decoded (fn-cbor-decode-exact (fn-frame-result-payload frame))))
          (if (and (fn-cbor-result-okp decoded)
                   (equal (fn-cbor-ag-car (fn-cbor-result-value decoded)) :uint)
                   (natp (fn-cbor-ag-cdr (fn-cbor-result-value decoded))))
              (fn-cbor-ag-cdr (fn-cbor-result-value decoded))
            nil))))))


; The codec round trip, over the FNSM frame lemmas of books/byte-store-frame.
(defthm fn-hm-frame-inputp
  (implies (fn-hm-countp n)
           (fn-frame-inputp *fn-bs-meta-magic* *fn-bs-meta-version* *fn-hm-kind*
                            (fn-cbor-encode (cons :uint n))
                            *fn-bs-meta-max-frontier-payload*))
  :hints (("Goal" :use ((:instance fn-bs-frontier-frame-inputp (n n)))
           :in-theory (e/d (fn-frame-inputp fn-frame-magicp)
                           (fn-bs-frontier-frame-inputp)))))

(verify-guards fn-hm-encode
  :hints (("Goal" :use ((:instance fn-hm-frame-inputp (n n)))
           :in-theory (e/d (fn-frame-inputp) (fn-hm-frame-inputp)))))

(defthm fn-hm-open-of-encode
  (implies (fn-hm-countp n)
           (equal (fn-frame-open (fn-hm-encode n) *fn-bs-meta-max-frontier-payload*)
                  (fn-frame-ok *fn-bs-meta-magic* *fn-bs-meta-version* *fn-hm-kind*
                               (fn-cbor-encode (cons :uint n)))))
  :hints (("Goal" :use ((:instance fn-frame-open-of-seal
                                   (magic *fn-bs-meta-magic*)
                                   (version *fn-bs-meta-version*)
                                   (kind *fn-hm-kind*)
                                   (payload (fn-cbor-encode (cons :uint n)))
                                   (max-payload *fn-bs-meta-max-frontier-payload*))
                        (:instance fn-hm-frame-inputp (n n)))
           :in-theory (e/d (fn-hm-encode)
                           (fn-frame-open fn-frame-seal fn-hm-frame-inputp)))))

(defthm fn-hm-protected-octet-listp
  (implies (fn-hm-countp n)
           (fn-cbor-octet-listp
            (fn-frame-protected *fn-bs-meta-magic* *fn-bs-meta-version*
                                *fn-hm-kind* (fn-cbor-encode (cons :uint n)))))
  :hints (("Goal"
           :use ((:instance fn-bs-frontier-protected-octet-listp (n n)))
           :in-theory (e/d (fn-frame-protected fn-frame-header)
                           (fn-bs-frontier-protected-octet-listp)))))

(defthm fn-hm-encode-octet-listp
  (implies (fn-hm-countp n)
           (fn-cbor-octet-listp (fn-hm-encode n)))
  :hints (("Goal"
           :use ((:instance fn-hm-protected-octet-listp (n n))
                 (:instance fn-frame-digestp-of-fn-frame-digest
                            (octets (fn-frame-protected
                                     *fn-bs-meta-magic* *fn-bs-meta-version*
                                     *fn-hm-kind* (fn-cbor-encode (cons :uint n)))))
                 (:instance fn-cbor-octet-listp-append
                            (xs (fn-frame-protected
                                 *fn-bs-meta-magic* *fn-bs-meta-version*
                                 *fn-hm-kind* (fn-cbor-encode (cons :uint n))))
                            (ys (fn-frame-digest
                                 (fn-frame-protected
                                  *fn-bs-meta-magic* *fn-bs-meta-version*
                                  *fn-hm-kind* (fn-cbor-encode (cons :uint n)))))))
           :in-theory (e/d (fn-hm-encode fn-frame-seal fn-frame-encode)
                           (fn-hm-protected-octet-listp)))))

(defthm fn-hm-decode-of-encode
  (implies (fn-hm-countp n)
           (equal (fn-hm-decode (fn-hm-encode n)) n))
  :hints (("Goal"
           :use ((:instance fn-hm-open-of-encode (n n))
                 (:instance fn-hm-encode-octet-listp (n n))
                 (:instance fn-hm-frame-inputp (n n))
                 (:instance fn-bs-frontier-cbor-round-trip (n n)))
           :in-theory (e/d (fn-hm-decode fn-bs-meta-frame-okp fn-frame-inputp)
                           (fn-hm-open-of-encode fn-hm-encode-octet-listp
                                                 fn-hm-frame-inputp)))))

(defthm fn-hm-decode-is-a-count-or-nil
  (or (natp (fn-hm-decode octets)) (null (fn-hm-decode octets)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-hm-decode))))

(verify-guards fn-hm-decode)

; -----------------------------------------------------------------------------
; The decisions the host calls.

; What the marker holds, and when: after the record of SEQUENCE has passed its
; transaction-directory barrier (fnn-publish returned :durable), and before
; fn-sn-finish, the marker is replaced by the count of records through it.
; Sequences are contiguous from 0, so that count is SEQUENCE + 1.  NIL (the
; host faults before any write) at the end of the uint32 domain.
(defun fn-hm-after-commit (sequence)
  (declare (xargs :guard t))
  (if (and (natp sequence) (< sequence *fn-cbor-max-uint*))
      (fn-hm-encode (1+ sequence))
    nil))

; The open's check, evaluated once per open over one bounded read of the
; marker.  OBSERVATION is (:absent) or (:present OCTETS); RECORD-COUNT is the
; length of the record list the open hands replay (pack events plus suffix
; files, so a reclaim that removed covered files does not shorten it).
;   (:admitted :unmarked)                  no marker (a store from before it)
;   (:admitted :marked M)                  M <= RECORD-COUNT
;   (:refused :history-short-of-marker M)  a committed suffix is missing
;   (:refused :marker-damaged)             present but not an FNSM kind-3 frame
;   (:refused :observation)                the host handed a malformed input
(defun fn-hm-open-verdict (observation record-count)
  (declare (xargs :guard t))
  (cond ((not (natp record-count)) (list :refused :observation))
        ((equal observation '(:absent)) (list :admitted :unmarked))
        ((and (consp observation) (eq (car observation) :present)
              (consp (cdr observation)) (null (cddr observation)))
         (let ((m (fn-hm-decode (cadr observation))))
           (cond ((null m) (list :refused :marker-damaged))
                 ((< record-count m) (list :refused :history-short-of-marker m))
                 (t (list :admitted :marked m)))))
        (t (list :refused :observation))))

; The marker's byte program: the shape fnn-mark-committed performs, in
; order.  The stage is a `.stage-' name in staging/ (a prefix the recovery
; sweep already collects, books/store-sweep: never read back, committed by
; rename), and the rename's target is committed-history.json in the root.
(defconst *fn-hm-marker-program*
  '((:create :staging stage) (:cut :marker-created)
    (:write stage) (:cut :marker-written)
    (:fsync-file stage) (:cut :marker-staged-durable)
    (:rename stage :root committed-history) (:cut :marker-replaced)
    (:fsync-dir :root) (:cut :marker-durable)))

; The developer cut selector's table (FN_NATIVE_POST_FAULT=CUT:kill|eio).
(defun fn-hm-marker-cut-names ()
  (declare (xargs :guard t))
  '("marker-created" "marker-written" "marker-staged-durable"
    "marker-replaced" "marker-durable"))

; -----------------------------------------------------------------------------
; The crash model of the marker program, and the history it runs in.
;
; A crash at CUT leaves the marker the open reads as OLD before the rename,
; either OLD or NEW after the rename and before the root directory barrier
; (CHOICE picks), and NEW after the barrier.  This table is the rename
; atomicity of the crash model (specs/crash-model-v2.md) transcribed for this one
; program; it is not yet derived from the fn-bs byte model, whose programs
; do not include this one (open, specs/storage.md).
(defun fn-hm-crash-image (cut choice old new)
  (declare (xargs :guard t))
  (cond ((equal cut :marker-durable) new)
        ((equal cut :marker-replaced) (if choice new old))
        (t old)))

; A history step, over (COUNT . MARKER-OBSERVATION):
;   (:burn)            a reservation abandoned (process death or a known
;                      abort before publication): the frontier moves, no
;                      record, no marker write
;   (:uncertain B)     a publication cut after its link and before its
;                      directory barrier: the record survives iff B; the
;                      marker is not written (fnn-publish raised)
;   (:commit CUT C)    the record of sequence COUNT is durable; the marker
;                      program then runs to CUT (:marker-durable = it
;                      completed, and only then may the node acknowledge)
(defun fn-hm-step (op st)
  (declare (xargs :guard t :verify-guards nil))
  (let ((count (car st)) (marker (cdr st)))
    (cond ((and (consp op) (eq (car op) :uncertain))
           (if (and (consp (cdr op)) (cadr op)) (cons (1+ (nfix count)) marker) st))
          ((and (consp op) (eq (car op) :commit))
           (cons (1+ (nfix count))
                 (fn-hm-crash-image (and (consp (cdr op)) (cadr op))
                                    (and (consp (cdr op)) (consp (cddr op)) (caddr op))
                                    marker
                                    (list :present (fn-hm-after-commit count)))))
          (t st))))

(defun fn-hm-run (ops st)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom ops) st (fn-hm-run (cdr ops) (fn-hm-step (car ops) st))))

(defun fn-hm-admittedp (st)
  (declare (xargs :guard t :verify-guards nil))
  (equal (car (fn-hm-open-verdict (cdr st) (car st))) :admitted))

; Burned reservations and publications that did not survive: steps that
; leave no record.
(defun fn-hm-burnsp (ops)
  (declare (xargs :guard t))
  (if (atom ops)
      (null ops)
    (and (or (equal (car ops) '(:burn)) (equal (car ops) '(:uncertain nil)))
         (fn-hm-burnsp (cdr ops)))))

; -----------------------------------------------------------------------------
; Keystone 1: the marker never refuses a history the host can produce.  From
; any admitted state, every interleaving of burned reservations, uncertain
; publications and commits crashed at any marker cut (or completed) leaves a
; state the open admits.  The one hypothesis beyond admission is the uint32
; count domain.
(defthm fn-hm-after-commit-decodes-to-the-next-count
  (implies (and (natp sequence) (< sequence *fn-cbor-max-uint*))
           (equal (fn-hm-decode (fn-hm-after-commit sequence)) (1+ sequence)))
  :hints (("Goal" :in-theory (disable fn-hm-encode fn-hm-decode))))
(defthm fn-hm-step-preserves-admitted
  (implies (and (fn-hm-admittedp st) (< (car st) *fn-cbor-max-uint*))
           (fn-hm-admittedp (fn-hm-step op st)))
  :hints (("Goal" :in-theory (disable fn-hm-after-commit fn-hm-decode))))
(defthm fn-hm-step-count-bound
  (implies (natp (car st))
           (<= (car (fn-hm-step op st)) (1+ (car st))))
  :rule-classes :linear)
(defthm fn-hm-admitted-count-is-natural
  (implies (fn-hm-admittedp st) (natp (car st)))
  :rule-classes :forward-chaining)
(defthm fn-hm-run-keeps-every-open-admitted
  (implies (and (fn-hm-admittedp st)
                (<= (+ (car st) (len ops)) *fn-cbor-max-uint*))
           (fn-hm-admittedp (fn-hm-run ops st)))
  :hints (("Goal" :in-theory (disable fn-hm-admittedp fn-hm-step))))

; Keystone 2: every acknowledged record is covered.  A commit whose marker
; program completed (the only commit the node may acknowledge: the host
; calls fn-sn-finish after the marker's root barrier), followed by ANY
; further history -- burned reservations, uncertain publications, commits
; crashed at any marker cut -- leaves an open that refuses, naming
; :history-short-of-marker, whenever the observed record count K is at most
; that record's sequence.  A burned allocation is not mistaken for a loss
; (keystone 1: it leaves the open admitted); a lost newest record is
; (this theorem with POST the burns after it).
(defun fn-hm-marker-value (st)
  (declare (xargs :guard t :verify-guards nil))
  (let ((obs (cdr st)))
    (if (and (consp obs) (eq (car obs) :present) (consp (cdr obs)))
        (nfix (fn-hm-decode (cadr obs)))
      0)))
(defthm fn-hm-step-marker-monotone
  (implies (and (fn-hm-admittedp st) (< (car st) *fn-cbor-max-uint*))
           (<= (fn-hm-marker-value st) (fn-hm-marker-value (fn-hm-step op st))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-hm-after-commit fn-hm-decode))))
(defthm fn-hm-run-marker-monotone
  (implies (and (fn-hm-admittedp st)
                (<= (+ (car st) (len ops)) *fn-cbor-max-uint*))
           (<= (fn-hm-marker-value st) (fn-hm-marker-value (fn-hm-run ops st))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-hm-admittedp fn-hm-step fn-hm-marker-value))))
(defthm fn-hm-completed-commit-marks-its-count
  (implies (and (natp (car st)) (< (car st) *fn-cbor-max-uint*))
           (equal (fn-hm-marker-value (fn-hm-step (list :commit :marker-durable choice) st))
                  (1+ (car st))))
  :hints (("Goal" :in-theory (disable fn-hm-after-commit fn-hm-decode))))
(defthm fn-hm-completed-commit-is-admitted
  (implies (and (natp (car st)) (< (car st) *fn-cbor-max-uint*))
           (fn-hm-admittedp (fn-hm-step (list :commit :marker-durable choice) st)))
  :hints (("Goal" :in-theory (disable fn-hm-after-commit fn-hm-decode))))
(defthm fn-hm-admitted-open-below-the-marker-names-it
  (implies (and (fn-hm-admittedp end) (natp k) (< k (fn-hm-marker-value end)))
           (equal (fn-hm-open-verdict (cdr end) k)
                  (list :refused :history-short-of-marker (fn-hm-marker-value end))))
  :hints (("Goal" :in-theory (disable fn-hm-decode))))

(defthm fn-hm-open-refuses-a-lost-acknowledged-record
  (let ((end (fn-hm-run post (fn-hm-step (list :commit :marker-durable choice) st))))
    (implies (and (natp (car st))
                  (<= (+ (car st) 1 (len post)) *fn-cbor-max-uint*)
                  (natp k) (<= k (car st)))
             (equal (fn-hm-open-verdict (cdr end) k)
                    (list :refused :history-short-of-marker
                          (fn-hm-marker-value end)))))
  :hints (("Goal"
           :use ((:instance fn-hm-completed-commit-is-admitted)
                 (:instance fn-hm-completed-commit-marks-its-count)
                 (:instance fn-hm-run-marker-monotone (ops post)
                            (st (fn-hm-step (list :commit :marker-durable choice) st)))
                 (:instance fn-hm-run-keeps-every-open-admitted (ops post)
                            (st (fn-hm-step (list :commit :marker-durable choice) st)))
                 (:instance fn-hm-admitted-open-below-the-marker-names-it
                            (end (fn-hm-run post (fn-hm-step (list :commit :marker-durable choice) st)))))
           :in-theory (disable fn-hm-run fn-hm-step fn-hm-admittedp fn-hm-marker-value
                               fn-hm-open-verdict fn-hm-run-keeps-every-open-admitted
                               fn-hm-completed-commit-is-admitted
                               fn-hm-completed-commit-marks-its-count
                               fn-hm-run-marker-monotone
                               fn-hm-admitted-open-below-the-marker-names-it))))

; Export: the codec and the history model close; the round trip, the
; decisions' shape facts and the keystones are what includers use.
(in-theory (disable fn-hm-encode fn-hm-decode fn-hm-step fn-hm-run
                    fn-hm-marker-value fn-hm-admittedp
                    fn-hm-after-commit-decodes-to-the-next-count
                    fn-hm-completed-commit-marks-its-count))
