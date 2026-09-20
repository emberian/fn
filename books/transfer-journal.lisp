; fn C2-04: a durable journal around the volatile transfer staging kernel.
;
; `books/transfer.lisp` stages fragments in memory and says so: its state "is
; volatile staging state; it deliberately makes no assertion about a disk
; commit or restart recovery".  This book adds the durable record family that
; makes restart a theorem instead of a hope.  Every record is an input to one
; of the two public kernel transitions, `fn-transfer-reserve` and
; `fn-transfer-add-chunk`, together with the outcome the kernel returned for
; it.  Replay re-runs the same transition on the same input and checks the
; recorded outcome; the state after replay is the kernel state, with the same
; gaps, retained bytes and reservations, because the kernel is a function.
;
; Logical records (the host writes them through `fn-tj-write`):
;   (:profile capacity max-object max-chunk max-chunks max-label max-reservations)
;   (:reserve label declared-length outcome)
;   (:chunk   label offset octets outcome)
; `:profile` is the first record of a journal and fixes the initial state;
; the other two are transition records.  A journaled refusal (any outcome
; other than `:reserved` or `:stored`) is evidence of an arrival the kernel
; turned away, including an `:overlap-conflict`; it replays to exactly the
; prior state (`transfer-journal-invariants`).
;
; Durable bytes: one frame per record under `books/frame.lisp`, in this
; book's own family (magic FNTJ, version 1, kind table `*fn-tj-kinds*`).  The
; frame's trailer is A-CRYPTO exactly as in `frame.lisp`: `fn-tj-decode` takes
; the host's digest of the protected prefix and `fn-tj-open` states the same
; decode against the constrained `fn-frame-digest`.  A frame that does not
; open, or whose record the kernel contradicts, ends replay at a typed fault
; with the state as of the last good record; no partial chunk exists, because
; the only way bytes enter the state is the kernel's own `:stored` branch.
;
; What this book does not do: it does not validate a candidate, name a content
; identity, issue a receipt, or accept anything.  A complete entry is exported
; as `(:unverified octets)` by `fn-tj-candidate` and nothing else; the
; container book (C2-05) is where validation and acceptance live.

(in-package "ACL2")
(include-book "transfer")
(include-book "frame")

; The codecs cluster withdraws the frame vocabulary at its export theory
; (BOARD, 2026-09-19 codecs).  This book opens it only where a guard proof
; needs it, in that event's own hint, never book-wide: `fn-frame-octet-
; vocabulary` is the `len`-backchaining cascade codecs measured at 108 s on a
; single `append` goal, and with it live the admission of the replay folds
; case-split past a 1800 s timeout (measured here, 2026-09-19).

; -----------------------------------------------------------------------------
; Frame family

(defconst *fn-tj-magic* '(70 78 84 74))          ; FNTJ
(defconst *fn-tj-version* 1)
(defconst *fn-tj-kinds* '(:profile :reserve :chunk))

; Every outcome symbol the two transitions can return, as enum fields.
(defconst *fn-tj-reserve-outcomes*
  '(:reserved :already-reserved :label-conflict :reservation-limit :capacity
    :object-limit :invalid-length :invalid-label :invalid-state))
(defconst *fn-tj-chunk-outcomes*
  '(:stored :covered :duplicate :empty-chunk :overlap-conflict :chunk-limit
    :bounds :unknown-label :invalid-offset :invalid-chunk :invalid-label
    :invalid-state))

; A chunk record is the largest: two maximal blobs, a u64 and an enum octet.
; 4 + 131072 + 8 + 4 + 131072 + 1.
(defconst *fn-tj-max-payload* 262161)

; The field specification of each kind, in the `fn-frame-` field grammar.
(defun fn-tj-spec-for (kind)
  (declare (xargs :guard t))
  (if (equal kind :profile)
      '(:nat :nat :nat :nat :nat :nat)
    (if (equal kind :reserve)
        (list :blob :nat (cons :enum *fn-tj-reserve-outcomes*))
      (if (equal kind :chunk)
          (list :blob :nat :blob (cons :enum *fn-tj-chunk-outcomes*))
        :none))))

(defthm fn-tj-spec-for-is-spec-list
  (implies (not (equal (fn-tj-spec-for kind) :none))
           (fn-frame-spec-listp (fn-tj-spec-for kind)))
  :hints (("Goal" :in-theory (enable fn-tj-spec-for fn-frame-spec-listp))))

(in-theory (disable fn-tj-spec-for))

; -----------------------------------------------------------------------------
; Records.  Every accessor is the total `fn-frame-item`, so nothing below has
; a guard that depends on the shape of a value that failed to parse.

(defun fn-tj-kind (r) (declare (xargs :guard t)) (fn-frame-item 0 r))
(defun fn-tj-label (r) (declare (xargs :guard t)) (fn-frame-item 1 r))
; Declared length of a `:reserve`, offset of a `:chunk`.
(defun fn-tj-arg (r) (declare (xargs :guard t)) (fn-frame-item 2 r))
(defun fn-tj-octets (r) (declare (xargs :guard t)) (fn-frame-item 3 r))
(defun fn-tj-outcome (r)
  (declare (xargs :guard t))
  (if (equal (fn-tj-kind r) :reserve)
      (fn-frame-item 3 r)
    (fn-frame-item 4 r)))

(defun fn-tj-transition-recordp (r)
  (declare (xargs :guard t))
  (and (true-listp r)
       (or (and (equal (fn-tj-kind r) :reserve) (equal (len r) 4))
           (and (equal (fn-tj-kind r) :chunk) (equal (len r) 5)))))

(defun fn-tj-profile-recordp (r)
  (declare (xargs :guard t))
  (and (true-listp r)
       (equal (len r) 7)
       (equal (fn-tj-kind r) :profile)
       (fn-frame-values-okp '(:nat :nat :nat :nat :nat :nat) (cdr r))))

(defun fn-tj-profile-of (r)
  (declare (xargs :guard t))
  (fn-transfer-make-profile (fn-frame-item 1 r) (fn-frame-item 2 r)
                            (fn-frame-item 3 r) (fn-frame-item 4 r)
                            (fn-frame-item 5 r) (fn-frame-item 6 r)))

(defun fn-tj-profile-record (profile)
  (declare (xargs :guard t))
  (list :profile
        (fn-transfer-capacity profile) (fn-transfer-max-object profile)
        (fn-transfer-max-chunk profile) (fn-transfer-max-chunks profile)
        (fn-transfer-max-label profile)
        (fn-transfer-max-reservations profile)))

; -----------------------------------------------------------------------------
; The transition an input or a record names.  This is the whole coupling to
; the kernel: the same two public functions, on the record's own fields.  An
; input is `(:reserve label declared-length)` or `(:chunk label offset octets)`;
; anything else is handed to `fn-transfer-add-chunk`, which refuses it.

(defun fn-tj-transition (st r)
  (declare (xargs :guard t))
  (if (equal (fn-tj-kind r) :reserve)
      (fn-transfer-reserve st (fn-tj-label r) (fn-tj-arg r))
    (fn-transfer-add-chunk st (fn-tj-label r) (fn-tj-arg r)
                           (fn-tj-octets r))))

; The host writes this record after the kernel answered and before it adopts
; the new state.  The outcome is the kernel's, never the host's.
(defun fn-tj-write (st input)
  (declare (xargs :guard t))
  (let ((outcome (fn-transfer-result-outcome (fn-tj-transition st input))))
    (if (equal (fn-tj-kind input) :reserve)
        (list :reserve (fn-tj-label input) (fn-tj-arg input) outcome)
      (list :chunk (fn-tj-label input) (fn-tj-arg input) (fn-tj-octets input)
            outcome))))

; The journal a live run leaves behind, and the state that run reaches.
(defun fn-tj-journal (st inputs)
  ; The measure is named: ACL2's first guess is over `st`, and refuting it
  ; opens the whole transfer kernel inside the termination proof.
  (declare (xargs :guard t :measure (acl2-count inputs)))
  (if (consp inputs)
      (cons (fn-tj-write st (car inputs))
            (fn-tj-journal (fn-transfer-result-state
                            (fn-tj-transition st (car inputs)))
                           (cdr inputs)))
    nil))

(defun fn-tj-run (st inputs)
  (declare (xargs :guard t :measure (acl2-count inputs)))
  (if (consp inputs)
      (fn-tj-run (fn-transfer-result-state
                  (fn-tj-transition st (car inputs)))
                 (cdr inputs))
    st))

; -----------------------------------------------------------------------------
; Replay of logical records.  A step answers (:ok state) or
; (:fault reason state); a replay answers (:ok state index) or
; (:fault reason state index), where the state is the one before the faulting
; record and the index counts records consumed.

(defun fn-tj-apply (st r)
  (declare (xargs :guard t))
  (if (not (fn-tj-transition-recordp r))
      (list :fault :not-a-transition st)
    (let ((result (fn-tj-transition st r)))
      (if (not (equal (fn-transfer-result-outcome result) (fn-tj-outcome r)))
          (list :fault :outcome-mismatch st)
        (list :ok (fn-transfer-result-state result))))))

(defun fn-tj-replay-records (st records index)
  (declare (xargs :guard t :measure (acl2-count records)))
  (if (consp records)
      (let ((step (fn-tj-apply st (car records))))
        (if (equal (fn-frame-item 0 step) :ok)
            (fn-tj-replay-records (fn-frame-item 1 step) (cdr records)
                                  (+ 1 (fix index)))
          (list :fault (fn-frame-item 1 step) st index)))
    (list :ok st index)))

(defun fn-tj-replay (records)
  (declare (xargs :guard t))
  (if (and (consp records) (fn-tj-profile-recordp (car records)))
      (fn-tj-replay-records
       (fn-transfer-initial-state (fn-tj-profile-of (car records)))
       (cdr records) 1)
    (list :fault :no-profile nil 0)))

; -----------------------------------------------------------------------------
; Frames

(defun fn-tj-record-okp (r)
  (declare (xargs :guard t :verify-guards nil))
  (let ((spec (fn-tj-spec-for (fn-tj-kind r))))
    (and (consp r)
         (true-listp r)
         (not (equal spec :none))
         (fn-frame-values-okp spec (cdr r))
         (<= (len (fn-frame-fields-octets spec (cdr r)))
             *fn-tj-max-payload*))))

(verify-guards fn-tj-record-okp
  :hints (("Goal" :in-theory (enable fn-frame-fields-vocabulary
                                     fn-frame-record-vocabulary))))

(defun fn-tj-records-okp (rs)
  (declare (xargs :guard t))
  (if (consp rs)
      (and (fn-tj-record-okp (car rs)) (fn-tj-records-okp (cdr rs)))
    (null rs)))

(defun fn-tj-code (r)
  (declare (xargs :guard t))
  (fn-frame-enum-index (fn-tj-kind r) *fn-tj-kinds*))

(defun fn-tj-payload (r)
  (declare (xargs :guard (fn-tj-record-okp r)))
  (fn-frame-fields-octets (fn-tj-spec-for (fn-tj-kind r)) (cdr r)))

(defun fn-tj-encode (r digest)
  ; The host entry point.  `digest` is the host's 32 octets over the protected
  ; prefix; `fn-tj-seal` says what must be true of it.
  (declare (xargs :guard t :verify-guards nil))
  (if (not (and (fn-tj-record-okp r) (fn-frame-digestp digest)))
      :bad
    (let ((code (fn-tj-code r)))
      (if (equal code 0)
          :bad
        (fn-frame-encode *fn-tj-magic* *fn-tj-version* code
                         (fn-tj-payload r) digest)))))

(verify-guards fn-tj-encode
  :hints (("Goal" :in-theory (enable fn-frame-fields-vocabulary
                                     fn-frame-record-vocabulary))))

(defun fn-tj-decode (octets digest)
  ; The host entry point.  Every bound is checked by `fn-frame-decode` before
  ; the corresponding split allocates.
  (declare (xargs :guard t :verify-guards nil))
  (let ((frame (fn-frame-decode octets digest *fn-tj-max-payload*)))
    (if (not (fn-frame-result-okp frame))
        frame
      (if (not (and (equal (fn-frame-result-magic frame) *fn-tj-magic*)
                    (equal (fn-frame-result-version frame) *fn-tj-version*)))
          (fn-frame-error :magic)
        (let ((code (fn-frame-result-kind frame)))
          (if (or (not (posp code)) (< (len *fn-tj-kinds*) code))
              (fn-frame-error :kind)
            (let* ((kind (fn-frame-item (- code 1) *fn-tj-kinds*))
                   (spec (fn-tj-spec-for kind)))
              (if (equal spec :none)
                  (fn-frame-error :kind)
                (let ((parsed (fn-frame-fields-parse
                               spec (fn-frame-result-payload frame))))
                  (if (not (fn-frame-parse-okp parsed))
                      (fn-frame-error (fn-frame-parse-value parsed))
                    (fn-frame-ok *fn-tj-magic* *fn-tj-version* kind
                                 (fn-frame-parse-value parsed))))))))))))

(verify-guards fn-tj-decode
  :hints (("Goal" :in-theory (enable fn-frame-fields-vocabulary
                                     fn-frame-record-vocabulary
                                     fn-frame-octet-vocabulary
                                     fn-frame-codec-vocabulary))))

; The logical record a decoded frame carries.
(defun fn-tj-frame-record (frame)
  (declare (xargs :guard t))
  (cons (fn-frame-result-kind frame) (fn-frame-result-payload frame)))

; The specification pair, stated against A-CRYPTO.  Not executable.
(defun fn-tj-seal (r)
  (declare (xargs :guard (fn-tj-record-okp r) :verify-guards nil))
  (fn-tj-encode r (fn-frame-digest
                   (fn-frame-protected *fn-tj-magic* *fn-tj-version*
                                       (fn-tj-code r) (fn-tj-payload r)))))

(defun fn-tj-open (octets)
  (declare (xargs :guard (fn-cbor-octet-listp octets) :verify-guards nil))
  (fn-tj-decode octets (fn-frame-digest (fn-frame-protected-prefix octets))))

(defun fn-tj-seal-journal (records)
  (declare (xargs :guard (fn-tj-records-okp records) :verify-guards nil))
  (if (consp records)
      (cons (fn-tj-seal (car records)) (fn-tj-seal-journal (cdr records)))
    nil))

; The digests a correct host supplies for a list of frames.
(defun fn-tj-digests-of (frames)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp frames)
      (cons (fn-frame-digest (fn-frame-protected-prefix (car frames)))
            (fn-tj-digests-of (cdr frames)))
    nil))

; Replay over frames.  A frame that does not open is a typed `:corrupt`
; fault carrying the frame decoder's reason; the state is the one before it.
(defun fn-tj-replay-frames (st frames index)
  (declare (xargs :guard t :verify-guards nil :measure (acl2-count frames)))
  (if (consp frames)
      (let ((frame (fn-tj-open (car frames))))
        (if (not (fn-frame-result-okp frame))
            (list :fault (list :corrupt (fn-frame-item 1 frame)) st index)
          (let ((step (fn-tj-apply st (fn-tj-frame-record frame))))
            (if (equal (fn-frame-item 0 step) :ok)
                (fn-tj-replay-frames (fn-frame-item 1 step) (cdr frames)
                                     (+ 1 (fix index)))
              (list :fault (fn-frame-item 1 step) st index)))))
    (list :ok st index)))

; The host entry point: the same replay with the host's digests.
(defun fn-tj-replay-frames-with (st frames digests index)
  (declare (xargs :guard t :measure (acl2-count frames)))
  (if (consp frames)
      (let ((frame (fn-tj-decode (car frames)
                                 (if (consp digests) (car digests) nil))))
        (if (not (fn-frame-result-okp frame))
            (list :fault (list :corrupt (fn-frame-item 1 frame)) st index)
          (let ((step (fn-tj-apply st (fn-tj-frame-record frame))))
            (if (equal (fn-frame-item 0 step) :ok)
                (fn-tj-replay-frames-with (fn-frame-item 1 step) (cdr frames)
                                          (if (consp digests) (cdr digests) nil)
                                          (+ 1 (fix index)))
              (list :fault (fn-frame-item 1 step) st index)))))
    (list :ok st index)))

; -----------------------------------------------------------------------------
; The only export of a complete entry: an unverified candidate.  No record
; kind and no result of this book carries an acceptance or a receipt.

(defun fn-tj-candidate (st label)
  (declare (xargs :guard t))
  (if (not (fn-transfer-statep st))
      nil
    (let ((entry (fn-transfer-find-entry label (fn-transfer-state-entries st))))
      (if (and entry (fn-transfer-entry-completep entry))
          (list :unverified
                (fn-transfer-assemble-from 0 (fn-transfer-entry-length entry)
                                           (fn-transfer-entry-chunks entry)))
        nil))))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md §2).  What leaves this book enabled: the
; record shape lemma `fn-tj-spec-for-is-spec-list`, and the list-recursive
; `fn-tj-records-okp` (the induction vocabulary of the frame keystones).  The
; accessors lose their definition rune only -- ground evaluation and type
; prescriptions still decide -- and every recognizer, transition, fold and
; codec entry point is withdrawn under one name.  A book above that must open
; one says so in a single `(local (in-theory (enable fn-tj-vocabulary)))`.

(in-theory (disable (:d fn-tj-kind) (:d fn-tj-label) (:d fn-tj-arg)
                    (:d fn-tj-octets) (:d fn-tj-outcome)
                    (:d fn-tj-profile-of) (:d fn-tj-profile-record)))

(deftheory fn-tj-vocabulary
  '(fn-tj-transition-recordp fn-tj-profile-recordp fn-tj-transition
    fn-tj-write fn-tj-journal fn-tj-run fn-tj-apply fn-tj-replay-records
    fn-tj-replay fn-tj-record-okp fn-tj-code fn-tj-payload fn-tj-encode
    fn-tj-decode fn-tj-frame-record fn-tj-seal fn-tj-open fn-tj-seal-journal
    fn-tj-digests-of fn-tj-replay-frames fn-tj-replay-frames-with
    fn-tj-candidate))

(in-theory (disable fn-tj-vocabulary))
