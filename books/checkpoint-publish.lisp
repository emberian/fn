; fn: the checkpoint generation machine (C2-09) over the file kernel's
; discipline.
;
; A generation is published exactly as the store publishes a record
; (books/store-files.lisp): the candidate bytes become data-durable under a
; staged name, are linked under their generation name, and the directory is
; barriered.  Only then may the generation be selected as authority, and the
; selection is itself the same three steps on the marker file, whose namespace
; step is an atomic old-or-new replacement.  Authority is the explicit marker,
; not a newest-valid rule: with a marker a corrupt selected generation is a
; distinct reported outcome (:corrupt), whereas a newest-valid rule would
; silently roll back to the predecessor.
;
; Every generation's bytes are the checkpoint codec's frame
; (books/checkpoint-codec.lisp) of the capture of a record prefix; the state
; carries that prefix and frontier as ghost fields so recovery can be related
; to the logical keystone fn-checkpoint-plus-suffix-equals-full-replay.  The
; host's digest (A-CRYPTO) is carried as a value: the model neither computes
; nor assumes anything about it beyond the frame's equality test.
;
; Crash points follow fn-sf-crash: a marker choice in {:old, :new} is live
; from the phase in which os.replace may have been issued, and a generation
; choice in {:absent, :present} from the phase in which os.link may have been
; issued.  A present generation is the exact data-durable candidate, never a
; partial file (the A-WRITE-ISOLATION premise the store already carries).

(in-package "ACL2")
(include-book "checkpoint-codec")
(include-book "journal-publish")
(include-book "defrecord")
; The codec withdraws its reader and encoder vocabulary at export
; (docs/proof-style.md s2); the proofs here induct with it.
(local (in-theory (enable fn-checkpoint-codec-vocabulary)))

(defconst *fn-cpp-phases*
  '(:idle :candidate-staged :candidate-data-durable :candidate-attempted
    :candidate-published :marker-staged :marker-data-durable :marker-attempted
    :fenced-candidate :fenced-marker))

; State: (:fn-cpp groups capacity phase authority candidate generations).
; An opaque record below its lemmas (docs/proof-style.md s1): nothing under
; this point opens it, and every rule about the machine is stated in
; accessor vocabulary.
(fn-defrecord fn-cpp
  :tag :fn-cpp
  :constructor (fn-cpp-make groups capacity phase authority candidate
                            generations)
  :fields ((fn-cpp-groups t) (fn-cpp-capacity t) (fn-cpp-phase t)
           (fn-cpp-authority t) (fn-cpp-candidate t) (fn-cpp-generations t))
  :recognizer nil)

; A generation entry: (name octets prefix frontier digest).  NAME is its
; position in the generation list; OCTETS are the framed bytes on disk;
; PREFIX, FRONTIER and DIGEST are the ghost record of how they were made.
(fn-defrecord fn-cpp-entry
  :constructor (fn-cpp-entry-make name octets prefix frontier digest)
  :fields ((fn-cpp-entry-name t) (fn-cpp-entry-octets t)
           (fn-cpp-entry-prefix t) (fn-cpp-entry-frontier t)
           (fn-cpp-entry-digest t))
  :recognizer nil)

(defun fn-cpp-entry-checkpoint (e groups capacity)
  (declare (xargs :guard t))
  (fn-checkpoint-capture-value
   (fn-checkpoint-capture groups capacity (fn-cpp-entry-prefix e)
                          (fn-cpp-entry-frontier e))))

; A prefix can become a generation when its capture succeeds, binds exactly
; this configuration, and encodes.
(defun fn-cpp-capturablep (groups capacity prefix frontier digest)
  (declare (xargs :guard t))
  (let* ((captured (fn-checkpoint-capture groups capacity prefix frontier))
         (checkpoint (fn-checkpoint-capture-value captured)))
    (and (equal (fn-frame-item 0 captured) :ok)
         (fn-cpc-encodablep checkpoint)
         (equal (fn-checkpoint-groups checkpoint) groups)
         (equal (fn-checkpoint-capacity checkpoint) capacity)
         (if (fn-cpc-encode checkpoint) t nil)
         (fn-frame-digestp digest))))

(defun fn-cpp-generation-octets (groups capacity prefix frontier digest)
  (declare (xargs :guard t))
  (fn-cpc-frame-encode
   (fn-checkpoint-capture-value
    (fn-checkpoint-capture groups capacity prefix frontier))
   digest))

(defun fn-cpp-entryp (e groups capacity)
  (declare (xargs :guard t))
  (and (fn-cpp-entry-shapep e)
       (natp (fn-cpp-entry-name e))
       (fn-cpp-capturablep groups capacity (fn-cpp-entry-prefix e)
                           (fn-cpp-entry-frontier e) (fn-cpp-entry-digest e))
       (equal (fn-cpp-entry-octets e)
              (fn-cpp-generation-octets groups capacity (fn-cpp-entry-prefix e)
                                        (fn-cpp-entry-frontier e)
                                        (fn-cpp-entry-digest e)))))

(defun fn-cpp-generation-listp (gens groups capacity index)
  (declare (xargs :guard t))
  (if (consp gens)
      (and (fn-cpp-entryp (car gens) groups capacity)
           (equal (fn-cpp-entry-name (car gens)) index)
           (fn-cpp-generation-listp (cdr gens) groups capacity
                                    (if (natp index) (+ 1 index) index)))
    (null gens)))

(defun fn-cpp-find (name gens)
  (declare (xargs :guard t))
  (if (consp gens)
      (if (equal (fn-cpp-entry-name (car gens)) name)
          (car gens)
        (fn-cpp-find name (cdr gens)))
    nil))

(defun fn-cpp-unpublished-phasep (phase)
  (declare (xargs :guard t))
  (if (member-equal phase '(:candidate-staged :candidate-data-durable
                            :candidate-attempted :fenced-candidate))
      t nil))

(defun fn-cpp-published-phasep (phase)
  (declare (xargs :guard t))
  (if (member-equal phase '(:candidate-published :marker-staged
                            :marker-data-durable :marker-attempted
                            :fenced-marker))
      t nil))

(defun fn-cpp-candidate-okp (phase candidate gens groups capacity)
  (declare (xargs :guard t))
  (cond ((equal phase :idle) (null candidate))
        ((fn-cpp-unpublished-phasep phase)
         (and (fn-cpp-entryp candidate groups capacity)
              (equal (fn-cpp-entry-name candidate) (len gens))))
        ((fn-cpp-published-phasep phase)
         (and (fn-cpp-entryp candidate groups capacity)
              (equal (fn-cpp-find (fn-cpp-entry-name candidate) gens)
                     candidate)))
        (t nil)))

(defun fn-cpp-statep (s)
  (declare (xargs :guard t))
  (and (fn-cpp-shapep s)
       (if (member-equal (fn-cpp-phase s) *fn-cpp-phases*) t nil)
       (fn-cpp-generation-listp (fn-cpp-generations s) (fn-cpp-groups s)
                                (fn-cpp-capacity s) 0)
       (or (null (fn-cpp-authority s))
           (if (fn-cpp-find (fn-cpp-authority s) (fn-cpp-generations s)) t nil))
       (fn-cpp-candidate-okp (fn-cpp-phase s) (fn-cpp-candidate s)
                             (fn-cpp-generations s) (fn-cpp-groups s)
                             (fn-cpp-capacity s))))

(defun fn-cpp-initial (groups capacity)
  (declare (xargs :guard t))
  (fn-cpp-make groups capacity :idle nil nil nil))

; -----------------------------------------------------------------------------
; Generation publication: stage, data barrier, link, directory barrier

(defun fn-cpp-stage (s prefix frontier digest)
  (declare (xargs :guard t))
  (if (and (fn-cpp-statep s) (equal (fn-cpp-phase s) :idle)
           (fn-cpp-capturablep (fn-cpp-groups s) (fn-cpp-capacity s)
                               prefix frontier digest))
      (fn-cpp-make (fn-cpp-groups s) (fn-cpp-capacity s) :candidate-staged
                   (fn-cpp-authority s)
                   (fn-cpp-entry-make (len (fn-cpp-generations s))
                                      (fn-cpp-generation-octets
                                       (fn-cpp-groups s) (fn-cpp-capacity s)
                                       prefix frontier digest)
                                      prefix frontier digest)
                   (fn-cpp-generations s))
    s))

(defun fn-cpp-candidate-file-result (s result)
  (declare (xargs :guard t))
  (if (and (fn-cpp-statep s) (equal (fn-cpp-phase s) :candidate-staged))
      (cond ((equal result :ok)
             (fn-cpp-make (fn-cpp-groups s) (fn-cpp-capacity s)
                          :candidate-data-durable (fn-cpp-authority s)
                          (fn-cpp-candidate s) (fn-cpp-generations s)))
            ((equal result :known-fail)
             (fn-cpp-make (fn-cpp-groups s) (fn-cpp-capacity s) :idle
                          (fn-cpp-authority s) nil (fn-cpp-generations s)))
            (t s))
    s))

(defun fn-cpp-candidate-link-result (s result)
  (declare (xargs :guard t))
  (if (and (fn-cpp-statep s) (equal (fn-cpp-phase s) :candidate-data-durable))
      (cond ((equal result :ok)
             (fn-cpp-make (fn-cpp-groups s) (fn-cpp-capacity s)
                          :candidate-attempted (fn-cpp-authority s)
                          (fn-cpp-candidate s) (fn-cpp-generations s)))
            ((equal result :error)
             (fn-cpp-make (fn-cpp-groups s) (fn-cpp-capacity s)
                          :fenced-candidate (fn-cpp-authority s)
                          (fn-cpp-candidate s) (fn-cpp-generations s)))
            (t s))
    s))

(defun fn-cpp-candidate-dir-result (s result)
  (declare (xargs :guard t))
  (if (and (fn-cpp-statep s) (equal (fn-cpp-phase s) :candidate-attempted))
      (cond ((equal result :ok)
             (fn-cpp-make (fn-cpp-groups s) (fn-cpp-capacity s)
                          :candidate-published (fn-cpp-authority s)
                          (fn-cpp-candidate s)
                          (fn-ag-append (fn-cpp-generations s)
                                        (list (fn-cpp-candidate s)))))
            ((equal result :error)
             (fn-cpp-make (fn-cpp-groups s) (fn-cpp-capacity s)
                          :fenced-candidate (fn-cpp-authority s)
                          (fn-cpp-candidate s) (fn-cpp-generations s)))
            (t s))
    s))

; -----------------------------------------------------------------------------
; Selection: stage the marker, data barrier, atomic replace, directory barrier

(defun fn-cpp-select (s)
  (declare (xargs :guard t))
  (if (and (fn-cpp-statep s) (equal (fn-cpp-phase s) :candidate-published))
      (fn-cpp-make (fn-cpp-groups s) (fn-cpp-capacity s) :marker-staged
                   (fn-cpp-authority s) (fn-cpp-candidate s)
                   (fn-cpp-generations s))
    s))

(defun fn-cpp-marker-file-result (s result)
  (declare (xargs :guard t))
  (if (and (fn-cpp-statep s) (equal (fn-cpp-phase s) :marker-staged))
      (cond ((equal result :ok)
             (fn-cpp-make (fn-cpp-groups s) (fn-cpp-capacity s)
                          :marker-data-durable (fn-cpp-authority s)
                          (fn-cpp-candidate s) (fn-cpp-generations s)))
            ((equal result :known-fail)
             (fn-cpp-make (fn-cpp-groups s) (fn-cpp-capacity s)
                          :candidate-published (fn-cpp-authority s)
                          (fn-cpp-candidate s) (fn-cpp-generations s)))
            (t s))
    s))

(defun fn-cpp-marker-replace-result (s result)
  (declare (xargs :guard t))
  (if (and (fn-cpp-statep s) (equal (fn-cpp-phase s) :marker-data-durable))
      (cond ((equal result :ok)
             (fn-cpp-make (fn-cpp-groups s) (fn-cpp-capacity s)
                          :marker-attempted (fn-cpp-authority s)
                          (fn-cpp-candidate s) (fn-cpp-generations s)))
            ((equal result :error)
             (fn-cpp-make (fn-cpp-groups s) (fn-cpp-capacity s)
                          :fenced-marker (fn-cpp-authority s)
                          (fn-cpp-candidate s) (fn-cpp-generations s)))
            (t s))
    s))

; The one step that changes authority: the marker's directory barrier.
(defun fn-cpp-marker-dir-result (s result)
  (declare (xargs :guard t))
  (if (and (fn-cpp-statep s) (equal (fn-cpp-phase s) :marker-attempted))
      (cond ((equal result :ok)
             (fn-cpp-make (fn-cpp-groups s) (fn-cpp-capacity s) :idle
                          (fn-cpp-entry-name (fn-cpp-candidate s))
                          nil (fn-cpp-generations s)))
            ((equal result :error)
             (fn-cpp-make (fn-cpp-groups s) (fn-cpp-capacity s)
                          :fenced-marker (fn-cpp-authority s)
                          (fn-cpp-candidate s) (fn-cpp-generations s)))
            (t s))
    s))

; The native checkpoint adapter drives marker replacement without retaining
; the publication machine's ghost generations.  These three functions are
; its decision surface.  Their phases are deliberately the phases above: the
; correspondence theorem below says the phase-only driver is exactly the
; projection of the full machine, rather than a second replacement policy.
(defun fn-cpp-marker-driver-action (phase)
  (declare (xargs :guard t))
  (cond ((equal phase :marker-staged) :stage-and-file-barrier)
        ((equal phase :marker-data-durable) :replace)
        ((equal phase :marker-attempted) :directory-barrier)
        (t :done)))

(defun fn-cpp-marker-driver-step (phase result)
  (declare (xargs :guard t))
  (cond ((equal phase :marker-staged)
         (cond ((equal result :ok) :marker-data-durable)
               ((equal result :known-fail) :candidate-published)
               (t phase)))
        ((equal phase :marker-data-durable)
         (cond ((equal result :ok) :marker-attempted)
               ((equal result :error) :fenced-marker)
               (t phase)))
        ((equal phase :marker-attempted)
         (cond ((equal result :ok) :idle)
               ((equal result :error) :fenced-marker)
               (t phase)))
        (t phase)))

(defun fn-cpp-marker-driver-outcome (phase)
  (declare (xargs :guard t))
  (cond ((equal phase :idle) :durable)
        ((equal phase :candidate-published) :refused)
        ((equal phase :fenced-marker) :uncertain)
        (t :pending)))

(defun fn-cpp-marker-step (s result)
  (declare (xargs :guard t))
  (cond ((equal (fn-cpp-phase s) :marker-staged)
         (fn-cpp-marker-file-result s result))
        ((equal (fn-cpp-phase s) :marker-data-durable)
         (fn-cpp-marker-replace-result s result))
        ((equal (fn-cpp-phase s) :marker-attempted)
         (fn-cpp-marker-dir-result s result))
        (t s)))

; The generation namespace is parsed at the host boundary, but choosing the
; next generation and distinguishing a gap from uint32 exhaustion is an ACL2
; decision.  NAMES must be ascending and gap-free from zero.
(defun fn-cpp-next-generation-from (names expected)
  (declare (xargs :guard t))
  (cond ((not (fn-record-uint32p expected)) :exhausted)
        ((null names) expected)
        ((atom names) :bad)
        ((equal (car names) expected)
         (fn-cpp-next-generation-from (cdr names) (+ 1 expected)))
        (t :bad)))

(defun fn-cpp-next-generation (names)
  (declare (xargs :guard t))
  (fn-cpp-next-generation-from names 0))

; Authorize the shared immutable publication machine only when the caller's
; boundary observations establish exclusive authority, a gap-free generation
; namespace, and absence of the exact final name.  The raw executor receives
; the returned fn-jpub state; it never manufactures authority itself.
(defun fn-cpp-publication-initial
  (names proposed-generation exclusivep final-absentp)
  (declare (xargs :guard t :verify-guards nil))
  (let ((next (fn-cpp-next-generation names)))
    (cond ((equal next :bad) '(:error :namespace))
          ((equal next :exhausted) '(:error :exhausted))
          ((not (equal proposed-generation next)) '(:error :generation))
          ((not (equal exclusivep t)) '(:error :authority))
          ((not (equal final-absentp t)) '(:error :occupied))
          (t (list :ok next (fn-jpub-initial t))))))

; -----------------------------------------------------------------------------
; Crash images and recovery

(defun fn-cpp-choicep (marker-choice generation-choice)
  (declare (xargs :guard t))
  (and (or (equal marker-choice :old) (equal marker-choice :new))
       (or (equal generation-choice :absent)
           (equal generation-choice :present))))

; The generation may be present from :candidate-data-durable: os.link is
; issued after the data barrier and before its result is observed.
(defun fn-cpp-candidate-present-visiblep (s)
  (declare (xargs :guard t))
  (if (member-equal (fn-cpp-phase s)
                    '(:candidate-data-durable :candidate-attempted
                      :fenced-candidate))
      t nil))

; The new marker may be visible from :marker-data-durable: os.replace is
; issued after the marker's data barrier and before its result is observed.
(defun fn-cpp-marker-new-visiblep (s)
  (declare (xargs :guard t))
  (if (member-equal (fn-cpp-phase s)
                    '(:marker-data-durable :marker-attempted :fenced-marker))
      t nil))

(fn-defrecord fn-cpp-image
  :tag :fn-cpp-image
  :constructor (fn-cpp-image-make marker gens)
  :fields ((fn-cpp-image-marker t) (fn-cpp-image-generations t))
  :recognizer nil)

(defun fn-cpp-crash (s marker-choice generation-choice)
  (declare (xargs :guard t))
  (if (and (fn-cpp-statep s) (fn-cpp-choicep marker-choice generation-choice))
      (fn-cpp-image-make
       (if (and (fn-cpp-marker-new-visiblep s) (equal marker-choice :new))
           (fn-cpp-entry-name (fn-cpp-candidate s))
         (fn-cpp-authority s))
       (if (and (fn-cpp-candidate-present-visiblep s)
                (equal generation-choice :present))
           (fn-ag-append (fn-cpp-generations s) (list (fn-cpp-candidate s)))
         (fn-cpp-generations s)))
    (fn-cpp-image-make (fn-cpp-authority s) (fn-cpp-generations s))))

(defun fn-cpp-imagep (image groups capacity)
  (declare (xargs :guard t))
  (and (fn-cpp-image-shapep image)
       (fn-cpp-generation-listp (fn-cpp-image-generations image) groups capacity 0)
       (or (null (fn-cpp-image-marker image))
           (if (fn-cpp-find (fn-cpp-image-marker image)
                            (fn-cpp-image-generations image))
               t nil))))

; Media damage to one generation: its bytes are replaced, nothing else moves.
(defun fn-cpp-replace-octets (name octets gens)
  (declare (xargs :guard t))
  (if (consp gens)
      (if (equal (fn-cpp-entry-name (car gens)) name)
          (cons (fn-cpp-entry-make name octets
                                   (fn-cpp-entry-prefix (car gens))
                                   (fn-cpp-entry-frontier (car gens))
                                   (fn-cpp-entry-digest (car gens)))
                (cdr gens))
        (cons (car gens) (fn-cpp-replace-octets name octets (cdr gens))))
    nil))

(defun fn-cpp-corrupt (image name octets)
  (declare (xargs :guard t))
  (fn-cpp-image-make (fn-cpp-image-marker image)
                     (fn-cpp-replace-octets name octets
                                            (fn-cpp-image-generations image))))

; Recovery reads the marker, then only the generation it names.  DIGEST is
; the host's digest over that generation's bytes; FRONTIER and COUNT are the
; observed durable allocator frontier and record count.  Three outcomes are
; kept distinct: (:none), (:ok name checkpoint), (:corrupt name reason); a
; marker naming an absent generation is (:missing name).
(defun fn-cpp-recover (image groups capacity frontier count digest)
  (declare (xargs :guard t))
  (let ((marker (fn-cpp-image-marker image)))
    (if (null marker)
        (list :none)
      (let ((entry (fn-cpp-find marker (fn-cpp-image-generations image))))
        (if (null entry)
            (list :missing marker)
          (let ((opened (fn-cpc-frame-decode (fn-cpp-entry-octets entry) digest
                                             groups capacity frontier count)))
            (if (fn-cpc-result-okp opened)
                (list :ok marker (fn-cpc-result-value opened))
              (list :corrupt marker opened))))))))

(defun fn-cpp-recover-okp (result)
  (declare (xargs :guard t))
  (equal (fn-frame-item 0 result) :ok))
(defun fn-cpp-recover-name (result)
  (declare (xargs :guard t))
  (fn-frame-item 1 result))
(defun fn-cpp-recover-checkpoint (result)
  (declare (xargs :guard t))
  (fn-frame-item 2 result))

; -----------------------------------------------------------------------------
; Facts about generation lists

(local (in-theory (enable fn-frame-item)))
(local (in-theory (disable fn-cpp-entryp fn-cpp-capturablep
                           fn-cpp-generation-octets fn-cpc-frame-decode
                           fn-cpc-frame-encode fn-checkpoint-capture
                           fn-checkpoint-capture-value fn-cpc-encodablep
                           fn-cpc-encode fn-checkpointp)))

(defthm fn-cpp-generation-listp-true-listp
  (implies (fn-cpp-generation-listp gens groups capacity index)
           (true-listp gens)))

(defthm fn-cpp-find-beyond-list
  (implies (and (fn-cpp-generation-listp gens groups capacity index)
                (natp index)
                (<= (+ index (len gens)) name))
           (equal (fn-cpp-find name gens) nil)))

(defthm fn-cpp-find-is-entry
  (implies (and (fn-cpp-generation-listp gens groups capacity index)
                (fn-cpp-find name gens))
           (fn-cpp-entryp (fn-cpp-find name gens) groups capacity)))

(defthm fn-cpp-find-has-name
  (implies (fn-cpp-find name gens)
           (equal (fn-cpp-entry-name (fn-cpp-find name gens)) name)))

; The three recognizer shape facts (docs/proof-style.md s1), forward-chaining
; only: they replace what type reasoning gave while the records opened.
(defthm fn-cpp-entryp-forward-shape
  (implies (fn-cpp-entryp e groups capacity) (and (consp e) (true-listp e)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-cpp-entryp))))
(defthm fn-cpp-statep-forward-shape
  (implies (fn-cpp-statep s) (and (consp s) (true-listp s)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-cpp-statep))))
(defthm fn-cpp-imagep-forward-shape
  (implies (fn-cpp-imagep image groups capacity)
           (and (consp image) (true-listp image)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-cpp-imagep))))

(defthm fn-cpp-generation-listp-append
  (implies (and (fn-cpp-generation-listp gens groups capacity index)
                (natp index)
                (fn-cpp-entryp e groups capacity)
                (equal (fn-cpp-entry-name e) (+ index (len gens))))
           (fn-cpp-generation-listp (append gens (list e)) groups capacity index)))

; The appended entry must BE an entry.  Without that hypothesis the rule is
; false: fn-cpp-find returns the matching element, so a NIL element of GENS
; that matches NAME is a hit the recursion reports as a miss, and the
; realignment (which withdrew the accessor unfold) made that branch visible.
; An entry's name is a natural, hence non-NIL, which refutes it.
(defthm fn-cpp-find-of-append
  (implies (fn-cpp-entry-name e)
           (equal (fn-cpp-find name (append gens (list e)))
                  (if (fn-cpp-find name gens)
                      (fn-cpp-find name gens)
                    (if (equal (fn-cpp-entry-name e) name) e nil)))))

(defthm fn-cpp-find-of-replace-same
  (implies (fn-cpp-find name gens)
           (and (fn-cpp-find name (fn-cpp-replace-octets name octets gens))
                (equal (fn-cpp-entry-octets
                        (fn-cpp-find name (fn-cpp-replace-octets name octets gens)))
                       octets))))

(defthm fn-cpp-find-of-replace-other
  (implies (not (equal name other))
           (equal (fn-cpp-find name (fn-cpp-replace-octets other octets gens))
                  (fn-cpp-find name gens))))

; -----------------------------------------------------------------------------
; The invariant is preserved by every step

(defthm fn-cpp-initial-is-state
  (fn-cpp-statep (fn-cpp-initial groups capacity)))

(local
 (defthm fn-cpp-staged-entry-is-entry
   (implies (and (fn-cpp-capturablep groups capacity prefix frontier digest)
                 (natp name))
            (fn-cpp-entryp (fn-cpp-entry-make
                            name (fn-cpp-generation-octets groups capacity prefix
                                                           frontier digest)
                            prefix frontier digest)
                           groups capacity))
   :hints (("Goal" :in-theory (enable fn-cpp-entryp)))))

(defthm fn-cpp-stage-preserves-state
  (implies (fn-cpp-statep s)
           (fn-cpp-statep (fn-cpp-stage s prefix frontier digest))))

(defthm fn-cpp-candidate-file-result-preserves-state
  (implies (fn-cpp-statep s)
           (fn-cpp-statep (fn-cpp-candidate-file-result s result))))

(defthm fn-cpp-candidate-link-result-preserves-state
  (implies (fn-cpp-statep s)
           (fn-cpp-statep (fn-cpp-candidate-link-result s result))))

(defthm fn-cpp-candidate-dir-result-preserves-state
  (implies (fn-cpp-statep s)
           (fn-cpp-statep (fn-cpp-candidate-dir-result s result))))

(defthm fn-cpp-select-preserves-state
  (implies (fn-cpp-statep s)
           (fn-cpp-statep (fn-cpp-select s))))

(defthm fn-cpp-marker-file-result-preserves-state
  (implies (fn-cpp-statep s)
           (fn-cpp-statep (fn-cpp-marker-file-result s result))))

(defthm fn-cpp-marker-replace-result-preserves-state
  (implies (fn-cpp-statep s)
           (fn-cpp-statep (fn-cpp-marker-replace-result s result))))

(defthm fn-cpp-marker-dir-result-preserves-state
  (implies (fn-cpp-statep s)
           (fn-cpp-statep (fn-cpp-marker-dir-result s result))))

(defthm fn-cpp-marker-step-preserves-state
  (implies (fn-cpp-statep s)
           (fn-cpp-statep (fn-cpp-marker-step s result))))

; This is the native marker driver's correspondence theorem.  The host calls
; FN-CPP-MARKER-DRIVER-STEP and retains only its returned phase; for every
; reachable marker phase that value is the full checkpoint publication
; machine's next phase under the same observed syscall result.
(defthm fn-cpp-marker-driver-step-corresponds
  (implies (fn-cpp-statep s)
           (equal (fn-cpp-marker-driver-step (fn-cpp-phase s) result)
                  (fn-cpp-phase (fn-cpp-marker-step s result))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-cpp-marker-step
                                      fn-cpp-marker-driver-step))))

(defthm fn-cpp-publication-initial-authorizes-state
  (implies (equal (car (fn-cpp-publication-initial
                        names proposed-generation exclusivep final-absentp))
                  :ok)
           (and (equal (car (cdr (fn-cpp-publication-initial
                                  names proposed-generation exclusivep
                                  final-absentp)))
                       proposed-generation)
                (fn-jpub-statep
                 (car (cdr (cdr (fn-cpp-publication-initial
                                 names proposed-generation exclusivep
                                 final-absentp)))))
                (fn-jpub-authorityp
                 (car (cdr (cdr (fn-cpp-publication-initial
                                 names proposed-generation exclusivep
                                 final-absentp)))))))
  :hints (("Goal" :in-theory (enable fn-cpp-publication-initial
                                      fn-cpp-next-generation
                                      fn-jpub-initial fn-jpub-state
                                      fn-jpub-statep fn-jpub-authorityp
                                      fn-jpub-phase fn-jpub-outcome
                                      fn-jpub-phasep fn-jpub-outcomep))))

(defthm fn-cpp-crash-image-is-image
  (implies (fn-cpp-statep s)
           (fn-cpp-imagep (fn-cpp-crash s marker-choice generation-choice)
                          (fn-cpp-groups s) (fn-cpp-capacity s))))

; -----------------------------------------------------------------------------
; KEYSTONE 1: after any cut, the image's authority is the previous authority
; or the complete new generation, never a partial one.
;
; The :new marker choice exists only in the marker phases, which the machine
; reaches only through :candidate-published, where the candidate was appended
; to the generation list after its directory barrier.  So whenever the image
; names the candidate, the image also holds the candidate's complete bytes.

(defthm fn-cpp-crash-selects-old-authority-or-complete-candidate
  (implies (and (fn-cpp-statep s)
                (fn-cpp-choicep marker-choice generation-choice))
           (let ((image (fn-cpp-crash s marker-choice generation-choice)))
             (or (equal (fn-cpp-image-marker image) (fn-cpp-authority s))
                 (and (fn-cpp-marker-new-visiblep s)
                      (equal (fn-cpp-image-marker image)
                             (fn-cpp-entry-name (fn-cpp-candidate s)))
                      (equal (fn-cpp-find (fn-cpp-image-marker image)
                                          (fn-cpp-image-generations image))
                             (fn-cpp-candidate s))
                      (fn-cpp-entryp (fn-cpp-candidate s)
                                     (fn-cpp-groups s) (fn-cpp-capacity s))))))
  :rule-classes nil)

; Before a selection is attempted the image's marker is exactly the old
; authority, whichever choices the crash makes.
(defthm fn-cpp-crash-marker-is-authority-before-selection-attempted
  (implies (and (fn-cpp-statep s)
                (not (fn-cpp-marker-new-visiblep s)))
           (equal (fn-cpp-image-marker
                   (fn-cpp-crash s marker-choice generation-choice))
                  (fn-cpp-authority s))))

; -----------------------------------------------------------------------------
; KEYSTONE 2: recovery of a complete selected generation yields its capture.

(local
 (defthm fn-cpp-entry-decodes
   (implies (and (fn-cpp-entryp e groups capacity)
                 (equal digest (fn-cpp-entry-digest e))
                 (natp frontier)
                 (<= (fn-checkpoint-frontier (fn-cpp-entry-checkpoint e groups capacity))
                     frontier)
                 (natp count)
                 (<= (fn-checkpoint-sequence (fn-cpp-entry-checkpoint e groups capacity))
                     count))
            (equal (fn-cpc-frame-decode (fn-cpp-entry-octets e) digest groups
                                        capacity frontier count)
                   (list :ok (fn-cpp-entry-checkpoint e groups capacity))))
   :hints (("Goal"
            :use ((:instance fn-cpc-frame-decode-of-encode
                             (x (fn-cpp-entry-checkpoint e groups capacity))
                             (digest (fn-cpp-entry-digest e))
                             (max-frontier frontier) (max-sequence count)))
            :in-theory (e/d (fn-cpp-entryp fn-cpp-capturablep
                             fn-cpp-generation-octets fn-cpp-entry-checkpoint)
                            (fn-cpc-frame-decode-of-encode))))))

(defthm fn-cpp-recover-selects-complete-generation
  (implies (and (fn-cpp-imagep image groups capacity)
                (fn-cpp-image-marker image)
                (equal digest
                       (fn-cpp-entry-digest
                        (fn-cpp-find (fn-cpp-image-marker image)
                                     (fn-cpp-image-generations image))))
                (natp frontier)
                (<= (fn-checkpoint-frontier
                     (fn-cpp-entry-checkpoint
                      (fn-cpp-find (fn-cpp-image-marker image)
                                   (fn-cpp-image-generations image))
                      groups capacity))
                    frontier)
                (natp count)
                (<= (fn-checkpoint-sequence
                     (fn-cpp-entry-checkpoint
                      (fn-cpp-find (fn-cpp-image-marker image)
                                   (fn-cpp-image-generations image))
                      groups capacity))
                    count))
           (equal (fn-cpp-recover image groups capacity frontier count digest)
                  (list :ok (fn-cpp-image-marker image)
                        (fn-cpp-entry-checkpoint
                         (fn-cpp-find (fn-cpp-image-marker image)
                                      (fn-cpp-image-generations image))
                         groups capacity))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cpp-find-is-entry
                            (gens (fn-cpp-image-generations image))
                            (name (fn-cpp-image-marker image))
                            (index 0)))
           :in-theory (disable fn-cpp-find-is-entry fn-cpp-find))))

; -----------------------------------------------------------------------------
; KEYSTONE 3: corruption of the selected generation is reported, not rolled
; back.  Whatever bytes replace the selected generation, recovery's verdict
; is (:corrupt name reason) whenever the codec refuses them; it is neither
; :ok for any generation nor :none.  Corruption of an unselected generation
; is invisible to recovery, which is the other half of "only the marker's
; generation is consulted".

(defthm fn-cpp-recover-reports-corruption
  (implies (and (natp name)
                (equal (fn-cpp-image-marker image) name)
                (fn-cpp-find name (fn-cpp-image-generations image))
                (not (fn-cpc-result-okp
                      (fn-cpc-frame-decode octets digest groups capacity
                                           frontier count))))
           (equal (fn-cpp-recover (fn-cpp-corrupt image name octets)
                                  groups capacity frontier count digest)
                  (list :corrupt name
                        (fn-cpc-frame-decode octets digest groups capacity
                                             frontier count))))
  :hints (("Goal" :in-theory (disable fn-cpp-find fn-cpp-replace-octets))))

(defthm fn-cpp-corrupting-unselected-generation-is-invisible
  (implies (not (equal (fn-cpp-image-marker image) name))
           (equal (fn-cpp-recover (fn-cpp-corrupt image name octets)
                                  groups capacity frontier count digest)
                  (fn-cpp-recover image groups capacity frontier count digest)))
  :hints (("Goal" :in-theory (disable fn-cpp-find fn-cpp-replace-octets))))

; -----------------------------------------------------------------------------
; KEYSTONE 4: the selected checkpoint plus the suffix equals full
; authoritative replay.  Composition of keystone 2 with the logical keystone
; fn-checkpoint-plus-suffix-equals-full-replay through the ghost prefix.

(defthm fn-cpp-selected-plus-suffix-equals-full-replay
  (implies (and (fn-cpp-imagep image groups capacity)
                (fn-cpp-image-marker image)
                (equal digest
                       (fn-cpp-entry-digest
                        (fn-cpp-find (fn-cpp-image-marker image)
                                     (fn-cpp-image-generations image))))
                (natp frontier)
                (<= (fn-checkpoint-frontier
                     (fn-cpp-entry-checkpoint
                      (fn-cpp-find (fn-cpp-image-marker image)
                                   (fn-cpp-image-generations image))
                      groups capacity))
                    frontier)
                (natp count)
                (<= (fn-checkpoint-sequence
                     (fn-cpp-entry-checkpoint
                      (fn-cpp-find (fn-cpp-image-marker image)
                                   (fn-cpp-image-generations image))
                      groups capacity))
                    count)
                (fn-checkpoint-admissible-splitp
                 groups capacity
                 (fn-cpp-entry-prefix
                  (fn-cpp-find (fn-cpp-image-marker image)
                               (fn-cpp-image-generations image)))
                 (fn-cpp-entry-frontier
                  (fn-cpp-find (fn-cpp-image-marker image)
                               (fn-cpp-image-generations image)))
                 suffix final-frontier))
           (equal (fn-checkpoint-restore
                   (fn-cpp-recover-checkpoint
                    (fn-cpp-recover image groups capacity frontier count digest))
                   groups capacity suffix final-frontier)
                  (fn-checkpoint-full-replay
                   groups capacity
                   (append (fn-cpp-entry-prefix
                            (fn-cpp-find (fn-cpp-image-marker image)
                                         (fn-cpp-image-generations image)))
                           suffix)
                   final-frontier)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cpp-recover-selects-complete-generation)
                 (:instance fn-checkpoint-plus-suffix-equals-full-replay
                            (prefix (fn-cpp-entry-prefix
                                     (fn-cpp-find (fn-cpp-image-marker image)
                                                  (fn-cpp-image-generations image))))
                            (checkpoint-frontier
                             (fn-cpp-entry-frontier
                              (fn-cpp-find (fn-cpp-image-marker image)
                                           (fn-cpp-image-generations image))))))
           :in-theory (e/d (fn-cpp-entry-checkpoint)
                           (fn-cpp-recover fn-cpp-find fn-cpp-imagep
                            fn-checkpoint-restore fn-checkpoint-full-replay
                            fn-checkpoint-admissible-splitp
                            fn-cpp-recover-selects-complete-generation
                            fn-checkpoint-plus-suffix-equals-full-replay)))))

; -----------------------------------------------------------------------------
; KEYSTONE 5: the old authority is retained until the selection is durable.
; No step but the marker's directory barrier changes the authority, and no
; step removes a published generation.

(defthm fn-cpp-authority-retained-until-selection-durable
  (and (equal (fn-cpp-authority (fn-cpp-stage s prefix frontier digest))
              (fn-cpp-authority s))
       (equal (fn-cpp-authority (fn-cpp-candidate-file-result s result))
              (fn-cpp-authority s))
       (equal (fn-cpp-authority (fn-cpp-candidate-link-result s result))
              (fn-cpp-authority s))
       (equal (fn-cpp-authority (fn-cpp-candidate-dir-result s result))
              (fn-cpp-authority s))
       (equal (fn-cpp-authority (fn-cpp-select s)) (fn-cpp-authority s))
       (equal (fn-cpp-authority (fn-cpp-marker-file-result s result))
              (fn-cpp-authority s))
       (equal (fn-cpp-authority (fn-cpp-marker-replace-result s result))
              (fn-cpp-authority s))
       (implies (not (and (equal (fn-cpp-phase s) :marker-attempted)
                          (equal result :ok)))
                (equal (fn-cpp-authority (fn-cpp-marker-dir-result s result))
                       (fn-cpp-authority s))))
  :hints (("Goal" :in-theory (disable fn-cpp-statep))))

; fn-cpp-find-of-append needs the appended element to BE an entry: its name
; must be non-NIL, or a NIL element of GENS that matches NAME is a hit the
; recursion reports as a miss.  Every transition that appends appends the
; state's own candidate, and fn-cpp-candidate-okp already says its name is a
; natural in every phase but :idle -- where nothing is appended.  Stated as a
; type-prescription as well, so the hypothesis is relieved by type reasoning
; and fn-cpp-statep stays closed at the keystone below.
(defthm fn-cpp-statep-candidate-name-is-a-natp
  (implies (and (fn-cpp-statep s)
                (not (equal (fn-cpp-phase s) :idle)))
           (natp (fn-cpp-entry-name (fn-cpp-candidate s))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable fn-cpp-statep fn-cpp-candidate-okp
                                     fn-cpp-entryp fn-cpp-published-phasep
                                     fn-cpp-unpublished-phasep))))

(defthm fn-cpp-published-generations-retained
  (implies (fn-cpp-find name (fn-cpp-generations s))
           (and (equal (fn-cpp-find name (fn-cpp-generations
                                          (fn-cpp-stage s prefix frontier digest)))
                       (fn-cpp-find name (fn-cpp-generations s)))
                (equal (fn-cpp-find name (fn-cpp-generations
                                          (fn-cpp-candidate-file-result s result)))
                       (fn-cpp-find name (fn-cpp-generations s)))
                (equal (fn-cpp-find name (fn-cpp-generations
                                          (fn-cpp-candidate-link-result s result)))
                       (fn-cpp-find name (fn-cpp-generations s)))
                (equal (fn-cpp-find name (fn-cpp-generations
                                          (fn-cpp-candidate-dir-result s result)))
                       (fn-cpp-find name (fn-cpp-generations s)))
                (equal (fn-cpp-find name (fn-cpp-generations (fn-cpp-select s)))
                       (fn-cpp-find name (fn-cpp-generations s)))
                (equal (fn-cpp-find name (fn-cpp-generations
                                          (fn-cpp-marker-file-result s result)))
                       (fn-cpp-find name (fn-cpp-generations s)))
                (equal (fn-cpp-find name (fn-cpp-generations
                                          (fn-cpp-marker-replace-result s result)))
                       (fn-cpp-find name (fn-cpp-generations s)))
                (equal (fn-cpp-find name (fn-cpp-generations
                                          (fn-cpp-marker-dir-result s result)))
                       (fn-cpp-find name (fn-cpp-generations s)))
                (equal (fn-cpp-find name (fn-cpp-image-generations
                                          (fn-cpp-crash s marker-choice
                                                        generation-choice)))
                       (fn-cpp-find name (fn-cpp-generations s)))))
  :hints (("Goal" :in-theory (disable fn-cpp-statep fn-cpp-find))))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md s2).  Withdrawn: the three recognizers
; and the candidate gate, the initial state, every transition, the crash and
; corruption operations, recovery, and the ghost projections that name a
; capture.  Withdrawn under a name: the generation-list and lookup vocabulary
; these proofs induct with, so a book above re-enables it in one line.
; Enabled on include: the record lemmas and the three forward-chaining shape
; facts per record, the eight -preserves-state keystones, and the five
; numbered keystones; the list-recursive definitions FN-CPP-GENERATION-LISTP,
; FN-CPP-FIND and FN-CPP-REPLACE-OCTETS (induction vocabulary, s8), the phase
; and choice glue predicates, and the result projections the host dispatches
; on.
(deftheory fn-checkpoint-publish-vocabulary
  '(fn-cpp-generation-listp-true-listp fn-cpp-find-beyond-list
    fn-cpp-find-is-entry fn-cpp-find-has-name fn-cpp-generation-listp-append
    fn-cpp-find-of-append fn-cpp-find-of-replace-same
    fn-cpp-find-of-replace-other))
(in-theory (disable fn-checkpoint-publish-vocabulary
                    fn-cpp-statep fn-cpp-entryp fn-cpp-imagep
                    fn-cpp-candidate-okp fn-cpp-initial
                    fn-cpp-stage fn-cpp-candidate-file-result
                    fn-cpp-candidate-link-result fn-cpp-candidate-dir-result
                    fn-cpp-select fn-cpp-marker-file-result
                    fn-cpp-marker-replace-result fn-cpp-marker-dir-result
                    fn-cpp-marker-step
                    fn-cpp-crash fn-cpp-corrupt fn-cpp-recover
                    fn-cpp-capturablep fn-cpp-generation-octets
                    fn-cpp-entry-checkpoint))
