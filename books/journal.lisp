; fn M2 storage slice: an executable isolated-slot journal and recovery model.
;
; This is deliberately a logical record model, not a byte format.  A slot's
; `:intact` / `:torn` tag abstracts a bounded frame/integrity check which a
; future codec must implement.  It neither chooses a frame grammar nor assumes
; a digest is injective (A-CRYPTO remains outside this book).
;
; A completed `fn-journal-barrier` is the model's A-DURABILITY event: every
; preceding volatile slot becomes durable.  `fn-journal-crash` uses that fact
; only while constructing a physical image.  Recovery is given neither
; durability bits nor host acknowledgements: it examines physical slot content
; and a separate durable acknowledgement anchor.  A-DURABILITY and
; A-WRITE-ISOLATION condition the claim that a completed barrier and its anchor
; survive intact and in order.  Volatile slots may be absent, torn, and appear
; in a different order.  This is not a claim about a real device.
;
; The anchor is deliberately small: it names the greatest transaction for which
; the host has already emitted success.  Thus a torn/missing acknowledged commit
; is a recovery fault, while a complete but unanchored commit may be published.
; No recovery rule consults a magical on-disk "acknowledged" flag.

(in-package "ACL2")

; -----------------------------------------------------------------------------
; Small records.  Object identities are natural numbers in this experiment;
; they stand for already validated content identities and do not define a hash.

(defun fn-journal-integrityp (x)
  (or (equal x :intact) (equal x :torn)))

(defun fn-journal-durabilityp (x)
  (or (equal x :volatile) (equal x :durable)))

(defun fn-journal-id-listp (xs)
  (if (consp xs)
      (and (natp (car xs))
           (not (member-equal (car xs) (cdr xs)))
           (fn-journal-id-listp (cdr xs)))
    (null xs)))

; Live slots have an implementation-only durability field:
; (:object txid object-id durability), (:commit txid referenced-object-ids durability).
(defun fn-journal-live-kind (slot) (car slot))
(defun fn-journal-live-txid (slot) (car (cdr slot)))
(defun fn-journal-live-data (slot) (car (cdr (cdr slot))))
(defun fn-journal-live-durability (slot) (car (cdr (cdr (cdr slot)))))

(defun fn-journal-make-live-object (txid object-id durability)
  (list :object txid object-id durability))

(defun fn-journal-make-live-commit (txid refs durability)
  (list :commit txid refs durability))

(defun fn-journal-live-slotp (slot)
  (and (true-listp slot)
       (equal (len slot) 4)
       (natp (fn-journal-live-txid slot))
       (fn-journal-durabilityp (fn-journal-live-durability slot))
       (if (equal (fn-journal-live-kind slot) :object)
           (natp (fn-journal-live-data slot))
         (and (equal (fn-journal-live-kind slot) :commit)
              (fn-journal-id-listp (fn-journal-live-data slot))))))

(defun fn-journal-live-listp (slots)
  (if (consp slots)
      (and (fn-journal-live-slotp (car slots))
           (fn-journal-live-listp (cdr slots)))
    (null slots)))

; Physical slots omit durability.  Recovery sees only these four fields.
(defun fn-journal-physical-kind (slot) (car slot))
(defun fn-journal-physical-txid (slot) (car (cdr slot)))
(defun fn-journal-physical-data (slot) (car (cdr (cdr slot))))
(defun fn-journal-physical-integrity (slot) (car (cdr (cdr (cdr slot)))))

(defun fn-journal-make-physical-object (txid object-id integrity)
  (list :object txid object-id integrity))

(defun fn-journal-make-physical-commit (txid refs integrity)
  (list :commit txid refs integrity))

(defun fn-journal-physical-slotp (slot)
  (and (true-listp slot)
       (equal (len slot) 4)
       (natp (fn-journal-physical-txid slot))
       (fn-journal-integrityp (fn-journal-physical-integrity slot))
       (if (equal (fn-journal-physical-kind slot) :object)
           (natp (fn-journal-physical-data slot))
         (and (equal (fn-journal-physical-kind slot) :commit)
              (fn-journal-id-listp (fn-journal-physical-data slot))))))

(defun fn-journal-materialize (slot integrity)
  (if (equal (fn-journal-live-kind slot) :object)
      (fn-journal-make-physical-object (fn-journal-live-txid slot)
                                       (fn-journal-live-data slot)
                                       integrity)
    (fn-journal-make-physical-commit (fn-journal-live-txid slot)
                                     (fn-journal-live-data slot)
                                     integrity)))

; -----------------------------------------------------------------------------
; Isolated append and barriers.  There is intentionally no mutation API which
; overwrites an existing slot.  Real layouts must justify that discipline under
; their write-unit/namespace assumptions (A-WRITE-ISOLATION).

(defun fn-journal-set-durable (slots)
  (if (consp slots)
      (cons (if (equal (fn-journal-live-durability (car slots)) :volatile)
                (if (equal (fn-journal-live-kind (car slots)) :object)
                    (fn-journal-make-live-object
                     (fn-journal-live-txid (car slots))
                     (fn-journal-live-data (car slots)) :durable)
                  (fn-journal-make-live-commit
                   (fn-journal-live-txid (car slots))
                   (fn-journal-live-data (car slots)) :durable))
              (car slots))
            (fn-journal-set-durable (cdr slots)))
    nil))

(defun fn-journal-object-bindingp (txid object-id slots)
  (if (consp slots)
      (or (and (equal (fn-journal-live-kind (car slots)) :object)
               (equal txid (fn-journal-live-txid (car slots)))
               (equal object-id (fn-journal-live-data (car slots))))
          (fn-journal-object-bindingp txid object-id (cdr slots)))
    nil))

(defun fn-journal-durable-objectp (txid object-id slots)
  (if (consp slots)
      (or (and (equal (fn-journal-live-kind (car slots)) :object)
               (equal txid (fn-journal-live-txid (car slots)))
               (equal object-id (fn-journal-live-data (car slots)))
               (equal (fn-journal-live-durability (car slots)) :durable))
          (fn-journal-durable-objectp txid object-id (cdr slots)))
    nil))

(defun fn-journal-durable-referencesp (txid refs slots)
  (if (consp refs)
      (and (fn-journal-durable-objectp txid (car refs) slots)
           (fn-journal-durable-referencesp txid (cdr refs) slots))
    t))

(defun fn-journal-durable-commitp (txid slots)
  (if (consp slots)
      (or (and (equal (fn-journal-live-kind (car slots)) :commit)
               (equal txid (fn-journal-live-txid (car slots)))
               (equal (fn-journal-live-durability (car slots)) :durable))
          (fn-journal-durable-commitp txid (cdr slots)))
    nil))

(defun fn-journal-commit-seenp (txid slots)
  (if (consp slots)
      (or (and (equal (fn-journal-live-kind (car slots)) :commit)
               (equal txid (fn-journal-live-txid (car slots))))
          (fn-journal-commit-seenp txid (cdr slots)))
    nil))

(defun fn-journal-stage-object (slots txid object-id)
  (if (and (fn-journal-live-listp slots)
           (natp txid) (natp object-id)
           (not (fn-journal-object-bindingp txid object-id slots)))
      (append slots (list (fn-journal-make-live-object txid object-id :volatile)))
    slots))

; A commit marker cannot even be staged until all of its named objects have
; crossed an earlier barrier.  A second barrier is needed before acknowledgement.
(defun fn-journal-stage-commit (slots txid refs)
  (if (and (fn-journal-live-listp slots)
           (natp txid) (fn-journal-id-listp refs)
           (fn-journal-durable-referencesp txid refs slots)
           (not (fn-journal-commit-seenp txid slots)))
      (append slots (list (fn-journal-make-live-commit txid refs :volatile)))
    slots))

(defun fn-journal-barrier (slots)
  (if (fn-journal-live-listp slots)
      (fn-journal-set-durable slots)
    slots))

; Host completions are inputs, never inferred from a socket write.  A known
; abort authorizes no success reply.  An indeterminate completion authorizes no
; further mutation: the caller must crash/recover using a physical image.  A
; `:durable` report is accepted only for an already barrier-protected marker.
; The returned `:acknowledge` is where the host must durably advance the anchor
; before reporting application success; this book does not supply that adapter.
(defun fn-journal-host-statusp (x)
  (or (equal x :durable) (equal x :aborted) (equal x :indeterminate)))

(defun fn-journal-completion-action (slots txid status)
  (if (not (fn-journal-host-statusp status))
      :ignore
    (if (equal status :indeterminate)
        :recover
      (if (equal status :aborted)
          :known-abort
        (if (and (natp txid) (fn-journal-durable-commitp txid slots))
            :acknowledge
          :ignore)))))

; -----------------------------------------------------------------------------
; Crash construction.  `choices` has one entry per volatile slot and permits
; :lost, :torn, or :intact.  Selected volatile slots are reversed in the image,
; explicitly ruling out a simplistic append-prefix assumption.  Durable slots
; remain in source order by A-DURABILITY/A-WRITE-ISOLATION.

(defun fn-journal-crash-choicep (x)
  (or (equal x :lost) (equal x :torn) (equal x :intact)))

(defun fn-journal-crash-choicesp (xs)
  (if (consp xs)
      (and (fn-journal-crash-choicep (car xs))
           (fn-journal-crash-choicesp (cdr xs)))
    (null xs)))

(defun fn-journal-crash-parts (slots choices durable volatile)
  (if (consp slots)
      (if (equal (fn-journal-live-durability (car slots)) :durable)
          (fn-journal-crash-parts
           (cdr slots) choices
           (append durable (list (fn-journal-materialize (car slots) :intact)))
           volatile)
        (if (consp choices)
            (fn-journal-crash-parts
             (cdr slots) (cdr choices) durable
             (if (equal (car choices) :lost)
                 volatile
               (cons (fn-journal-materialize (car slots) (car choices)) volatile)))
          ; Missing choice is conservative loss of a volatile write.
          (fn-journal-crash-parts (cdr slots) nil durable volatile)))
    (append durable volatile)))

(defun fn-journal-crash (slots choices)
  (if (and (fn-journal-live-listp slots)
           (fn-journal-crash-choicesp choices))
      (fn-journal-crash-parts slots choices nil nil)
    nil))

; A small executable enumeration used by the scenario book.  It covers every
; absent/present subset; the three-way crash function above additionally covers
; torn present writes.
(defun fn-journal-prefix-choice (choice choices)
  (if (consp choices)
      (cons (cons choice (car choices))
            (fn-journal-prefix-choice choice (cdr choices)))
    nil))

(defun fn-journal-binary-choices (n)
  (if (zp n)
      (list nil)
    (append (fn-journal-prefix-choice :lost (fn-journal-binary-choices (1- n)))
            (fn-journal-prefix-choice :intact (fn-journal-binary-choices (1- n))))))

(defun fn-journal-count-volatile (slots)
  (if (consp slots)
      (+ (if (equal (fn-journal-live-durability (car slots)) :volatile) 1 0)
         (fn-journal-count-volatile (cdr slots)))
    0))

(defun fn-journal-crash-matrix-choices (slots choices)
  (if (consp choices)
      (cons (fn-journal-crash slots (car choices))
            (fn-journal-crash-matrix-choices slots (cdr choices)))
    nil))

(defun fn-journal-crash-matrix (slots)
  (fn-journal-crash-matrix-choices slots
                                   (fn-journal-binary-choices
                                    (fn-journal-count-volatile slots))))

; -----------------------------------------------------------------------------
; Recovery.  A durable anchor is `:none` before any acknowledgement, otherwise
; a natural transaction number.  It is supplied by the recovery environment,
; not inferred from the success process's RAM.  A real adapter needs a separate
; protected anchor/generation mechanism before it may instantiate this model.

(defun fn-journal-anchorp (x)
  (or (equal x :none) (natp x)))

(defun fn-journal-object-seenp (txid object-id objects)
  (if (consp objects)
      (or (and (equal txid (car (car objects)))
               (equal object-id (cdr (car objects))))
          (fn-journal-object-seenp txid object-id (cdr objects)))
    nil))

(defun fn-journal-references-seenp (txid refs objects)
  (if (consp refs)
      (and (fn-journal-object-seenp txid (car refs) objects)
           (fn-journal-references-seenp txid (cdr refs) objects))
    t))

(defun fn-journal-result-ok (txids)
  (list :ok txids))

(defun fn-journal-result-fault (code)
  (list :fault code))

(defun fn-journal-result-okp (x)
  (and (true-listp x) (equal (len x) 2) (equal (car x) :ok)))

(defun fn-journal-result-txids (x) (car (cdr x)))

; `next` enforces whole, contiguous transactions.  Torn slots can be ignored
; only because a surviving later commit must still pass this gap/dependency
; check.  An intact duplicate object is reported as corruption, never silently
; selected by a last-writer-wins rule.
(defun fn-journal-scan (image next objects txids)
  (if (consp image)
      (let ((slot (car image)))
        (if (not (fn-journal-physical-slotp slot))
            (fn-journal-result-fault :malformed-slot)
          (if (equal (fn-journal-physical-integrity slot) :torn)
              (fn-journal-scan (cdr image) next objects txids)
            (if (equal (fn-journal-physical-kind slot) :object)
                (if (fn-journal-object-seenp (fn-journal-physical-txid slot)
                                            (fn-journal-physical-data slot)
                                            objects)
                    (fn-journal-result-fault :object-conflict)
                  (fn-journal-scan
                   (cdr image) next
                   (cons (cons (fn-journal-physical-txid slot)
                               (fn-journal-physical-data slot)) objects)
                   txids))
              (if (not (equal (fn-journal-physical-txid slot) next))
                  (fn-journal-result-fault :commit-gap)
                (if (fn-journal-references-seenp
                     next (fn-journal-physical-data slot) objects)
                    (fn-journal-scan (cdr image) (1+ next) objects
                                     (append txids (list next)))
                  (fn-journal-result-fault :missing-dependency)))))))
    (fn-journal-result-ok txids)))

(defun fn-journal-anchor-satisfiedp (anchor txids)
  (if (equal anchor :none)
      t
    (member-equal anchor txids)))

(defun fn-journal-recover (image anchor)
  (if (not (fn-journal-anchorp anchor))
      (fn-journal-result-fault :bad-anchor)
    (let ((answer (fn-journal-scan image 0 nil nil)))
      (if (and (fn-journal-result-okp answer)
               (fn-journal-anchor-satisfiedp anchor
                                             (fn-journal-result-txids answer)))
          answer
        (if (fn-journal-result-okp answer)
            (fn-journal-result-fault :ack-gap)
          answer)))))

(defun fn-journal-recover-matrix (images anchor)
  (if (consp images)
      (cons (fn-journal-recover (car images) anchor)
            (fn-journal-recover-matrix (cdr images) anchor))
    nil))

(defun fn-journal-no-published-txsp (answers)
  (if (consp answers)
      (and (or (not (fn-journal-result-okp (car answers)))
               (equal (fn-journal-result-txids (car answers)) nil))
           (fn-journal-no-published-txsp (cdr answers)))
    t))

; -----------------------------------------------------------------------------
; Certified local recovery facts.  These are logical properties of the scanner,
; conditional on the crash constructor's stated platform assumptions.

(defthm fn-journal-recover-empty
  (equal (fn-journal-recover nil :none)
         (fn-journal-result-ok nil)))

(defthm fn-journal-indeterminate-forces-recovery
  (equal (fn-journal-completion-action slots txid :indeterminate)
         :recover))

(defthm fn-journal-scan-missing-dependency-fault
  (implies (and (natp txid)
                (fn-journal-id-listp refs)
                (not (fn-journal-references-seenp txid refs objects)))
           (equal (fn-journal-scan
                   (list (fn-journal-make-physical-commit txid refs :intact))
                   txid objects txids)
                  (fn-journal-result-fault :missing-dependency))))

(defthm fn-journal-scan-commit-gap-fault
  (implies (and (natp txid) (natp next) (not (equal txid next)))
           (equal (fn-journal-scan
                   (list (fn-journal-make-physical-commit txid nil :intact))
                   next objects txids)
                  (fn-journal-result-fault :commit-gap))))

(defthm fn-journal-recover-torn-anchored-commit-fault
  (implies (natp txid)
           (equal (fn-journal-recover
                   (list (fn-journal-make-physical-commit txid nil :torn))
                   txid)
                  (fn-journal-result-fault :ack-gap))))

(defthm fn-journal-scan-valid-single-commit
  (implies (and (natp txid)
                (fn-journal-id-listp refs)
                (fn-journal-references-seenp txid refs objects))
           (equal (fn-journal-scan
                   (list (fn-journal-make-physical-commit txid refs :intact))
                   txid objects txids)
                  (fn-journal-result-ok (append txids (list txid))))))
