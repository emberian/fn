; Teeth for books/productive-contract.lisp (lane productive-contract,
; 2026-09-29; PRF-1001 fn-pcx-post-productive, PRF-1002
; fn-pcx-uncertain-has-a-named-cause).
;
; The witness is owner-tests' plain served POST: *own-taken*, the owner
; after connection 4 POSTed "Hello, news." through fn-own-read and the
; writer took it (:take), whose Store is :ready; the record is the row the
; submission's own octets intern at sequence 2 (owner-served-invariants-
; tests' osi-sub-record), and the arena holds the journal's prior as the
; host's does (osi-finish-in).  The nine steps are own-post-events, which
; is fn-pcx-post-script of (:prepare record) by definition.
(in-package "ACL2")
(include-book "owner-served-invariants-tests")
(include-book "../../books/productive-contract")
(include-book "must-fail-checked")

(defconst *pcx-o* *own-taken*)
(defconst *pcx-id* 4)
(defconst *pcx-r* (osi-sub-record 2 2 *osi-sub*))
(defconst *pcx-prior* *osi-completing-prior*)
(defconst *pcx-cfg* *osi-cfg*)

; The script the keystone bounds is the one owner-tests runs.
(assert-event (equal (own-post-events *pcx-r*) (fn-pcx-post-script (list :prepare *pcx-r*))))
(assert-event (equal (len (own-post-events *pcx-r*)) *fn-pcx-post-steps*))

; -----------------------------------------------------------------------------
; Reachable positive witness of fn-pcx-post-productive: the complete
; antecedent, then the complete conclusion, each per literal theorem, over
; the arena that holds the prior (handles 0, 1, 2).

(defun pcx-antecedent-in (o r id cfg prior fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (rows fn-arena)
    (fn-hrt-events prior nil 0 fn-arena)
    (declare (ignore rows))
    (let* ((s (fn-own-store o))
           (sub (fn-own-inflight o))
           (w (fn-row-wire-of r fn-arena))
           (conn (fn-own-find-conn id (fn-own-conns o))))
      (mv (and (fn-sn-statep s)
               (fn-pcx-admissiblep s r)
               (eq (fn-th-at 0 (fn-th-prefix-step (fn-sn-topic s) r)) :ok)
               sub
               (equal (fn-own-sub-id sub) id)
               conn
               (natp (fn-own-sub-mark sub))
               (<= (fn-own-sub-mark sub) (len (fn-own-ledger o)))
               (equal (fn-record-msgid w) (fn-record-octets-string (fn-own-sub-msgid sub)))
               (equal (fn-record-payload w) (fn-own-sub-stored-octets cfg sub (fn-own-node-secret o)))
               t)
          fn-arena))))

(defun pcx-antecedent (o r id cfg prior)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (pcx-antecedent-in o r id cfg prior fn-arena)
      result)))

(defun pcx-conclusion-in (o r id cfg prior fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (rows fn-arena)
    (fn-hrt-events prior nil 0 fn-arena)
    (declare (ignore rows))
    (let* ((s (fn-own-store o))
           (conn (fn-own-find-conn id (fn-own-conns o)))
           (o8 (fn-own-run o (fn-pcx-wrap-store (fn-pcx-store-script (list :prepare r))) fn-arena))
           (o9 (fn-own-run o (fn-pcx-post-script (list :prepare r)) fn-arena))
           (pair (fn-sf-record-pair r))
           (out (fn-own-outcome o9 id :durable)))
      (mv (and (equal (len (fn-pcx-post-script (list :prepare r))) *fn-pcx-post-steps*)
               (equal (car (fn-own-finish o8 cfg fn-arena)) :durable)
               (equal o9 (cdr (fn-own-finish o8 cfg fn-arena)))
               (fn-own-completion-consumedp o9)
               (equal (fn-own-ledger o9) (append (fn-own-ledger o) (list pair)))
               (equal (fn-sf-successes (fn-sn-files (fn-own-store o9)))
                      (append (fn-sf-successes (fn-sn-files s)) (list pair)))
               (member-equal r (fn-sf-records (fn-sn-files (fn-own-store o9))))
               (equal (car out)
                      (fn-served-result-effects
                       (fn-served-post-outcome
                        (fn-served-make-conn-group-indexed
                         (fn-own-conn-wire conn) (fn-own-conn-session conn)
                         (fn-own-conn-archive conn) (fn-own-conn-config conn)
                         (fn-own-conn-observation conn) (fn-own-clock o)
                         (fn-own-conn-verdicts conn) (fn-own-conn-index conn)
                         (fn-own-conn-group-index conn) (fn-own-conn-control conn))
                        :durable)))
               ; and the octets the host writes for it are the 240 line
               (equal (fn-served-reply-octets (car out))
                      (append (fn-nntp-string-octets "240 article received OK") '(13 10)))
               t)
          fn-arena))))

(defun pcx-conclusion (o r id cfg prior)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (pcx-conclusion-in o r id cfg prior fn-arena)
      result)))

(assert-event (pcx-antecedent *pcx-o* *pcx-r* *pcx-id* *pcx-cfg* *pcx-prior*))
(assert-event (pcx-conclusion *pcx-o* *pcx-r* *pcx-id* *pcx-cfg* *pcx-prior*))

; Not trivial: the owner before the nine steps has no consumed completion,
; and its Store is :ready, not :completing.
(assert-event (not (fn-own-completion-consumedp *pcx-o*)))
(assert-event (equal (fn-sf-phase (fn-sn-files (fn-own-store *pcx-o*))) :ready))

; Hypothesis removal (admission): a record whose sequence is not the
; history's length is not admissible, and the same nine steps leave the
; Store short of :completing (the prepare refuses; the record observations
; find no staged record).
(defconst *pcx-wrong-sequence* (osi-sub-record 5 2 *osi-sub*))
(assert-event (not (fn-pcx-admissiblep (fn-own-store *pcx-o*) *pcx-wrong-sequence*)))
(assert-event (not (equal (fn-sf-phase (fn-sn-files (fn-own-store
                                                    (in-arena-fn-own-run *sr-arena* *pcx-o*
                                                                         (osi-drop-last (own-post-events *pcx-wrong-sequence*))))))
                          :completing)))
(must-fail-checked (assert-event (pcx-conclusion *pcx-o* *pcx-wrong-sequence* *pcx-id* *pcx-cfg* *pcx-prior*)))

; -----------------------------------------------------------------------------
; MUTATION witness: the regression's shape.  The completed row's payload
; position is a handle into the arena; comparing the HANDLE against the
; staged octets (instead of the bytes under it, fn-row-wire-of) is false on
; every completion, and the finish word is :fault -- every served POST
; answered the uncertain 441 until the read went through the arena
; (books/owner-served-invariants.lisp).  fn-pcx-post-productive's
; conclusion (word :durable) fails for that finish.

(defun pcx-mutant-names-submission-p (o cfg fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let* ((sub (fn-own-inflight o))
         (record (fn-sn-completion-record (fn-own-store o)))
         (w (fn-row-wire-of record fn-arena)))
    (and sub
         (fn-held-p record)
         (equal (fn-record-msgid w) (fn-record-octets-string (fn-own-sub-msgid sub)))
         ; MUTANT: the handle, not the bytes under it
         (equal (fn-record-payload record) (fn-own-sub-stored-octets cfg sub (fn-own-node-secret o)))
         t)))

(defun pcx-mutant-finish-word-in (o r cfg prior fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (rows fn-arena)
    (fn-hrt-events prior nil 0 fn-arena)
    (declare (ignore rows))
    (let ((o8 (fn-own-run o (fn-pcx-wrap-store (fn-pcx-store-script (list :prepare r))) fn-arena)))
      (mv (if (and (fn-sn-completion-enabledp (fn-own-store o8))
                   (pcx-mutant-names-submission-p o8 cfg fn-arena))
              :durable
            :fault)
          fn-arena))))

(defun pcx-mutant-finish-word (o r cfg prior)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (pcx-mutant-finish-word-in o r cfg prior fn-arena)
      result)))

(assert-event (equal (pcx-mutant-finish-word *pcx-o* *pcx-r* *pcx-cfg* *pcx-prior*) :fault))
(must-fail-checked
 (assert-event (equal (pcx-mutant-finish-word *pcx-o* *pcx-r* *pcx-cfg* *pcx-prior*) :durable)))

; -----------------------------------------------------------------------------
; fn-pcx-uncertain-has-a-named-cause: a positive witness per named cause,
; the outcomes that have no cause, and the must-fail for an uncertain with
; no cause.

; The owner with the completion consumed (after (:complete)) and the one
; before it, both reached by the real served step.
(defconst *pcx-consumed* (in-arena-fn-own-step *sr-arena* *osi-completing* '(:complete)))
(assert-event (fn-own-completion-consumedp *pcx-consumed*))
(assert-event (not (fn-own-completion-consumedp *osi-completing*)))

; Cause 1: consumed, and the host's word is not durable (the OS error after
; publication): uncertain, :effect-failed-after-publication.
(assert-event (equal (fn-own-outcome-completion *pcx-consumed* :storage-failed) :uncertain))
(assert-event (equal (fn-pcx-uncertain-cause *pcx-consumed* :storage-failed)
                     :effect-failed-after-publication))
(assert-event (equal (fn-pcx-uncertain-cause *pcx-consumed* :fault)
                     :effect-failed-after-publication))

; Cause 2: nothing consumed after the take, and the word names no refusal
; (a :durable claim the ledger does not confirm; a :fault before the
; completion): uncertain, :completion-outstanding.
(assert-event (equal (fn-own-outcome-completion *osi-completing* :durable) :uncertain))
(assert-event (equal (fn-pcx-uncertain-cause *osi-completing* :durable) :completion-outstanding))
(assert-event (equal (fn-own-outcome-completion *osi-completing* :fault) :uncertain))
(assert-event (equal (fn-pcx-uncertain-cause *osi-completing* :fault) :completion-outstanding))

; No cause: the durable, refused and clock-refused outcomes.
(assert-event (equal (fn-own-outcome-completion *pcx-consumed* :durable) :durable))
(assert-event (null (fn-pcx-uncertain-cause *pcx-consumed* :durable)))
(assert-event (equal (fn-own-outcome-completion *osi-completing* :duplicate) :refused))
(assert-event (null (fn-pcx-uncertain-cause *osi-completing* :duplicate)))
(assert-event (equal (fn-own-outcome-completion *osi-completing* :clock-unusable) :clock-unusable))
(assert-event (null (fn-pcx-uncertain-cause *osi-completing* :clock-unusable)))

; An uncertain with no cause does not exist on these states.
(must-fail-checked
 (assert-event (and (equal (fn-own-outcome-completion *osi-completing* :durable) :uncertain)
                    (null (fn-pcx-uncertain-cause *osi-completing* :durable)))))
(must-fail-checked
 (assert-event (and (equal (fn-own-outcome-completion *pcx-consumed* :storage-failed) :uncertain)
                    (null (fn-pcx-uncertain-cause *pcx-consumed* :storage-failed)))))

; MUTATION: a cause function that drops the outstanding-completion case
; leaves the :durable-claimed-but-unconfirmed uncertain without a cause.
(defun pcx-mutant-cause (o word)
  (declare (xargs :guard t))
  (if (and (fn-own-completion-consumedp o) (not (fn-own-durable-wordp word)))
      :effect-failed-after-publication
    nil))
(must-fail-checked
 (assert-event (implies (equal (fn-own-outcome-completion *osi-completing* :durable) :uncertain)
                        (member-equal (pcx-mutant-cause *osi-completing* :durable)
                                      '(:effect-failed-after-publication :completion-outstanding)))))
