; Teeth for books/def-carried-writer.lisp: a stobj carrier (the target of
; stage 5's carrier move), its profile, the accepted writers with their
; generated statements pinned literally, every refusal asserted by its words
; (fn-cwt-refused runs exactly the check def-carried-writer runs), the row
; from the table and the owed report.
;
;   1. The fixture: a stobj `cwt-st' whose core field the invariant reads,
;      an installer, a frame (other field; install of a value the model
;      invariant holds of), a bridge, a model keystone, a step transition.
;   2. The profile; its refusals.
;   3. Accepted writers: through the installer and a :via keystone; a
;      frame-only writer; a writer through the step at an event; a writer
;      whose guard adds a bridge (:bridges); :name and :hints recorded.
;      The generated statement is def-carried's (fn-cd-statement), pinned.
;   4. Refusals: malformed forms; a :program writer; a direct updater of the
;      carrier (not opened, not an installer, no theorem about it); an
;      installer fed a value no theorem covers; a guard conjunct over a
;      per-call argument; a guard conjunct over the carried state with no
;      bridge; a duplicate; :via / :lemmas / :opens naming nothing.
;   5. The row: def-carried-writers-row over the pilot row and the table; its
;      transitions are the pilot's then the writers'; def-carried-check
;      re-checks it; the bridge a writer added is in :concludes.  The owed
;      report is 0 here (no fn-interfaces entry in this world).

(in-package "ACL2")
(include-book "../../books/def-carried-writer")
(include-book "../../books/payload-kinds") ; *fn-entry-guard-kinds*: natp is a kind
(include-book "must-fail-checked")

; ---------------------------------------------------------------------------
; Running the macro's check and asserting the refusal's words.

(defun fn-cwt-msg-string (m)
  (declare (xargs :mode :program))
  ; the format string of a msg (a pair) or the string itself
  (cond ((stringp m) m)
        ((and (consp m) (stringp (car m))) (car m))
        (t "")))

(defmacro fn-cwt-refused (fn kvs expected)
  ; the first refusal of (def-carried-writer FN . KVS) mentions EXPECTED (a
  ; substring of the message's format string, so never across a ~ line break)
  `(make-event
    (mv-let (problem uncovered)
      (fn-cw-problem ',fn ',kvs (w state))
      (declare (ignore uncovered))
      (let ((text (fn-cwt-msg-string problem)))
        (if (and (stringp text) (search ,expected text))
            (value '(value-triple :refused))
          (er soft 'fn-cwt-refused "~x0 refused by ~@1, expected ~x2"
              ',fn (or problem "nothing") ,expected))))))

(defmacro fn-cwt-profile-refused (name kvs expected)
  `(make-event
    (let* ((problem (fn-cw-profile-problem ',name ',kvs (w state)))
           (text (fn-cwt-msg-string problem)))
      (if (and (stringp text) (search ,expected text))
          (value '(value-triple :refused))
        (er soft 'fn-cwt-profile-refused "~x0 refused by ~@1, expected ~x2"
            ',name (or problem "nothing") ,expected)))))

; ---------------------------------------------------------------------------
; 1. The fixture.

(defstobj cwt-st
  (cwt-core :type integer :initially 0)
  (cwt-note :type t :initially nil))

; The model invariant of the carried value, and the carried relation.
(defun cwt-okp (c) (declare (xargs :guard t)) (and (integerp c) (< 0 c)))
(defun cwt-relp (cwt-st)
  (declare (xargs :stobjs cwt-st))
  (cwt-okp (cwt-core cwt-st)))

; The installer: the one writer of the carried value.
(defun cwt-install (c cwt-st)
  (declare (xargs :stobjs cwt-st :guard (integerp c)))
  (update-cwt-core c cwt-st))

; The frame: a write beside the carried value keeps the relation; an install
; of a value the model invariant holds of establishes it.
(defthm cwt-relp-of-update-note
  (equal (cwt-relp (update-cwt-note x cwt-st)) (cwt-relp cwt-st)))
(defthm cwt-relp-of-install
  (implies (cwt-okp c) (cwt-relp (cwt-install c cwt-st))))

; The bridge: the relation gives the model invariant at the carried value.
(defthm cwt-relp-implies-corep
  (implies (cwt-relp cwt-st) (cwt-okp (cwt-core cwt-st)))
  :rule-classes nil)

; The model step and its keystone (over the model's variable c).
(defun cwt-bump-core (c n) (declare (xargs :guard (and (integerp c) (natp n)))) (+ c (nfix n)))
(defthm cwt-bump-core-keeps-corep
  (implies (cwt-okp c) (cwt-okp (cwt-bump-core c n))))
(defthm cwt-bump-core-integerp
  (implies (integerp c) (integerp (cwt-bump-core c n))))

; The step transition: events dispatched by kind, through the installer.
(defun cwt-step (event cwt-st)
  (declare (xargs :stobjs cwt-st :guard (and (true-listp event) (cwt-relp cwt-st))))
  (case (car event)
    (:bump (cwt-install (cwt-bump-core (cwt-core cwt-st) (nfix (cadr event))) cwt-st))
    (otherwise cwt-st)))
(defthm cwt-step-bump-keeps-corep
  ; the keystone a :step writer names, over the model's c
  (implies (cwt-okp c) (cwt-okp (cwt-bump-core c (nfix n)))))

; The open and the pilot row (def-carried's; the writers' row reads it).
(defun cwt-open (cwt-st)
  (declare (xargs :stobjs cwt-st))
  (cwt-install 1 cwt-st))
(defthm cwt-open-establishes (cwt-relp (cwt-open cwt-st)))
(defun cwt-touch (cwt-st)
  (declare (xargs :stobjs cwt-st :guard (cwt-relp cwt-st)))
  (update-cwt-note :touched cwt-st))
(defthm cwt-touch-carries
  (implies (cwt-relp cwt-st) (cwt-relp (cwt-touch cwt-st))))
(def-carried cwt-pilot
  :invariant cwt-relp
  :established ((cwt-open cwt-open-establishes :witness ((create-cwt-st))))
  :transitions ((cwt-touch cwt-touch-carries))
  :concludes ((cwt-relp cwt-touch-carries))
  :trace nil)

; ---------------------------------------------------------------------------
; 2. The profile, and what it refuses.

(fn-cwt-profile-refused cwt-none (:invariant cwt-relp :installers (cwt-install))
                        "has no :bridge")
(fn-cwt-profile-refused cwt-none (:invariant cwt-relp :bridge cwt-relp-implies-corep)
                        "has no :installers")
(fn-cwt-profile-refused cwt-none (:invariant cwt-okp :installers (cwt-install)
                                  :bridge cwt-relp-implies-corep)
                        "takes a value, not a stobj")
(fn-cwt-profile-refused cwt-none (:invariant cwt-relp :installers (cwt-okp)
                                  :bridge cwt-relp-implies-corep)
                        "is not a function returning")
(fn-cwt-profile-refused cwt-none (:invariant cwt-relp :installers (cwt-install)
                                  :bridge cwt-relp-implies-corep :frame (cwt-nothing))
                        "is not a theorem in this world")
(fn-cwt-profile-refused cwt-none (:invariant cwt-relp :installers (cwt-install)
                                  :bridge cwt-relp-implies-corep :at ((c (cwt-core other))))
                        "mentions a variable other than")
(fn-cwt-profile-refused cwt-none (:invariant cwt-relp :installers (cwt-install)
                                  :bridge cwt-relp-implies-corep :step (cwt-step ev))
                        "is not a formal of")
(fn-cwt-profile-refused cwt-none (:invariant cwt-relp :installers (cwt-install)
                                  :bridge cwt-relp-implies-corep :carried-globals (x))
                        "is for the legacy carrier")
(fn-cwt-profile-refused cwt-none (:invariant cwt-relp :installers (cwt-install)
                                  :bridge cwt-relp-implies-corep :row cwt-nothing)
                        "is not a carried invariant")
(fn-cwt-profile-refused cwt-none (:invariant cwt-relp :installers (cwt-install)
                                  :bridge cwt-relp-implies-corep :bogus 1)
                        "unknown keyword")

(def-carried-profile cwt-profile
  :invariant cwt-relp
  :installers (cwt-install)
  :at ((c (cwt-core cwt-st)))
  :bridge cwt-relp-implies-corep
  :frame (cwt-relp-of-update-note cwt-relp-of-install)
  :theory (mv-nth zp car-cons cdr-cons (:executable-counterpart zp)
           (:executable-counterpart binary-+) (:executable-counterpart unary--)
           (:executable-counterpart equal) (:executable-counterpart nfix) nfix)
  :guard-theory (cwt-relp cwt-okp cwt-bump-core-integerp cwt-stp cwt-okp
                 (:type-prescription cwt-core))
  :step (cwt-step event)
  :row cwt-pilot
  :suffix relp)

(fn-cwt-profile-refused cwt-profile (:invariant cwt-relp :installers (cwt-install)
                                     :bridge cwt-relp-implies-corep)
                        "already a profile")

(assert-event
 (equal (cdr (assoc-eq 'cwt-profile (table-alist 'fn-carried-profiles (w state))))
        '(:invariant cwt-relp :state cwt-st :formal cwt-st
          :installers (cwt-install) :carried-globals nil
          :at ((c (cwt-core cwt-st))) :bridge cwt-relp-implies-corep
          :frame (cwt-relp-of-update-note cwt-relp-of-install)
          :theory (mv-nth zp car-cons cdr-cons (:executable-counterpart zp)
                   (:executable-counterpart binary-+) (:executable-counterpart unary--)
                   (:executable-counterpart equal) (:executable-counterpart nfix) nfix)
          :guard-theory (cwt-relp cwt-okp cwt-bump-core-integerp cwt-stp cwt-okp
                         (:type-prescription cwt-core))
          :step (cwt-step event) :row cwt-pilot :suffix relp)))

; ---------------------------------------------------------------------------
; 3. Accepted writers.

; Through the installer, the installed value produced by the model step a
; :via keystone is about; a value returned beside the carrier; guards
; verified by the generated event (the defun said :verify-guards nil).
(defun cwt-bump (n cwt-st)
  (declare (xargs :stobjs cwt-st :guard (and (natp n) (cwt-relp cwt-st)) :verify-guards nil))
  (let ((cwt-st (cwt-install (cwt-bump-core (cwt-core cwt-st) n) cwt-st)))
    (mv :ok cwt-st)))
; The whole expansion, pinned literally (a reviewer reads the events; a drift
; fails here): the guard verification under minimal-theory and the named
; rules, the theorem with its hints, the two table rows.
(assert-event
 (equal (fn-cw-events 'cwt-bump '(:profile cwt-profile :via (cwt-bump-core-keeps-corep))
                      nil (w state))
        '(progn
          (verify-guards cwt-bump
            :hints (("Goal" :in-theory (union-theories
                                        '(cwt-bump cwt-relp cwt-okp cwt-bump-core-integerp
                                          cwt-stp cwt-okp (:type-prescription cwt-core))
                                        (theory 'minimal-theory)))))
          (defthm cwt-bump-preserves-relp
            (implies (cwt-relp cwt-st) (cwt-relp (mv-nth 1 (cwt-bump n cwt-st))))
            :hints (("Goal" :in-theory (union-theories
                                        '(cwt-bump cwt-relp-of-update-note cwt-relp-of-install
                                          mv-nth zp car-cons cdr-cons
                                          (:executable-counterpart zp)
                                          (:executable-counterpart binary-+)
                                          (:executable-counterpart unary--)
                                          (:executable-counterpart equal)
                                          (:executable-counterpart nfix) nfix)
                                        (theory 'minimal-theory))
                     :use ((:instance cwt-bump-core-keeps-corep (c (cwt-core cwt-st)))
                           cwt-relp-implies-corep))))
          (table fn-carried-writers 'cwt-bump
                 '(:profile cwt-profile :theorem cwt-bump-preserves-relp
                   :via (cwt-bump-core-keeps-corep) :opens nil :lemmas nil :step nil
                   :bridges nil :hyps nil :put-keys nil :uncovered nil :hand-hints nil))
          (table fn-teeth-owed 'cwt-bump-preserves-relp
                 '(:by def-carried-writer
                   :claim (((inv (cwt-relp cwt-st))) (cwt-relp (mv-nth 1 (cwt-bump n cwt-st))))
                   :subject cwt-bump)))))
(def-carried-writer cwt-bump
  :profile cwt-profile
  :via (cwt-bump-core-keeps-corep))

(assert-event (eq (symbol-class 'cwt-bump (w state)) :common-lisp-compliant))
(assert-event
 (equal (getpropc 'cwt-bump-preserves-relp 'theorem nil (w state))
        '(implies (cwt-relp cwt-st)
                  (cwt-relp (mv-nth '1 (cwt-bump n cwt-st))))))
; the stronger statement, not def-carried's (which carries the guard too and
; is derived from this one by the row, section 5)
(assert-event
 (mv-let (msg statement)
   (fn-cd-statement :carries 'cwt-relp 'cwt-st '(cwt-bump none :hyps nil) (w state))
   (and (null msg)
        (equal statement
               ; the world's guard: ACL2 conjoins the stobj recognizer to the declared one
               '(implies (if (cwt-relp cwt-st)
                             (if (cwt-stp cwt-st) (if (natp n) (cwt-relp cwt-st) 'nil) 'nil)
                           'nil)
                         (cwt-relp (mv-nth '1 (cwt-bump n cwt-st)))))
        (not (equal statement (getpropc 'cwt-bump-preserves-relp 'theorem nil (w state)))))))
(assert-event
 (equal (cdr (assoc-eq 'cwt-bump (table-alist 'fn-carried-writers (w state))))
        '(:profile cwt-profile :theorem cwt-bump-preserves-relp
          :via (cwt-bump-core-keeps-corep) :opens nil :lemmas nil :step nil
          :bridges nil :hyps nil :put-keys nil :uncovered nil :hand-hints nil)))
(assert-event
 (equal (cdr (assoc-eq 'cwt-bump-preserves-relp (table-alist 'fn-teeth-owed (w state))))
        '(:by def-carried-writer
          :claim (((inv (cwt-relp cwt-st))) (cwt-relp (mv-nth 1 (cwt-bump n cwt-st))))
          :subject cwt-bump)))

; A frame-only writer (the other field); it carries the stobj alone.
(defun cwt-annotate (x cwt-st)
  (declare (xargs :stobjs cwt-st :guard (cwt-relp cwt-st)))
  (update-cwt-note x cwt-st))
(def-carried-writer cwt-annotate :profile cwt-profile)
(assert-event
 (equal (getpropc 'cwt-annotate-preserves-relp 'theorem nil (w state))
        '(implies (cwt-relp cwt-st) (cwt-relp (cwt-annotate x cwt-st)))))

; Through the step at an event: the step lemma is generated first, from the
; model keystone, and the writer's proof uses it as a rule.
(defun cwt-bump-by-step (n cwt-st)
  (declare (xargs :stobjs cwt-st :guard (and (natp n) (cwt-relp cwt-st))))
  (cwt-step (list :bump n) cwt-st))
(def-carried-writer cwt-bump-by-step
  :profile cwt-profile
  :step ((list :bump n) cwt-step-bump-keeps-corep))
(assert-event
 (equal (getpropc 'cwt-step-bump-preserves-relp 'theorem nil (w state))
        '(implies (cwt-relp cwt-st) (cwt-relp (cwt-step (cons ':bump (cons n 'nil)) cwt-st)))))
(assert-event (getpropc 'cwt-bump-by-step-preserves-relp 'theorem nil (w state)))
; a second writer through the same kind, naming the step itself: the step
; lemma is REUSED (its statement is the regenerated one), not refused
(defun cwt-bump-twice (n cwt-st)
  (declare (xargs :stobjs cwt-st :guard (and (natp n) (cwt-relp cwt-st))))
  (let ((cwt-st (cwt-step (list :bump n) cwt-st)))
    (cwt-step (list :bump n) cwt-st)))
(def-carried-writer cwt-bump-twice
  :profile cwt-profile
  :step (cwt-step (list :bump n) cwt-step-bump-keeps-corep))
(assert-event (getpropc 'cwt-bump-twice-preserves-relp 'theorem nil (w state)))
(assert-event
 (equal (fn-cd-get :step (cdr (assoc-eq 'cwt-bump-twice (table-alist 'fn-carried-writers (w state)))))
        '(cwt-step (list :bump n) cwt-step-bump-keeps-corep)))

; A writer whose guard applies a predicate to the carried state that no
; bridge concludes: refused with the bridge to declare; accepted with it
; (the row, section 5, then generates cwt-row-cwt-positivep-bridge from the
; named theorem).
(defun cwt-positivep (cwt-st)
  (declare (xargs :stobjs cwt-st))
  (< 0 (cwt-core cwt-st)))
(defun cwt-renote (cwt-st)
  (declare (xargs :stobjs cwt-st :guard (and (cwt-relp cwt-st) (cwt-positivep cwt-st))))
  (update-cwt-note :again cwt-st))
(fn-cwt-refused cwt-renote (:profile cwt-profile) "no bridge concludes it")
(defthm cwt-relp-implies-positivep
  (implies (cwt-relp cwt-st) (cwt-positivep cwt-st))
  :rule-classes nil)
(def-carried-writer cwt-renote
  :profile cwt-profile
  :bridges ((cwt-positivep cwt-relp-implies-positivep))
  :name cwt-renote-keeps
  :hints (("Goal" :in-theory (union-theories '(cwt-renote cwt-relp-of-update-note)
                                             (theory 'minimal-theory)))))
(assert-event
 (equal (cdr (assoc-eq 'cwt-renote (table-alist 'fn-carried-writers (w state))))
        '(:profile cwt-profile :theorem cwt-renote-keeps :via nil :opens nil :lemmas nil
          :step nil :bridges ((cwt-positivep cwt-relp-implies-positivep)) :hyps nil
          :put-keys nil :uncovered nil :hand-hints t)))

; A conjunct over another stobj alone is recorded, not refused.
(defstobj cwt-other (cwt-flag :type t :initially nil))
(defun cwt-flaggedp (cwt-other) (declare (xargs :stobjs cwt-other)) (if (cwt-flag cwt-other) t nil))
(defun cwt-two (cwt-other cwt-st)
  (declare (xargs :stobjs (cwt-other cwt-st) :guard (and (cwt-relp cwt-st) (cwt-flaggedp cwt-other))))
  (let ((cwt-st (if (cwt-flaggedp cwt-other)
                    (update-cwt-note :two cwt-st)
                  (cwt-install 0 cwt-st))))   ; the arm the guard excludes breaks R
    (mv cwt-other cwt-st)))
; without the premise the statement is false (the excluded arm): refused by
; the prover, not by the expansion
(must-fail-checked (def-carried-writer cwt-two :profile cwt-profile)
                   :unchecked "the generated theorem is false without the two-stobj premise")
; a :hyps the guard does not state is refused at expansion
(fn-cwt-refused cwt-two (:profile cwt-profile :hyps ((cwt-flag cwt-other)))
                "is not a conjunct of")
(def-carried-writer cwt-two :profile cwt-profile :hyps ((cwt-flaggedp cwt-other)))
(assert-event
 (equal (fn-cd-get :uncovered (cdr (assoc-eq 'cwt-two (table-alist 'fn-carried-writers (w state)))))
        '((cwt-flaggedp cwt-other))))
(assert-event
 (equal (getpropc 'cwt-two-preserves-relp 'theorem nil (w state))
        '(implies (if (cwt-relp cwt-st) (cwt-flaggedp cwt-other) 'nil)
                  (cwt-relp (mv-nth '1 (cwt-two cwt-other cwt-st))))))

; ---------------------------------------------------------------------------
; 4. Refusals.

(fn-cwt-refused cwt-bump (:profile cwt-profile) "already a declared writer")
(fn-cwt-refused cwt-annotate (:profile cwt-nothing) "is not a carried-writer profile")
(fn-cwt-refused cwt-touch (:profile cwt-profile :bogus 1) "unknown keyword")
(fn-cwt-refused cwt-nothing (:profile cwt-profile) "is not a function in this world")
(fn-cwt-refused cwt-okp (:profile cwt-profile) "takes no ~x1 argument")

; :program: no theorem can be stated
(defun cwt-prog (cwt-st) (declare (xargs :stobjs cwt-st :mode :program)) (update-cwt-note 1 cwt-st))
(fn-cwt-refused cwt-prog (:profile cwt-profile) "is :program mode")

; a direct updater of the carrier: not opened, not an installer, no theorem
(defun cwt-bad (c cwt-st)
  (declare (xargs :stobjs cwt-st :guard (and (integerp c) (cwt-relp cwt-st))))
  (update-cwt-core c cwt-st))
(fn-cwt-refused cwt-bad (:profile cwt-profile)
                "and is neither opened")

; the installer fed a value no theorem covers (a formal the caller passes)
(defun cwt-install-arg (c cwt-st)
  (declare (xargs :stobjs cwt-st :guard (and (integerp c) (cwt-relp cwt-st))))
  (cwt-install c cwt-st))
(fn-cwt-refused cwt-install-arg (:profile cwt-profile)
                "and no :via, :lemmas, :frame or step")

; a guard conjunct over a per-call argument that is not a kind check
(defun cwt-arg-guard (c cwt-st)
  (declare (xargs :stobjs cwt-st :guard (and (cwt-okp c) (cwt-relp cwt-st))))
  (cwt-install c cwt-st))
(fn-cwt-refused cwt-arg-guard (:profile cwt-profile) "an argument the host")

; names that are not what they must be
(fn-cwt-refused cwt-touch (:profile cwt-profile :via (cwt-nothing)) "is not a theorem in this world")
(fn-cwt-refused cwt-touch (:profile cwt-profile :via ((cwt-nothing 1 2))) "is not (THM | (THM (VAR TERM) ...) ...)")
(fn-cwt-refused cwt-touch (:profile cwt-profile :lemmas (cwt-nothing)) "is not a theorem in this world")
(fn-cwt-refused cwt-touch (:profile cwt-profile :opens (cwt-nothing)) "is not a function in this world")
(fn-cwt-refused cwt-touch (:profile cwt-profile :bridges ((cwt-positivep cwt-nothing))) "is not a theorem in this world")
(fn-cwt-refused cwt-touch (:profile cwt-profile :step (1 2)) "is not a (list :KIND ...) term")
(fn-cwt-refused cwt-touch (:profile cwt-profile :step (cwt-okp (list :bump n) cwt-step-bump-keeps-corep))
                "is not a function returning")
(fn-cwt-refused cwt-touch (:profile cwt-profile :step (1 2 3 4)) "is not (EVENT-TERM THM) or")
(fn-cwt-refused cwt-touch (:profile cwt-profile :step ((list :nudge m) cwt-step-bump-keeps-corep))
                "mentions variables that are not")
(fn-cwt-refused cwt-touch (:profile cwt-profile :name 7) "is not a symbol")
(fn-cwt-refused cwt-touch (:profile cwt-profile :name cwt-bump-preserves-relp)
                "is already a theorem of this world")

; the whole form, refused as the macro refuses it
(must-fail-checked (def-carried-writer cwt-bad :profile cwt-profile)
                   :unchecked "a refusal at expansion: the macro names the uncovered updater")

; ---------------------------------------------------------------------------
; 5. The row and the owed report.

(def-carried-writers-row cwt-row :profile cwt-profile :from cwt-pilot)
(assert-event
 (equal (strip-cars (fn-cd-get :transitions
                               (cdr (assoc-eq 'cwt-row (table-alist 'fn-carried (w state))))))
        '(cwt-touch cwt-bump cwt-annotate cwt-bump-by-step cwt-bump-twice cwt-renote cwt-two)))
(assert-event
 (equal (fn-cw-pairs (fn-cd-get :concludes
                                (cdr (assoc-eq 'cwt-row (table-alist 'fn-carried (w state))))))
        '((cwt-relp cwt-touch-carries) (cwt-positivep cwt-relp-implies-positivep))))
(assert-event
 (equal (getpropc 'cwt-row-cwt-positivep-bridge 'theorem nil (w state))
        '(implies (cwt-relp cwt-st) (cwt-positivep cwt-st))))
(def-carried-check cwt-row)
; the row's generated transition statement carries the guard; it was proved
; from the writer's stronger theorem by :use
(assert-event
 (equal (getpropc 'cwt-row-cwt-bump-carries 'theorem nil (w state))
        '(implies (if (cwt-relp cwt-st)
                      (if (cwt-stp cwt-st) (if (natp n) (cwt-relp cwt-st) 'nil) 'nil)
                    'nil)
                  (cwt-relp (mv-nth '1 (cwt-bump n cwt-st))))))
(def-carried-writers-owed cwt-profile :from cwt-pilot)
(assert-event (null (fn-cw-owed 'cwt-profile 'cwt-pilot (w state))))

; a second row over the same profile is a second def-carried row: refused by
; def-carried when NAME is taken
(must-fail-checked (def-carried-writers-row cwt-row :profile cwt-profile :from cwt-pilot)
                   :unchecked "def-carried refuses a redeclared row")
(must-fail-checked (def-carried-writers-row cwt-row2 :profile cwt-nothing :from cwt-pilot)
                   :unchecked "no such profile")
