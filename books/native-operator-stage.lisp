; fn: a store action over an absent store beside an interrupted publication
; names the stage (PKT-781 (1), PRF-971).
;
; `operator CONFIG init' and `store import' build the store beside ROOT, in
; ROOT.init-XXXX or ROOT.import-XXXX, and publish it by renaming
; (books/store-init-publication.lisp, books/store-import-publication.lisp).
; A process death before the rename leaves the stage and no ROOT.  Init and
; import name that stage when run again (init discards it: PKT-894,
; fn-bs-init-pub-admission's :discard-stage; import refuses
; :interrupted-import).  Every other store action (`run', `recover',
; `status', ...) answered NO-STORE there, the refusal of a node that was
; never initialized, and its hint said to run init -- which then refused.
;
; Here the host's observation carries the stage it found beside ROOT (the
; first entry of ROOT's parent named BASENAME.init-* or BASENAME.import-*,
; host/native/io.lisp fnn-import-leftover-stage, the same lookup init and
; import make), and ACL2 decides: an accepted plan that needs a store, with
; none of the store's entries beside ROOT and a stage there, is refused
; :interrupted-init (or :interrupted-import) with the stage as its argument,
; and the hint names it and says what to run.  Without a stage the decision
; is exactly fn-native-operator-store-outcome's (PRF-130 part 1).  A partial
; store (some entries) is never this refusal: it proceeds to the open, which
; recovers or refuses it.
(in-package "ACL2")
(include-book "native-operator")

(defun fn-nsst-stage-refusal (result reason stage)
  (declare (xargs :guard t))
  (fn-nop-refused reason
                  (fn-native-operator-result-command result)
                  (fn-native-operator-result-config result)
                  (list stage)))

(defun fn-nsst-store-outcome (result observed init-stage import-stage)
  "RESULT's store outcome: an absent store beside an init stage (INIT-STAGE)
or an import stage (IMPORT-STAGE), each the stage's path or NIL, is refused
by the stage's name; otherwise fn-native-operator-store-outcome."
  (declare (xargs :guard t))
  (cond ((and (fn-native-operator-result-needs-storep result)
              (not (consp observed))
              (stringp init-stage))
         (fn-nsst-stage-refusal result :interrupted-init init-stage))
        ((and (fn-native-operator-result-needs-storep result)
              (not (consp observed))
              (stringp import-stage))
         (fn-nsst-stage-refusal result :interrupted-import import-stage))
        (t (fn-native-operator-store-outcome result observed))))

(defun fn-nsst-result-hint (result)
  "The line printed before a result's tagged line: for a stage refusal, the
stage and what to run; otherwise fn-native-operator-result-hint's."
  (declare (xargs :guard t))
  (let ((status (fn-native-operator-result-status result))
        (reason (fn-native-operator-result-reason result))
        (stage (fn-ncfg-first (fn-native-operator-result-arguments result))))
    (cond ((and (equal status :refused) (equal reason :interrupted-init)
                (stringp stage))
           (concatenate 'string
                        "no store at the configured [store] path: an init was interrupted before it published the store; its stage "
                        stage
                        " remains; it holds nothing any command acknowledged. Run: fn operator CONFIG init GROUP... (init removes the stage)"))
          ((and (equal status :refused) (equal reason :interrupted-import)
                (stringp stage))
           (concatenate 'string
                        "no store at the configured [store] path: an import was interrupted before it published the store; its stage "
                        stage
                        " remains. Remove it and run the import again"))
          (t (fn-native-operator-result-hint result)))))

(local
 (defthm fn-nsst-refused-fields
   (let ((r (list :refused reason command config arguments)))
     (and (equal (fn-native-operator-result-status r) :refused)
          (equal (fn-native-operator-result-reason r) reason)
          (equal (fn-native-operator-result-arguments r) arguments)
          (equal (fn-native-operator-result-native-action r) :none)
          (equal (fn-native-operator-exit-code r) (fn-outcome-code :refused))))
   :hints (("Goal" :in-theory (enable fn-native-operator-result-status
                                      fn-native-operator-result-reason
                                      fn-native-operator-result-arguments
                                      fn-native-operator-result-native-action
                                      fn-native-operator-exit-code
                                      fn-native-operator-outcome-class
                                      fn-ncfg-first fn-ncfg-second fn-ncfg-rest)))))

; KEYSTONE PRF-971.  The subject is `fn-nsst-store-outcome', which
; host/native/operator.lisp `fnn-operator-store-outcome' calls (through
; fn-native-operator-host-store-outcome) on every accepted plan before it
; executes the action.  An accepted plan that needs a store, over a root
; holding none of the store's entries, beside an init stage, is refused
; :interrupted-init with the stage as its one argument: never accepted (no
; action runs, no open is attempted), exit the refusal code 1, and its hint
; names the stage and says to run init, which discards the stage and
; proceeds (PKT-894).
(defthm fn-nsst-absent-store-beside-an-init-stage-names-it
  (implies (and (fn-native-operator-result-needs-storep result)
                (not (consp observed))
                (stringp init-stage))
           (let ((outcome (fn-nsst-store-outcome result observed init-stage
                                                 import-stage)))
             (and (equal (fn-native-operator-result-status outcome) :refused)
                  (equal (fn-native-operator-result-reason outcome)
                         :interrupted-init)
                  (equal (fn-native-operator-result-arguments outcome)
                         (list init-stage))
                  (equal (fn-native-operator-exit-code outcome)
                         (fn-outcome-code :refused))
                  (equal (fn-native-operator-result-native-action outcome) :none)
                  (equal (fn-nsst-result-hint outcome)
                         (concatenate 'string
                                      "no store at the configured [store] path: an init was interrupted before it published the store; its stage "
                                      init-stage
                                      " remains; it holds nothing any command acknowledged. Run: fn operator CONFIG init GROUP... (init removes the stage)")))))
  :hints (("Goal" :in-theory '(fn-nsst-store-outcome fn-nsst-stage-refusal
                                fn-nop-refused fn-nop-result fn-nsst-refused-fields
                                fn-nsst-result-hint fn-ncfg-first car-cons))))

; The import stage, when no init stage is there.
(defthm fn-nsst-absent-store-beside-an-import-stage-names-it
  (implies (and (fn-native-operator-result-needs-storep result)
                (not (consp observed))
                (not (stringp init-stage))
                (stringp import-stage))
           (let ((outcome (fn-nsst-store-outcome result observed init-stage
                                                 import-stage)))
             (and (equal (fn-native-operator-result-status outcome) :refused)
                  (equal (fn-native-operator-result-reason outcome)
                         :interrupted-import)
                  (equal (fn-native-operator-result-arguments outcome)
                         (list import-stage))
                  (equal (fn-native-operator-exit-code outcome)
                         (fn-outcome-code :refused))
                  (equal (fn-native-operator-result-native-action outcome) :none))))
  :hints (("Goal" :in-theory '(fn-nsst-store-outcome fn-nsst-stage-refusal
                                fn-nop-refused fn-nop-result
                                fn-nsst-refused-fields))))

; Without a stage, or with any store entry beside ROOT, or for a plan that
; needs no store, the outcome is PRF-130's: the stage observation refuses
; nothing the store actions would have served and changes no other answer.
(defthm fn-nsst-store-outcome-without-a-stage-is-the-store-outcome
  (implies (or (not (fn-native-operator-result-needs-storep result))
               (consp observed)
               (and (not (stringp init-stage)) (not (stringp import-stage))))
           (equal (fn-nsst-store-outcome result observed init-stage import-stage)
                  (fn-native-operator-store-outcome result observed)))
  :hints (("Goal" :in-theory '(fn-nsst-store-outcome))))

; The hint of every result but a stage refusal is the operator's.
(defthm fn-nsst-result-hint-of-another-result-unfolds
  (implies (not (member-equal (fn-native-operator-result-reason result)
                              '(:interrupted-init :interrupted-import)))
           (equal (fn-nsst-result-hint result)
                  (fn-native-operator-result-hint result)))
  :hints (("Goal" :in-theory '(fn-nsst-result-hint member-equal))))

(in-theory (disable fn-nsst-store-outcome fn-nsst-result-hint
                    fn-nsst-stage-refusal))
