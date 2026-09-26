; Teeth of books/outcome-class.lisp and the families' PRF-143 keystones
; (specs/host.md "CLI exit codes", HST-009).  Per keystone a reachable
; witness; per hypothesis a witness that holds the retained hypotheses, fails
; the omitted one and fails the conclusion, then a must-fail of the weakened
; theorem (its search cut short on purpose; the counterexample is the
; assert-event before it).
(in-package "ACL2")
(include-book "../../books/bp-run-class")
(include-book "../../books/native-operator")
(include-book "../../books/topic-history-local-control")
(include-book "std/testing/must-fail" :dir :system)

;; ---------------------------------------------------------------------------
;; fn-outcome-code-separates-the-classes.  Witness: the seven classes answer
;; seven different codes.
(assert-event
 (equal (list (fn-outcome-code :accepted) (fn-outcome-code :refused)
              (fn-outcome-code :fenced) (fn-outcome-code :fault)
              (fn-outcome-code :usage) (fn-outcome-code :interrupted)
              (fn-outcome-code :not-connected))
        '(0 1 3 4 5 6 7)))
(assert-event (and (fn-outcome-classp :interrupted) (fn-outcome-classp :refused)
                   (not (equal (fn-outcome-code :interrupted)
                               (fn-outcome-code :refused)))))
;; Without (fn-outcome-classp c1): a word that is no class answers the fenced
;; code and collides with :fenced.
(assert-event (and (not (fn-outcome-classp :bogus)) (fn-outcome-classp :fenced)
                   (not (equal :bogus :fenced))
                   (equal (fn-outcome-code :bogus) (fn-outcome-code :fenced))))
(must-fail
 (defthm oct-separates-without-c1
   (implies (and (fn-outcome-classp :fenced) (not (equal :bogus :fenced)))
            (not (equal (fn-outcome-code :bogus) (fn-outcome-code :fenced))))))
(must-fail
 (defthm oct-separates-without-c2
   (implies (and (fn-outcome-classp :fenced) (not (equal :fenced :bogus)))
            (not (equal (fn-outcome-code :fenced) (fn-outcome-code :bogus))))))
;; Without (not (equal c1 c2)): one class, one code.
(assert-event (and (fn-outcome-classp :usage)
                   (equal (fn-outcome-code :usage) (fn-outcome-code :usage))))
(must-fail
 (defthm oct-separates-without-distinct
   (implies (and (fn-outcome-classp :usage) (fn-outcome-classp :usage))
            (not (equal (fn-outcome-code :usage) (fn-outcome-code :usage))))))

;; ---------------------------------------------------------------------------
;; fn-outcome-code-is-fenced-iff-fenced.  Witness: :fenced is 3, :refused not.
(assert-event (and (fn-outcome-classp :fenced) (equal (fn-outcome-code :fenced) 3)))
(assert-event (and (fn-outcome-classp :refused) (not (equal (fn-outcome-code :refused) 3))))
;; Without (fn-outcome-classp class): a non-class answers 3 and is not :fenced.
(assert-event (and (not (fn-outcome-classp :bogus))
                   (equal (fn-outcome-code :bogus) 3)
                   (not (equal :bogus :fenced))))
(must-fail
 (defthm oct-fenced-iff-without-classp
   (equal (equal (fn-outcome-code class) (fn-outcome-code :fenced))
          (equal class :fenced))
   :hints (("Goal" :do-not-induct t :in-theory (theory 'minimal-theory)))))

;; fn-outcome-of-status-fences-iff-uncertain and the host conditions (no
;; hypotheses): both directions reachable.
(assert-event (equal (fn-outcome-code (fn-outcome-of-status :uncertain)) 3))
(assert-event (equal (fn-outcome-code (fn-outcome-of-status :refused)) 1))
(assert-event (equal (fn-outcome-code (fn-outcome-of-status :bogus)) 4))
(assert-event (equal (fn-outcome-host-condition-exit-code :indeterminate) 3))
(assert-event (equal (list (fn-outcome-host-condition-exit-code :refusal)
                           (fn-outcome-host-condition-exit-code :usage)
                           (fn-outcome-host-condition-exit-code :fault)
                           (fn-outcome-host-condition-exit-code :bogus))
                     '(1 5 4 4)))

;; ---------------------------------------------------------------------------
;; BP: fn-bprc-run-exit-code-is-fenced-iff-fenced (no hypotheses).
(assert-event (equal (fn-bprc-run-exit-code (fn-bprc-note (fn-bprc-empty) :fenced)) 3))
(assert-event (equal (fn-bprc-run-exit-code (fn-bprc-note (fn-bprc-empty) :uncertain)) 6))
(assert-event (equal (fn-bprc-run-exit-code (fn-bprc-note (fn-bprc-empty) :failed)) 7))
;; fn-bprc-decode-never-fences.  Witness: the clock-undecided verdict exits 1.
(assert-event (equal (fn-bprc-decode-exit-code :uncertain) 1))
(assert-event (equal (fn-bprc-decode-exit-code :accepted) 0))
;; Without (equal outcome :uncertain) the second conjunct fails: :accepted is 0.
(assert-event (and (not (equal :accepted :uncertain))
                   (not (equal (fn-bprc-decode-exit-code :accepted)
                               (fn-outcome-code :refused)))))
(must-fail
 (defthm oct-decode-without-uncertain
   (equal (fn-bprc-decode-exit-code outcome) (fn-outcome-code :refused))
   :hints (("Goal" :do-not-induct t :in-theory (theory 'minimal-theory)))))

;; ---------------------------------------------------------------------------
;; Operator: fn-native-operator-exit-is-fenced-iff-uncertain (no hypotheses).
(assert-event (equal (fn-native-operator-exit-code
                      (fn-nop-result :uncertain :publication "store" nil nil)) 3))
;; NO-STORE is a refusal (specs/host.md "CLI exit codes": 1), never 3 or 6.
(assert-event (equal (fn-native-operator-exit-code
                      (fn-nop-refused :no-store "status" nil nil)) 1))
(assert-event (equal (fn-native-operator-exit-code
                      (fn-nop-usage :bad "status" nil nil)) 5))

;; ---------------------------------------------------------------------------
;; Control: fn-native-control-exit-is-fenced-iff-uncertain (no hypotheses).
(assert-event (equal (fn-native-control-status-exit-code :uncertain) 3))
(assert-event (equal (fn-native-control-status-exit-code :conflict) 1))
(assert-event (equal (fn-thlc-status-exit-code :replayed-historical) 0))
(assert-event (equal (fn-thlc-status-exit-code :uncertain) 3))

;; fn-native-control-conflict-is-a-refusal.  Witness: an owner refusal whose
;; completion word was :conflict answers :conflict.
(assert-event (equal (fn-native-control-completion-status :refused :conflict) :conflict))
;; Without the first conjunct's link to the owner: an owner acceptance is never
;; renamed, whatever word the host passed.
(assert-event (equal (fn-native-control-completion-status :accepted :conflict) :accepted))
(assert-event (equal (fn-native-control-completion-status :uncertain :conflict) :uncertain))
;; Fourth conjunct, without (not (equal word :conflict)): the refusal is renamed.
(assert-event (and (equal :conflict :conflict)
                   (not (equal (fn-native-control-completion-status :refused :conflict)
                               :refused))))
(must-fail
 (defthm oct-completion-passes-without-word
   (equal (fn-native-control-completion-status :refused :conflict) :refused)))

;; fn-nctrl-conflict-keeps-every-earlier-octet.  Witness: every earlier word.
(assert-event
 (equal (fn-native-control-reply-encode :article-exceeds-profile-bound)
        (fn-nctrl-reply-encode-with *fn-nctrl-statuses-before-conflict*
                                    :article-exceeds-profile-bound)))
(assert-event
 (not (equal (fn-native-control-reply-encode :accepted) :bad)))
;; Without the membership hypothesis: :conflict is sealed now and was :bad.
(assert-event
 (and (not (member-equal :conflict *fn-nctrl-statuses-before-conflict*))
      (not (equal (fn-native-control-reply-encode :conflict)
                  (fn-nctrl-reply-encode-with *fn-nctrl-statuses-before-conflict*
                                              :conflict)))))
(must-fail
 (defthm oct-octets-without-membership
   (equal (fn-native-control-reply-encode status)
          (fn-nctrl-reply-encode-with *fn-nctrl-statuses-before-conflict* status))
   :hints (("Goal" :do-not-induct t :in-theory (theory 'minimal-theory)))))

;; The round trip of the new word, executed (the seal's digest runs under its
;; attachment here; in a proof it is A-CRYPTO's constrained function).
(assert-event
 (equal (fn-native-control-reply-decode (fn-native-control-reply-encode :conflict))
        :conflict))
(assert-event
 (equal (fn-native-control-reply-decode (fn-native-control-reply-encode :busy))
        :busy))
;; An image before :conflict decodes the new word as :bad; every earlier word
;; it still decodes.
(assert-event
 (equal (fn-nctrl-reply-decode-with *fn-nctrl-statuses-before-conflict*
                                    (fn-native-control-reply-encode :conflict))
        :bad))
(assert-event
 (equal (fn-nctrl-reply-decode-with *fn-nctrl-statuses-before-conflict*
                                    (fn-native-control-reply-encode
                                     :article-exceeds-profile-bound))
        :article-exceeds-profile-bound))
;; The old image's reading:
;; :bad is not among its statuses, so its client takes the transport outcome
;; after submission, :uncertain, exit 3.
(assert-event
 (and (not (member-equal :bad *fn-nctrl-statuses-before-conflict*))
      (equal (fn-native-control-transport-outcome :after-submission) :uncertain)
      (equal (fn-native-control-status-exit-code
              (fn-native-control-transport-outcome :after-submission))
             3)))
