; Exact six-field carry through the actual replay decision, including effects.
(in-package "ACL2")
(include-book "replay-identity-effects")
(include-book "identity-context-size")

(defun fn-ris-step (ctx carries event child-carry)
  (declare (xargs :guard (and (fn-ics-carriesp carries)
                              (fn-scs-carryp child-carry))
                  :verify-guards nil))
  (mv-let (checked effect child) (fn-replay-identity-effects ctx event)
    (declare (ignore child))
    (mv checked
        (fn-ics-fields
         checked
         (if (equal effect :snapshot)
             (fn-scs-cons child-carry (fn-ics-field 2 carries))
           (fn-ics-field 2 carries))
         (if (equal effect :verdict)
             (fn-scs-cons child-carry (fn-ics-field 3 carries))
           (fn-ics-field 3 carries))))))

(local
 (defthm fn-ris-field-carryp
   (implies (and (fn-scs-carry-listp cs) (natp n) (< n (len cs)))
            (fn-scs-carryp (fn-ics-field n cs)))
   :hints (("Goal" :in-theory (enable fn-ics-field fn-scs-carry-listp)))))
(verify-guards fn-ris-step :hints (("Goal" :in-theory (enable fn-ics-carriesp))))

(defthm fn-ris-step-is-actual-replay-by-definition
  (equal (mv-nth 0 (fn-ris-step ctx carries event child-carry))
         (fn-replay-identity-step ctx event))
  :hints (("Goal" :use fn-replay-identity-effects-context-is-original-by-definition
           :in-theory (e/d (fn-ris-step)
                           (fn-replay-identity-effects fn-replay-identity-step)))))

(local
 (defthm fn-ris-snapshot-generation-natural
   (implies (fn-stxk-p e) (natp (fn-stxk-keyring-generation e)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-stxk-p fn-record-uint32p)))))

; This is the semantic list effect, not a coordinate-equality shortcut.
(defthm fn-ris-actual-effects-shared-lists
  (implies (fn-ics-contextp ctx)
   (let ((checked (mv-nth 0 (fn-replay-identity-effects ctx event)))
         (effect (mv-nth 1 (fn-replay-identity-effects ctx event)))
         (child (mv-nth 2 (fn-replay-identity-effects ctx event))))
     (and (fn-ics-contextp checked)
          (equal (fn-stxk-context-snapshots checked)
                 (if (equal effect :snapshot)
                     (cons child (fn-stxk-context-snapshots ctx))
                   (fn-stxk-context-snapshots ctx)))
          (equal (fn-stxk-context-verdicts checked)
                 (if (equal effect :verdict)
                     (cons child (fn-stxk-context-verdicts ctx))
                   (fn-stxk-context-verdicts ctx))))))
  :hints (("Goal" :in-theory
    (e/d (fn-replay-identity-effects fn-replay-identity-verdict-effect
          fn-replay-apply-carried-verdict fn-replay-apply-revoked-verdict
          fn-replay-identity-advance fn-stxk-apply-snapshot fn-stxk-apply-verdict
          fn-stxk-fault fn-stxk-context fn-ics-contextp)
         (fn-stxk-p fn-stxe-p fn-stxa-p fn-stxk-find
          fn-stxk-same-snapshotp fn-stxe-decode-exact fn-stmt-okp
          fn-hsig-revoked-tombstone-bindsp
          fn-hsig-article-event-carried-bindsp
          fn-hsig-article-event-revoked-bindsp
          fn-hsig-article-event-snapshot-bindsp fn-stxa-bindsp
          fn-replay-identity-wire)))))

(local
 (defthm fn-ris-field-is-nth
   (equal (fn-ics-field n xs) (nth n xs))
   :hints (("Goal" :in-theory (enable fn-ics-field)))))
(local
 (defthm fn-ris-field-of-correspondence
   (implies (and (fn-scs-correspondsp carries ctx) (natp n) (< n (len ctx)))
            (equal (fn-ics-field n carries) (fn-scs-summary (fn-ics-field n ctx))))
   :hints (("Goal" :in-theory (enable fn-scs-correspondsp fn-ics-field)))))
(local
 (defthm fn-ris-len-zero
   (equal (equal (len x) 0) (not (consp x)))))
(local (include-book "arithmetic/top" :dir :system))

(local
 (defthm fn-ris-fields-correspond
   (implies (and (fn-ics-contextp ctx)
                 (equal s (fn-scs-summary (fn-stxk-context-snapshots ctx)))
                 (equal v (fn-scs-summary (fn-stxk-context-verdicts ctx))))
            (fn-scs-correspondsp (fn-ics-fields ctx s v) ctx))
   :hints (("Goal" :in-theory (enable fn-ics-contextp fn-ics-fields
                                     fn-ics-scalar fn-scs-correspondsp)
            :expand ((len ctx) (len (cdr ctx)) (len (cddr ctx))
                     (len (cdddr ctx)) (len (cddddr ctx))
                     (len (cdr (cddddr ctx))))))))
(local
 (defthm fn-ris-cons-summaries
   (equal (fn-scs-cons (fn-scs-summary x) (fn-scs-summary y))
          (fn-scs-summary (cons x y)))
   :hints (("Goal" :use ((:instance fn-scs-cons-preserves-canonical-size
                                    (a (fn-scs-summary x)) (d (fn-scs-summary y))))))))

(local
 (defthm fn-ris-context-length
   (implies (fn-ics-contextp ctx) (equal (len ctx) 6))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-ics-contextp)))))
(local
 (defthm fn-ris-field-2
   (equal (fn-ics-field 2 ctx) (fn-stxk-context-snapshots ctx))
   :hints (("Goal" :in-theory (enable fn-ics-field fn-stxk-context-snapshots)))))
(local
 (defthm fn-ris-field-3
   (equal (fn-ics-field 3 ctx) (fn-stxk-context-verdicts ctx))
   :hints (("Goal" :in-theory (enable fn-ics-field fn-stxk-context-verdicts)))))

(defthm fn-ris-step-preserves-canonical-size
  (implies
   (and (fn-ics-contextp ctx)
        (fn-scs-correspondsp carries ctx)
        (implies (member-eq (mv-nth 1 (fn-replay-identity-effects ctx event))
                            '(:snapshot :verdict))
                 (equal child-carry
                        (fn-scs-summary
                         (mv-nth 2 (fn-replay-identity-effects ctx event))))))
   (fn-scs-correspondsp
    (mv-nth 1 (fn-ris-step ctx carries event child-carry))
    (mv-nth 0 (fn-ris-step ctx carries event child-carry))))
  :hints (("Goal"
           :use (fn-ris-actual-effects-shared-lists
                 (:instance fn-ris-field-of-correspondence (n 2))
                 (:instance fn-ris-field-of-correspondence (n 3)))
           :in-theory
           (e/d (fn-ris-step member-eq)
                (fn-replay-identity-effects
                 fn-ris-actual-effects-shared-lists fn-ris-field-of-correspondence
                 fn-ics-contextp fn-ics-fields fn-ics-field
                 fn-ris-field-is-nth fn-scs-correspondsp
                 fn-stxk-context-snapshots fn-stxk-context-verdicts
                 fn-stxk-context-current-generation fn-stxk-context-kind)))))

(in-theory (disable fn-ris-step))
