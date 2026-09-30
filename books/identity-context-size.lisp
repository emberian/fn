; PRF-1120. Canonical size sidecars at the actual identity-context transition boundary.
; No context tree is scanned; old snapshot/verdict trees and their carries are
; shared. The new event's carry is supplied by its constructor/decoder.
(in-package "ACL2")
(include-book "store-tree-size")
(include-book "stx-keyring-records")

(defun fn-ics-scalar (x)
  (declare (xargs :guard t))
  (if (or (integerp x) (characterp x) (stringp x) (symbolp x))
      (fn-scs-atom x)
    (fn-scs-atom nil)))

(defthm fn-ics-scalar-is-carry
  (fn-scs-carryp (fn-ics-scalar x)))

(defun fn-ics-field (n cs)
  (declare (xargs :guard (natp n)))
  (if (consp cs)
      (if (zp n) (car cs) (fn-ics-field (1- n) (cdr cs)))
    nil))

(defun fn-ics-carriesp (cs)
  (declare (xargs :guard t))
  (fn-scs-fixed-carriesp 6 cs))

(defun fn-ics-fields (ctx snapshots verdicts)
  (declare (xargs :guard t))
  (list (fn-ics-scalar (fn-stxk-context-kind ctx))
        (fn-ics-scalar (fn-stxk-context-next ctx))
        snapshots verdicts
        (fn-ics-scalar (fn-stxk-context-current-generation ctx))
        (fn-ics-scalar (fn-stxk-context-tail ctx))))

(defun fn-ics-contextp (ctx)
  (declare (xargs :guard t))
  (and (true-listp ctx) (equal (len ctx) 6)
       (symbolp (fn-stxk-context-kind ctx))
       (natp (fn-stxk-context-next ctx))
       (or (natp (fn-stxk-context-current-generation ctx))
           (null (fn-stxk-context-current-generation ctx)))
       (symbolp (fn-stxk-context-tail ctx))))

; These wrappers call the original decision exactly once. Change in the
; checked generation identifies the original constructor's snapshot cons.
(defun fn-ics-snapshot (ctx carries event event-carry)
  (declare (xargs :guard (and (fn-ics-carriesp carries)
                              (fn-scs-carryp event-carry))
                  :verify-guards nil))
  (let* ((checked (fn-stxk-apply-snapshot ctx event))
         (snapshots (fn-ics-field 2 carries))
         (snapshots (if (equal (fn-stxk-context-current-generation checked)
                               (fn-stxk-context-current-generation ctx))
                        snapshots
                      (fn-scs-cons event-carry snapshots))))
    (mv checked (fn-ics-fields checked snapshots (fn-ics-field 3 carries)))))

(defun fn-ics-verdict (ctx carries event event-carry)
  (declare (xargs :guard (and (fn-ics-carriesp carries)
                              (fn-scs-carryp event-carry))
                  :verify-guards nil))
  (let* ((checked (fn-stxk-apply-verdict ctx event))
         (verdicts (fn-ics-field 3 carries))
         (verdicts (if (and (equal (fn-stxk-context-kind ctx) :ok)
                            (equal (fn-stxk-context-kind checked) :ok))
                       (fn-scs-cons event-carry verdicts)
                     verdicts)))
    (mv checked (fn-ics-fields checked (fn-ics-field 2 carries) verdicts))))

(local
 (defthm fn-ics-field-carryp
   (implies (and (fn-scs-carry-listp cs) (natp n) (< n (len cs)))
            (fn-scs-carryp (fn-ics-field n cs)))
   :hints (("Goal" :in-theory (enable fn-scs-carry-listp)))))
(verify-guards fn-ics-snapshot)
(verify-guards fn-ics-verdict)

; The checked context is exactly the existing transition's result: no new
; authority or publication decision in this sidecar adapter.
(defthm fn-ics-snapshot-context-is-actual-by-definition
  (equal (mv-nth 0 (fn-ics-snapshot ctx carries event event-carry))
         (fn-stxk-apply-snapshot ctx event)))
(defthm fn-ics-verdict-context-is-actual-by-definition
  (equal (mv-nth 0 (fn-ics-verdict ctx carries event event-carry))
         (fn-stxk-apply-verdict ctx event)))

(local
 (defthm fn-ics-field-of-correspondence
   (implies (and (fn-scs-correspondsp carries ctx) (natp n) (< n (len ctx)))
            (equal (fn-ics-field n carries) (fn-scs-summary (fn-ics-field n ctx))))
   :hints (("Goal" :in-theory (enable fn-scs-correspondsp)))))

(local (include-book "arithmetic/top" :dir :system))
(local
 (defthm fn-ics-len-zero
   (equal (equal (len x) 0) (not (consp x)))))

(local
 (defthm fn-ics-fields-correspond
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
 (defthm fn-ics-snapshot-generation-natural
   (implies (fn-stxk-p e) (natp (fn-stxk-keyring-generation e)))
   :hints (("Goal" :in-theory (enable fn-stxk-p fn-record-uint32p)))
   :rule-classes :forward-chaining))

(local
 (defthm fn-ics-snapshot-contextp
   (implies (fn-ics-contextp ctx)
            (fn-ics-contextp (fn-stxk-apply-snapshot ctx event)))
   :hints (("Goal" :in-theory (e/d (fn-ics-contextp fn-stxk-apply-snapshot
                                     fn-stxk-context fn-stxk-fault)
                                    (fn-stxk-p fn-stxk-find fn-stxk-same-snapshotp))))))
(local
 (defthm fn-ics-verdict-contextp
   (implies (fn-ics-contextp ctx)
            (fn-ics-contextp (fn-stxk-apply-verdict ctx event)))
   :hints (("Goal" :in-theory (e/d (fn-ics-contextp fn-stxk-apply-verdict
                                     fn-stxk-context fn-stxk-fault)
                                    (fn-stxe-p fn-stxk-find))))))

(local
 (defthm fn-ics-field-is-nth
   (equal (fn-ics-field n xs) (nth n xs))))

(local
 (defthm fn-ics-context-length
   (implies (fn-ics-contextp ctx) (equal (len ctx) 6))
   :rule-classes :forward-chaining))
(local
 (defthm fn-ics-snapshot-shared-fields
   (implies (fn-ics-contextp ctx)
    (let ((checked (fn-stxk-apply-snapshot ctx event)))
     (and
      (equal (fn-stxk-context-snapshots checked)
             (if (equal (fn-stxk-context-current-generation checked)
                        (fn-stxk-context-current-generation ctx))
                 (fn-stxk-context-snapshots ctx)
               (cons event (fn-stxk-context-snapshots ctx))))
      (equal (fn-stxk-context-verdicts checked) (fn-stxk-context-verdicts ctx)))))
   :hints (("Goal" :in-theory (e/d (fn-stxk-apply-snapshot fn-stxk-context
                                     fn-stxk-fault fn-ics-contextp)
                                    (fn-stxk-p fn-stxk-find fn-stxk-same-snapshotp))))))
(local
 (defthm fn-ics-verdict-shared-fields
   (let ((checked (fn-stxk-apply-verdict ctx event)))
    (and
     (equal (fn-stxk-context-verdicts checked)
            (if (and (equal (fn-stxk-context-kind ctx) :ok)
                     (equal (fn-stxk-context-kind checked) :ok))
                (cons event (fn-stxk-context-verdicts ctx))
              (fn-stxk-context-verdicts ctx)))
     (equal (fn-stxk-context-snapshots checked) (fn-stxk-context-snapshots ctx))))
   :hints (("Goal" :in-theory (e/d (fn-stxk-apply-verdict fn-stxk-context fn-stxk-fault)
                                    (fn-stxe-p fn-stxk-find))))))

(local
 (defthm fn-ics-field-2
   (equal (fn-ics-field 2 ctx) (fn-stxk-context-snapshots ctx))))
(local
 (defthm fn-ics-field-3
   (equal (fn-ics-field 3 ctx) (fn-stxk-context-verdicts ctx))))

(local
 (defthm fn-ics-cons-summaries
   (equal (fn-scs-cons (fn-scs-summary x) (fn-scs-summary y))
          (fn-scs-summary (cons x y)))
   :hints (("Goal" :use ((:instance fn-scs-cons-preserves-canonical-size
                                    (a (fn-scs-summary x)) (d (fn-scs-summary y))))))))

(defthm fn-ics-snapshot-preserves-canonical-size
  (implies (and (fn-ics-contextp ctx) (fn-scs-correspondsp carries ctx)
                (equal event-carry (fn-scs-summary event)))
           (fn-scs-correspondsp
            (mv-nth 1 (fn-ics-snapshot ctx carries event event-carry))
            (mv-nth 0 (fn-ics-snapshot ctx carries event event-carry))))
  :hints (("Goal"
           :use ((:instance fn-ics-field-of-correspondence (n 2))
                 (:instance fn-ics-field-of-correspondence (n 3)))
           :in-theory (e/d (fn-ics-snapshot)
                            (fn-ics-fields fn-ics-field fn-ics-field-is-nth
                             fn-ics-contextp fn-scs-correspondsp
                             fn-stxk-context-snapshots fn-stxk-context-verdicts
                             fn-stxk-context-current-generation fn-stxk-context-kind
                             fn-stxk-apply-snapshot)))))

(defthm fn-ics-verdict-preserves-canonical-size
  (implies (and (fn-ics-contextp ctx) (fn-scs-correspondsp carries ctx)
                (equal event-carry (fn-scs-summary event)))
           (fn-scs-correspondsp
            (mv-nth 1 (fn-ics-verdict ctx carries event event-carry))
            (mv-nth 0 (fn-ics-verdict ctx carries event event-carry))))
  :hints (("Goal"
           :use ((:instance fn-ics-field-of-correspondence (n 2))
                 (:instance fn-ics-field-of-correspondence (n 3)))
           :in-theory (e/d (fn-ics-verdict)
                            (fn-ics-fields fn-ics-field fn-ics-field-is-nth
                             fn-ics-contextp fn-scs-correspondsp
                             fn-stxk-context-snapshots fn-stxk-context-verdicts
                             fn-stxk-context-current-generation fn-stxk-context-kind
                             fn-stxk-apply-verdict)))))

(in-theory (disable fn-ics-scalar fn-ics-field fn-ics-carriesp fn-ics-fields
                    fn-ics-contextp fn-ics-snapshot fn-ics-verdict))

; The empty Store context starts with exact carries, before any event is added.
(defun fn-ics-begin (next)
  (declare (xargs :guard (natp next)))
  (let ((ctx (fn-stxk-initial-context next)))
    (mv ctx (fn-ics-fields ctx (fn-scs-atom nil) (fn-scs-atom nil)))))

(defthm fn-ics-begin-establishes-canonical-size
  (implies (natp next)
           (and (fn-ics-contextp (mv-nth 0 (fn-ics-begin next)))
                (fn-scs-correspondsp (mv-nth 1 (fn-ics-begin next))
                                     (mv-nth 0 (fn-ics-begin next)))))
  :hints (("Goal" :in-theory (enable fn-ics-begin fn-ics-contextp fn-ics-fields
                                    fn-ics-scalar fn-stxk-initial-context
                                    fn-stxk-context fn-scs-correspondsp))))
(in-theory (disable fn-ics-begin))
