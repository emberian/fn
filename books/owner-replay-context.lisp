; Original full identity replay accumulator and fixed-width bootstrap bookkeeping.
; One authenticated, usable retained row is consumed per scheduling step.
; Borrowed decoder roots are not resident contexts and cannot enter this API.
(in-package "ACL2")
(include-book "replay-identity-size")
(include-book "snapshot-source-token")
(local (in-theory (disable (tau-system))))

; Fixed six-cell state. All child collections remain opaque shared pointers.
; PHASE SOURCE TOTAL CONSUMED ORIGINAL-FULLCTX SIX-FIELD-CARRIES.
(defun fn-orcb-at (n x)
 (declare (xargs :guard (natp n) :measure (nfix n)))
 (if (zp n) (if (consp x) (car x) nil)
  (fn-orcb-at (1- n) (if (consp x) (cdr x) nil))))
(defun fn-orcb-statep (s)
 (declare (xargs :guard t))
 (and (fn-omk-widthp s 6)
      (member-eq (fn-orcb-at 0 s) '(:replaying :ready :refused))
      (fn-omk-tokenp (fn-orcb-at 1 s))
      (natp (fn-orcb-at 2 s)) (natp (fn-orcb-at 3 s))
      (<= (fn-orcb-at 3 s) (fn-orcb-at 2 s))
      (fn-omk-widthp (fn-orcb-at 4 s) 6)
      (fn-ics-contextp (fn-orcb-at 4 s))
      (fn-ics-carriesp (fn-orcb-at 5 s))))
(defun fn-orcb-state (phase source total consumed ctx carries)
 (declare (xargs :guard t))
 (list phase source total consumed ctx carries))

(defun fn-orcb-begin (source total)
 (declare (xargs :guard (and (fn-omk-tokenp source) (natp total))))
 (mv-let (ctx carries) (fn-ics-begin 0)
  (let ((phase (if (zp total) :ready :replaying)))
   (mv phase (fn-orcb-state phase source total 0 ctx carries)))))

(defun fn-orcb-row-source (s)
 (declare (xargs :guard (fn-orcb-statep s)
                  :guard-hints (("Goal" :in-theory (enable fn-orcb-statep fn-orcb-at fn-omk-tokenp)))))
 (let ((base (fn-orcb-at 1 s)))
  (list (fn-omk-at 0 base) (fn-omk-at 1 base) (fn-omk-at 2 base)
        (+ (fn-omk-at 3 base) (fn-orcb-at 3 s)))))

; SOURCE is the source identity actually returned by the authenticated row
; provider. The controller supplies the constructor/decoder's exact carry
; of the actual appended snapshot/verdict child; it computes none itself.
(defun fn-orcb-step (s source row child-carry)
 (declare (xargs :guard (and (fn-orcb-statep s)
                             (fn-scs-carryp child-carry))
                  :verify-guards nil))
 (let ((phase (fn-orcb-at 0 s)) (expected (fn-orcb-at 1 s))
       (total (fn-orcb-at 2 s)) (consumed (fn-orcb-at 3 s))
       (ctx (fn-orcb-at 4 s)) (carries (fn-orcb-at 5 s)))
  (if (not (and (eq phase :replaying)
                (fn-omk-token-matchp source (fn-orcb-row-source s))
                (< consumed total)))
   (mv :refused (fn-orcb-state :refused expected total consumed ctx carries))
   (mv-let (next next-carries) (fn-ris-step ctx carries row child-carry)
    (let* ((count (1+ consumed))
           (phase (cond ((not (eq (fn-stxk-context-kind next) :ok)) :refused)
                        ((equal count total) :ready) (t :replaying))))
     (mv phase (fn-orcb-state phase expected total count next next-carries)))))))

(verify-guards fn-orcb-step
 :hints (("Goal" :in-theory (enable fn-orcb-statep fn-orcb-at))))
(defthm fn-orcb-begin-has-initial-original-context
 (implies (and (fn-omk-tokenp source) (natp total))
  (and (equal (fn-orcb-at 4 (mv-nth 1 (fn-orcb-begin source total)))
              (fn-stxk-initial-context 0))
       (fn-scs-correspondsp
        (fn-orcb-at 5 (mv-nth 1 (fn-orcb-begin source total)))
        (fn-orcb-at 4 (mv-nth 1 (fn-orcb-begin source total))))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-ics-begin-establishes-canonical-size (next 0)))
          :in-theory (e/d (fn-orcb-begin fn-orcb-state fn-orcb-at)
                          (fn-ics-begin fn-scs-correspondsp)))))
(defthm fn-orcb-one-row-is-the-actual-original-replay
 (implies (and (fn-orcb-statep s)
               (eq (fn-orcb-at 0 s) :replaying)
               (fn-omk-token-matchp source (fn-orcb-row-source s))
               (< (fn-orcb-at 3 s) (fn-orcb-at 2 s)))
  (equal (fn-orcb-at 4 (mv-nth 1 (fn-orcb-step s source row child-carry)))
         (fn-replay-identity-step (fn-orcb-at 4 s) row)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-ris-step-is-actual-replay-by-definition
                      (ctx (fn-orcb-at 4 s)) (carries (fn-orcb-at 5 s))
                      (event row)))
          :in-theory (e/d (fn-orcb-step fn-orcb-state fn-orcb-at)
                          (fn-ris-step fn-replay-identity-step fn-orcb-statep
                           fn-omk-token-matchp)))))

; Constant-size installation packet. The field carries retain all six fields.
; The complete canonical ready tuple is installed by owner-canonical-state.
(defun fn-orcb-install (s source)
 (declare (xargs :guard (fn-orcb-statep s) :verify-guards nil))
 (if (and (eq (fn-orcb-at 0 s) :ready)
          (equal (fn-orcb-at 3 s) (fn-orcb-at 2 s))
          (equal (fn-stxk-context-next (fn-orcb-at 4 s)) (fn-orcb-at 3 s))
          (eq (fn-stxk-context-kind (fn-orcb-at 4 s)) :ok)
          (fn-omk-token-matchp source (fn-orcb-at 1 s)))
  (list :ready (fn-orcb-at 4 s) (fn-scs-spine (fn-orcb-at 5 s))
        (fn-orcb-at 5 s) (fn-orcb-at 1 s) (fn-orcb-at 2 s))
  (list :refused nil nil nil nil nil)))

(verify-guards fn-orcb-install
 :hints (("Goal" :in-theory (enable fn-orcb-statep fn-orcb-at fn-ics-carriesp
                                    fn-scs-fixed-carriesp fn-scs-carry-listp))))
; Resident open already has the original full accumulator in its extended
; checkpoint. Exact carries come from that source's constructor/decoder.
(defun fn-orcb-resident (source total ctx carries)
 (declare (xargs :guard (and (fn-omk-tokenp source) (natp total)
                             (fn-ics-contextp ctx) (fn-ics-carriesp carries))))
 (let ((phase (if (and (eq (fn-stxk-context-kind ctx) :ok)
                       (equal (fn-stxk-context-next ctx) total)) :ready :refused)))
  (mv phase (fn-orcb-state phase source total total ctx carries))))

; Live completion invokes the same actual replay decision, once. The owner
; calls only for the row it durably completed and supplies its issued source
; identity. Source scalar0 is the captured Store frontier, which can change
; across ordinary captures; it is not a process incarnation. Actual owner
; completion authenticates the issued operation and its predecessor before
; this leaf. A restart never derives the accumulator from a Store projection.
(defun fn-orcb-append (s source row child-carry)
 (declare (xargs :guard (and (fn-orcb-statep s) (fn-omk-tokenp source)
                             (fn-scs-carryp child-carry))
                  :verify-guards nil))
 (let ((ctx (fn-orcb-at 4 s)) (carries (fn-orcb-at 5 s))
       (total (fn-orcb-at 2 s)) (consumed (fn-orcb-at 3 s)))
  (if (not (and (eq (fn-orcb-at 0 s) :ready) (equal consumed total)))
   (mv :refused (fn-orcb-state :refused (fn-orcb-at 1 s) total consumed ctx carries))
   (mv-let (next next-carries) (fn-ris-step ctx carries row child-carry)
    (let ((phase (if (eq (fn-stxk-context-kind next) :ok) :ready :refused)))
     (mv phase (fn-orcb-state phase source (1+ total) (1+ consumed) next next-carries)))))))
(verify-guards fn-orcb-append
 :hints (("Goal" :in-theory (enable fn-orcb-statep fn-orcb-at))))
(local
 (defthm fn-orcb-selected-carry-valid-by-definition
  (implies (fn-ics-carriesp carries)
   (and (fn-scs-carryp (fn-ics-field 2 carries))
        (fn-scs-carryp (fn-ics-field 3 carries))))
  :hints (("Goal" :do-not-induct t
           :expand ((fn-scs-fixed-carriesp 6 carries)
                    (fn-scs-fixed-carriesp 5 (cdr carries))
                    (fn-scs-fixed-carriesp 4 (cddr carries))
                    (fn-scs-fixed-carriesp 3 (cdddr carries))
                    (fn-ics-field 2 carries) (fn-ics-field 3 carries)
                    (fn-ics-field 1 (cdr carries)) (fn-ics-field 2 (cdr carries))
                    (fn-ics-field 0 (cddr carries)) (fn-ics-field 1 (cddr carries))
                    (fn-ics-field 0 (cdddr carries)))
           :in-theory (enable fn-ics-carriesp)))))

(local
 (defthm fn-orcb-replay-preserves-carry-shape
  (implies (and (fn-ics-carriesp carries) (fn-scs-carryp child-carry))
   (fn-ics-carriesp (mv-nth 1 (fn-ris-step ctx carries row child-carry))))
  :hints (("Goal" :in-theory
   (e/d (fn-ris-step fn-ics-carriesp fn-ics-fields fn-scs-fixed-carriesp)
        (fn-replay-identity-effects fn-ics-scalar fn-scs-cons fn-ics-field))))))
(defthm fn-orcb-row-preserves-exact-full-context-carries
 (implies
  (and (fn-orcb-statep s)
       (fn-scs-correspondsp (fn-orcb-at 5 s) (fn-orcb-at 4 s))
       (implies (member-eq (mv-nth 1 (fn-replay-identity-effects (fn-orcb-at 4 s) row))
                           '(:snapshot :verdict))
                (equal child-carry
                 (fn-scs-summary
                  (mv-nth 2 (fn-replay-identity-effects (fn-orcb-at 4 s) row))))))
  (fn-scs-correspondsp
   (fn-orcb-at 5 (mv-nth 1 (fn-orcb-step s source row child-carry)))
   (fn-orcb-at 4 (mv-nth 1 (fn-orcb-step s source row child-carry)))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-ris-step-preserves-canonical-size
         (ctx (fn-orcb-at 4 s)) (carries (fn-orcb-at 5 s)) (event row)))
  :in-theory (e/d (fn-orcb-step fn-orcb-state fn-orcb-at fn-orcb-statep)
                 (fn-scs-correspondsp fn-ris-step fn-replay-identity-effects
                  fn-scs-summary fn-ics-contextp fn-ics-carriesp fn-omk-token-matchp)))))

(local (defthm fn-orcb-width-from-proper-length
 (implies (and (natp n) (true-listp x) (equal (len x) n))
          (fn-omk-widthp x n))
 :hints (("Goal" :induct (fn-omk-widthp x n)
          :in-theory (enable fn-omk-widthp)))))
(defthm fn-orcb-step-preserves-bootstrap-shape
 (implies (and (fn-orcb-statep s) (fn-scs-carryp child-carry))
  (fn-orcb-statep (mv-nth 1 (fn-orcb-step s source row child-carry))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-orcb-replay-preserves-carry-shape
         (ctx (fn-orcb-at 4 s)) (carries (fn-orcb-at 5 s)))
        (:instance fn-ris-actual-effects-shared-lists
         (ctx (fn-orcb-at 4 s)) (event row)))
  :in-theory (e/d (fn-orcb-step fn-orcb-state fn-orcb-statep fn-orcb-at
                   fn-omk-widthp fn-ics-contextp fn-ris-step fn-ics-fields fn-ics-carriesp fn-scs-fixed-carriesp)
                 (fn-replay-identity-effects fn-ics-scalar fn-scs-cons fn-ics-field fn-omk-token-matchp)))))


; A validated prefix summary seeds the original accumulator at its actual
; sequence. The producer separately establishes that this is the SAME prefix
; of the captured Store. Numeric sequence/frontier equality is insufficient.
; A full-history cursor must advance past CONSUMED prefix rows before STEP;
; a suffix-only cursor needs an explicit ordinal-offset correspondence.
(defun fn-orcb-seed (source total consumed ctx carries)
 (declare (xargs :guard (and (fn-omk-tokenp source) (natp total) (natp consumed)
                             (<= consumed total) (fn-ics-contextp ctx)
                             (fn-ics-carriesp carries))))
 (let ((phase (if (and (eq (fn-stxk-context-kind ctx) :ok)
                       (equal (fn-stxk-context-next ctx) consumed))
                  (if (equal consumed total) :ready :replaying) :refused)))
  (mv phase (fn-orcb-state phase source total consumed ctx carries))))
