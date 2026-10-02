; UNHOOKED cert-roots (2026-10-02): out of the Makefile certify roots -- its include closure reaches host/owner-host.lisp, which `ld's host/store-node-host.lisp and so is a host file, never a certifiable book (d4826a7b1). The code stays; it certifies again when it names the books it needs instead of the owner host file.
(in-package "ACL2")
(include-book "../../books/admission-semantic-census-step-refinement")
; Corrupted-source witness: actual slot + actual writer gate, never a funds
; fixture or a claim that this malformed source came from accepted Store.
(defun rccap-step-invalid-fixture (state)
 (declare (xargs :stobjs state :mode :program))
 (let* ((token '(:admission-grant 1 0 0 0 0 :identity))
        (current (list token nil :reserved '(old-roots) nil))
        (parent '(:history-installed 0 0 0 0 0))
        (source '(invalid-source)) (remap '(retained-remap))
        (census '(:need-row 1 0 0 nil nil nil))
        (job (list :history-census token source remap census))
        (state (f-put-global 'fn-owner-canonical-admission-pending current state))
        (state (f-put-global 'fn-owner-canonical-admission-executor '(same-intent) state))
        (state (f-put-global 'fn-owner-canonical-epoch 0 state))
        (state (f-put-global 'fn-owner-history-completion-fault nil state))
        (state (f-put-global 'fn-owner-history-publication parent state))
        (lease (list :history-semantic-source token parent '(same-source)))
        (state (f-put-global 'fn-owner-history-semantic-source lease state))
        (state (f-put-global 'fn-owner-history-semantic-census job state))
        (antecedent (and (fn-apr-tokenp token) (fn-apr-livep token current)
          (eq (fn-owner-history-writer-gate token state) :writer-current)
          (fn-apr-widthp 5 job) (eq (fn-prl-nth 0 job) :history-census)
          (fn-apr-tokenp (fn-prl-nth 1 job)) (equal token (fn-prl-nth 1 job))
          (eq (fn-omk-at 0 census) :need-row) (not (fn-osrc-guardp source)))))
  (mv-let (word state) (fn-owner-admission-census-step-logic state)
   (let ((ok (and antecedent (eq word :recovery-required)
     (equal (f-get-global 'fn-owner-history-semantic-census state)
            (list :history-census-fenced token source remap census))
     (equal (fn-apr-owner-current state) current)
     (equal (f-get-global 'fn-owner-canonical-admission-executor state) '(same-intent))
     (equal (f-get-global 'fn-owner-history-semantic-source state) lease))))
    (mv-let (again state) (fn-owner-admission-census-step-logic state)
     (mv (and ok (eq again :recovery-required)
       (equal (f-get-global 'fn-owner-history-semantic-census state)
              (list :history-census-fenced token source remap census))) state))))))
(make-event (mv-let (ok state) (rccap-step-invalid-fixture state)
 (value (list 'assert-event ok))))

; Literal resident model witness at the actual registered STEP boundary.
; This isolated source cursor is not a captured accepted Store or funds.
(thm
 (let* ((token '(:admission-grant 1 0 0 0 0 :identity))
        (current (list token nil :reserved '(old-roots) nil))
        (parent '(:history-installed 0 0 0 0 0))
        (source '(:suffix (:raw nil) 0 1 0 nil 0 nil (nil) 7 (11 1) (nil) 0))
        (expected '(7 (11 1) 0 0))
        (remapper (fn-osm-begin expected))
        (census (fn-hct-begin 1 '(11 1) :lease))
        (job (list :history-census token source remapper census))
        (state (f-put-global 'fn-owner-canonical-admission-pending current state))
        (state (f-put-global 'fn-owner-canonical-admission-executor '(same-intent) state))
        (state (f-put-global 'fn-owner-canonical-epoch 0 state))
        (state (f-put-global 'fn-owner-history-completion-fault nil state))
        (state (f-put-global 'fn-owner-history-publication parent state))
        (state (f-put-global 'fn-owner-history-semantic-source
          (list :history-semantic-source token parent '(same-source)) state))
        (state (f-put-global 'fn-owner-history-semantic-census job state))
        (step (fn-osrc-tick source nil))
        (next-source (fn-osrc-at 4 step))
        (mapped (mv-nth 0 (fn-osm-row-source '(:resident nil) 0)))
        (row (fn-omk-at 1 mapped))
        (next-state (mv-nth 1 (fn-owner-admission-census-step-logic state)))
        (next-job (f-get-global 'fn-owner-history-semantic-census next-state)))
  (and (fn-apr-tokenp token) (fn-apr-livep token current)
       (eq (fn-owner-history-writer-gate token state) :writer-current)
       (fn-apr-widthp 5 job) (eq (fn-prl-nth 0 job) :history-census)
       (fn-apr-tokenp (fn-prl-nth 1 job)) (equal token (fn-prl-nth 1 job))
       (eq (fn-omk-at 0 census) :need-row)
       (fn-osrc-guardp source) (not (eq (fn-osrc-at 0 source) :waiting))
       (equal step (list :row (fn-omk-at 3 expected) '(:resident nil) expected next-source))
       (fn-rccap-idle-original-prefixp remapper census nil)
       (fn-omk-widthp mapped 2)
       (natp (mv-nth 1 (fn-osm-row-source '(:resident nil) 0)))
       (fn-hrcur-tree-domainp row)
       (< (len (fn-scc-encode row)) *fn-hrcur-u64-bound*)
       (eq (car (mv-nth 0 (fn-osm-offer remapper expected '(:resident nil)))) :mapped)
       (equal (fn-prl-nth 1 next-job) token)
       (equal (fn-prl-nth 2 next-job) next-source)
       (fn-rccap-waiting-original-prefixp
         (fn-prl-nth 3 next-job) (fn-prl-nth 4 next-job) nil nil row nil)
       (eq (mv-nth 0 (fn-owner-admission-census-step-logic state)) :continue)
       (eq (fn-prl-nth 0 next-job) :history-census)))
 :hints (("Goal" :in-theory (enable fn-rccap-idle-original-prefixp
  fn-rccap-waiting-original-prefixp fn-rccap-remapped-prefix
  fn-rcca-idle-prefixp fn-rcca-waiting-rowp fn-rcct-current-row-invariantp
  fn-hsrcc-invariantp fn-hsrcc-total fn-hsrcb-invariantp fn-hsrcb-rest
  fn-hsrcb-coldp fn-hrcur-census-invariantp fn-hrcur-census-total
  fn-hrcur-byte-invariantp fn-hrcur-byte-rest fn-hct-shapep
  fn-owner-admission-census-step-logic fn-owner-history-writer-gate
  fn-apr-owner-current fn-owner-canonical-epoch))))

; Hypothesis-removal corrupted-state witness: only source scalar guard fails;
; all other resident Offer antecedents hold, while actual STEP fences.
(thm
 (let* ((token '(:admission-grant 1 0 0 0 0 :identity))
        (current (list token nil :reserved '(old-roots) nil))
        (parent '(:history-installed 0 0 0 0 0))
        (source '(:suffix (:raw nil) 0 1 0 nil -1 nil (nil) 7 (11 1) (nil) 0))
        (expected '(7 (11 1) 0 0))
        (remapper (fn-osm-begin expected))
        (census (fn-hct-begin 1 '(11 1) :lease))
        (job (list :history-census token source remapper census))
        (state (f-put-global 'fn-owner-canonical-admission-pending current state))
        (state (f-put-global 'fn-owner-canonical-admission-executor '(same-intent) state))
        (state (f-put-global 'fn-owner-canonical-epoch 0 state))
        (state (f-put-global 'fn-owner-history-completion-fault nil state))
        (state (f-put-global 'fn-owner-history-publication parent state))
        (state (f-put-global 'fn-owner-history-semantic-source
          (list :history-semantic-source token parent '(same-source)) state))
        (state (f-put-global 'fn-owner-history-semantic-census job state))
        (step (fn-osrc-tick source nil))
        (next-source (fn-osrc-at 4 step))
        (mapped (mv-nth 0 (fn-osm-row-source '(:resident nil) 0)))
        (row (fn-omk-at 1 mapped))
        (next-state (mv-nth 1 (fn-owner-admission-census-step-logic state)))
        (next-job (f-get-global 'fn-owner-history-semantic-census next-state)))
  (and (fn-apr-tokenp token) (fn-apr-livep token current)
       (eq (fn-owner-history-writer-gate token state) :writer-current)
       (fn-apr-widthp 5 job) (eq (fn-prl-nth 0 job) :history-census)
       (fn-apr-tokenp (fn-prl-nth 1 job)) (equal token (fn-prl-nth 1 job))
       (eq (fn-omk-at 0 census) :need-row)
       (not (fn-osrc-guardp source)) (not (eq (fn-osrc-at 0 source) :waiting))
       (equal step (list :row (fn-omk-at 3 expected) '(:resident nil) expected next-source))
       (fn-rccap-idle-original-prefixp remapper census nil)
       (fn-omk-widthp mapped 2)
       (natp (mv-nth 1 (fn-osm-row-source '(:resident nil) 0)))
       (fn-hrcur-tree-domainp row)
       (< (len (fn-scc-encode row)) *fn-hrcur-u64-bound*)
       (eq (car (mv-nth 0 (fn-osm-offer remapper expected '(:resident nil)))) :mapped)
       (equal (fn-prl-nth 1 next-job) token)
       (not (equal (fn-prl-nth 2 next-job) next-source))
       (not (fn-rccap-waiting-original-prefixp
         (fn-prl-nth 3 next-job) (fn-prl-nth 4 next-job) nil nil row nil))
       (eq (mv-nth 0 (fn-owner-admission-census-step-logic state)) :recovery-required)
       (eq (fn-prl-nth 0 next-job) :history-census-fenced)))
 :hints (("Goal" :in-theory (enable fn-rccap-idle-original-prefixp
  fn-rccap-waiting-original-prefixp fn-rccap-remapped-prefix
  fn-rcca-idle-prefixp fn-rcca-waiting-rowp fn-rcct-current-row-invariantp
  fn-hsrcc-invariantp fn-hsrcc-total fn-hsrcb-invariantp fn-hsrcb-rest
  fn-hsrcb-coldp fn-hrcur-census-invariantp fn-hrcur-census-total
  fn-hrcur-byte-invariantp fn-hrcur-byte-rest fn-hct-shapep
  fn-owner-admission-census-step-logic fn-owner-history-writer-gate
  fn-apr-owner-current fn-owner-canonical-epoch))))
