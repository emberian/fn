(in-package "ACL2")
(include-book "../../books/replay-produced-evidence")
(include-book "../../books/records-attach")
; Exact existing statement interface: this source world predates the separate
; sized seam symbol, while FnSTXS invokes the actual sized implementation.
(defattach (fn-stmt-encode-items fn-stmt-encode-items-impl)
           (fn-stmt-decode-items-bounded fn-stmt-decode-items-bounded-impl)
           (fn-stmt-decode-prefix-items-bounded fn-stmt-decode-prefix-items-bounded-impl)
 :hints (("Goal" :use (fn-stmt-impl-encode-items-of-atom
                       fn-stmt-impl-encode-items-of-cons
                       fn-stmt-impl-decode-items-bounded-of-encode
                       fn-stmt-impl-decode-items-bounded-canonical
                       fn-stmt-impl-decode-items-bounded-items)
                  :in-theory (theory 'minimal-theory))))

(defconst *rpet-child* (fn-stxe-make 1 2 2 "<a@x>" :unverified '(9 8) 0 '(1 2 3)))
(make-event `(defconst *rpet-event*
 ',(fn-stxa-make 1 2 2 0 '(1 2 3) nil nil (fn-stxe-encode *rpet-child*))))
; Complete retained success and typed-length conclusion. Article is deliberately
; absent: this is parser evidence, not an article-binding acceptance witness.
(assert-event
 (let* ((event *rpet-event*) (evidence (fn-rpe-produce event))
        (result (fn-rpe-result evidence)))
  (and (fn-rpe-originp event evidence)
       (equal (fn-rpe-event evidence) event)
       (equal (fn-rpe-octets evidence) (fn-stxa-verdict-event event))
       (fn-stmt-okp result) (fn-rpe-typedp evidence) (fn-rpe-canonicalp evidence)
       (equal (fn-stmt-value result) *rpet-child*)
       (equal (fn-rpe-lengths evidence) '(5 2 3))
       (not (fn-rpe-stxa-bindsp evidence))
       (equal (fn-rpe-stxa-bindsp evidence) (fn-stxa-bindsp event)))))
; Corrupted provenance is distinct from a produced successful carrier.
(assert-event
 (let ((evidence (update-nth 4 '(99 2 3) (fn-rpe-produce *rpet-event*))))
  (and (not (fn-rpe-originp *rpet-event* evidence))
       (not (equal (fn-rpe-lengths evidence) '(5 2 3))))))
; Invalid wire octets retain their actual failure, never a fabricated ready bit.
(assert-event
 (let* ((event (fn-stxa-make 1 2 2 0 nil nil nil '(255)))
        (evidence (fn-rpe-produce event)))
  (and (fn-rpe-originp event evidence)
       (not (fn-stmt-okp (fn-rpe-result evidence)))
       (not (fn-rpe-typedp evidence)) (not (fn-rpe-canonicalp evidence))
       (not (fn-rpe-stxa-bindsp evidence))
       (equal (fn-rpe-carried-bindsp evidence)
              (fn-hsig-article-event-carried-bindsp event))
       (equal (fn-rpe-revoked-bindsp evidence)
              (fn-hsig-article-event-revoked-bindsp event)))))

(defun rpet-original-effects-conclusion (ctx event)
 (mv-let (checked effect child sizes) (fn-rpe-produced-effects ctx event)
  (declare (ignore sizes))
  (mv-let (expected expected-effect expected-child) (fn-replay-identity-effects ctx event)
   (and (equal checked expected) (equal effect expected-effect)
        (equal child expected-child)))))
(defconst *rpet-ctx* (fn-stxk-initial-context 0))
(defconst *rpet-snapshot* (fn-stxk-make 0 1 1 0 '(1) '(7 8)))
; Complete unconditional composition conclusion at reachable snapshot arm.
(assert-event
 (and (rpet-original-effects-conclusion *rpet-ctx* *rpet-snapshot*)
      (mv-let (checked effect child sizes)
       (fn-rpe-produced-effects *rpet-ctx* *rpet-snapshot*)
       (and (equal (fn-stxk-context-kind checked) :ok)
            (eq effect :snapshot) (equal child *rpet-snapshot*) (null sizes)))))
; Original early sequence refusal remains prior to composite parser work.
(assert-event
 (and (rpet-original-effects-conclusion *rpet-ctx* *rpet-event*)
      (mv-let (checked effect child sizes)
       (fn-rpe-produced-effects *rpet-ctx* *rpet-event*)
       (and (equal checked (fn-stxk-fault *rpet-ctx* :sequence))
            (eq effect :none) (null child) (null sizes)))))
 ; Corrupted article bytes inside a structurally valid retained event. This is
; a corruption witness, not an admitted producer-origin/retention witness.
(defconst *rpet-record*
 (fn-record-make 0 2 2 "<a@x>" '(1) '("example") "o" "s" "r" 1 0))
(make-event `(defconst *rpet-retained-nonbinding-event*
 ',(fn-hstxa-make
    (fn-stxa-make 0 2 2 0 '(1 2 3) '(1) '(255) (fn-stxe-encode *rpet-child*))
    (fn-held-plain *rpet-record* 0))))
(assert-event
 (and (fn-record-p *rpet-record*) (fn-hstxa-p *rpet-retained-nonbinding-event*)
      (rpet-original-effects-conclusion *rpet-ctx* *rpet-retained-nonbinding-event*)
      (mv-let (checked effect child sizes)
       (fn-rpe-produced-effects *rpet-ctx* *rpet-retained-nonbinding-event*)
       (and (equal checked (fn-stxk-fault *rpet-ctx* :composite-binding))
            (eq effect :none) (null child) (null sizes)))))
