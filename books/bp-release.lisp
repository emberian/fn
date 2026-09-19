; fn sender-side obligation release for the forwarding obligation (wave 2,
; packet A).
;
; Before this book nothing in fn-bp called fn-retain-release: an authorized
; receipt only made a work stop being fn-bp-work-outstandingp, and the node's
; retention ledger compared release evidence as a bare string (review §4, row
; 1; §6 item 6).  This book adds two decisions over the workflow state's node
; image, both total and both no-ops on refusal:
;
;   fn-bprl-undertake         admit the :forward pin for a durable outstanding
;                             work under fn-bp-work-obligation-id, with the
;                             pin's required evidence rendered from the work
;                             and the fixed configuration (the receipt id is
;                             not known yet, so it cannot be part of the pin);
;   fn-bprl-release-decision  on a committed authorized receipt, build the
;                             typed release evidence, render it, and call the
;                             node's fn-retain-release for exactly that pin.
;
; The typed evidence carries the receipt id; the ledger's release record keeps
; the rendered term.  The retention ledger still compares a string: making
; fn-retain-release take the typed structure is a retention-book change that
; this lane does not own (C2-10).  A-POLICY is an environmental premise here
; exactly as in fn-bp-prepare-receipt: the receipt was admitted with the
; explicit boolean, and this book releases only what that admission committed.
; A-PEER is the hypothesis under which the released bytes may be reclaimed;
; nothing here reclaims.

(in-package "ACL2")
(include-book "bp-workflow-records")
(include-book "assumptions")

; -----------------------------------------------------------------------------
; Policy term placeholder and typed release evidence

; Term: (:fn-forward-term policy-id terms-id).  A cons, so that A-POLICY's
; constraint fn-assume-policy-needs-terms cannot refuse it for shape.
(defun fn-bprl-term-policy-id (x) (declare (xargs :guard t)) (fn-bp-nth 1 x))
(defun fn-bprl-term-terms-id (x) (declare (xargs :guard t)) (fn-bp-nth 2 x))
(defun fn-bprl-make-term (policy-id terms-id)
  (declare (xargs :guard t))
  (list :fn-forward-term policy-id terms-id))
(defun fn-bprl-termp (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 3)
       (equal (car x) :fn-forward-term)
       (stringp (fn-bprl-term-policy-id x))
       (stringp (fn-bprl-term-terms-id x))))

; Evidence: (receipt-id work-id subject issuer term incarnation).
(defun fn-bprl-evidence-receipt-id (x) (declare (xargs :guard t)) (fn-bp-nth 0 x))
(defun fn-bprl-evidence-work-id (x) (declare (xargs :guard t)) (fn-bp-nth 1 x))
(defun fn-bprl-evidence-subject (x) (declare (xargs :guard t)) (fn-bp-nth 2 x))
(defun fn-bprl-evidence-issuer (x) (declare (xargs :guard t)) (fn-bp-nth 3 x))
(defun fn-bprl-evidence-term (x) (declare (xargs :guard t)) (fn-bp-nth 4 x))
(defun fn-bprl-evidence-incarnation (x) (declare (xargs :guard t)) (fn-bp-nth 5 x))
(defun fn-bprl-make-evidence (receipt-id work-id subject issuer term incarnation)
  (declare (xargs :guard t))
  (list receipt-id work-id subject issuer term incarnation))
(defun fn-bprl-evidencep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 6)
       (stringp (fn-bprl-evidence-receipt-id x))
       (stringp (fn-bprl-evidence-work-id x))
       (stringp (fn-bprl-evidence-subject x))
       (stringp (fn-bprl-evidence-issuer x))
       (fn-bprl-termp (fn-bprl-evidence-term x))
       (stringp (fn-bprl-evidence-incarnation x))))

; Rendering to the ledger's required-evidence string.  ACL2 owns this
; derivation (assurance rule: one owner per decision); the separator is a
; laboratory placeholder, not a portable grammar.
(defun fn-bprl-cat (a b)
  (declare (xargs :guard t))
  (if (and (stringp a) (stringp b)) (string-append a b) ""))

(defun fn-bprl-render (work-id subject issuer policy-id terms-id incarnation)
  (declare (xargs :guard t))
  (fn-bprl-cat
   "fn-forward-release/1|"
   (fn-bprl-cat
    work-id
    (fn-bprl-cat
     "|"
     (fn-bprl-cat
      subject
      (fn-bprl-cat
       "|"
       (fn-bprl-cat
        issuer
        (fn-bprl-cat
         "|"
         (fn-bprl-cat
          policy-id
          (fn-bprl-cat
           "|"
           (fn-bprl-cat terms-id (fn-bprl-cat "|" incarnation))))))))))))

(defun fn-bprl-evidence-string (ev)
  (declare (xargs :guard t))
  (fn-bprl-render (fn-bprl-evidence-work-id ev)
                  (fn-bprl-evidence-subject ev)
                  (fn-bprl-evidence-issuer ev)
                  (fn-bprl-term-policy-id (fn-bprl-evidence-term ev))
                  (fn-bprl-term-terms-id (fn-bprl-evidence-term ev))
                  (fn-bprl-evidence-incarnation ev)))

; The evidence the pin demands, fixed when the obligation is undertaken.
(defun fn-bprl-required-evidence (config work)
  (declare (xargs :guard t))
  (fn-bprl-render (fn-bp-work-id work)
                  (fn-bp-work-subject work)
                  (fn-bp-config-authority config)
                  (fn-bp-work-policy-id work)
                  (fn-bp-work-terms-id work)
                  (fn-bp-work-incarnation work)))

; The typed evidence a committed receipt yields.
(defun fn-bprl-receipt-evidence (receipt)
  (declare (xargs :guard t))
  (fn-bprl-make-evidence (fn-bp-receipt-id receipt)
                         (fn-bp-receipt-work-id receipt)
                         (fn-bp-receipt-subject receipt)
                         (fn-bp-receipt-issuer receipt)
                         (fn-bprl-make-term (fn-bp-receipt-policy-id receipt)
                                            (fn-bp-receipt-terms-id receipt))
                         (fn-bp-receipt-incarnation receipt)))

; -----------------------------------------------------------------------------
; Node surgery: only the retention component changes.

(defun fn-bprl-node-with-retention (node retention)
  (declare (xargs :guard t :verify-guards nil))
  (fn-node-make-state (fn-node-acceptance node) retention
                      (fn-node-stage node) (fn-node-bindings node)))

(defun fn-bprl-with-node (s node)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bp-make-state node (fn-bp-state-config s) (fn-bp-state-works s)
                    (fn-bp-state-receipts s) (fn-bp-state-pending s)
                    (fn-bp-state-fenced s) (fn-bp-state-used-txs s)))

(defun fn-bprl-pins (s)
  (declare (xargs :guard t :verify-guards nil))
  (fn-retain-pins (fn-node-retention (fn-bp-state-node s))))

(defun fn-bprl-work-pin (s work)
  (declare (xargs :guard t :verify-guards nil))
  (fn-retain-find-id (fn-bp-work-obligation-id work) (fn-bprl-pins s)))

; The :forward pin for this work is present with the required evidence.
(defun fn-bprl-work-pinnedp (s work)
  (declare (xargs :guard t :verify-guards nil))
  (fn-retain-matching-releasep
   (fn-bprl-work-pin s work)
   (fn-bp-work-obligation-id work) (fn-bp-work-subject work) :forward
   (fn-bprl-required-evidence (fn-bp-state-config s) work)))

; -----------------------------------------------------------------------------
; Undertaking: admit the forwarding obligation's pin.

; Refusals, each with its own tooth in tests/acl2/bp-release-tests.lisp: no
; live workflow intent, a staged archive transaction on the node (its
; prospective retention would go stale), a forwarding id that is the archive
; id (one pin cannot be two obligations), a non-positive charge, and the
; ledger's own admissibility (known id or no capacity).
(defun fn-bprl-undertake-okp (s work charge)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-bp-statep s)
       (not (consp (fn-bp-state-pending s)))
       (not (fn-bp-state-fenced s))
       (consp work)
       (fn-bp-work-outstandingp work)
       (null (fn-node-stage (fn-bp-state-node s)))
       (not (equal (fn-bp-work-obligation-id work) (fn-bp-work-archive-id work)))
       (posp charge)
       (fn-retain-admissiblep (fn-node-retention (fn-bp-state-node s))
                              (fn-bp-work-obligation-id work)
                              (fn-bp-work-subject work) :forward
                              (fn-bprl-required-evidence (fn-bp-state-config s) work)
                              charge)))

(defun fn-bprl-undertake (s work-id charge)
  (declare (xargs :guard t :verify-guards nil))
  (let ((work (fn-bp-find-work work-id (fn-bp-state-works s))))
    (if (not (fn-bprl-undertake-okp s work charge))
        s
      (fn-bprl-with-node
       s
       (fn-bprl-node-with-retention
        (fn-bp-state-node s)
        (fn-retain-admit (fn-node-retention (fn-bp-state-node s))
                         (fn-bp-work-obligation-id work)
                         (fn-bp-work-subject work) :forward
                         (fn-bprl-required-evidence (fn-bp-state-config s) work)
                         charge))))))

; -----------------------------------------------------------------------------
; Release decision

(defun fn-bprl-find-receipt (receipt-id receipts)
  (declare (xargs :guard t))
  (if (consp receipts)
      (if (equal receipt-id (fn-bp-receipt-id (car receipts)))
          (car receipts)
        (fn-bprl-find-receipt receipt-id (cdr receipts)))
    nil))

; Every conjunct is one RET-004 adjective or one node-shape guard:
;   receipt in committed history           stale
;   work carries this very receipt         wrong-work, duplicated
;   fn-bp-authorized-receiptp              wrong-subject, wrong-incarnation,
;                                          unauthorized, insufficient (terms)
;   pin present with required evidence     duplicated (second decision)
;   stage null, id not an archive binding  node invariant guards
(defun fn-bprl-release-okp (s receipt work)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-bp-statep s)
       (not (consp (fn-bp-state-pending s)))
       (not (fn-bp-state-fenced s))
       (consp receipt)
       (consp work)
       (equal (fn-bp-work-receipt work) receipt)
       (fn-bp-authorized-receiptp (fn-bp-state-config s) work receipt)
       (null (fn-node-stage (fn-bp-state-node s)))
       (not (equal (fn-bp-work-obligation-id work) (fn-bp-work-archive-id work)))
       (not (member-equal (fn-bp-work-obligation-id work)
                          (fn-node-binding-ids
                           (fn-node-bindings (fn-bp-state-node s)))))
       (fn-bprl-work-pinnedp s work)))

; Result: (okp state evidence).
(defun fn-bprl-decision-okp (d) (declare (xargs :guard t)) (fn-bp-nth 0 d))
(defun fn-bprl-decision-state (d) (declare (xargs :guard t)) (fn-bp-nth 1 d))
(defun fn-bprl-decision-evidence (d) (declare (xargs :guard t)) (fn-bp-nth 2 d))

(defun fn-bprl-release-decision (s receipt-id)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((receipt (fn-bprl-find-receipt receipt-id (fn-bp-state-receipts s)))
         (work (fn-bp-find-work (fn-bp-receipt-work-id receipt)
                                (fn-bp-state-works s))))
    (if (not (fn-bprl-release-okp s receipt work))
        (list nil s nil)
      (let ((evidence (fn-bprl-receipt-evidence receipt)))
        (list t
              (fn-bprl-with-node
               s
               (fn-bprl-node-with-retention
                (fn-bp-state-node s)
                (fn-retain-release (fn-node-retention (fn-bp-state-node s))
                                   (fn-bp-work-obligation-id work)
                                   (fn-bp-work-subject work) :forward
                                   (fn-bprl-evidence-string evidence))))
              evidence)))))

; -----------------------------------------------------------------------------
; Journal records (proposed FNWF additions; see specs/retention.md).
;
;   (:undertake work-id charge)
;   (:release receipt-id work-id subject issuer policy-id terms-id incarnation)
;
; fn-bp-journal-recordp does not know these kinds, so fn-bp-apply-journal-record
; refuses them; this wrapper is a strict extension of the host-called function
; and equals it on every record that function accepts
; (fn-bprl-apply-journal-record-agrees-with-host-on-bp-records).  The host
; switch (host/workflow-host.lisp:27 and :40) is an open item.

(defun fn-bprl-undertake-recordp (r)
  (declare (xargs :guard t :verify-guards nil))
  (and (true-listp r) (equal (len r) 3) (equal (car r) :undertake)
       (fn-bp-journal-textp (fn-bp-journal-nth 1 r))
       (posp (fn-bp-journal-nth 2 r))
       (fn-bp-u64p (fn-bp-journal-nth 2 r))))

(defun fn-bprl-release-recordp (r)
  (declare (xargs :guard t :verify-guards nil))
  (and (true-listp r) (equal (len r) 8) (equal (car r) :release)
       (fn-bp-journal-textp (fn-bp-journal-nth 1 r))
       (fn-bp-journal-textp (fn-bp-journal-nth 2 r))
       (fn-bp-journal-textp (fn-bp-journal-nth 3 r))
       (fn-bp-journal-textp (fn-bp-journal-nth 4 r))
       (fn-bp-journal-textp (fn-bp-journal-nth 5 r))
       (fn-bp-journal-textp (fn-bp-journal-nth 6 r))
       (fn-bp-journal-textp (fn-bp-journal-nth 7 r))))

(defun fn-bprl-record-evidence (r)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bprl-make-evidence (fn-bp-journal-nth 1 r) (fn-bp-journal-nth 2 r)
                         (fn-bp-journal-nth 3 r) (fn-bp-journal-nth 4 r)
                         (fn-bprl-make-term (fn-bp-journal-nth 5 r)
                                            (fn-bp-journal-nth 6 r))
                         (fn-bp-journal-nth 7 r)))

; Result is (okp state effects), the shape fn-bp-apply-journal-record returns.
; A release record whose evidence fields disagree with the decision ACL2
; computes from the state is refused: the record does not carry authority,
; it carries what the decision was, and replay recomputes it.
(defun fn-bprl-apply-journal-record (s r)
  (declare (xargs :guard t :verify-guards nil))
  (cond
   ((fn-bprl-release-recordp r)
    (let ((d (fn-bprl-release-decision s (fn-bp-journal-nth 1 r))))
      (if (and (fn-bprl-decision-okp d)
               (equal (fn-bprl-decision-evidence d) (fn-bprl-record-evidence r)))
          (list t (fn-bprl-decision-state d)
                (list (list :released (fn-bp-journal-nth 2 r))))
        (list nil s nil))))
   ((fn-bprl-undertake-recordp r)
    (let ((next (fn-bprl-undertake s (fn-bp-journal-nth 1 r)
                                   (fn-bp-journal-nth 2 r))))
      (if (equal next s)
          (list nil s nil)
        (list t next (list (list :undertaken (fn-bp-journal-nth 1 r)))))))
   (t (fn-bp-apply-journal-record s r))))
