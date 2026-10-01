; Same-issued snapshot semantic evidence, staged before ORIGINALctx exposure.
; This internal pure producer is not a grant or an installed STATE setter.
(in-package "ACL2")
(include-book "replay-enrollment-lookup")
(include-book "statement-items-cursor")
(include-book "stx-keyring-records")
(include-book "hybrid-profile")
(include-book "hybrid-signature")

(defun fn-rse-result-spans (result)
 (declare (xargs :guard t))
 (let ((items (fn-rsc-at 1 result)))
  (if (and (fn-rsc-widthp 2 result) (eq (fn-rsc-at 0 result) :ok)
           (fn-rsc-widthp 5 items)
           (fn-rse-span-shapep (fn-rsc-at 0 items))
           (fn-rse-span-shapep (fn-rsc-at 2 items))
           (fn-rse-span-shapep (fn-rsc-at 4 items))
           (consp (fn-rsc-at 1 items)) (eq (car (fn-rsc-at 1 items)) :uint)
           (equal (cdr (fn-rsc-at 1 items)) *fn-hsig-ed25519-algorithm*)
           (consp (fn-rsc-at 3 items)) (eq (car (fn-rsc-at 3 items)) :uint)
           (equal (cdr (fn-rsc-at 3 items)) *fn-hsig-ml-dsa-65-algorithm*)
           (equal (fn-rse-span-length (fn-rsc-at 0 items)) 32)
           (equal (fn-rse-span-length (fn-rsc-at 2 items)) *fn-hsig-ed25519-public-key-octets*)
           (equal (fn-rse-span-length (fn-rsc-at 4 items)) *fn-hsig-ml-dsa-65-public-key-octets*))
   (list (fn-rsc-at 0 items) (fn-rsc-at 2 items) (fn-rsc-at 4 items)) nil)))
; The literal selected profile is twelve octets. Comparison still reads one
; octet per tick; no deep EQUAL of a retained profile is hidden in extraction.
(defun fn-rse-profile-comparison-begin (profile source)
 (declare (xargs :guard t))
 (fn-rse-equality-begin profile '((:ed25519) (:ml-dsa-65))
  (list (list :bytes 0 (len *fn-hsig-profile-tag*) *fn-hsig-profile-tag*)
        '(:bytes 0 0 nil) '(:bytes 0 0 nil)) source))

; Fixed9: phase, original context, exact produced MV6 packet, old ledger,
; issued source, exact selected snapshot, parser, profile comparison, spans.
(defun fn-rse-produced-state (phase original packet ledger source snapshot parser comparison spans)
 (declare (xargs :guard t))
 (list phase original packet ledger source snapshot parser comparison spans))
(defun fn-rse-produced-begin (original packet ledger source)
 (declare (xargs :guard t))
 (cond
  ((not (fn-rsc-widthp 6 packet))
   (fn-rse-produced-state :refused original packet ledger source nil nil nil nil))
  ((eq (fn-rsc-at 3 packet) :snapshot)
   (let ((snapshot (fn-rsc-at 4 packet)))
    (fn-rse-produced-state :decode original packet ledger source snapshot
     (fn-sic-begin-legacy 5 (fn-stxk-snapshot snapshot)) nil nil)))
  ((member-eq (fn-rsc-at 3 packet) '(:none :verdict))
   (fn-rse-produced-state :unchanged original packet ledger source nil nil nil nil))
  (t (fn-rse-produced-state :refused original packet ledger source nil nil nil nil))))
(defun fn-rse-produced-step (s)
 (declare (xargs :guard t))
 (if (not (fn-rsc-widthp 9 s)) (mv :refused s)
  (let ((phase (fn-rsc-at 0 s)) (original (fn-rsc-at 1 s))
        (packet (fn-rsc-at 2 s)) (ledger (fn-rsc-at 3 s))
        (source (fn-rsc-at 4 s)) (snapshot (fn-rsc-at 5 s)))
   (cond
    ((member-eq phase '(:enrolled :none :unchanged)) (mv :done s))
    ((eq phase :decode)
     (let* ((parser (fn-sic-step (fn-rsc-at 6 s)))
            (result (fn-sic-result parser)))
      (cond
       ((eq result :pending)
        (mv :working (fn-rse-produced-state :decode original packet ledger source
                       snapshot parser nil nil)))
       ((and (fn-rsc-widthp 2 result) (eq (fn-rsc-at 0 result) :error))
        (mv :done (fn-rse-produced-state :none original packet ledger source
                    snapshot parser nil nil)))
       ((and (fn-rsc-widthp 2 result) (eq (fn-rsc-at 0 result) :ok))
        (let ((spans (fn-rse-result-spans result)))
         (if spans
          (mv :working (fn-rse-produced-state :profile original packet ledger source
           snapshot parser (fn-rse-profile-comparison-begin
                              (fn-stxk-profile snapshot) source) spans))
          (mv :done (fn-rse-produced-state :none original packet ledger source
                      snapshot parser nil nil)))))
       (t (mv :refused s)))))
    ((eq phase :profile)
     (mv-let (word comparison) (fn-rse-equality-step (fn-rsc-at 7 s))
      (cond
       ((eq word :refused) (mv :refused s))
       ((eq word :done)
        (mv :done (fn-rse-produced-state
          (if (fn-rsc-at 7 comparison) :enrolled :none)
          original packet ledger source snapshot (fn-rsc-at 6 s)
          comparison (if (fn-rsc-at 7 comparison) (fn-rsc-at 8 s) nil))))
       (t (mv :working (fn-rse-produced-state :profile original packet ledger source
           snapshot (fn-rsc-at 6 s) comparison (fn-rsc-at 8 s)))))))
    (t (mv :refused s))))))
(defun fn-rse-produced-readout (s)
 (declare (xargs :guard t))
 (if (not (fn-rsc-widthp 9 s)) :refused
  (case (fn-rsc-at 0 s)
   (:unchanged (list :produced (fn-rsc-at 1 s) (fn-rsc-at 2 s)
                     (fn-rsc-at 3 s) (fn-rsc-at 4 s)))
   ((:enrolled :none)
    (list :produced (fn-rsc-at 1 s) (fn-rsc-at 2 s)
     (cons (fn-rse-evidence (fn-rsc-at 5 s) (fn-rsc-at 0 s)
                            (fn-rsc-at 8 s) (fn-rsc-at 4 s))
           (fn-rsc-at 3 s)) (fn-rsc-at 4 s)))
   (:refused :refused)
   (otherwise :pending))))

; Authenticated checkpoint bootstrap uses the SAME semantic worker on each
; original snapshot, without fabricating an identity replay decision.
(defun fn-rse-snapshot-evidence-begin (snapshot source)
 (declare (xargs :guard t))
 (fn-rse-produced-state :decode nil nil nil source snapshot
  (fn-sic-begin-legacy 5 (fn-stxk-snapshot snapshot)) nil nil))
(defun fn-rse-snapshot-evidence-readout (s)
 (declare (xargs :guard t))
 (if (not (fn-rsc-widthp 9 s)) :refused
  (case (fn-rsc-at 0 s)
   ((:enrolled :none)
    (fn-rse-evidence (fn-rsc-at 5 s) (fn-rsc-at 0 s)
                     (fn-rsc-at 8 s) (fn-rsc-at 4 s)))
   (:refused :refused)
   (otherwise :pending))))

(defthm fn-rse-produced-step-preserves-original-operation-custody
 (implies (fn-rsc-widthp 9 s)
  (let ((next (mv-nth 1 (fn-rse-produced-step s))))
   (and (fn-rsc-widthp 9 next)
        (equal (fn-rsc-at 1 next) (fn-rsc-at 1 s))
        (equal (fn-rsc-at 2 next) (fn-rsc-at 2 s))
        (equal (fn-rsc-at 3 next) (fn-rsc-at 3 s))
        (equal (fn-rsc-at 4 next) (fn-rsc-at 4 s))
        (equal (fn-rsc-at 5 next) (fn-rsc-at 5 s)))))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (e/d (fn-rse-produced-step fn-rse-produced-state fn-rsc-at fn-rsc-widthp)
       (fn-sic-step fn-sic-result fn-rse-result-spans
        fn-rse-profile-comparison-begin fn-rse-equality-step)))))
