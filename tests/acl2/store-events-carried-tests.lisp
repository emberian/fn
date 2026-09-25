; Teeth for books/store-events-carried.lisp and the carried kind in
; books/owner-commit-carried.lisp (lane carry-kind, 2026-09-25).
(in-package "ACL2")
(include-book "../../books/owner-commit-carried")
(include-book "owner-signed-post-tests")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; Reachable witness: owner-signed-post-tests' *ospt-completing*, the owner
; at :completing after a signed POST's composite (kind 4) was staged and
; its record directory observed, reached by fn-own-run.  Its completion
; record is the composite, and its history holds the other kinds it met.

(defconst *evct-o* *ospt-completing*)
(defconst *evct-s* (fn-own-store *evct-o*))
(defconst *evct-history* (fn-sf-records (fn-sn-files *evct-s*)))
(assert-event (fn-sn-statep *evct-s*))
(assert-event (fn-stxa-p *ospt-event*))
(assert-event (equal (fn-ccar-completion-record *evct-s*) *ospt-event*))

; Each reading by shape equals its reference on every record of the
; reachable history and on the composite, and the readings are not trivial:
; the composite's class is :stxa and its fields are its coordinates.
(defun evct-agree-p (records)
  (if (consp records)
      (let ((x (car records)))
        (and (fn-store-event-p x)
             (equal (fn-evc-field-by-shape 0 x) (fn-store-event-sequence x))
             (equal (fn-evc-field-by-shape 1 x) (fn-store-event-txid x))
             (equal (fn-evc-field-by-shape 2 x) (fn-store-event-generation x))
             (iff (fn-record-p x) (eq (fn-evc-class-by-shape x) :record))
             (iff (fn-store-retention-event-p x) (eq (fn-evc-class-by-shape x) :retention))
             (iff (fn-stxe-p x) (eq (fn-evc-class-by-shape x) :stxe))
             (iff (fn-stxk-p x) (eq (fn-evc-class-by-shape x) :stxk))
             (iff (fn-stxa-p x) (eq (fn-evc-class-by-shape x) :stxa))
             (iff (fn-cpe-eventp x) (eq (fn-evc-class-by-shape x) :consumer))
             (iff (fn-th-topic-eventp x) (eq (fn-evc-class-by-shape x) :topic))
             (evct-agree-p (cdr records))))
    t))
(assert-event (< 1 (len *evct-history*)))
(assert-event (evct-agree-p *evct-history*))
(assert-event (eq (fn-evc-class-by-shape *ospt-event*) :stxa))
(assert-event (natp (fn-evc-field-by-shape 0 *ospt-event*)))
(assert-event (equal (cons (fn-evc-sequence *ospt-event*) (fn-evc-txid *ospt-event*))
                     (fn-sf-completion (fn-sn-files *evct-s*))))

; -----------------------------------------------------------------------------
; The hypothesis of each keystone.  Lists shaped like each kind that are not
; Store events: the shape reads a class and a field, the references do not.

(defconst *evct-junk-stxa* (make-list 10 :initial-element 0))
(defconst *evct-junk-record* (make-list 11 :initial-element 0))
(defconst *evct-junk-stxe* (make-list 8 :initial-element 0))
(defconst *evct-junk-stxk* (make-list 6 :initial-element 0))
(defconst *evct-junk-retention* '(:retention :undertake))
(defconst *evct-junk-consumer* '(:consumer 0))
(defconst *evct-junk-topic* '(:topic-anchor 0))
; The composite itself with its article record replaced by a non-octet: one
; field fails, the shape is untouched.
(defconst *evct-bad-composite* (update-nth 6 '(256) *ospt-event*))
(assert-event (not (fn-store-event-p *evct-bad-composite*)))
(assert-event (eq (fn-evc-class-by-shape *evct-bad-composite*) :stxa))
(assert-event (null (fn-store-event-sequence *evct-bad-composite*)))
(assert-event (equal (fn-evc-field-by-shape 0 *evct-bad-composite*)
                     (fn-store-event-sequence *ospt-event*)))
(assert-event
 (and (not (fn-store-event-p *evct-junk-stxa*))
      (not (fn-store-event-p *evct-junk-record*))
      (not (fn-store-event-p *evct-junk-stxe*))
      (not (fn-store-event-p *evct-junk-stxk*))
      (not (fn-store-event-p *evct-junk-retention*))
      (not (fn-store-event-p *evct-junk-consumer*))
      (not (fn-store-event-p *evct-junk-topic*))))
; fn-evc-field-by-shape-is-store-event-sequence without fn-store-event-p.
(assert-event (not (let ((x *evct-junk-stxa*)) (equal (fn-evc-field-by-shape 0 x) (fn-store-event-sequence x)))))
(must-fail
 (defthm evct-field-by-shape-is-store-event-sequence-without-hypothesis
   (equal (fn-evc-field-by-shape 0 x) (fn-store-event-sequence x))))
; fn-evc-field-by-shape-is-store-event-txid without fn-store-event-p.
(assert-event (not (let ((x *evct-junk-stxa*)) (equal (fn-evc-field-by-shape 1 x) (fn-store-event-txid x)))))
(must-fail
 (defthm evct-field-by-shape-is-store-event-txid-without-hypothesis
   (equal (fn-evc-field-by-shape 1 x) (fn-store-event-txid x))))
; fn-evc-field-by-shape-is-store-event-generation without fn-store-event-p.
(assert-event (not (let ((x *evct-junk-stxa*)) (equal (fn-evc-field-by-shape 2 x) (fn-store-event-generation x)))))
(must-fail
 (defthm evct-field-by-shape-is-store-event-generation-without-hypothesis
   (equal (fn-evc-field-by-shape 2 x) (fn-store-event-generation x))))
; fn-evc-class-by-shape-is-fn-record-p without fn-store-event-p.
(assert-event (not (let ((x *evct-junk-record*)) (iff (fn-record-p x) (equal (fn-evc-class-by-shape x) :record)))))
(must-fail
 (defthm evct-class-by-shape-is-fn-record-p-without-hypothesis
   (iff (fn-record-p x) (equal (fn-evc-class-by-shape x) :record))))
; fn-evc-class-by-shape-is-fn-store-retention-event-p without fn-store-event-p.
(assert-event (not (let ((x *evct-junk-retention*)) (iff (fn-store-retention-event-p x) (equal (fn-evc-class-by-shape x) :retention)))))
(must-fail
 (defthm evct-class-by-shape-is-fn-store-retention-event-p-without-hypothesis
   (iff (fn-store-retention-event-p x) (equal (fn-evc-class-by-shape x) :retention))))
; fn-evc-class-by-shape-is-fn-stxe-p without fn-store-event-p.
(assert-event (not (let ((x *evct-junk-stxe*)) (iff (fn-stxe-p x) (equal (fn-evc-class-by-shape x) :stxe)))))
(must-fail
 (defthm evct-class-by-shape-is-fn-stxe-p-without-hypothesis
   (iff (fn-stxe-p x) (equal (fn-evc-class-by-shape x) :stxe))))
; fn-evc-class-by-shape-is-fn-stxk-p without fn-store-event-p.
(assert-event (not (let ((x *evct-junk-stxk*)) (iff (fn-stxk-p x) (equal (fn-evc-class-by-shape x) :stxk)))))
(must-fail
 (defthm evct-class-by-shape-is-fn-stxk-p-without-hypothesis
   (iff (fn-stxk-p x) (equal (fn-evc-class-by-shape x) :stxk))))
; fn-evc-class-by-shape-is-fn-stxa-p without fn-store-event-p.
(assert-event (not (let ((x *evct-junk-stxa*)) (iff (fn-stxa-p x) (equal (fn-evc-class-by-shape x) :stxa)))))
(must-fail
 (defthm evct-class-by-shape-is-fn-stxa-p-without-hypothesis
   (iff (fn-stxa-p x) (equal (fn-evc-class-by-shape x) :stxa))))
; fn-evc-class-by-shape-is-fn-cpe-eventp without fn-store-event-p.
(assert-event (not (let ((x *evct-junk-consumer*)) (iff (fn-cpe-eventp x) (equal (fn-evc-class-by-shape x) :consumer)))))
(must-fail
 (defthm evct-class-by-shape-is-fn-cpe-eventp-without-hypothesis
   (iff (fn-cpe-eventp x) (equal (fn-evc-class-by-shape x) :consumer))))
; fn-evc-class-by-shape-is-fn-th-topic-eventp without fn-store-event-p.
(assert-event (not (let ((x *evct-junk-topic*)) (iff (fn-th-topic-eventp x) (equal (fn-evc-class-by-shape x) :topic)))))
(must-fail
 (defthm evct-class-by-shape-is-fn-th-topic-eventp-without-hypothesis
   (iff (fn-th-topic-eventp x) (equal (fn-evc-class-by-shape x) :topic))))

; -----------------------------------------------------------------------------
; The carried commit on the reachable witness.  The owner's completion
; through the carried gate is the owner event (:complete) the trace takes,
; and the store moves (the composite is published).

(assert-event (fn-ccar-completion-enabledp *evct-s*))
(assert-event (equal (fn-ccar-own-complete *evct-o*) *ospt-finished*))
(assert-event (not (equal *ospt-finished* *evct-o*)))
(assert-event (equal (fn-ccar-sn-finish *evct-s*) (fn-sn-finish *evct-s*)))
(assert-event (not (equal (fn-ccar-sn-finish *evct-s*) *evct-s*)))
; The configured owner's completion the host installs: equal to fn-ocfg-step
; of (:complete), unstaged and staged.
(defconst *evct-oc* (fn-ocfg-make *evct-o* nil nil nil))
(assert-event (equal (fn-ccar-ocfg-complete *evct-oc*)
                     (fn-ocfg-step *evct-oc* '(:complete))))
(assert-event (equal (fn-ocfg-owner (fn-ccar-ocfg-complete *evct-oc*))
                     *ospt-finished*))
(assert-event
 (and (eq (symbol-class 'fn-ccar-ocfg-complete (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-evc-sequence (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-evc-stxap (w state)) :common-lisp-compliant)
      (equal (guard 'fn-evc-sequence nil (w state)) '(fn-store-event-p x))))
