(in-package "ACL2")
(include-book "../../books/bpsec-target")

(defconst *fn-bpst-limits* (fn-bps-limits-make 4096 128 16 16 2048 2048))
(defconst *fn-bpst-primary*
  (fn-bpp-make-block 0 2 '(:ipn 10 1) '(:ipn 10 0) '(:ipn 10 0)
                     1000 1 3600000 nil nil))
(defconst *fn-bpst-payload* (fn-bpb-make-block 1 1 0 0 (make-list 32 :initial-element 1)))
(defun fn-bpst-bib (targets)
  (declare (xargs :guard t))
  (fn-bps-asb-make 11 targets 1 0 '(:ipn 10 0) nil
                   (list (list (list 1 (cons :bytes (make-list 48 :initial-element 65)))))))
(defconst *fn-bpst-asb* (fn-bpst-bib '(0)))
(defconst *fn-bpst-block* (fn-bpb-make-block 11 7 0 0 (fn-bps-asb-encode *fn-bpst-asb*)))
(defconst *fn-bpst-bundle* (fn-bpb-make-bundle *fn-bpst-primary* (list *fn-bpst-block*) *fn-bpst-payload*))
(defconst *fn-bpst-bindings* (list (cons 7 *fn-bpst-asb*)))

(assert-event (fn-bpb-bundlep *fn-bpst-bundle*))
(assert-event (fn-bps-parsed-bindings-matchp *fn-bpst-bundle* *fn-bpst-bindings* *fn-bpst-limits*))
(assert-event (equal (fn-bps-target-check *fn-bpst-bundle* *fn-bpst-bindings* nil *fn-bpst-limits*) :valid))

; Stale supplied metadata still has the same number/type. Metadata validity
; cannot authorize the actual bundle: its literal data-binding premise fails.
(assert-event
 (let* ((other (fn-bpb-make-block 11 7 0 0 (fn-bps-asb-encode (fn-bpst-bib '(1)))))
        (bundle (fn-bpb-make-bundle *fn-bpst-primary* (list other) *fn-bpst-payload*)))
   (and (fn-bpb-bundlep bundle) (fn-bps-bindingsp *fn-bpst-bindings*)
        (fn-bps-bindings-kind-matchp bundle *fn-bpst-bindings*)
        (equal (fn-bps-target-check bundle *fn-bpst-bindings* nil *fn-bpst-limits*) :valid)
        (not (fn-bps-parsed-bindings-matchp bundle *fn-bpst-bindings* *fn-bpst-limits*)))))

(assert-event
 (equal (fn-bps-target-check *fn-bpst-bundle* (list (cons 1 *fn-bpst-asb*)) nil *fn-bpst-limits*)
        '(:refused :binding-kind)))
(assert-event
 (equal (fn-bps-target-check *fn-bpst-bundle* (append *fn-bpst-bindings* *fn-bpst-bindings*) nil *fn-bpst-limits*)
        '(:refused :duplicate-binding)))
(assert-event
 (equal (fn-bps-target-check *fn-bpst-bundle* (list (cons 7 (fn-bpst-bib '(7)))) nil *fn-bpst-limits*)
        '(:refused :bib-security-target)))
(assert-event
 (equal (fn-bps-target-check *fn-bpst-bundle* (list (cons 7 (fn-bpst-bib '(99)))) nil *fn-bpst-limits*)
        '(:refused :missing-target)))
(assert-event
 (equal (fn-bps-target-check *fn-bpst-bundle* nil nil *fn-bpst-limits*)
        '(:unsupported :incomplete-security-coverage)))

(defconst *fn-bpst-bcb*
  (fn-bps-asb-make 12 '(1 7) 2 1 '(:dtn-none)
                   (list (list 1 (cons :bytes '(0 1 2 3 4 5 6 7 8 9 10 11)))) '(nil nil)))
(defconst *fn-bpst-cipher-bib* (fn-bpb-make-block 11 7 0 0 '(255 255 255)))
(defconst *fn-bpst-bcb-block* (fn-bpb-make-block 12 8 1 0 (fn-bps-asb-encode *fn-bpst-bcb*)))
(defconst *fn-bpst-opaque-bundle*
  (fn-bpb-make-bundle *fn-bpst-primary* (list *fn-bpst-cipher-bib* *fn-bpst-bcb-block*) *fn-bpst-payload*))
(defconst *fn-bpst-bcb-bindings* (list (cons 8 *fn-bpst-bcb*)))
(assert-event (fn-bpb-bundlep *fn-bpst-opaque-bundle*))
(assert-event
 (and (fn-bps-parsed-bindings-matchp *fn-bpst-opaque-bundle* *fn-bpst-bcb-bindings* *fn-bpst-limits*)
      (equal (fn-bps-target-check *fn-bpst-opaque-bundle* *fn-bpst-bcb-bindings* '(7) *fn-bpst-limits*)
             :pending-plaintext)))
(assert-event
 (equal (fn-bps-target-check *fn-bpst-opaque-bundle* *fn-bpst-bcb-bindings* nil *fn-bpst-limits*)
        '(:refused :opaque-set)))
(assert-event
 (equal (fn-bps-target-check *fn-bpst-opaque-bundle* (append *fn-bpst-bcb-bindings* *fn-bpst-bindings*) '(7)
                            *fn-bpst-limits*) '(:refused :encrypted-bib-parsed)))
(assert-event
 (let ((bundle (fn-bpb-make-bundle *fn-bpst-primary*
                 (list *fn-bpst-cipher-bib* *fn-bpst-bcb-block* (fn-bpb-make-block 12 9 0 0 '(255)))
                 *fn-bpst-payload*)))
   (and (fn-bpb-bundlep bundle)
        (equal (fn-bps-target-check bundle *fn-bpst-bcb-bindings* '(7) *fn-bpst-limits*)
               '(:unsupported :incomplete-security-coverage)))))
(assert-event
 (let ((bundle (fn-bpb-make-bundle *fn-bpst-primary*
                 (list *fn-bpst-cipher-bib* (fn-bpb-make-block 12 8 0 0 (fn-bps-asb-encode *fn-bpst-bcb*)))
                 *fn-bpst-payload*)))
   (equal (fn-bps-target-check bundle *fn-bpst-bcb-bindings* '(7) *fn-bpst-limits*)
          '(:refused :payload-bcb-flags))))
