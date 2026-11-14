; Eleven independent semantic checker names. A4 implements TRACE/WORK/OWN.
; Missing evidence and unimplemented checks are never passing results.
(in-package "ACL2")
(include-book "../books/assembly")
(include-book "check-core")
(include-book "check-trace")
(include-book "check-work")

(defconst *fn2-checker-names*
  '(:trace :work :own :account :fair :history :identity :wire :consumer :recovery :reclaim))
(defun fn2-checker-namep (name)
  (declare (xargs :guard t))
  (if (member-eq name *fn2-checker-names*) t nil))
(defun fn2-check-resultp (result)
  (declare (xargs :guard t))
  (or (eq result :pass) (eq result :not-yet)
      (and (consp result) (eq (car result) :fail) (consp (cdr result)))))

(defun fn2-check (name fn2-core fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-own) :verify-guards nil))
  (cond ((eq name :own) (fn2-check-own fn2-core fn2-own))
        ((member-eq name '(:trace :work)) '(:fail :checker-evidence-required))
        ((fn2-checker-namep name) :not-yet)
        (t '(:fail :unknown-checker))))

(assert-event (and (= (len *fn2-checker-names*) 11)
                   (no-duplicatesp-eq *fn2-checker-names*)
                   (fn2-check-resultp :pass) (fn2-check-resultp :not-yet)
                   (fn2-check-resultp '(:fail :example))
                   (not (fn2-check-resultp nil))))

(assert-event
 (fn2-assert-compliant-p
  '(fn2-checker-namep fn2-check-resultp fn2-own-observe-issue
    fn2-own-observe-output fn2-own-record-input-byte fn2-own-observe-read
    fn2-own-observe-core-write)
  (w state)))

 ; TRACE needs a pre-turn reference copy: call fn2-check-trace-turn.

