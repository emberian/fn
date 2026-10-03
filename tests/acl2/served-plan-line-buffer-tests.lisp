(in-package "ACL2")
(include-book "../../books/served-plan-line-buffer")

; Positive literal witnesses cover all four host-boundary keystones; their
; statements have no hypotheses to remove. The actual abstract buffer is used.
(defun slbuf-witness (p bytes fn-octets fn-arena fn-cat)
 (declare (xargs :stobjs (fn-octets fn-arena fn-cat) :guard (natp bytes) :verify-guards nil))
 (let ((fn-octets (fn-octets-from-list '(222 223 224) fn-octets)))
  (mv-let (status next fn-octets)
   (fn-splan-line-window p bytes fn-octets)
   (declare (ignore status))
   (mv (and
        (equal (append (fn-octets-list fn-octets)
                (fn-nnw-stream-remaining (fn-cur-at 1 (car (fn-splan-rest next))) fn-arena fn-cat))
               (fn-nnw-stream-remaining (fn-cur-at 1 (car (fn-splan-rest p))) fn-arena fn-cat))
        (equal (cdr (fn-splan-rest next)) (cdr (fn-splan-rest p)))
        (equal (fn-cur-context (fn-cur-at 1 (car (fn-splan-rest next))))
               (fn-cur-context (fn-cur-at 1 (car (fn-splan-rest p)))))
        (<= (fn-octets-len fn-octets) (nfix bytes)))
       fn-octets fn-arena fn-cat))))
(defun slbuf-witness-value (p bytes)
 (declare (xargs :guard (natp bytes) :verify-guards nil))
 (with-local-stobj fn-arena
  (mv-let (ok fn-arena)
   (with-local-stobj fn-cat
    (mv-let (ok fn-arena fn-cat)
     (with-local-stobj fn-octets
      (mv-let (ok fn-octets fn-arena fn-cat)
       (slbuf-witness p bytes fn-octets fn-arena fn-cat)
       (mv ok fn-arena fn-cat)))
     (mv ok fn-arena))) ok)))
(defun slbuf-plan (text)
 (fn-splan-of-effects
  (list (fn-nnw-meta-effect
         (fn-cur-make '(:captured-context 42)
                      (fn-nnw-stream-render (fn-sl-start text) nil) nil nil))
        '(:reply (99 13 10)))))
(assert-event (slbuf-witness-value (slbuf-plan ".abc") 1))
(assert-event (slbuf-witness-value (slbuf-plan ".abc") 4))
(assert-event (slbuf-witness-value (slbuf-plan ".abc") 256))
(assert-event (slbuf-witness-value (slbuf-plan "") 1))
(assert-event (slbuf-witness-value (slbuf-plan "") 0))
; Refusal/corrupted-state witnesses do not assert native reachability.
(assert-event (slbuf-witness-value nil 8))
(assert-event (slbuf-witness-value 'bad 8))
(assert-event (slbuf-witness-value '(nil (:newnews-cursor (nil (:terminator) nil :blocked))) 8))
(assert-event (eq (symbol-class 'fn-splan-line-window (w state)) :common-lisp-compliant))
