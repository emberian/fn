; Actual RC-to-served-step constructor used by the serialized reader commit.
; Domain hypotheses are established by the producer, not checked by scanning
; the whole step on the served path. Source-only until that producer joins.
(in-package "ACL2")
(include-book "served-step")
(include-book "owner-read-result")

(defun fn-irr-step-from-read-result (result closep starttlsp submittedp refusal-lines exposure-close)
 (declare (xargs :guard t))
 (let ((effects (fn-own-tls-result-effects result)))
  (fn-splan-step-make effects
   closep starttlsp submittedp (fn-own-tls-result-consumed result)
   refusal-lines exposure-close)))

(defthm fn-irr-read-result-establishes-step-domain
 (implies
  (and (true-listp (fn-own-tls-result-effects result))
       (true-listp refusal-lines)
       (or (null exposure-close) (fn-cbor-octet-listp exposure-close)))
  (fn-splan-step-p
   (fn-irr-step-from-read-result result closep starttlsp submittedp refusal-lines exposure-close)))
 :hints (("Goal" :use
  ((:instance fn-splan-step-make-is-a-step
    (effects (fn-own-tls-result-effects result))
    (consumed (fn-own-tls-result-consumed result))))
  :in-theory (union-theories (theory 'minimal-theory)
                            '(fn-irr-step-from-read-result)))))

(defthm fn-irr-read-result-step-consumed-unfolds
 (equal
  (fn-splan-step-consumed
   (fn-irr-step-from-read-result result closep starttlsp submittedp refusal-lines exposure-close))
  (nfix (fn-own-tls-result-consumed result)))
 :hints (("Goal" :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-irr-step-from-read-result fn-splan-step-accessors-of-make)))))
