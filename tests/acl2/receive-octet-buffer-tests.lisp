(in-package "ACL2")
(include-book "../../books/receive-octet-buffer")
(defun rxb-test-in (before limits byte fn-octets-rx)
  (declare (xargs :stobjs fn-octets-rx :verify-guards nil))
  (let ((fn-octets-rx (fn-octets-rx-from-list before fn-octets-rx)))
    (mv-let (word fn-octets-rx) (fn-rxb-append-byte limits byte fn-octets-rx)
      (mv (list word (fn-octets-rx-list fn-octets-rx)) fn-octets-rx))))
(defun rxb-test (before limits byte)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-octets-rx
    (mv-let (result fn-octets-rx) (rxb-test-in before limits byte fn-octets-rx) result)))
; Reachable complete output/effect conclusion for accepted command octet.
(assert-event
 (and (unsigned-byte-p 8 65)
      (< (len '(78 69)) (fn-cbud-step-read-octets nil))
      (equal (rxb-test '(78 69) nil 65) '(:received (78 69 65)))))
(defconst *rxb-full* (make-list *fn-cbud-read-quantum* :initial-element 78))
; Quantum exhaustion yields unchanged input; it is not a data-size ceiling.
(assert-event
 (and (unsigned-byte-p 8 65)
      (>= (len *rxb-full*) (fn-cbud-step-read-octets nil))
      (equal (rxb-test *rxb-full* nil 65) (list :receive-quantum-full *rxb-full*))))
