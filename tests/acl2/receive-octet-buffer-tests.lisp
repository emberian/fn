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

(defun rxb-cost-test-in (capacity used byte fn-octets$c)
  (declare (xargs :stobjs fn-octets$c :verify-guards nil))
  (let* ((fn-octets$c (resize-fn-octets$c-buf capacity fn-octets$c))
         (fn-octets$c (update-fn-octets$c-fill used fn-octets$c))
         (before-capacity (fn-octets$c-buf-length fn-octets$c))
         (before-fill (fn-octets$c-fill fn-octets$c))
         (fn-octets$c (fn-octets$c-append-octet byte fn-octets$c)))
    (mv (list before-capacity before-fill
              (fn-octets$c-buf-length fn-octets$c) (fn-octets$c-fill fn-octets$c))
        fn-octets$c)))
(defun rxb-cost-test (capacity used byte)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-octets$c
    (mv-let (result fn-octets$c)
      (rxb-cost-test-in capacity used byte fn-octets$c) result)))
(defconst *rxb-cost-positive* (rxb-cost-test 4096 1 65))
; Complete two-premise concrete no-resize theorem tooth.
(assert-event
 (and (<= *fn-cbud-read-quantum* (nth 0 *rxb-cost-positive*))
      (< (nth 1 *rxb-cost-positive*) (fn-cbud-step-read-octets nil))
      (equal (nth 2 *rxb-cost-positive*) (nth 0 *rxb-cost-positive*))
      (equal (nth 3 *rxb-cost-positive*) (+ 1 (nth 1 *rxb-cost-positive*)))))
(defconst *rxb-no-capacity* (rxb-cost-test 0 0 65))
; Remove installed-capacity premise, affirm remaining quantum premise,
; and falsify complete no-resize conclusion on an actual initially empty array.
(assert-event
 (and (not (<= *fn-cbud-read-quantum* (nth 0 *rxb-no-capacity*)))
      (< (nth 1 *rxb-no-capacity*) (fn-cbud-step-read-octets nil))
      (not (and (equal (nth 2 *rxb-no-capacity*) (nth 0 *rxb-no-capacity*))
                (equal (nth 3 *rxb-no-capacity*) (+ 1 (nth 1 *rxb-no-capacity*)))))))
(defconst *rxb-no-quantum* (rxb-cost-test 4096 4096 65))
; Remove quantum premise, affirm installed capacity, and falsify conclusion.
(assert-event
 (and (<= *fn-cbud-read-quantum* (nth 0 *rxb-no-quantum*))
      (not (< (nth 1 *rxb-no-quantum*) (fn-cbud-step-read-octets nil)))
      (not (and (equal (nth 2 *rxb-no-quantum*) (nth 0 *rxb-no-quantum*))
                (equal (nth 3 *rxb-no-quantum*) (+ 1 (nth 1 *rxb-no-quantum*)))))))
