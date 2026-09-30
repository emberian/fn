(in-package "ACL2")
(include-book "../../books/page-window-read")
(include-book "page-window-executor-tests")
; Test-only bytes source follows the actual core-issued effects and digest.
(defun pwrtest-run (fuel archive s pgs-digest-state fn-ew-buffer fn-octets reads)
  (declare (xargs :stobjs (pgs-digest-state fn-ew-buffer fn-octets)
                  :measure (nfix fuel) :verify-guards nil))
  (cond ((zp fuel) (mv :fuel s pgs-digest-state fn-ew-buffer fn-octets reads))
        ((not (member-eq (nth 0 s) '(:scan :trailer)))
         (mv (nth 0 s) s pgs-digest-state fn-ew-buffer fn-octets reads))
        (t (let ((effect (fn-ews-effect s pgs-digest-state)))
             (if effect
                 (let* ((bytes (fn-b3-firstn (nth 5 effect)
                                   (fn-b3-nthcdrx (- (nth 4 effect) (nth 2 s)) archive)))
                        (fn-octets (fn-octets-from-list bytes fn-octets)))
                   (mv-let (status s pgs-digest-state fn-ew-buffer)
                     (fn-ews-read effect :ok s fn-octets pgs-digest-state fn-ew-buffer)
                     (declare (ignore status))
                     (pwrtest-run (1- fuel) archive s pgs-digest-state fn-ew-buffer fn-octets
                               (+ reads (len bytes)))))
               (mv-let (status s pgs-digest-state)
                 (fn-ews-tick s pgs-digest-state)
                 (declare (ignore status))
                 (pwrtest-run (1- fuel) archive s pgs-digest-state fn-ew-buffer fn-octets reads)))))))


(defun-nx pwrtest-ready ()
  (let* ((msg '(1 2 3)) (digest (fn-blake3 msg))
         (descriptor (list 11 100 3 100 3 0 (fn-bch-pack digest)))
         (admit (fn-prw-admit *prw-registered* descriptor '(256 0 0 1 1)))
         (token (nth 1 admit))
         (acquire (fn-pwx-acquire (nth 2 admit) (fn-pxe-new 0) token))
         (begin (fn-ews-begin 11 100 3 100 3 0 (nth 1 token) 47 token
                              (fn-bch-pack digest) (create-pgs-digest-state)))
         (run (pwrtest-run 40 (append msg digest) (car begin) (cadr begin)
                          (create-fn-ew-buffer) nil 0))
         (returned (fn-pwx-return (nth 2 acquire) (nth 1 acquire) token)))
    (list token acquire returned run)))

; REACHABLE POSITIVE: actual authenticated stream, complete literal
; antecedent/conclusion of fn-pwr-byte-authorization-by-definition.
(defun-nx pwrtest-positive ()
 (let* ((r (pwrtest-ready)) (token (nth 0 r)) (returned (nth 2 r))
        (run (nth 3 r)) (s (nth 1 run)) (buffer (nth 3 run))
        (ledger (nth 2 returned)) (worker (nth 1 returned))
        (answer (fn-pwr-byte ledger worker token s 1 buffer)))
   (and (equal (nth 0 run) :verified) (equal (nth 0 returned) :returned)
        (equal (nth 0 answer) :byte)
        (fn-pwx-boundp ledger worker token :returned)
        (fn-pwr-plan-matches-token s token) (fn-ewp-publication s)
        (natp 1) (< 1 (nth 5 s)) (<= (nth 5 s) 16384)
        (equal (nth 1 answer) (nth 1 (nth 0 buffer)))
        (equal (nth 1 answer) 2))))
(defthm pwrtest-positive-witness (pwrtest-positive) :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwr-byte fn-pwr-plan-matches-token))))

; HYPOTHESIS-REMOVAL: sole antecedent fails on actually running slot;
; conclusion fails too, because exact returned ownership is absent.
(defun-nx pwrtest-removal ()
 (let* ((r (pwrtest-ready)) (token (nth 0 r)) (acquire (nth 1 r))
        (run (nth 3 r)) (s (nth 1 run)) (buffer (nth 3 run))
        (ledger (nth 2 acquire)) (worker (nth 1 acquire))
        (answer (fn-pwr-byte ledger worker token s 1 buffer)))
   (and (not (equal (nth 0 answer) :byte))
        (not (and (fn-pwx-boundp ledger worker token :returned)
                  (fn-pwr-plan-matches-token s token) (fn-ewp-publication s)
                  (natp 1) (< 1 (nth 5 s)) (<= (nth 5 s) 16384)
                  (equal (nth 1 answer) (nth 1 (nth 0 buffer))))))))

(defthm pwrtest-removal-witness (pwrtest-removal) :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwr-byte fn-pwr-plan-matches-token))))
