; Physical worker/window publication join; fn-ews is the actual byte digest.
(in-package "ACL2")
(include-book "page-window-executor")
(include-book "extent-window-stream")

(defun fn-pwr-plan-matches-token (s token)
  (declare (xargs :guard (true-listp s)
                  :guard-hints (("Goal" :in-theory (enable fn-pwx-tokenp)))))
  (and (fn-pwx-tokenp token)
       (equal (nth 8 s) (fn-prl-nth 1 token))
       (equal (nth 10 s) token)
       (equal (list (nth 1 s) (nth 2 s) (nth 3 s) (nth 11 s)
                    (nth 12 s) (nth 13 s) (nth 6 s))
              (cddr token))))

; Scalar only: no vector/list alias can escape the physical borrow. I is
; relative to the requested window. Bounds and publication are core choices.
(defun fn-pwr-byte (ledger worker token s i fn-ew-buffer)
  (declare (xargs :stobjs fn-ew-buffer :guard (true-listp s)))
  (if (and (fn-pwx-boundp ledger worker token :returned)
           (fn-pwr-plan-matches-token s token)
           (fn-ewp-publication s)
           (natp i) (natp (nth 5 s)) (<= (nth 5 s) 16384) (< i (nth 5 s)))
      (mv :byte (fn-ew-bytesi i fn-ew-buffer))
    (mv :unavailable nil)))

(defthm fn-pwr-byte-authorization-by-definition
  (implies (equal (mv-nth 0 (fn-pwr-byte ledger worker token s i fn-ew-buffer)) :byte)
           (and (fn-pwx-boundp ledger worker token :returned)
                (fn-pwr-plan-matches-token s token)
                (fn-ewp-publication s)
                (natp i) (< i (nth 5 s)) (<= (nth 5 s) 16384)
                (equal (mv-nth 1 (fn-pwr-byte ledger worker token s i fn-ew-buffer))
                       (nth i (nth 0 fn-ew-buffer)))))
  :rule-classes nil)

(in-theory (disable fn-pwr-plan-matches-token fn-pwr-byte))
