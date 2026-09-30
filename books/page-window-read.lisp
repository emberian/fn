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

; An authenticated terminal success, a failed read and stale ownership are
; separate core answers. A failed integrity check never asks for a rescan.
(defun fn-pwr-outcome (ledger worker token s)
  (declare (xargs :guard (true-listp s)))
  (cond ((not (fn-pwx-boundp ledger worker token :returned)) :stale-job)
        ((not (fn-pwr-plan-matches-token s token)) '(:fault :state))
        ((fn-ewp-publication s) :ready)
        ((member-eq (nth 0 s) '(:bounds :commitment :digest :state :read))
         (list :fault (nth 0 s)))
        (t '(:fault :state))))

(defthm fn-pwr-ready-requires-exact-publication-by-definition
  (implies (equal (fn-pwr-outcome ledger worker token s) :ready)
           (and (fn-pwx-boundp ledger worker token :returned)
                (fn-pwr-plan-matches-token s token) (fn-ewp-publication s)))
  :rule-classes nil)

(in-theory (disable fn-pwr-outcome))

; The arena passes payload-relative I. The core alone chooses the relative
; window index, after checking the unchanged physical/payload descriptor.
(defun fn-pwr-byte-at (ledger worker token s file eoff elen poff plen trailer i fn-ew-buffer)
  (declare (xargs :stobjs fn-ew-buffer :guard (true-listp s)))
  (let ((outcome (fn-pwr-outcome ledger worker token s)))
    (if (not (equal outcome :ready)) (mv outcome nil)
      (if (and (fn-pwx-tokenp token)
           (equal (list file eoff elen poff plen trailer)
                  (list (fn-prl-nth 2 token) (fn-prl-nth 3 token)
                        (fn-prl-nth 4 token) (fn-prl-nth 5 token)
                        (fn-prl-nth 6 token) (fn-prl-nth 8 token)))
           (natp i) (natp plen) (< i plen)
           (natp (fn-prl-nth 7 token)) (<= (fn-prl-nth 7 token) i))
      (fn-pwr-byte ledger worker token s (- i (fn-prl-nth 7 token)) fn-ew-buffer)
    (mv :unavailable nil)))))

(defthm fn-pwr-byte-at-refines-payload-coordinate-by-definition
  (implies (equal (mv-nth 0 (fn-pwr-byte-at ledger worker token s file eoff elen poff plen trailer i fn-ew-buffer)) :byte)
           (and (fn-pwx-boundp ledger worker token :returned)
                (fn-pwr-plan-matches-token s token) (fn-ewp-publication s)
                (natp i) (natp plen) (< i plen)
                (natp (fn-prl-nth 7 token)) (<= (fn-prl-nth 7 token) i)
                (< (- i (fn-prl-nth 7 token)) (nth 5 s))
                (equal (mv-nth 1 (fn-pwr-byte-at ledger worker token s file eoff elen poff plen trailer i fn-ew-buffer))
                       (nth (- i (fn-prl-nth 7 token)) (nth 0 fn-ew-buffer)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwr-byte fn-pwr-outcome))))

(defun fn-pwr-cold-descriptor (file eoff elen poff plen trailer i)
  (declare (xargs :guard t))
  (list file eoff elen poff plen i trailer))

(in-theory (disable fn-pwr-byte-at fn-pwr-cold-descriptor))
