; Literal full-state scanner carry. No buffer range hypothesis is required
; by the total logical theorem; executable witnesses use valid bounded ranges.
(in-package "ACL2")
(include-book "../../books/wire-scan-full-state")
(defconst *wsft-command* (fn-wire-initial-state 64 4096))
(defconst *wsft-article*
 (fn-wire-result-state (fn-wire-begin-article *wsft-command*)))
(defun wsft-positive (initial bytes cut fn-octets)
 (declare (xargs :stobjs fn-octets :guard t :verify-guards nil))
 (let* ((fn-octets (fn-octets-from-list bytes fn-octets))
        (end (fn-octets-len fn-octets))
        (f1 (fn-wire-span-fold initial 0 cut fn-octets))
        (r1 (fn-wire-scan initial 0 cut fn-octets))
        (s1 (fn-wsp-state r1))
        (f2 (fn-wire-span-fold s1 (fn-wsp-next r1) end fn-octets))
        (r2 (fn-wire-scan s1 (fn-wsp-next r1) end fn-octets)))
  (mv (and (fn-wire-statep initial)
           (fn-wire-statep s1)
           (fn-wire-statep (fn-wsp-state f1))
           (fn-wire-statep (fn-wsp-state f2))
           (fn-wire-statep (fn-wsp-state r2))) fn-octets)))
(defun wsft-positive-pair (fn-octets)
 (declare (xargs :stobjs fn-octets :verify-guards nil))
 (mv-let (command fn-octets)
  (wsft-positive *wsft-command* '(79 86 69 82 13 10) 2 fn-octets)
  (mv-let (article fn-octets)
   (wsft-positive *wsft-article* '(46 46 65 13 10 46 13 10) 3 fn-octets)
   (mv (and command article) fn-octets))))
(defun wsft-positives ()
 (with-local-stobj fn-octets
  (mv-let (v fn-octets) (wsft-positive-pair fn-octets) v)))
(assert-event (wsft-positives))
; Corrupted-state literal hypothesis removal: the fixed fast shape cannot
; substitute for the full retained-octet invariant. Empty scan preserves the
; existing bad tail and affirmatively falsifies the claimed conclusion.
(defconst *wsft-bad*
 (fn-wire-make-state :command '(not-an-octet) 1 nil nil 0 64 4096))
(defun wsft-removal (fn-octets)
 (declare (xargs :stobjs fn-octets :verify-guards nil))
 (mv (and (fn-wire-fast-statep *wsft-bad*)
      (not (fn-wire-statep *wsft-bad*))
      (not (fn-wire-statep
             (fn-wsp-state (fn-wire-scan *wsft-bad* 0 0 fn-octets))))
      (not (fn-wire-statep
             (fn-wsp-state (fn-wire-span-fold *wsft-bad* 0 0 fn-octets))))) fn-octets))
(defun wsft-removal-value ()
 (with-local-stobj fn-octets
  (mv-let (v fn-octets) (wsft-removal fn-octets) v)))
(assert-event (wsft-removal-value))
