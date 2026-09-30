; Internal authority capture/recheck; no runtime caller or funding installed.
(in-package "ACL2")
(include-book "../books/owner-incoming-freshness")
(include-book "../books/definterface")

(definterface fn-owner-incoming-authority-capture :class :common-lisp-compliant)
(definterface fn-owner-incoming-authority-recheck :class :common-lisp-compliant
 :keystones (fn-owner-incoming-recheck-current-matches-live-authority
             fn-owner-incoming-recapture-retains-original-roots))
