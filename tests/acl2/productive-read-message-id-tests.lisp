; Literal READ witnesses: each complete retained antecedent and conclusion.
; Bounds derived by the final theorem are not separate hypotheses.
; Funding removals use a reader-reachable owner paired with an empty ledger:
; these are corrupted-credit-state witnesses, not complete native traces.
(in-package "ACL2")

(include-book "productive-read-chain-tests")
(defconst *pcrm-token* (fn-nntp-string-octets "<pcrt@x>"))

(defconst *pcrm-line* (append (fn-nntp-string-octets "ARTICLE ") *pcrm-token*))

(defconst *pcrm-line-bytes* (append *pcrm-line* (quote (13 10))))

