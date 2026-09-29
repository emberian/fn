; fn: the transit decision with its authority verdict (W5b's fn-pta-decide,
; books/peer-transit-authority.lisp), its byte decision's capacity arm
; answered from the carried obligation-id trie (Q5a-2, served-costs-6).
;
; fn-owner-transit-decide (host/owner-host.lisp) calls fn-pta-decide for
; every IHAVE/TAKETHIS and BP transit article.  Its byte decision is
; fn-peer-decide-transfer-under's, whose capacity arm (fn-retain-admissiblep)
; scans every pin and release of the node's ledger.  fn-ptac-decide is
; fn-pta-decide with that decision taken by fn-irc-peer-decide-transfer-under
; (books/identity-retain-carried.lisp) over the host's carry; the verdict is
; fn-pta-decide's, term for term.  The KEYSTONE names the host's call: with
; the carry refreshed to any ledger, the pair is fn-pta-decide's.

(in-package "ACL2")
(include-book "identity-retain-carried")
(include-book "peer-transit-authority")

(defun fn-ptac-decide (index keyring v gen node cfg peer msgid octets clock id
                             subject limits carry)
  (declare (xargs :guard (and (fn-node-statep node) (fn-prin-keyringp keyring))
                  :verify-guards nil))
  (let ((d (fn-irc-peer-decide-transfer-under node cfg peer msgid octets clock
                                              id subject limits carry)))
    (if (not (equal (fn-peer-decision-kind d) :want))
        (mv d :none)
      (let* ((a (fn-stx-parse (fn-peer-relayed-octets cfg peer octets)))
             (s (if a (fn-stx-statement-of a) nil))
             (groups (nth 3 (fn-peer-injection-arguments node cfg peer msgid octets
                                                         0 id subject clock))))
        (mv d (fn-pta-groups-verdict index keyring v gen groups s))))))

;; KEYSTONE (the host's call, fn-owner-transit-decide): with the carry
;; refreshed to a ledger, the decision and its verdict are fn-pta-decide's.
(defthm fn-ptac-decide-of-refresh-is-pta-decide
  (implies (fn-prc-carryp carry)
           (equal (fn-ptac-decide index keyring v gen node cfg peer msgid octets
                                  clock id subject limits
                                  (fn-prc-refresh carry ledger))
                  (fn-pta-decide index keyring v gen node cfg peer msgid octets
                                 clock id subject limits)))
  :hints (("Goal" :in-theory
           '(fn-ptac-decide fn-pta-decide
             fn-irc-peer-decide-transfer-under-of-refresh-is-reference))))

(verify-guards fn-ptac-decide)

(in-theory (disable (:d fn-ptac-decide)))
