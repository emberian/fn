; fn: transit and delivery under the store profile's header limits (PRF-230,
; PKT-660, lane header-limits-profile-2, 2026-09-27; D27).
;
; A POST is refused past the opened profile's max-header-fields, -lines and
; -octets (books/injection.lisp `fn-inj-decide', PRF-230).  PKT-660, decided
; by the coordinator as its default: every other admission receives the same
; limits and refuses by the same names.
;
;   peer transit (IHAVE, TAKETHIS)  `fn-peer-decide-transfer-under'
;       (books/peer-inbound.lisp), called by host/owner-host.lisp
;       `fn-owner-transit-decide' with the owner's limits; 437 / 439 with the
;       limit's reason text (`fn-peer-reason-text')
;   BP transit delivery             `fn-own-bp-transit-submit-result'
;       (books/owner.lisp), called by host/owner-host.lisp
;       `fn-owner-bp-transit-submit'; the refusal line names the limit
;   BP (and CLI) control delivery   `fn-own-control-decision'
;       (books/owner.lisp), called through `fn-own-control-submit-result' by
;       host/owner-host.lisp `fn-owner-control-submit'
;
; The limits are the owner's injection configuration's
; (`fn-own-config-header-limits'), which host/owner-host.lisp
; `fn-owner-served-post-bound' builds from the opened profile for POST.  Each
; theorem below says the admission admits exactly what the parse under
; those limits admits (books/article-header-limits.lisp
; `fn-article-census-refusal-is-the-parse', the keystone
; `fn-article-parse-under-admits-exactly-the-limits'), and refuses the rest
; by a limit's name.  For transit the census is of the octets the node would
; store (the Path-updated `fn-peer-relayed-octets'): what is stored reparses
; under the limits it was admitted under.
(in-package "ACL2")
(include-book "owner")
(include-book "article-header-limits")

(defthm fn-peer-transfer-want-or-defer-parses-the-stored-article
  (implies (member-equal (fn-peer-decision-kind
                          (fn-peer-decide-transfer node cfg peer msgid octets
                                                   clock id subject))
                         '(:want :defer))
           (fn-article-result-okp
            (fn-article-parse (fn-peer-relayed-octets cfg peer octets))))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-peer-decide-transfer
                                fn-peer-decision-kind-of-fn-peer-decision
                                member-equal)
                              (theory 'minimal-theory)))))

(defthm fn-peer-decide-transfer-under-admits-exactly-the-limits
  (let* ((d (fn-peer-decide-transfer node cfg peer msgid octets clock id subject))
         (u (fn-peer-decide-transfer-under node cfg peer msgid octets clock id
                                           subject limits))
         (stored (fn-peer-relayed-octets cfg peer octets))
         (p (fn-article-parse-under stored limits)))
    (implies (member-equal (fn-peer-decision-kind d) '(:want :defer))
             (if (fn-article-result-okp p)
                 (and (equal u d)
                      (equal p (fn-article-parse stored)))
               (and (equal (fn-peer-decision-kind u) :refuse)
                    (fn-article-limit-reasonp (fn-peer-decision-reason u))
                    (fn-article-limit-reasonp (cadr p))))))
  :hints (("Goal"
           :use ((:instance fn-peer-transfer-want-or-defer-parses-the-stored-article)
                 (:instance fn-article-census-refusal-is-the-parse
                            (octets (fn-peer-relayed-octets cfg peer octets))))
           :in-theory (union-theories
                       '(fn-peer-decide-transfer-under
                         fn-peer-header-limit-refusal
                         fn-peer-decision-kind-of-fn-peer-decision
                         fn-peer-decision-reason-of-fn-peer-decision
                         fn-article-census-refusal-is-a-limit-reason
                         member-equal)
                       (theory 'minimal-theory)))))

(defthm fn-peer-decide-transfer-under-wants-only-what-transfer-wants
  (let ((u (fn-peer-decide-transfer-under node cfg peer msgid octets clock id
                                          subject limits))
        (stored (fn-peer-relayed-octets cfg peer octets)))
    (implies (equal (fn-peer-decision-kind u) :want)
             (and (equal u (fn-peer-decide-transfer node cfg peer msgid octets
                                                    clock id subject))
                  (fn-article-result-okp (fn-article-parse-under stored limits))
                  (equal (fn-article-parse-under stored limits)
                         (fn-article-parse stored)))))
  :hints (("Goal"
           :use ((:instance fn-peer-decide-transfer-under-admits-exactly-the-limits))
           :in-theory (union-theories
                       '(fn-peer-decide-transfer-under
                         fn-peer-decision-kind-of-fn-peer-decision
                         member-equal)
                       (theory 'minimal-theory)))))

(defthm fn-peer-decide-transfer-under-keeps-refusals-and-duplicates-by-definition
  (let ((d (fn-peer-decide-transfer node cfg peer msgid octets clock id subject)))
    (implies (not (member-equal (fn-peer-decision-kind d) '(:want :defer)))
             (equal (fn-peer-decide-transfer-under node cfg peer msgid octets
                                                   clock id subject limits)
                    d)))
  :hints (("Goal" :in-theory (union-theories '(fn-peer-decide-transfer-under)
                                             (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; The owner's BP transit delivery

(defthm fn-own-bp-transit-submits-only-within-the-limits
  (let ((limits (fn-own-config-header-limits (fn-own-config o))))
    (implies (equal (fn-own-bp-transit-submit-result o cfg peer msgid octets
                                                     id subject)
                    :submitted)
             (and (equal (fn-peer-decision-kind
                          (fn-peer-decide-transfer
                           (fn-sn-node (fn-own-store o)) cfg peer msgid octets
                           (fn-own-clock o) id subject))
                         :want)
                  (fn-article-result-okp
                   (fn-article-parse-under
                    (fn-peer-relayed-octets cfg peer octets) limits)))))
  :hints (("Goal"
           :use ((:instance fn-peer-decide-transfer-under-wants-only-what-transfer-wants
                            (node (fn-sn-node (fn-own-store o)))
                            (clock (fn-own-clock o))
                            (limits (fn-own-config-header-limits (fn-own-config o)))))
           :in-theory (e/d (fn-own-bp-transit-submit-result)
                           (fn-peer-decide-transfer-under
                            fn-peer-decide-transfer fn-peer-relayed-octets
                            fn-article-parse-under fn-article-parse
                            fn-own-config-header-limits)))))

; Past the limits the delivery is refused, whatever else holds; the host
; names the reason from the same decision (`fn-owner-bp-transit-submit').
(defthm fn-own-bp-transit-refuses-past-the-limits
  (implies (not (fn-article-result-okp
                 (fn-article-parse-under
                  (fn-peer-relayed-octets cfg peer octets)
                  (fn-own-config-header-limits (fn-own-config o)))))
           (equal (fn-own-bp-transit-submit-result o cfg peer msgid octets
                                                   id subject)
                  :refused))
  :hints (("Goal"
           :use ((:instance fn-peer-decide-transfer-under-admits-exactly-the-limits
                            (node (fn-sn-node (fn-own-store o)))
                            (clock (fn-own-clock o))
                            (limits (fn-own-config-header-limits (fn-own-config o))))
                 (:instance fn-peer-decide-transfer-under-keeps-refusals-and-duplicates-by-definition
                            (node (fn-sn-node (fn-own-store o)))
                            (clock (fn-own-clock o))
                            (limits (fn-own-config-header-limits (fn-own-config o)))))
           :in-theory (union-theories
                       '(fn-own-bp-transit-submit-result member-equal
                         fn-own-bp-transit-kind-word
                         (:executable-counterpart equal))
                       (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; The owner's control delivery (a BP application's article, the CLI's)

; The gate `fn-own-control-decision' asks before the header limits.
(defun fn-thl-control-gatep (cfg msgid groups octets)
  (declare (xargs :guard t))
  (and (fn-inj-config-allow cfg)
       (fn-af-message-idp msgid)
       (fn-inj-group-namesp groups)
       (consp groups)
       (fn-octet-listp octets)
       (posp (fn-inj-config-max-octets cfg))
       (<= (len octets) (fn-inj-config-max-octets cfg))))

(defthm fn-own-control-decision-injects-only-within-the-limits
  (let ((limits (fn-own-config-header-limits cfg)))
    (implies (and (fn-article-result-okp (fn-article-parse octets))
                  (fn-inj-injectedp (fn-own-control-decision cfg msgid groups
                                                             octets)))
             (and (fn-article-result-okp (fn-article-parse-under octets limits))
                  (equal (fn-article-parse-under octets limits)
                         (fn-article-parse octets)))))
  :hints (("Goal"
           :use ((:instance fn-article-census-refusal-is-the-parse
                            (limits (fn-own-config-header-limits cfg))))
           :in-theory (e/d (fn-own-control-decision
                            fn-inj-refuse fn-inj-injectedp)
                           (fn-article-parse fn-article-parse-under
                            fn-article-result-okp fn-article-header-census
                            fn-article-census-refusal fn-own-config-header-limits
                            fn-af-message-idp fn-inj-group-namesp
                            fn-octet-listp)))))

(defthm fn-own-control-decision-refuses-past-the-limits-by-name
  (let ((limits (fn-own-config-header-limits cfg))
        (dec (fn-own-control-decision cfg msgid groups octets)))
    (implies (and (fn-thl-control-gatep cfg msgid groups octets)
                  (fn-article-result-okp (fn-article-parse octets))
                  (not (fn-article-result-okp
                        (fn-article-parse-under octets limits))))
             (and (not (fn-inj-injectedp dec))
                  (fn-article-limit-reasonp (fn-inj-decision-reason dec)))))
  :hints (("Goal"
           :use ((:instance fn-article-census-refusal-is-the-parse
                            (limits (fn-own-config-header-limits cfg))))
           :in-theory (e/d (fn-own-control-decision fn-thl-control-gatep
                            fn-inj-refuse fn-inj-injectedp)
                           (fn-article-parse fn-article-parse-under
                            fn-article-result-okp fn-article-header-census
                            fn-article-census-refusal fn-own-config-header-limits
                            fn-af-message-idp fn-inj-group-namesp
                            fn-octet-listp)))))
