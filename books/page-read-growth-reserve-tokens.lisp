; KNOWN GAP: shapes other than fn-prl-token are COPIED from their call sites (file:line
; below); a call site that changes its shape is not caught here.
; G5(a): the growth-reserve token (:growth-reserve N) is disjoint from every token
; constructor whose row can sit in the ledger bindings, so no other holder's
; token can ever name, free or forge the reserve row.  Constructors covered
; (heads as written at the issuing call sites, found by
; `git grep -n fn-prs-issue -- books host`):
;   binding writers: fn-prl-token (page-read-ledger fn-prl-admit); (:incarnation file)
;   (fn-prl-register) and (:incarnation next) (recovery-page-file-controller);
;   (:window next . descriptor) (page-window-lease); (:decoded-window next . descriptor)
;   (decoded-window-lease); (:discovery ...) (page-discovery-ledger); (:file-pin ...)
;   (page-file-lease); (:maintenance ...) (page-maintenance-lease);
;   (tag next . fields) of fn-bca-admit (fixed-buffer-capacity; the only caller
;   passes :rx-capacity).
;   non-binding issuers (token held in the issuer's own slot): fn-act-token
;   :account-preparation-turn; fn-apr-token :admission-grant; fn-ioh-token :incoming;
;   :history-capture; :bp-job; :connection-holder; :index-generation; :index-page;
;   :ninep-mount; :owner-report; :reader-output-window; :rx-capacity.
(in-package "ACL2")
(include-book "page-read-budget-growth")

(defthm fn-prl-growth-token-disjoint-from-fn-prl-token
  (not (equal (fn-prl-token id cid file eoff elen trailer) (fn-prl-growth-token n)))
  :hints (("Goal" :in-theory (enable fn-prl-token fn-prl-growth-token))))

(defthm fn-prl-growth-token-disjoint-from-keyword-headed-tokens
  (and ; page-read-ledger.lisp:63, recovery-page-file-controller.lisp:75
       (not (equal (cons :incarnation rest) (fn-prl-growth-token n)))
       ; page-window-lease.lisp:31
       (not (equal (cons :window (cons next descriptor)) (fn-prl-growth-token n)))
       ; decoded-window-lease.lisp:22
       (not (equal (cons :decoded-window (cons next descriptor)) (fn-prl-growth-token n)))
       ; page-discovery-ledger.lisp:25
       (not (equal (list :discovery next file eoff elen) (fn-prl-growth-token n)))
       ; page-file-lease.lisp:25
       (not (equal (list :file-pin next file) (fn-prl-growth-token n)))
       ; page-maintenance-lease.lisp:26
       (not (equal (list :maintenance next epoch suffix-count) (fn-prl-growth-token n)))
       ; receiver-capacity-current.lisp:46, host/receiver-resource-host.lisp:16 (fn-bca-admit)
       (not (equal (cons :rx-capacity (cons next fields)) (fn-prl-growth-token n)))
       ; account-adoption-turn.lisp:10
       (not (equal (cons :account-preparation-turn rest) (fn-prl-growth-token n)))
       ; admission-preallocation-resources.lisp:31
       (not (equal (cons :admission-grant rest) (fn-prl-growth-token n)))
       ; incoming-octet-holder.lisp:11
       (not (equal (cons :incoming rest) (fn-prl-growth-token n)))
       ; history-capture-custody.lisp:58
       (not (equal (cons :history-capture rest) (fn-prl-growth-token n)))
       ; bp-controller-checkpoint-current.lisp:43
       (not (equal (cons :bp-job rest) (fn-prl-growth-token n)))
       ; index-connection-issuer.lisp:65
       (not (equal (cons :connection-holder rest) (fn-prl-growth-token n)))
       ; index-generation-issuer.lisp:59
       (not (equal (cons :index-generation rest) (fn-prl-growth-token n)))
       ; index-page-issuer.lisp:59
       (not (equal (cons :index-page rest) (fn-prl-growth-token n)))
       ; ninep-mount.lisp:66
       (not (equal (cons :ninep-mount rest) (fn-prl-growth-token n)))
       ; owner-report-reservation.lisp:62
       (not (equal (cons :owner-report rest) (fn-prl-growth-token n)))
       ; reader-output-job.lisp:54
       (not (equal (cons :reader-output-window rest) (fn-prl-growth-token n))))
  :hints (("Goal" :in-theory (enable fn-prl-growth-token))))

(defthm fn-prl-growth-token-disjoint-from-fn-bca-tokens
  (implies (not (equal tag :growth-reserve))
           (not (equal (cons tag (cons next fields)) (fn-prl-growth-token n))))
  :hints (("Goal" :in-theory (enable fn-prl-growth-token))))
