; Productive inbound transit: actual configured host outcome after the
; shared nine successful store/completion observations. Source-admitted;
; remaining hypothesis teeth and qualification are open, so no registry claim.
(in-package "ACL2")
(include-book "productive-contract")
(include-book "owner-outcome-pinned")

; The wire strings are fn policy; the reply codes are RFC 3977 section
; 6.3.2 (235) and RFC 4644 section 2.5 (239, echoing the Message-ID).
(defun fn-pct-inbound-success-octets (submission)
 (declare (xargs :guard (true-listp (fn-peer-submission-msgid submission))))
 (if (equal (fn-peer-submission-kind submission) :ihave)
     (append (fn-nntp-string-octets "235 article transferred OK") '(13 10))
   (append (fn-nntp-string-octets "239 ")
           (fn-peer-submission-msgid submission) '(13 10))))

(local
 (defthm fn-pct-inj-nth-1-of-cons
  (equal (fn-inj-nth 1 (cons a (cons b c))) b)
  :hints (("Goal" :expand ((fn-inj-nth 1 (cons a (cons b c)))
                            (fn-inj-nth 0 (cons b c)))
           :in-theory (enable fn-inj-nth fn-inj-car fn-inj-cdr)))))

(defthm fn-pct-durable-transit-observer
 (equal (fn-served-reply-octets
         (fn-served-result-effects
          (fn-served-transit-outcome conn submission decision :durable)))
        (fn-pct-inbound-success-octets submission))
 :rule-classes nil
 :hints (("Goal" :in-theory
          (e/d (fn-inj-nth fn-served-transit-outcome fn-peer-transit-outcome
                fn-peer-transit-outcome-effects fn-peer-transit-code
                fn-peer-single fn-peer-echo-reply fn-nntp-single
                fn-pct-inbound-success-octets fn-served-reply-octets
                fn-nntp-crlf fn-nntp-reply-effect
                fn-post-result-effects fn-post-make-result
                fn-served-result-effects fn-served-make-result
                fn-nntp-result-effects fn-nntp-make-result)
               (fn-peer-submission-kind fn-peer-submission-msgid
                fn-served-conn-session fn-auth-session-base)))))

(local
 (defthm fn-pct-transit-submission-nonempty
  (implies (fn-own-transit-subp sub) sub)
  :rule-classes nil
  :hints (("Goal" :in-theory
            (union-theories '(fn-own-transit-subp) (theory 'minimal-theory))))))

(defthm fn-pct-consumed-transit-host-outcome-has-success-octets
 (let* ((o (fn-ocfg-owner oc))
        (sub (fn-own-inflight o))
        (conn (fn-own-find-conn id (fn-own-conns o))))
  (implies (and conn (equal (fn-own-sub-id sub) id)
                (fn-own-transit-subp sub)
                (fn-own-completion-consumedp o))
           (equal (fn-served-reply-octets
                   (car (fn-oop-transit-outcome oc id :want reason :durable)))
                  (fn-pct-inbound-success-octets (fn-own-sub-decision sub)))))
 :rule-classes nil
 :hints (("Goal"
          :use ((:instance fn-pct-transit-submission-nonempty
                           (sub (fn-own-inflight (fn-ocfg-owner oc))))
                (:instance fn-oop-transit-outcome-is-own-transit-outcome
                           (kind :want) (word :durable))
                (:instance fn-pct-durable-transit-observer
                 (conn (fn-served-make-conn-group-indexed
                        (fn-own-conn-wire (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))
                        (fn-own-conn-session (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))
                        (fn-own-conn-archive (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))
                        (fn-own-conn-config (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))
                        (fn-own-conn-observation (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))
                        (fn-own-clock (fn-ocfg-owner oc))
                        (fn-own-conn-verdicts (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))
                        (fn-own-conn-index (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))
                        (fn-own-conn-group-index (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))
                        (fn-own-conn-control (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))))
                 (submission (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner oc))))
                 (decision (fn-peer-decision :want reason))))
          :in-theory
          (e/d (fn-own-transit-outcome fn-own-outcome-rendering
                fn-own-outcome-completion fn-own-durable-wordp)
               (fn-oop-transit-outcome fn-oop-transit-outcome-is-own-transit-outcome
                fn-own-completion-consumedp fn-own-find-conn fn-own-sub-id
                fn-own-inflight fn-own-conns fn-own-transit-subp
                fn-own-sub-decision fn-own-advance fn-own-feed-durable
                fn-own-transit-refused fn-served-transit-outcome
                fn-served-result-effects fn-served-reply-octets
                fn-pct-inbound-success-octets fn-served-make-conn-group-indexed)))))

(in-theory (disable fn-pct-inbound-success-octets))

; The subject is fn-oop-transit-outcome, called by fn-owner-transit-outcome
; in host/owner-host.lisp. Its equality to the raw owner's outcome is named
; in owner-outcome-pinned. The nine observations run the same store as POST;
; the actual transit reply is derived from consumed durable completion.
(defthm fn-pct-inbound-nine-steps-produce-durable-success
 (let* ((o (fn-ocfg-owner oc))
        (s (fn-own-store o))
        (sub (fn-own-inflight o))
        (w (fn-row-wire-of r fn-arena))
        (conn (fn-own-find-conn id (fn-own-conns o)))
        (o8 (fn-own-run o (fn-pcx-wrap-store (fn-pcx-store-script (list :prepare r))) fn-arena))
        (o9 (fn-own-run o (fn-pcx-post-script (list :prepare r)) fn-arena))
        (pair (fn-sf-record-pair r))
        (out (fn-oop-transit-outcome (fn-ocfg-with-owner oc o9) id :want reason :durable)))
  (implies (and (fn-sn-statep s) (fn-pcx-admissiblep s r)
                (eq (fn-th-at 0 (fn-th-prefix-step (fn-sn-topic s) r)) :ok)
                (equal (fn-own-sub-id sub) id) conn
                (fn-own-transit-subp sub)
                (natp (fn-own-sub-mark sub))
                (<= (fn-own-sub-mark sub) (len (fn-own-ledger o)))
                (equal (fn-record-msgid w) (fn-record-octets-string (fn-own-sub-msgid sub)))
                (equal (fn-record-payload w) (fn-own-sub-stored-octets cfg sub (fn-own-node-secret o))))
           (and (equal (len (fn-pcx-post-script (list :prepare r))) *fn-pcx-post-steps*)
                (equal (car (fn-own-finish o8 cfg fn-arena)) :durable)
                (equal o9 (cdr (fn-own-finish o8 cfg fn-arena)))
                (fn-own-completion-consumedp o9)
                (equal (fn-own-ledger o9) (append (fn-own-ledger o) (list pair)))
                (equal (fn-sf-successes (fn-sn-files (fn-own-store o9)))
                       (append (fn-sf-successes (fn-sn-files s)) (list pair)))
                (member-equal r (fn-sf-records (fn-sn-files (fn-own-store o9))))
                (equal (fn-served-reply-octets (car out))
                       (fn-pct-inbound-success-octets (fn-own-sub-decision sub))))))
 :rule-classes nil
 :hints (("Goal"
          :use ((:instance fn-pct-transit-submission-nonempty
                           (sub (fn-own-inflight (fn-ocfg-owner oc))))
                (:instance fn-pcx-post-productive (o (fn-ocfg-owner oc)))
                (:instance fn-pcx-own-run-store (o (fn-ocfg-owner oc)))
                (:instance fn-pcx-post-run-is-complete-of-store-run
                           (o (fn-ocfg-owner oc)) (p (list :prepare r)))
                (:instance fn-own-complete-keeps-every-connection
                 (o (fn-own-run (fn-ocfg-owner oc)
                      (fn-pcx-wrap-store (fn-pcx-store-script (list :prepare r))) fn-arena)))
                (:instance fn-pct-consumed-transit-host-outcome-has-success-octets
                 (oc (fn-ocfg-with-owner oc
                      (fn-own-run (fn-ocfg-owner oc)
                       (fn-pcx-post-script (list :prepare r)) fn-arena)))))
          :in-theory (union-theories
                       '(fn-ocfg-owner fn-ocfg-with-owner fn-ocfg-make
                         car-cons cdr-cons)
                       (theory 'minimal-theory)))))
