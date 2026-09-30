; S9 counted durable outcomes. Each served variant executes one target fold
; and carries its aggregate alongside the exact prior effects/owner projection.
(in-package "ACL2")
(include-book "owner-outcome-pinned")
(include-book "owner-feed-live-carried")

(defun fn-oct-durable (o sub pending)
  (declare (xargs :guard (and (acl2-numberp pending)
                              (fn-own-feed-tablep (fn-own-feeds o))
                              (fn-ofct-table-relationp (fn-own-feeds o)))
                  :verify-guards nil))
  (fn-own-feed-enqueue-all-counted-carried
   (fn-own-submission-targets o) (fn-own-feeds o)
   (fn-own-sub-msgid sub) (fn-own-feed-stamp o) pending))

(defun fn-oct-outcome-next (o id sub completion icar carry feeds)
  (declare (xargs :guard t) (ignore sub completion icar carry))
  (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
               (fn-own-next-id o) (fn-own-max-conns o)
               (if (equal (fn-own-pending o) id) nil (fn-own-pending o))
               (fn-own-ledger-field o) (fn-own-clock o) (fn-own-facts o)
               (fn-own-config o) (fn-own-queue o) nil
               feeds
               (fn-own-node-secret o) (fn-own-refused o)))

(defun fn-oct-outcome (oc id word icar carry pending)
  (declare (xargs :guard (and (acl2-numberp pending)
                              (fn-own-feed-tablep (fn-own-feeds (fn-ocfg-owner oc)))
                              (fn-ofct-table-relationp (fn-own-feeds (fn-ocfg-owner oc))))
                  :verify-guards nil))
  (let* ((o (fn-ocfg-owner oc))
         (conn (fn-own-find-conn id (fn-own-conns o)))
         (sub (fn-own-inflight o)))
    (if (and conn sub (equal (fn-own-sub-id sub) id))
        (let* ((completion (fn-own-outcome-completion o word))
               (counted (if (equal completion :durable)
                            (fn-own-feed-enqueue-all-counted-carried
                         (fn-apc-submission-targets o icar carry)
                         (fn-own-feeds o) (fn-own-sub-msgid sub)
                         (fn-own-feed-stamp o) pending)
                          (cons (fn-own-feeds o) pending)))
               (oc2 (fn-ocfg-with-owner
                     oc (fn-oct-outcome-next o id sub completion icar carry (car counted)))))
          (cons (cons (fn-served-result-effects
                 (fn-served-post-outcome
                  (fn-served-make-conn-group-indexed (fn-own-conn-wire conn)
                                       (fn-own-conn-session conn)
                                       (fn-own-conn-archive conn)
                                       (fn-own-conn-config conn)
                                       (fn-own-conn-observation conn)
                                       (fn-own-clock o)
                                       (fn-own-conn-verdicts conn)
                                       (fn-own-conn-index conn)
                                       (fn-own-conn-group-index conn)
                                       (fn-own-conn-control conn))
                  (fn-own-post-rendering o word)))
                (if (equal completion :durable)
                    (fn-oop-advance oc2 id)
                  oc2)) (cdr counted)))
      (cons (cons nil oc) pending))))

(defun fn-oct-transit-next (o id conn sub completion kind reason feeds)
  (declare (xargs :guard t) (ignore completion))
  (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
               (fn-own-next-id o) (fn-own-max-conns o)
               (if (equal (fn-own-pending o) id) nil (fn-own-pending o))
               (fn-own-ledger-field o) (fn-own-clock o) (fn-own-facts o)
               (fn-own-config o) (fn-own-queue o) nil
               feeds
               (fn-own-node-secret o)
               (fn-own-transit-refused o conn sub kind reason)))

(defun fn-oct-transit (oc id kind reason word pending)
  (declare (xargs :guard (and (acl2-numberp pending)
                              (fn-own-feed-tablep (fn-own-feeds (fn-ocfg-owner oc)))
                              (fn-ofct-table-relationp (fn-own-feeds (fn-ocfg-owner oc))))
                  :verify-guards nil))
  (let* ((o (fn-ocfg-owner oc))
         (conn (fn-own-find-conn id (fn-own-conns o)))
         (sub (fn-own-inflight o)))
    (if (and conn sub (equal (fn-own-sub-id sub) id) (fn-own-transit-subp sub))
        (let* ((d (fn-peer-decision kind reason))
               (completion (if (equal kind :want)
                               (fn-own-outcome-completion o word)
                             nil))
               (counted (if (equal completion :durable)
                            (fn-oct-durable o sub pending)
                          (cons (fn-own-feeds o) pending)))
               (oc2 (fn-ocfg-with-owner
                     oc (fn-oct-transit-next o id conn sub completion kind reason (car counted)))))
          (cons (cons (fn-served-result-effects
                 (fn-served-transit-outcome
                  (fn-served-make-conn-group-indexed (fn-own-conn-wire conn)
                                       (fn-own-conn-session conn)
                                       (fn-own-conn-archive conn)
                                       (fn-own-conn-config conn)
                                       (fn-own-conn-observation conn)
                                       (fn-own-clock o)
                                       (fn-own-conn-verdicts conn)
                                       (fn-own-conn-index conn)
                                       (fn-own-conn-group-index conn)
                                       (fn-own-conn-control conn))
                  (fn-own-sub-decision sub) d
                  (if (equal kind :want) (fn-own-outcome-rendering o word) nil)))
                (if (equal completion :durable)
                    (fn-ocfg-advance oc2 id)
                  oc2)) (cdr counted)))
      (cons (cons nil oc) pending))))

(defun fn-oct-control (o word pending)
  (declare (xargs :guard (and (acl2-numberp pending)
                              (fn-own-feed-tablep (fn-own-feeds o))
                              (fn-ofct-table-relationp (fn-own-feeds o)))
                  :verify-guards nil))
  (let ((sub (fn-own-inflight o)))
    (if (not (fn-own-control-submissionp sub))
        (cons o pending)
      (let* ((completion (fn-own-outcome-completion o word))
             (counted (if (equal completion :durable)
                          (fn-oct-durable o sub pending)
                        (cons (fn-own-feeds o) pending))))
        (cons (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                     (fn-own-next-id o) (fn-own-max-conns o)
                     (if (equal (fn-own-pending o) *fn-own-control-id*)
                         nil (fn-own-pending o))
                     (fn-own-ledger-field o) (fn-own-clock o) (fn-own-facts o)
                     (fn-own-config o) (fn-own-queue o) nil
                     (car counted) (fn-own-node-secret o) (fn-own-refused o)) (cdr counted))))))

(defun fn-oct-bp-transit (o word pending)
  (declare (xargs :guard (and (acl2-numberp pending)
                              (fn-own-feed-tablep (fn-own-feeds o))
                              (fn-ofct-table-relationp (fn-own-feeds o)))
                  :verify-guards nil))
  (if (fn-own-bp-transit-submissionp (fn-own-inflight o))
      (fn-oct-control o word pending)
    (cons o pending)))

(verify-guards fn-oct-durable)
(verify-guards fn-oct-outcome)
(verify-guards fn-oct-transit)
(verify-guards fn-oct-control)
(verify-guards fn-oct-bp-transit)

(defthm fn-oct-outcome-has-the-original-result
  (equal (car (fn-oct-outcome oc id word icar carry pending))
         (fn-oop-outcome oc id word icar carry))
  :hints (("Goal" :in-theory
           (e/d (fn-oct-outcome fn-oct-outcome-next
                 fn-oop-outcome fn-oop-outcome-next)
                (fn-own-make fn-own-outcome-completion
                 fn-apc-submission-targets fn-own-feed-stamp
                 fn-own-feed-enqueue-all fn-own-feed-enqueue-all-counted
                 fn-oop-advance fn-ocfg-with-owner fn-served-result-effects
                 fn-served-post-outcome fn-served-make-conn-group-indexed
                 fn-own-post-rendering)))))

(defthm fn-oct-transit-has-the-original-result
  (equal (car (fn-oct-transit oc id kind reason word pending))
         (fn-oop-transit-outcome oc id kind reason word))
  :hints (("Goal" :in-theory
           (e/d (fn-oct-transit fn-oct-transit-next fn-oct-durable
                 fn-oop-transit-outcome fn-oop-transit-next fn-own-feed-durable)
                (fn-own-make fn-own-outcome-completion fn-own-transit-subp
                 fn-own-submission-targets fn-own-feed-stamp fn-own-transit-refused
                 fn-own-feed-enqueue-all fn-own-feed-enqueue-all-counted
                 fn-ocfg-advance fn-ocfg-with-owner fn-served-result-effects
                 fn-served-transit-outcome fn-served-make-conn-group-indexed
                 fn-own-outcome-rendering fn-peer-decision)))))

(defthm fn-oct-control-has-the-original-owner
  (equal (car (fn-oct-control o word pending)) (fn-own-control-outcome o word))
  :hints (("Goal" :in-theory
           (e/d (fn-oct-control fn-oct-durable fn-own-control-outcome
                 fn-own-feed-durable)
                (fn-own-make fn-own-outcome-completion fn-own-control-submissionp
                 fn-own-submission-targets fn-own-feed-stamp
                 fn-own-feed-enqueue-all fn-own-feed-enqueue-all-counted)))))

(defthm fn-oct-bp-transit-has-the-original-owner
  (equal (car (fn-oct-bp-transit o word pending))
         (fn-own-bp-transit-outcome o word))
  :hints (("Goal" :in-theory
           (e/d (fn-oct-bp-transit fn-own-bp-transit-outcome)
                (fn-oct-control fn-own-control-outcome
                 fn-own-bp-transit-submissionp)))))

 ; The actual configured control/BP event is the owner projection above.
; These unfold dispatcher branches, not independent keystones.
(defthm fn-oct-control-is-actual-configured-step-unfolds
  (equal (fn-ocfg-with-owner oc (car (fn-oct-control (fn-ocfg-owner oc) word pending)))
         (fn-ocfg-step oc (list :control-outcome word) fn-arena))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ocfg-step fn-ocfg-pass fn-own-step)
                                  (fn-oct-control fn-own-control-outcome fn-ocfg-with-owner)))))

(defthm fn-oct-bp-transit-is-actual-configured-step-unfolds
  (equal (fn-ocfg-with-owner oc (car (fn-oct-bp-transit (fn-ocfg-owner oc) word pending)))
         (fn-ocfg-step oc (list :bp-transit-outcome word) fn-arena))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ocfg-step fn-ocfg-pass fn-own-step)
                                  (fn-oct-bp-transit fn-own-bp-transit-outcome fn-ocfg-with-owner)))))


(local
 (defthm fn-oct-set-conns-keeps-feeds
   (equal (fn-own-feeds (fn-own-set-conns o conns)) (fn-own-feeds o))
   :hints (("Goal" :in-theory (e/d (fn-own-set-conns) (fn-own-make))))))

(local
 (defthm fn-oct-acar-advance-keeps-feeds
   (equal (fn-own-feeds (cdr (fn-acar-own-advance-result o id))) (fn-own-feeds o))
   :hints (("Goal" :in-theory (e/d (fn-acar-own-advance-result)
                                  (fn-own-set-conns fn-own-find-conn fn-own-replace-conn
                                   fn-own-conn-make-group-indexed fn-auth-with-base
                                   fn-peer-with-base fn-post-make-session fn-nntp-set-cursor
                                   fn-scar-conn-boundedp fn-acar-open-session))))))

(local
 (defthm fn-oct-reference-advance-keeps-feeds
   (equal (fn-own-feeds (cdr (fn-own-advance-result o id))) (fn-own-feeds o))
   :hints (("Goal" :in-theory (e/d (fn-own-advance-result)
                                  (fn-own-set-conns fn-own-find-conn fn-own-replace-conn
                                   fn-own-conn-make-group-indexed fn-auth-with-base
                                   fn-peer-with-base fn-post-make-session fn-nntp-set-cursor
                                   fn-own-conn-boundedp fn-nntp-open-session))))))

(local
 (defthm fn-oct-oop-advance-keeps-feeds
   (equal (fn-own-feeds (fn-ocfg-owner (fn-oop-advance oc id)))
          (fn-own-feeds (fn-ocfg-owner oc)))
   :hints (("Goal" :in-theory (e/d (fn-oop-advance)
                                  (fn-acar-own-advance-result fn-ocfg-make
                                   fn-ocfg-owner fn-own-feeds))))))

(local
 (defthm fn-oct-ocfg-advance-keeps-feeds
   (equal (fn-own-feeds (fn-ocfg-owner (fn-ocfg-advance oc id)))
          (fn-own-feeds (fn-ocfg-owner oc)))
   :hints (("Goal" :in-theory (e/d (fn-ocfg-advance)
                                  (fn-own-advance-result fn-ocfg-make
                                   fn-ocfg-owner fn-own-feeds))))))

(defthm fn-oct-control-preserves-aggregate
  (implies (equal pending (fn-own-feed-table-pending-model (fn-own-feeds o)))
           (equal (cdr (fn-oct-control o word pending))
                  (fn-own-feed-table-pending-model
                   (fn-own-feeds (car (fn-oct-control o word pending))))))
  :hints (("Goal" :in-theory
           (e/d (fn-oct-control fn-oct-durable)
                (fn-own-make fn-own-control-outcome fn-oct-control-has-the-original-owner
                 fn-ofct-enqueue-all-counted-has-the-original-table fn-own-feed-enqueue-all-counted
                 fn-own-feed-table-pending-model fn-own-feed-enqueue-all
                 fn-own-feeds fn-own-submission-targets fn-own-feed-stamp)))))

(defthm fn-oct-bp-transit-preserves-aggregate
  (implies (equal pending (fn-own-feed-table-pending-model (fn-own-feeds o)))
           (equal (cdr (fn-oct-bp-transit o word pending))
                  (fn-own-feed-table-pending-model
                   (fn-own-feeds (car (fn-oct-bp-transit o word pending))))))
  :hints (("Goal" :in-theory (e/d (fn-oct-bp-transit)
                                  (fn-oct-control fn-own-bp-transit-outcome fn-oct-bp-transit-has-the-original-owner
                                   fn-own-feed-table-pending-model fn-own-feeds)))))

(defthm fn-oct-outcome-preserves-aggregate
  (implies (equal pending (fn-own-feed-table-pending-model (fn-own-feeds (fn-ocfg-owner oc))))
           (equal (cdr (fn-oct-outcome oc id word icar carry pending))
                  (fn-own-feed-table-pending-model
                   (fn-own-feeds (fn-ocfg-owner
                                 (cdr (car (fn-oct-outcome oc id word icar carry pending))))))))
  :hints (("Goal" :in-theory
           (e/d (fn-oct-outcome fn-oct-outcome-next fn-ocfg-with-owner)
                (fn-own-make fn-oop-outcome fn-oct-outcome-has-the-original-result
                 fn-ofct-enqueue-all-counted-has-the-original-table fn-oop-advance
                 fn-own-feed-table-pending-model fn-own-feed-enqueue-all-counted
                 fn-own-feeds fn-ocfg-owner fn-apc-submission-targets fn-own-feed-stamp)))))

(defthm fn-oct-transit-preserves-aggregate
  (implies (equal pending (fn-own-feed-table-pending-model (fn-own-feeds (fn-ocfg-owner oc))))
           (equal (cdr (fn-oct-transit oc id kind reason word pending))
                  (fn-own-feed-table-pending-model
                   (fn-own-feeds (fn-ocfg-owner
                                 (cdr (car (fn-oct-transit oc id kind reason word pending))))))))
  :hints (("Goal" :in-theory
           (e/d (fn-oct-transit fn-oct-transit-next fn-oct-durable fn-ocfg-with-owner)
                (fn-own-make fn-oop-transit-outcome fn-oct-transit-has-the-original-result
                 fn-ofct-enqueue-all-counted-has-the-original-table fn-ocfg-advance
                 fn-own-feed-table-pending-model fn-own-feed-enqueue-all-counted
                 fn-own-feeds fn-ocfg-owner fn-own-submission-targets fn-own-feed-stamp)))))

(defthm fn-oct-control-preserves-table-count-relation
  (implies (fn-ofct-table-relationp (fn-own-feeds o))
           (fn-ofct-table-relationp (fn-own-feeds (car (fn-oct-control o word pending)))))
  :hints (("Goal" :in-theory
           (e/d (fn-oct-control fn-oct-durable)
                (fn-oct-control-has-the-original-owner fn-own-control-outcome fn-own-make fn-own-feeds fn-ocfg-owner
                 fn-own-feed-enqueue-all-counted fn-own-feed-enqueue-all
                 fn-ofct-enqueue-all-counted-has-the-original-table
                 fn-ofct-table-relationp fn-own-feed-stamp
                 fn-apc-submission-targets fn-own-submission-targets)))))

(defthm fn-oct-bp-transit-preserves-table-count-relation
  (implies (fn-ofct-table-relationp (fn-own-feeds o))
           (fn-ofct-table-relationp (fn-own-feeds (car (fn-oct-bp-transit o word pending)))))
  :hints (("Goal" :in-theory
           (e/d (fn-oct-bp-transit)
                (fn-oct-bp-transit-has-the-original-owner fn-oct-control-has-the-original-owner
                 fn-oct-control fn-own-bp-transit-outcome fn-own-make fn-own-feeds fn-ocfg-owner
                 fn-own-feed-enqueue-all-counted fn-own-feed-enqueue-all
                 fn-ofct-enqueue-all-counted-has-the-original-table
                 fn-ofct-table-relationp fn-own-feed-stamp
                 fn-apc-submission-targets fn-own-submission-targets)))))

(defthm fn-oct-outcome-preserves-table-count-relation
  (implies (fn-ofct-table-relationp (fn-own-feeds (fn-ocfg-owner oc)))
           (fn-ofct-table-relationp (fn-own-feeds (fn-ocfg-owner (cdr (car (fn-oct-outcome oc id word icar carry pending)))))))
  :hints (("Goal" :in-theory
           (e/d (fn-oct-outcome fn-oct-outcome-next fn-ocfg-with-owner)
                (fn-oct-outcome-has-the-original-result fn-oop-outcome fn-oop-advance fn-own-make fn-own-feeds fn-ocfg-owner
                 fn-own-feed-enqueue-all-counted fn-own-feed-enqueue-all
                 fn-ofct-enqueue-all-counted-has-the-original-table
                 fn-ofct-table-relationp fn-own-feed-stamp
                 fn-apc-submission-targets fn-own-submission-targets)))))

(defthm fn-oct-transit-preserves-table-count-relation
  (implies (fn-ofct-table-relationp (fn-own-feeds (fn-ocfg-owner oc)))
           (fn-ofct-table-relationp (fn-own-feeds (fn-ocfg-owner (cdr (car (fn-oct-transit oc id kind reason word pending)))))))
  :hints (("Goal" :in-theory
           (e/d (fn-oct-transit fn-oct-transit-next fn-oct-durable fn-ocfg-with-owner)
                (fn-oct-transit-has-the-original-result fn-oop-transit-outcome fn-ocfg-advance fn-own-make fn-own-feeds fn-ocfg-owner
                 fn-own-feed-enqueue-all-counted fn-own-feed-enqueue-all
                 fn-ofct-enqueue-all-counted-has-the-original-table
                 fn-ofct-table-relationp fn-own-feed-stamp
                 fn-apc-submission-targets fn-own-submission-targets)))))

(in-theory (disable fn-oct-durable fn-oct-outcome-next fn-oct-outcome
                    fn-oct-transit-next fn-oct-transit fn-oct-control
                    fn-oct-bp-transit))
