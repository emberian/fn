; BP checkpoint disk ownership in the shared maintenance pool. This algebra
; is not an initial runtime envelope or a standalone profile installation.
; The physical caller serializes the actual publish observation, this transfer
; and installed-incarnation registration before any reusable release.
(in-package "ACL2")
(include-book "bp-node-checkpoint-job")
(include-book "page-maintenance-lease")
(set-verify-guards-eagerness 0)

(defun fn-bpck-installed-key (token)
  (declare (xargs :guard t))
  (list :bp-checkpoint-installed token))

; Keep the installed disk claim separately after the action token is released.
; A distinct row kind also prevents generic grow from clearing the transfer
; receipt and authorizing a duplicate transfer. Spent IDs are never refunded.
(defun fn-bpck-publish-transfer (ledger job control source aliases fd)
  (declare (xargs :guard t))
  (let* ((token (fn-bpn-nth 1 job))
         (bindings (fn-prl-nth 3 ledger))
         (entry (fn-prl-binding token bindings))
         (row (if (consp entry) (cdr entry) nil))
         (demand (fn-prl-nth 0 row))
         (charged (fn-prl-nth 1 ledger))
         (baseline (fn-prl-baseline ledger))
         (key (fn-bpck-installed-key token))
         (disk (list 0 (+ 46 (nfix (fn-bpn-nth 8 job))) 0 0 0)))
    (cond
     ((fn-prl-nth 3 row) (mv :foreign-initial-custody ledger))
     ((not (and (equal (fn-bpn-nth 11 job) :published)
                (equal control '(:done :written))
                (equal source :returned) (equal aliases :relinquished)
                (equal fd :closed))) (mv :pending ledger))
     ((not (and (equal (fn-prl-nth 0 token) :maintenance)
                (equal (fn-prl-nth 1 row) :maintenance)
                (equal (fn-prl-nth 2 token) (fn-bpn-nth 2 job))
                (posp (fn-bpn-nth 8 job))
                (not (fn-prl-binding key bindings)))) (mv :stale ledger))
     ((not (and (fn-prs-vectorp charged) (fn-prs-vectorp demand)
                (fn-prs-vectorp baseline)
                (fn-prs-below disk demand) (fn-prs-below disk charged)))
      (mv :invalid-transfer ledger))
     (t
      (let* ((charged1 (fn-prs-release-reusable charged disk))
             (baseline1 (fn-prs-plus baseline disk))
             (remaining (fn-prs-release-reusable demand disk)))
        (if (not (fn-prs-fundedp (fn-prl-nth 0 ledger) baseline1
                                 '(0 0 0 0 0) charged1))
            (mv :invalid-transfer ledger)
          (mv :transferred
              (fn-prl-build
               (fn-prl-nth 0 ledger) charged1 (fn-prl-nth 2 ledger)
               (cons (cons key (list disk :bp-checkpoint-installed
                                    (fn-bpn-nth 3 job)))
                     (cons (cons token (list remaining :bp-maintenance-published key))
                           (fn-prl-remove token bindings)))
               baseline1))))))))

; The installed disk row is retained. This releases only the actual action's
; remaining reusable credit; uncertainty and a missing transfer retain all C.
(defun fn-bpck-release-action (ledger job control source aliases fd)
  (declare (xargs :guard t))
  (let* ((token (fn-bpn-nth 1 job))
         (entry (fn-prl-binding token (fn-prl-nth 3 ledger)))
         (row (if (consp entry) (cdr entry) nil))
         (key (fn-bpck-installed-key token))
         (installed (fn-prl-binding key (fn-prl-nth 3 ledger)))
         (transferred (and (equal (fn-prl-nth 1 row) :bp-maintenance-published)
                           (equal (fn-prl-nth 2 row) key)
                           (equal (fn-prl-nth 1 (cdr installed))
                                  :bp-checkpoint-installed)))
         (word (fn-bpck-cleanup-word job source aliases fd
                                     (if transferred :transferred :pending))))
    (cond
     ((fn-prl-nth 3 row) (mv :foreign-initial-custody ledger))
     ((not (equal (fn-prl-nth 0 control) :done)) (mv :pending ledger))
     ((not (equal word :release)) (mv word ledger))
     ((not transferred) (fn-pmn-release ledger token))
     ((not (and (equal (fn-bpn-nth 11 job) :published)
                (fn-prs-vectorp (fn-prl-nth 1 ledger))
                (fn-prs-vectorp (fn-prl-nth 0 row)))) (mv :stale ledger))
     (t (mv :released
            (fn-prl-build
             (fn-prl-nth 0 ledger)
             (fn-prs-release-reusable (fn-prl-nth 1 ledger) (fn-prl-nth 0 row))
             (fn-prl-nth 2 ledger)
             (fn-prl-remove token (fn-prl-nth 3 ledger))
             (fn-prl-nth 4 ledger)))))))

(local
 (defthm fn-bpck-resource-nats-are-proper
   (implies (fn-prs-nats-p x) (true-listp x))
   :hints (("Goal" :induct (fn-prs-nats-p x)
            :in-theory (enable fn-prs-nats-p)))))

(local
 (defthm fn-bpck-resource-vector-is-proper
   (implies (fn-prs-vectorp x) (true-listp x))
   :hints (("Goal" :in-theory (enable fn-prs-vectorp)
            :use ((:instance fn-bpck-resource-nats-are-proper))))))

(verify-guards fn-bpck-installed-key)
(verify-guards fn-bpck-publish-transfer
  :hints (("Goal" :in-theory (enable fn-prs-vectorp))))
(verify-guards fn-bpck-release-action
  :hints (("Goal" :in-theory (enable fn-prs-vectorp))))

(local (defthm fn-bpck-built-ledger-next-by-definition
 (equal (fn-prl-nth 2 (fn-prl-build budget charged next bindings baseline)) next)
 :hints (("Goal" :in-theory (enable fn-prl-build fn-prl-nth)))))

(defthm fn-bpck-publish-transfer-never-reuses-identity
  (equal (fn-prl-nth 2 (mv-nth 1 (fn-bpck-publish-transfer ledger job control source aliases fd)))
         (fn-prl-nth 2 ledger))
  :hints (("Goal" :in-theory (union-theories
    '(fn-bpck-publish-transfer fn-bpck-built-ledger-next-by-definition)
    (theory 'minimal-theory)))))

(in-theory (disable fn-bpck-installed-key fn-bpck-publish-transfer
                    fn-bpck-release-action))
