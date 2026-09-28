; fn: the served owner's records are the history image followed by the
; log suffix (lane arena-store-5, 2026-09-28, m3c P1's link).  Prefix fn-hpo-.
;
; books/history-pages-view.lisp answers record I of the history the image
; holds (H, length N) followed by an in-memory SUFFIX (KEYSTONE
; fn-hp-records-at-is-nth) and leaves one link open: that the store the host
; keeps has (fn-sf-records s) = (append H SUFFIX).  This book is that link
; for the owner the host installs from a checkpoint.
;
; The host's open (host/store-node-host.lisp fn-store-sn-recover-from-checkpoint)
; calls `fn-rii-sco-extend-open' over the checkpoint C and the log's rows
; after it, and the owner (host/owner-host.lisp fn-owner-recover-from-store-open)
; installs with `fn-ock-install' over the pair that open answered.
; KEYSTONE fn-hpo-installed-records-are-checkpoint-then-suffix: whenever the
; install does not refuse, the installed owner's store holds exactly C's
; records followed by the suffix.  So an image written from C's records
; (H = (fn-sco-records C)) answers the installed owner's records through
; `fn-hp-records-at' with the suffix the open replayed
; (KEYSTONE fn-hpo-records-at-is-installed-nth), and, as the served owner's
; records only grow by extension, with the suffix since H for every later
; store whose records extend H (fn-hpo-records-at-is-nth-of-extension; the
; owner's steps extend: owner-invariants-served fn-own-run-records-prefix).
;
; The cycle closes at the snapshot: appending the records since H to the
; image (`fn-hp-x-append-all', what the host calls) leaves the image of
; exactly the records the next checkpoint holds (`fn-ock-next-checkpoint',
; the publication's; KEYSTONE fn-hpo-snapshot-image-is-next-checkpoint),
; so the open's hypothesis -- the image holds C's records -- is what the
; previous snapshot established.  Scope: the image and the checkpoint are
; two durable writes; that the pair the open reads is one snapshot's is the
; host's to establish (the header's N against the checkpoint's sequence),
; stated here as the hypothesis H = (fn-sco-records C).
(in-package "ACL2")
(include-book "owner-checkpoint-open")
(include-book "replay-identity-index")
(include-book "history-pages-view")
(include-book "history-pages-import")

(local
 (defthm fn-hpo-finalize-records
  (implies (equal (fn-sn-open-kind (fn-sco-finalize e configs frontier)) :ok)
           (equal (fn-sf-records (fn-sn-files (fn-sn-open-state (fn-sco-finalize e configs frontier))))
                  (fn-sco-records e)))
  :hints (("Goal" :in-theory (e/d (fn-sco-finalize fn-sn-open-ok fn-sn-open-error fn-sn-open-kind fn-sn-open-state
                                   fn-sn-with-event-index fn-sn-with-topic fn-sn-with-consumer fn-cpo-install
                                   fn-sn-with-configuration fn-sn-update-replayed fn-sn-files fn-sn-make-v6
                                   fn-sf-records fn-sf-records-field fn-sf-make fn-sf-make-fields)
                                  (fn-sn-statep fn-sco-cpr-finish fn-cnode-statep fn-replay-advance-okp
                                   fn-sn-observed-historyp fn-sn-observed-seed fn-replay-advance-txid
                                   fn-stxk-context-kind fn-th-at fn-sl-of fn-sl-list))))))

(local
 (defthm fn-hpo-own-start-store
  (equal (fn-own-store (fn-own-start store max-conns)) store)
  :hints (("Goal" :in-theory (e/d (fn-own-start fn-own-refresh)
                                  (fn-own-store-idlep fn-ctl-refresh-visible fn-ctl-refresh-withdrawals
                                   fn-ctl-refresh-withdrawn fn-midx-refresh fn-gidx-refresh
                                   fn-own-prefix-archive fn-ctl-visible-state fn-midx-build fn-gidx-build
                                   fn-ctl-subseq-diff fn-ctl-visible-state-of))))))
(defthm fn-hpo-ock-install-store
  (implies (not (equal (fn-ock-install replayed opened max-conns) :fault))
           (and (equal (fn-own-store (fn-ocfg-owner (fn-ock-install replayed opened max-conns)))
                       (fn-sn-open-state opened))
                (equal (fn-sn-open-kind opened) :ok)))
  :hints (("Goal" :in-theory (e/d (fn-ock-install) (fn-own-start fn-own-configure)))))

(defthm fn-hpo-classified-open-records
  (let ((r (fn-rii-classified-open e configs frontier)))
    (implies (equal (fn-sn-open-kind (cadr r)) :ok)
             (equal (fn-sf-records (fn-sn-files (fn-sn-open-state (cadr r))))
                    (fn-sco-records e))))
  :hints (("Goal" :in-theory (e/d (fn-rii-classified-open-is-classified-open fn-sopc-classified-open
                                   fn-sopc-open-refusal fn-sco-store-open fn-sn-open-kind)
                                  (fn-rii-classified-open fn-sco-finalize fn-sco-cpr-finish
                                   fn-sopc-pre-c1-control-record-p fn-store-event-sequence)))))
(defthm fn-hpo-sco-records-of-extend
  (equal (fn-sco-records (fn-sco-extend c configs suffix))
         (append (true-list-fix (fn-sco-records c)) suffix))
  :hints (("Goal" :in-theory (e/d (fn-sco-extend fn-sco-make fn-sco-records)
                                  (fn-sco-cpr-resume fn-replay-identity-loop fn-sco-consumer-resume
                                   fn-th-prefix-loop fn-cei-build-aux)))))
(defthm fn-hpo-installed-records-are-checkpoint-then-suffix
  (let* ((pair (fn-rii-sco-extend-open c configs suffix frontier))
         (oc (fn-ock-install (car (cadr pair)) (cadr (cadr pair)) max-conns)))
    (implies (not (equal oc :fault))
             (equal (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
                    (append (true-list-fix (fn-sco-records c)) suffix))))
  :hints (("Goal" :in-theory (union-theories '(fn-rii-sco-extend-open-is-extend-then-open fn-rii-sco-extend-is-sco-extend
                                               fn-hpo-sco-records-of-extend car-cons cdr-cons)
                                             (theory 'minimal-theory))
           :use ((:instance fn-hpo-ock-install-store
                            (replayed (car (fn-rii-classified-open (fn-sco-extend c configs suffix) configs frontier)))
                            (opened (cadr (fn-rii-classified-open (fn-sco-extend c configs suffix) configs frontier))))
                 (:instance fn-hpo-classified-open-records (e (fn-sco-extend c configs suffix)))))))

(defthm fn-hpo-events-okp-true-listp
  (implies (fn-hp-events-okp h) (true-listp h))
  :rule-classes :forward-chaining
  :hints (("Goal" :induct (true-listp h) :in-theory (union-theories '(fn-hp-events-okp true-listp) (theory 'minimal-theory)))))
(defthm fn-hpo-okp-true-listp
  (implies (fn-hp-okp h salt) (true-listp h))
  :rule-classes :forward-chaining
  :hints (("Goal" :use fn-hpo-events-okp-true-listp
           :in-theory (union-theories '(fn-hp-okp) (theory 'minimal-theory)))))
(local (defthm fn-hpo-len-append (equal (len (append a b)) (+ (len a) (len b)))))
(local (defthm fn-hpo-tlf-id (implies (true-listp x) (equal (true-list-fix x) x))))
(defthm fn-hpo-records-at-is-installed-nth
  (let* ((pair (fn-rii-sco-extend-open c configs suffix frontier))
         (oc (fn-ock-install (car (cadr pair)) (cadr (cadr pair)) max-conns))
         (records (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
         (h (fn-sco-records c))
         (res (fn-hp-records-at i n suffix salt lens starts pgs-mem)))
    (implies (and (not (equal oc :fault))
                  (fn-hp-okp h salt) (equal n (len h)) (equal lens (fn-hp-lens h salt))
                  (fn-hp-starts-okp starts) (adt-placement-ok starts lens np)
                  (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np))
                  (natp i))
             (and (implies (and (< i (len records)) (equal (mv-nth 0 res) :ok))
                           (equal (mv-nth 1 res) (list :ok (nth i records))))
                  (implies (< i (len records))
                           (or (equal (mv-nth 0 res) :ok) (fn-hp-need-verdictp (mv-nth 0 res))))
                  (implies (not (< i (len records)))
                           (and (equal (mv-nth 0 res) :ok) (equal (mv-nth 1 res) '(:refused :seq)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-hpo-installed-records-are-checkpoint-then-suffix
                 (:instance fn-hp-records-at-is-nth (h (fn-sco-records c))))
           :in-theory (union-theories '(fn-hpo-len-append fn-hpo-tlf-id fn-hpo-okp-true-listp) (theory 'minimal-theory)))))

(local
 (defthm fn-hpo-append-nthcdr-of-prefix
   (implies (fn-sf-prefixp h r)
            (equal (append h (nthcdr (len h) r)) r))
   :hints (("Goal" :induct (fn-sf-prefixp h r) :in-theory (enable fn-sf-prefixp nthcdr)))))
(defthm fn-hpo-records-at-is-nth-of-extension
  (let ((res (fn-hp-records-at i (len h) (nthcdr (len h) r) salt lens starts pgs-mem)))
    (implies (and (fn-sf-prefixp h r)
                  (fn-hp-okp h salt) (equal lens (fn-hp-lens h salt))
                  (fn-hp-starts-okp starts) (adt-placement-ok starts lens np)
                  (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np))
                  (natp i))
             (and (implies (and (< i (len r)) (equal (mv-nth 0 res) :ok))
                           (equal (mv-nth 1 res) (list :ok (nth i r))))
                  (implies (< i (len r))
                           (or (equal (mv-nth 0 res) :ok) (fn-hp-need-verdictp (mv-nth 0 res))))
                  (implies (not (< i (len r)))
                           (and (equal (mv-nth 0 res) :ok) (equal (mv-nth 1 res) '(:refused :seq)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-hpo-append-nthcdr-of-prefix
                 (:instance fn-hp-records-at-is-nth (n (len h)) (suffix (nthcdr (len h) r))))
           :in-theory (union-theories '(fn-hpo-len-append) (theory 'minimal-theory)))))

(local
 (defthm fn-hpo-ock-prefixp-splits
   (implies (and (fn-ock-prefixp p r) (true-listp p))
            (equal (append p (nthcdr (len p) r)) r))
   :hints (("Goal" :induct (fn-ock-prefixp p r)))))
(local
 (defthm fn-hpo-true-listp-nthcdr
   (implies (true-listp r) (true-listp (nthcdr n r)))))
(local
 (defthm fn-hpo-take-len
   (implies (true-listp x) (equal (take (len x) x) x))))
(defthm fn-hpo-snapshot-image-is-next-checkpoint
  (let* ((h (fn-sco-records base))
         (evs (nthcdr (len h) r))
         (res (fn-hp-x-append-all evs 0 salt (len h) lens starts np pgs-mem))
         (next (fn-ock-next-checkpoint base configs r)))
    (implies (and (true-listp r) (fn-ock-prefixp h r)
                  (fn-hp-okp h salt) (equal lens (fn-hp-lens h salt))
                  (fn-hp-starts-okp starts)
                  (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np))
                  (equal (mv-nth 0 res) :ok))
             (and (equal (fn-sco-records next) r)
                  (fn-hp-okp r salt)
                  (equal (mv-nth 2 res) (len r))
                  (equal (mv-nth 3 res) (fn-hp-lens r salt))
                  (fn-hp-starts-okp (mv-nth 4 res))
                  (fn-hp-vhold 0 (pgs-v-length (mv-nth 6 res)) (mv-nth 6 res)
                               (fn-hp-piw r salt (mv-nth 4 res) (mv-nth 5 res))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-append-all-refines (h (fn-sco-records base)) (n (len (fn-sco-records base)))
                            (evs (nthcdr (len (fn-sco-records base)) r)))
                 (:instance fn-hpo-ock-prefixp-splits (p (fn-sco-records base))))
           :in-theory (union-theories '(fn-ock-next-checkpoint fn-hpo-sco-records-of-extend fn-hpo-take-len
                                        fn-hpo-tlf-id fn-hpo-okp-true-listp fn-hpo-true-listp-nthcdr)
                                      (theory 'minimal-theory)))))
