; The reclaim-aware history invariant (books/filed-history.lisp
; FN-O1-FILES-INVP) carried through the owner's lifecycle beyond the Store
; transitions: the arena's release of handles no row names (K2), the fresh
; handle of an intern then stage (K3, K3a, K3b), the content-reclaim swap,
; which rewrites payloads to tombstones and keeps groups (K4), reopen from the
; full journal and from a checkpoint (K5a, K5b), the journal a live history
; writes (K5c), and the catalog every install loads (K6, K7).  Each keystone
; premises filed-or-reclaimed articles, never filed-only: a legitimate reclaim
; makes the filed-only form false, and the served path already refuses a
; reclaimed article (FN-NNTP-ARTICLE-TOMBSTONEP) where the header fact would
; fail.

(in-package "ACL2")

(include-book "filed-history")
(include-book "arena-forget")
(include-book "owner-reclaim-pass")
(include-book "owner-reclaim-seal")
(include-book "store-checkpoint-arena")
(include-book "owner-checkpoint-open")
(include-book "history-pages-owner")
(include-book "served-catalog-owner")
(include-book "catalog-availability-owner-load")

; The arena is read through its interface, never through the opened list view.
(local (in-theory (disable fn-arena-payload-is-nth fn-arena-count-is-len
                           fn-arena-seal-list-is-append fn-scka-seal-list-is-append fn-arena-p-is-payload-listp
                           fn-arena-get-is-nth fn-arena-payload-len-is-len-nth)))

(local
 (defthm o1l-disjoint-cons
   (implies (fn-arf-disjointp xs (cons y ys))
            (and (not (member-equal y xs)) (fn-arf-disjointp xs ys)))
   :hints (("Goal" :in-theory (enable fn-arf-disjointp)))))

(local
 (defthm o1l-row-bytes-release
   (implies (not (and (natp (fn-record-payload h)) (member-equal (fn-record-payload h) (fn-arf-pend-handles rel))))
            (equal (fn-row-bytes h (fn-arf-apply-released rel fn-arena))
                   (fn-row-bytes h fn-arena)))
   :hints (("Goal" :in-theory (e/d (fn-row-bytes) (fn-arf-apply-released))
            :use ((:instance fn-arf-apply-released-payload (k (fn-record-payload h))))))))

(local
 (defthm o1l-row-wire-release
   (implies (not (member-equal (fn-arf-row-handle row) (fn-arf-pend-handles rel)))
            (equal (fn-row-wire-of row (fn-arf-apply-released rel fn-arena))
                   (fn-row-wire-of row fn-arena)))
   :hints (("Goal" :in-theory (e/d (fn-row-wire-of fn-arf-row-handle) (fn-arf-apply-released fn-row-bytes)))
           ("Subgoal 3" :use ((:instance o1l-row-bytes-release (h row)))))))

(local
 (defthm o1l-history-article-release
   (implies (not (member-equal (fn-arf-row-handle row) (fn-arf-pend-handles rel)))
            (equal (fn-cat-history-article row (fn-arf-apply-released rel fn-arena))
                   (fn-cat-history-article row fn-arena)))
   :hints (("Goal" :in-theory (e/d (fn-cat-history-article fn-arf-row-handle) (fn-arf-apply-released fn-row-wire-of))
            :use ((:instance o1l-row-wire-release (row (fn-hstxa-held row)))
                  (:instance o1l-row-wire-release (row row)))))))

(local
 (defthm o1l-composite-release
   (implies (not (member-equal (fn-arf-row-handle row) (fn-arf-pend-handles rel)))
            (equal (fn-row-composite-okp row (fn-arf-apply-released rel fn-arena))
                   (fn-row-composite-okp row fn-arena)))
   :hints (("Goal" :in-theory (e/d (fn-row-composite-okp fn-arf-row-handle) (fn-arf-apply-released fn-row-wire-of))
            :use ((:instance o1l-row-wire-release (row (fn-hstxa-held row)))
                  (:instance o1l-row-wire-release (row row)))))))

(local
 (defthm o1l-items-natp (implies (member-equal x (fn-arf-items-handles items)) (natp x))
   :hints (("Goal" :in-theory (enable fn-arf-items-handles fn-arf-forget-item-p)))))

(local
 (defthm o1l-pend-natp (implies (member-equal x (fn-arf-pend-handles pend)) (natp x))
   :hints (("Goal" :in-theory (enable fn-arf-pend-handles)))))

(local
 (defthm o1l-rows-release
   (implies (fn-arf-disjointp (fn-arf-pend-handles rel) (fn-arf-rows-handles rows))
            (and (equal (fn-cat-history-articles rows (fn-arf-apply-released rel fn-arena))
                        (fn-cat-history-articles rows fn-arena))
                 (equal (fn-rows-composites-okp rows (fn-arf-apply-released rel fn-arena))
                        (fn-rows-composites-okp rows fn-arena))))
   :hints (("Goal" :induct (fn-cat-history-articles rows fn-arena)
            :in-theory (e/d (fn-cat-history-articles fn-rows-composites-okp fn-arf-rows-handles)
                            (fn-arf-apply-released fn-arf-row-handle fn-row-wire-of fn-cat-history-article fn-row-composite-okp
                             o1l-history-article-release o1l-composite-release o1l-pend-natp)))
           ("Subgoal *1/2" :use ((:instance o1l-history-article-release (row (car rows)))
                                 (:instance o1l-pend-natp (x nil) (pend rel))
                                 (:instance o1l-composite-release (row (car rows))))))))

(local
 (defthm o1l-handles-release
   (equal (fn-rows-handles-inp rows (fn-arf-apply-released rel fn-arena))
          (fn-rows-handles-inp rows fn-arena))
   :hints (("Goal" :induct (fn-rows-handles-inp rows fn-arena)
            :in-theory (e/d (fn-rows-handles-inp fn-row-handle-inp) (fn-arf-apply-released)))
           ("Goal'" :use ((:instance fn-arf-apply-released-payload (k 0)))))))

(local
 (defthm o1l-invp-release
   (implies (and (fn-arf-disjointp (fn-arf-pend-handles rel) (fn-arf-rows-handles rows))
                 (fn-o1-rows-invp rows fn-arena))
            (fn-o1-rows-invp rows (fn-arf-apply-released rel fn-arena)))
   :hints (("Goal" :in-theory (e/d (fn-o1-rows-invp) (fn-arf-apply-released fn-arf-rows-handles fn-arf-disjointp
                                                         fn-cat-history-articles fn-rows-composites-okp fn-rows-handles-inp
                                                         fn-o1-records-filed-or-reclaimedp))
            :use (o1l-rows-release o1l-handles-release)))))

(local
 (defthm o1l-disjoint-cons-rows
   (implies (fn-arf-disjointp pend (fn-arf-rows-handles (cons c rs)))
            (and (fn-arf-disjointp pend (fn-arf-rows-handles rs))
                 (fn-arf-disjointp pend (fn-arf-rows-handles (list c)))))
   :hints (("Goal" :in-theory (enable fn-arf-rows-handles fn-arf-disjointp)
            :use ((:instance o1l-disjoint-cons (xs pend) (y (fn-arf-row-handle c)) (ys (fn-arf-rows-handles rs))))))))

(defthm fn-o1-release-keeps-the-history
  (implies (and (fn-arena-p fn-arena)
                (fn-o1-files-invp files fn-arena)
                (fn-arf-disjointp (fn-arf-pend-handles rel)
                                  (fn-arf-rows-handles
                                   (cons (fn-sf-record-candidate files) (fn-sf-records files)))))
           (fn-o1-files-invp files (fn-arf-apply-released rel fn-arena)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-o1-files-invp) (fn-arf-apply-released fn-arf-rows-handles fn-arf-disjointp fn-o1-rows-invp))
           :use ((:instance o1l-disjoint-cons-rows (pend (fn-arf-pend-handles rel)) (c (fn-sf-record-candidate files)) (rs (fn-sf-records files)))
                 (:instance o1l-invp-release (rows (fn-sf-records files)))
                 (:instance o1l-invp-release (rows (list (fn-sf-record-candidate files))))))))

(local
 (defthm o1l-article-alpha2
   (implies (fn-row-composite-okp row fn-arena)
            (equal (fn-cat-history-article row fn-arena)
                   (fn-bpr-event-article (fn-row-wire-of row fn-arena))))
   :hints (("Goal" :cases ((fn-hstxa-p row) (fn-held-p row))
            :use fn-bpr-event-article-over-alpha
            :in-theory (e/d (fn-cat-history-article fn-bpr-event-article fn-row-composite-okp)
                            (fn-row-wire-of fn-bpr-event-article-over-alpha fn-stxa-p fn-replay-composite-record fn-held-wire))))))

(local
 (defthm o1l-bad-invp (fn-o1-rows-invp (list :bad) fn-arena)
   :hints (("Goal" :in-theory (enable fn-o1-rows-invp fn-cat-history-article fn-row-wire-of fn-hstxa-p fn-held-p fn-row-composite-okp fn-stxa-p fn-rows-composites-okp fn-rows-handles-inp fn-o1-records-filed-or-reclaimedp)))))

(local
 (defthm o1l-intern-row-invp-good
   (implies (and (fn-arena-p fn-arena) (natp generation)
                 (not (equal (mv-nth 0 (fn-intern-event w keyring generation fn-arena)) :bad))
                 (fn-o1-records-filed-or-reclaimedp (list (fn-bpr-event-article w))))
            (fn-o1-rows-invp (list (mv-nth 0 (fn-intern-event w keyring generation fn-arena)))
                             (mv-nth 1 (fn-intern-event w keyring generation fn-arena))))
   :hints (("Goal" 
            :in-theory (e/d (fn-o1-rows-invp fn-rows-composites-okp)
                            (fn-intern-event fn-row-wire-of fn-row-composite-okp fn-cat-history-article fn-bpr-event-article
                             fn-rows-handles-inp fn-o1-records-filed-or-reclaimedp))
            :use (fn-intern-event-handle-in fn-intern-event-composite-okp fn-intern-event-materializes
                  (:instance o1l-article-alpha2 (row (mv-nth 0 (fn-intern-event w keyring generation fn-arena)))
                             (fn-arena (mv-nth 1 (fn-intern-event w keyring generation fn-arena)))))))))

(local
 (defthm o1l-intern-row-invp2
   (implies (and (fn-arena-p fn-arena) (natp generation)
                 (fn-o1-records-filed-or-reclaimedp (list (fn-bpr-event-article w))))
            (fn-o1-rows-invp (list (mv-nth 0 (fn-intern-event w keyring generation fn-arena)))
                             (mv-nth 1 (fn-intern-event w keyring generation fn-arena))))
   :hints (("Goal" :cases ((equal (mv-nth 0 (fn-intern-event w keyring generation fn-arena)) :bad))
            :use (o1l-intern-row-invp-good
                  (:instance o1l-bad-invp (fn-arena (mv-nth 1 (fn-intern-event w keyring generation fn-arena)))))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm o1l-intern-keeps-files
   (implies (and (fn-arena-p fn-arena) (fn-o1-files-invp files fn-arena))
            (fn-o1-files-invp files (mv-nth 1 (fn-intern-event w keyring generation fn-arena))))
   :hints (("Goal" :in-theory (disable fn-intern-event fn-o1-files-invp fn-arena-seal-list)
            :use (fn-intern-event-arena
                  (:instance fn-o1-seal-keeps-the-history (xs (fn-record-payload w)))
                  (:instance fn-o1-seal-keeps-the-history (xs (fn-record-payload (fn-replay-composite-record w)))))))))

(defthm fn-o1-intern-then-stage-keeps-the-history
  (let ((row (mv-nth 0 (fn-intern-event w keyring generation fn-arena)))
        (arena2 (mv-nth 1 (fn-intern-event w keyring generation fn-arena))))
    (implies (and (fn-arena-p fn-arena)
                  (natp generation)
                  (fn-o1-files-invp files fn-arena)
                  (fn-o1-records-filed-or-reclaimedp (list (fn-bpr-event-article w)))
                  (or (equal files2 files)
                      (equal files2 (fn-sf-prepare-record files row groups capacity))))
             (fn-o1-files-invp files2 arena2)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-intern-event fn-o1-files-invp fn-o1-rows-invp fn-sf-prepare-record fn-o1-records-filed-or-reclaimedp fn-bpr-event-article)
           :use (o1l-intern-keeps-files o1l-intern-row-invp2
                 (:instance fn-o1-staging-keeps-the-history
                            (f1 files) (f2 files2)
                            (record (mv-nth 0 (fn-intern-event w keyring generation fn-arena)))
                            (fn-arena (mv-nth 1 (fn-intern-event w keyring generation fn-arena))))))))

(local
 (defthm o1l-intern-event-record
   (implies (fn-record-p w)
            (equal (fn-intern-event w k g fn-arena) (fn-cat-intern-list w k g fn-arena)))
   :hints (("Goal" :in-theory (enable fn-intern-event)))))

(local
 (defthm o1l-event-article-record
   (implies (fn-record-p w) (equal (fn-bpr-event-article w) w))
   :hints (("Goal" :use ((:instance fn-stxa-is-no-other-wire-event (x w)) (:instance fn-hstxa-is-no-wire-event (x w)))
            :in-theory (enable fn-bpr-event-article)))))

(local
 (defthm o1l-intern-row-at-invp
   (implies (and (fn-arena-p fn-arena) (natp g) (fn-record-p w)
                 (fn-o1-records-filed-or-reclaimedp (list w)))
            (fn-o1-rows-invp (list (fn-intern-row-at w k g (fn-arena-count fn-arena)))
                             (fn-arena-seal-list (fn-record-payload w) fn-arena)))
   :hints (("Goal" :in-theory (disable fn-intern-event fn-cat-intern-list fn-o1-rows-invp fn-intern-row-at fn-o1-records-filed-or-reclaimedp fn-bpr-event-article)
            :use ((:instance o1l-intern-row-invp2 (keyring k) (generation g))
                  o1l-intern-event-record o1l-event-article-record fn-cat-intern-list-is-row-at-count)))))

(local
 (defthm o1l-prepare-interned-off-gate
   (implies (not (and (fn-record-p w) (fn-prin-keyringp (fn-sn-keyring s)) (natp (fn-sn-keyring-generation s))))
            (and (equal (mv-nth 0 (fn-store-prepare-interned s w fn-arena)) s)
                 (equal (mv-nth 1 (fn-store-prepare-interned s w fn-arena)) fn-arena)))
   :hints (("Goal" :in-theory (enable fn-store-prepare-interned)))))

(defthm fn-o1-prepare-interned-keeps-the-history
  (implies (and (fn-arena-p fn-arena)
                (fn-o1-files-invp (fn-sn-files s) fn-arena)
                (fn-o1-records-filed-or-reclaimedp (list w)))
           (fn-o1-files-invp (fn-sn-files (mv-nth 0 (fn-store-prepare-interned s w fn-arena)))
                             (mv-nth 1 (fn-store-prepare-interned s w fn-arena))))
  :rule-classes nil
  :hints (("Goal" :cases ((and (fn-record-p w) (fn-prin-keyringp (fn-sn-keyring s)) (natp (fn-sn-keyring-generation s))))
           :in-theory (disable fn-store-prepare-interned fn-sn-prepare fn-intern-event fn-cat-intern-list fn-o1-files-invp fn-o1-rows-invp
                               fn-o1-records-filed-or-reclaimedp fn-intern-row-at fn-arena-seal-list)
           :use (fn-store-prepare-interned-is-intern-then-prepare
                 (:instance o1l-intern-row-at-invp (k (fn-sn-keyring s)) (g (fn-sn-keyring-generation s)))
                 fn-cat-intern-list-is-row-at-count
                 (:instance fn-o1-prepare-keeps-the-history
                            (record (fn-intern-row-at w (fn-sn-keyring s) (fn-sn-keyring-generation s) (fn-arena-count fn-arena)))
                            (fn-arena (fn-arena-seal-list (fn-record-payload w) fn-arena)))
                 (:instance fn-o1-seal-keeps-the-history (files (fn-sn-files s)) (xs (fn-record-payload w)))
                 o1l-prepare-interned-off-gate))))

(local
 (defthm o1l-statep-generation
   (implies (fn-sn-statep s) (natp (fn-sn-keyring-generation s)))
   :hints (("Goal" :in-theory (e/d (fn-sn-statep) (fn-sf-statep fn-node-statep))))))

(defthm fn-o1-prepare-identity-interned-keeps-the-history
  (let* ((k (fn-sn-keyring s)) (g (fn-sn-keyring-generation s))
         (row (mv-nth 0 (fn-intern-event w k g fn-arena)))
         (arena2 (mv-nth 1 (fn-intern-event w k g fn-arena))))
    (implies (and (fn-arena-p fn-arena)
                  (fn-sn-statep s)
                  (fn-o1-files-invp (fn-sn-files s) fn-arena)
                  (fn-o1-records-filed-or-reclaimedp (list (fn-bpr-event-article w))))
             (fn-o1-files-invp (fn-sn-files (fn-sn-prepare-identity s row)) arena2)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-intern-event fn-o1-files-invp fn-o1-rows-invp fn-sn-prepare-identity
                                      fn-o1-records-filed-or-reclaimedp fn-bpr-event-article fn-sn-statep fn-sn-keyring fn-sn-keyring-generation)
           :use (o1l-statep-generation
                 (:instance o1l-intern-keeps-files (files (fn-sn-files s)) (keyring (fn-sn-keyring s)) (generation (fn-sn-keyring-generation s)))
                 (:instance o1l-intern-row-invp2 (keyring (fn-sn-keyring s)) (generation (fn-sn-keyring-generation s)))
                 (:instance fn-o1-prepare-identity-keeps-the-history
                            (event (mv-nth 0 (fn-intern-event w (fn-sn-keyring s) (fn-sn-keyring-generation s) fn-arena)))
                            (fn-arena (mv-nth 1 (fn-intern-event w (fn-sn-keyring s) (fn-sn-keyring-generation s) fn-arena))))))))

(local
 (defthm o1l-finalize-files
   (implies (equal (fn-sn-open-kind (fn-sco-finalize e configs frontier)) :ok)
            (and (equal (fn-sf-records (fn-sn-files (fn-sn-open-state (fn-sco-finalize e configs frontier))))
                        (fn-sco-records e))
                 (equal (fn-sf-record-candidate (fn-sn-files (fn-sn-open-state (fn-sco-finalize e configs frontier))))
                        nil)))
   :hints (("Goal" :in-theory (e/d (fn-sco-finalize fn-sn-open-ok fn-sn-open-error fn-sn-open-kind fn-sn-open-state
                                    fn-sn-with-event-index fn-sn-with-topic fn-sn-with-consumer fn-cpo-install
                                    fn-sn-with-configuration fn-sn-update-replayed fn-sn-files fn-sn-make-v6
                                    fn-sf-records fn-sf-records-field fn-sf-make fn-sf-make-fields fn-sf-record-candidate)
                                   (fn-sn-statep fn-sco-cpr-finish fn-cnode-statep fn-replay-advance-okp
                                    fn-sn-observed-historyp fn-sn-observed-seed fn-replay-advance-txid
                                    fn-stxk-context-kind fn-th-at fn-sl-of fn-sl-list
                                    fn-sf-make-fields-canonical-is-make))))))

(local
 (defthm o1l-recover-extended-files
   (implies (not (equal (fn-ock-recover-extended e configs frontier mc) :fault))
            (and (equal (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner (fn-ock-recover-extended e configs frontier mc)))))
                        (fn-sco-records e))
                 (equal (fn-sf-record-candidate (fn-sn-files (fn-own-store (fn-ocfg-owner (fn-ock-recover-extended e configs frontier mc)))))
                        nil)))
   :hints (("Goal" :in-theory (disable fn-ock-install fn-sco-finalize fn-sn-open-kind fn-sn-open-state fn-sco-records)
            :use ((:instance fn-hpo-ock-install-store
                             (replayed (fn-sco-cpr-finish (fn-sco-cpr e) configs))
                             (opened (fn-sco-finalize e configs frontier)) (max-conns mc))
                  (:instance o1l-finalize-files)))
           ("Goal'" :in-theory (enable fn-ock-recover-extended)))))

(local
 (defun o1l-rewrite-okp (new fn-arena)
   (declare (xargs :stobjs fn-arena :verify-guards nil))
   (if (atom new)
       t
     (and (if (fn-record-p (car new))
              (fn-o1-records-filed-or-reclaimedp (list (car new)))
            (fn-o1-rows-invp (list (car new)) fn-arena))
          (o1l-rewrite-okp (cdr new) fn-arena)))))

(local
 (defthm o1l-seed-natp
   (natp (fn-ssr-at 2 (fn-ssr-seed id)))
   :hints (("Goal" :use fn-ssr-seed-establishes-statep :in-theory (e/d (fn-ssr-statep) (fn-ssr-seed-establishes-statep fn-ssr-seed fn-ssr-at))))))

(local
 (defthm o1l-rewrite-okp-seal
   (implies (and (fn-arena-p fn-arena) (o1l-rewrite-okp new fn-arena))
            (o1l-rewrite-okp new (fn-arena-seal-list xs fn-arena)))
   :hints (("Goal" :induct (o1l-rewrite-okp new fn-arena)
            :in-theory (disable fn-arena-seal-list fn-o1-rows-invp fn-o1-records-filed-or-reclaimedp))
           ("Subgoal *1/2" :use ((:instance fn-o1-rows-invp-seal (rows (list (car new)))))))))

(local
 (defthm o1l-record-payload-octets
   (implies (fn-record-p w) (fn-cbor-octet-listp (fn-record-payload w)))
   :hints (("Goal" :in-theory (enable fn-record-p fn-record-payloadp)))))

(local
 (defthm o1l-seal-arena-p
   (implies (and (fn-arena-p fn-arena) (fn-cbor-octet-listp xs))
            (fn-arena-p (fn-arena-seal-list xs fn-arena)))
   :hints (("Goal" :in-theory (enable fn-arena-p-is-payload-listp fn-arn-payload-listp fn-arena-seal-list-is-append)))))

(local
 (defthm o1l-seal-invp
   (implies (and (fn-arena-p fn-arena) (fn-o1-rows-invp rows fn-arena))
            (fn-o1-rows-invp rows (fn-arena-seal-list xs fn-arena)))
   :hints (("Goal" :use fn-o1-rows-invp-seal))))

(local
 (defthm o1l-intern-rows-at-seal
   (implies (and (fn-arena-p fn-arena) (fn-o1-rows-invp rows fn-arena))
            (fn-o1-rows-invp rows (mv-nth 1 (fn-orcp-intern-rows-at new id h fn-arena))))
   :hints (("Goal" :induct (fn-orcp-intern-rows-at new id h fn-arena)
            :in-theory (disable fn-o1-rows-invp fn-intern-row-at fn-ssr-seed fn-ssr-at fn-replay-identity-loop fn-record-p fn-arena-seal-list)))))

(local
 (defthm o1l-seal-count
   (equal (fn-arena-count (fn-arena-seal-list xs fn-arena)) (+ 1 (fn-arena-count fn-arena)))
   :hints (("Goal" :in-theory (enable fn-arena-seal-list fn-arena-count)))))

(local
 (defthm o1l-cons-invp
   (implies (and (fn-o1-rows-invp (list a) fn-arena) (fn-o1-rows-invp b fn-arena))
            (fn-o1-rows-invp (cons a b) fn-arena))
   :hints (("Goal" :use ((:instance fn-o1-rows-invp-append (a (list a)) (b b)))
            :in-theory (union-theories '((:definition binary-append) (:executable-counterpart consp) car-cons cdr-cons) (theory 'minimal-theory))))))

(local
 (defthm o1l-badsym-invp (fn-o1-rows-invp :bad fn-arena)
   :hints (("Goal" :in-theory (enable fn-o1-rows-invp fn-cat-history-articles fn-rows-composites-okp fn-rows-handles-inp fn-o1-records-filed-or-reclaimedp)))))

(local
 (in-theory (disable o1l-cons-invp o1l-seal-count o1l-intern-rows-at-seal o1l-intern-row-at-invp o1l-seal-invp)))

(local
 (in-theory (disable o1l-cons-invp o1l-seal-count o1l-intern-rows-at-seal o1l-intern-row-at-invp o1l-seal-invp)))

(local
 (defthm o1l-step-rec2
   (implies (and (fn-arena-p fn-arena) (fn-record-p r) (fn-o1-records-filed-or-reclaimedp (list r))
                 (natp g) (equal h (fn-arena-count fn-arena))
                 (fn-o1-rows-invp (car (fn-orcp-intern-rows-at rest id2 h2 (fn-arena-seal-list (fn-record-payload r) fn-arena)))
                                  (mv-nth 1 (fn-orcp-intern-rows-at rest id2 h2 (fn-arena-seal-list (fn-record-payload r) fn-arena)))))
            (fn-o1-rows-invp (cons (fn-intern-row-at r k g h)
                                   (car (fn-orcp-intern-rows-at rest id2 h2 (fn-arena-seal-list (fn-record-payload r) fn-arena))))
                             (mv-nth 1 (fn-orcp-intern-rows-at rest id2 h2 (fn-arena-seal-list (fn-record-payload r) fn-arena)))))
   :hints (("Goal" :in-theory (disable fn-o1-rows-invp fn-intern-row-at fn-arena-seal-list fn-orcp-intern-rows-at fn-record-p fn-o1-records-filed-or-reclaimedp)
            :use ((:instance o1l-intern-row-at-invp (w r))
                  (:instance o1l-intern-rows-at-seal (rows (list (fn-intern-row-at r k g h))) (new rest) (id id2) (h h2)
                             (fn-arena (fn-arena-seal-list (fn-record-payload r) fn-arena)))
                  (:instance o1l-cons-invp (a (fn-intern-row-at r k g h))
                             (b (car (fn-orcp-intern-rows-at rest id2 h2 (fn-arena-seal-list (fn-record-payload r) fn-arena))))
                             (fn-arena (mv-nth 1 (fn-orcp-intern-rows-at rest id2 h2 (fn-arena-seal-list (fn-record-payload r) fn-arena))))))))))

(local
 (defthm o1l-step-non2
   (implies (and (fn-arena-p fn-arena) (fn-o1-rows-invp (list r) fn-arena)
                 (fn-o1-rows-invp (car (fn-orcp-intern-rows-at rest id2 h2 fn-arena))
                                  (mv-nth 1 (fn-orcp-intern-rows-at rest id2 h2 fn-arena))))
            (fn-o1-rows-invp (cons r (car (fn-orcp-intern-rows-at rest id2 h2 fn-arena)))
                             (mv-nth 1 (fn-orcp-intern-rows-at rest id2 h2 fn-arena))))
   :hints (("Goal" :in-theory (disable fn-o1-rows-invp fn-orcp-intern-rows-at)
            :use ((:instance o1l-intern-rows-at-seal (rows (list r)) (new rest) (id id2) (h h2))
                  (:instance o1l-cons-invp (a r) (b (car (fn-orcp-intern-rows-at rest id2 h2 fn-arena)))
                             (fn-arena (mv-nth 1 (fn-orcp-intern-rows-at rest id2 h2 fn-arena)))))))))

(local
 (defthm o1l-nil-invp (fn-o1-rows-invp nil fn-arena)
   :hints (("Goal" :in-theory (enable fn-o1-rows-invp fn-cat-history-articles fn-rows-composites-okp fn-rows-handles-inp fn-o1-records-filed-or-reclaimedp)))))

(local
 (defthm o1l-intern-rows-at-invp
   (implies (and (fn-arena-p fn-arena) (equal h (fn-arena-count fn-arena))
                 (o1l-rewrite-okp new fn-arena))
            (fn-o1-rows-invp (mv-nth 0 (fn-orcp-intern-rows-at new id h fn-arena))
                             (mv-nth 1 (fn-orcp-intern-rows-at new id h fn-arena))))
   :hints (("Goal" :induct (fn-orcp-intern-rows-at new id h fn-arena)
            :in-theory (e/d (o1l-seal-count o1l-step-rec2 o1l-step-non2 o1l-rewrite-okp-seal o1l-seal-arena-p o1l-record-payload-octets o1l-badsym-invp o1l-seed-natp o1l-nil-invp)
                            (fn-o1-rows-invp fn-intern-row-at fn-ssr-seed fn-ssr-at fn-replay-identity-loop fn-record-p fn-arena-seal-list
                             fn-o1-records-filed-or-reclaimedp))))))

(local
 (defthm o1l-rewrite-row-cases
   (let ((n (fn-orc-rewrite-row r ctx fn-arena)))
     (or (equal n r)
         (and (fn-record-p n) (fn-o1-records-filed-or-reclaimedp (list n)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-orc-rewrite-row fn-rclp-rewrites-p) (fn-rclp-tombstoned fn-o1-records-filed-or-reclaimedp fn-orc-row-octets))
            :use ((:instance fn-o1-tombstoned-record-is-reclaimed
                             (r (fn-record-result-record (fn-record-decode-exact (fn-orc-row-octets r fn-arena))))))))))

(local
 (defthm o1l-invp-car-cdr
   (implies (and (consp rows) (fn-o1-rows-invp rows fn-arena))
            (and (fn-o1-rows-invp (list (car rows)) fn-arena) (fn-o1-rows-invp (cdr rows) fn-arena)))
   :hints (("Goal" :use ((:instance fn-o1-rows-invp-append (a (list (car rows))) (b (cdr rows))))
            :in-theory (union-theories '((:definition binary-append) (:executable-counterpart consp) car-cons cdr-cons (:rewrite cons-car-cdr)) (theory 'minimal-theory))))))

(local
 (defthm o1l-record-row-fr
   (implies (and (fn-record-p r) (fn-o1-rows-invp (list r) fn-arena))
            (fn-o1-records-filed-or-reclaimedp (list r)))
   :hints (("Goal" :in-theory (e/d (fn-o1-rows-invp fn-cat-history-article fn-row-wire-of) (fn-o1-records-filed-or-reclaimedp))
            :use (fn-record-is-no-other-wire-event (:instance fn-hstxa-is-no-wire-event (x r)) (:instance fn-held-is-no-wire-event (x r)))))))

(local
 (defthm o1l-rewrite-okp-row
   (implies (fn-o1-rows-invp (list r) fn-arena)
            (o1l-rewrite-okp (list (fn-orc-rewrite-row r ctx fn-arena)) fn-arena))
   :hints (("Goal" :in-theory (disable fn-o1-rows-invp fn-o1-records-filed-or-reclaimedp fn-orc-rewrite-row)
            :use ((:instance o1l-rewrite-row-cases)
                  (:instance o1l-record-row-fr))))))

(local
 (defthm o1l-invp-cdr
   (implies (and (consp rows) (fn-o1-rows-invp rows fn-arena))
            (fn-o1-rows-invp (cdr rows) fn-arena))
   :hints (("Goal" :use o1l-invp-car-cdr :in-theory (disable o1l-invp-car-cdr)))))

(local
 (defthm o1l-rewrite-okp-step
   (implies (and (consp rows) (fn-o1-rows-invp rows fn-arena)
                 (o1l-rewrite-okp (fn-orc-rewrite-rows (cdr rows) ctx fn-arena) fn-arena))
            (o1l-rewrite-okp (fn-orc-rewrite-rows rows ctx fn-arena) fn-arena))
   :hints (("Goal" :in-theory (disable fn-o1-rows-invp fn-orc-rewrite-row o1l-rewrite-okp-row o1l-invp-car-cdr o1l-invp-cdr)
            :expand ((fn-orc-rewrite-rows rows ctx fn-arena)
                     (o1l-rewrite-okp (list (fn-orc-rewrite-row (car rows) ctx fn-arena)) fn-arena)
                     (o1l-rewrite-okp (cons (fn-orc-rewrite-row (car rows) ctx fn-arena) (fn-orc-rewrite-rows (cdr rows) ctx fn-arena)) fn-arena))
            :use (o1l-invp-car-cdr (:instance o1l-rewrite-okp-row (r (car rows))))))))

(local
 (defthm o1l-rewrite-okp-base
   (implies (not (consp rows))
            (o1l-rewrite-okp (fn-orc-rewrite-rows rows ctx fn-arena) fn-arena))
   :hints (("Goal" :expand ((fn-orc-rewrite-rows rows ctx fn-arena))))))

(local
 (defthm o1l-rewrite-okp-of-rewrite
   (implies (fn-o1-rows-invp rows fn-arena)
            (o1l-rewrite-okp (fn-orc-rewrite-rows rows ctx fn-arena) fn-arena))
   :hints (("Goal" :induct (len rows)
            :in-theory (disable fn-o1-rows-invp fn-orc-rewrite-row o1l-rewrite-okp-row o1l-invp-car-cdr fn-orc-rewrite-rows fn-orc-row-octets o1l-rewrite-okp)))))

(local
 (defthm o1l-capture-records-nil
   (equal (fn-sco-records (fn-sco-capture configs nil)) nil)
   :hints (("Goal" :in-theory (enable fn-sco-capture fn-sco-records)))))

(local
 (defthm o1l-rebuild-records
   (equal (fn-sco-records (car (fn-orcp-rebuild rows configs frontier mc))) rows)
   :hints (("Goal" :in-theory (e/d (fn-orcp-rebuild fn-rii-sco-extend-is-sco-extend fn-hpo-sco-records-of-extend o1l-capture-records-nil)
                                   (fn-sco-records fn-sco-capture fn-ock-recover-extended fn-sco-extend))))))

(local
 (defthm o1l-swapped-store
   (equal (fn-own-store (fn-orcp-swapped-owner live o)) (fn-own-store o))
   :hints (("Goal" :in-theory (e/d (fn-orcp-swapped-owner fn-orcp-swap-base fn-own-set-conns) (fn-orcp-repin-conns))))))

(local
 (defthm o1l-fault-owner-invp
   (fn-o1-files-invp (fn-sn-files (fn-own-store (fn-ocfg-owner :fault))) fn-arena)
   :hints (("Goal" :in-theory (enable fn-o1-files-invp fn-o1-rows-invp fn-sn-files fn-own-store fn-ocfg-owner fn-sf-records fn-sf-record-candidate
                                      fn-cat-history-articles fn-rows-composites-okp fn-rows-handles-inp fn-o1-records-filed-or-reclaimedp fn-cat-history-article fn-row-wire-of fn-row-composite-okp fn-held-p fn-hstxa-p fn-stxa-p)))))

(local
 (defthm o1l-list-nil-invp (fn-o1-rows-invp (list nil) fn-arena)
   :hints (("Goal" :in-theory (enable fn-o1-rows-invp fn-cat-history-article fn-row-wire-of fn-hstxa-p fn-held-p fn-row-composite-okp fn-stxa-p)))))

(local
 (defthm o1l-rebuild-shape
   (equal (cadr (fn-orcp-rebuild rows configs frontier mc))
          (fn-ock-recover-extended (car (fn-orcp-rebuild rows configs frontier mc)) configs frontier mc))
   :hints (("Goal" :in-theory (union-theories '(fn-orcp-rebuild car-cons cdr-cons) (theory 'minimal-theory))))))

(local
 (defthm o1l-rebuilt-files
   (implies (not (equal (cadr (fn-orcp-rebuild rows configs frontier mc)) :fault))
            (and (equal (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner (cadr (fn-orcp-rebuild rows configs frontier mc)))))) rows)
                 (equal (fn-sf-record-candidate (fn-sn-files (fn-own-store (fn-ocfg-owner (cadr (fn-orcp-rebuild rows configs frontier mc)))))) nil)))
   :hints (("Goal" :in-theory (theory 'minimal-theory)
            :use (o1l-rebuild-shape o1l-rebuild-records
                  (:instance o1l-recover-extended-files (e (car (fn-orcp-rebuild rows configs frontier mc))) (mc mc)))))))

(local
 (defthm o1l-ocfg-files-invp
   (implies (and (fn-o1-rows-invp rows2 arena2)
                 (or (equal oc :fault)
                     (and (equal (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))) rows2)
                          (equal (fn-sf-record-candidate (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))) nil))))
            (fn-o1-files-invp (fn-sn-files (fn-own-store (fn-ocfg-owner oc))) arena2))
   :hints (("Goal" :cases ((equal oc :fault))
            :in-theory (e/d (fn-o1-files-invp) (fn-o1-rows-invp fn-own-store fn-ocfg-owner fn-sn-files fn-sf-records fn-sf-record-candidate o1l-fault-owner-invp))
            :use (o1l-fault-owner-invp (:instance o1l-list-nil-invp (fn-arena arena2)))))))

(local
 (defthm o1l-rebuilt-files-invp2
   (implies (fn-o1-rows-invp rows2 arena2)
            (fn-o1-files-invp (fn-sn-files (fn-own-store (fn-ocfg-owner (cadr (fn-orcp-rebuild rows2 configs frontier mc))))) arena2))
   :hints (("Goal" :in-theory (theory 'minimal-theory)
            :use ((:instance o1l-ocfg-files-invp (oc (cadr (fn-orcp-rebuild rows2 configs frontier mc))))
                  (:instance o1l-rebuilt-files (rows rows2)))))))

(defthm fn-o1-reclaim-swap-keeps-the-history
  (let* ((rows (fn-sf-records (fn-sn-files (fn-own-store live))))
         (rw (fn-orc-rewrite-rows rows ctx fn-arena))
         (rows2 (mv-nth 0 (fn-orcp-intern-rows rw id fn-arena)))
         (arena2 (mv-nth 1 (fn-orcp-intern-rows rw id fn-arena)))
         (rebuilt (cadr (fn-orcp-rebuild rows2 configs frontier max-conns))))
    (implies (and (fn-arena-p fn-arena)
                  (fn-o1-rows-invp rows fn-arena))
             (fn-o1-files-invp
              (fn-sn-files (fn-own-store (fn-orcp-swapped-owner live (fn-ocfg-owner rebuilt))))
              arena2)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-orcp-intern-rows fn-orcp-rebuild fn-orc-rewrite-rows fn-o1-rows-invp fn-o1-files-invp fn-orcp-swapped-owner fn-own-store
                                      fn-orcp-intern-rows-at o1l-rewrite-okp-of-rewrite o1l-intern-rows-at-invp)
           :use (o1l-swapped-store
                 (:instance o1l-rebuilt-files-invp2
                            (rows2 (mv-nth 0 (fn-orcp-intern-rows (fn-orc-rewrite-rows (fn-sf-records (fn-sn-files (fn-own-store live))) ctx fn-arena) id fn-arena)))
                            (arena2 (mv-nth 1 (fn-orcp-intern-rows (fn-orc-rewrite-rows (fn-sf-records (fn-sn-files (fn-own-store live))) ctx fn-arena) id fn-arena)))
                            (configs configs) (frontier frontier) (mc max-conns))
                 (:instance o1l-intern-rows-at-invp
                            (new (fn-orc-rewrite-rows (fn-sf-records (fn-sn-files (fn-own-store live))) ctx fn-arena))
                            (h (fn-arena-count fn-arena)))
                 (:instance o1l-rewrite-okp-of-rewrite (rows (fn-sf-records (fn-sn-files (fn-own-store live))))))
           :expand ((fn-orcp-intern-rows (fn-orc-rewrite-rows (fn-sf-records (fn-sn-files (fn-own-store live))) ctx fn-arena) id fn-arena)))))

(local
 (defthm o1l-fr-cons
   (equal (fn-o1-records-filed-or-reclaimedp (cons x y))
          (and (fn-o1-records-filed-or-reclaimedp (list x)) (fn-o1-records-filed-or-reclaimedp y)))
   :hints (("Goal" :expand ((fn-o1-records-filed-or-reclaimedp (cons x y)) (fn-o1-records-filed-or-reclaimedp (list x)))))))

(local
 (defthm o1l-article-records-cons
   (equal (fn-bpr-article-records (cons w ws))
          (cons (fn-bpr-event-article w) (fn-bpr-article-records ws)))
   :hints (("Goal" :in-theory (enable fn-bpr-article-records)))))

(local
 (defthm o1l-sco-records-bad (equal (fn-sco-records :bad) nil)
   :hints (("Goal" :in-theory (enable fn-sco-records fn-sco-at)))))

(local
 (in-theory (disable o1l-fr-cons)))

(local
 (defthm o1l-fr-cons-fwd
   (implies (fn-o1-records-filed-or-reclaimedp (cons x y))
            (and (fn-o1-records-filed-or-reclaimedp (list x)) (fn-o1-records-filed-or-reclaimedp y)))
   :hints (("Goal" :use o1l-fr-cons :in-theory (disable o1l-fr-cons)))
   :rule-classes :forward-chaining))

(local
 (defthm o1l-count-len (implies (true-listp a) (equal (fn-arena-count a) (len a)))
   :hints (("Goal" :in-theory (enable fn-arena-count-is-len)))))

(local
 (defthm o1l-scka-intern-row-len
   (implies (fn-arena-p fn-arena)
            (equal (mv-nth 0 (fn-intern-event w keyring generation fn-arena))
                   (fn-scka-intern-one w keyring generation (len fn-arena))))
   :hints (("Goal" :use (fn-scka-intern-event-row (:instance o1l-count-len (a fn-arena)))
            :in-theory (disable fn-scka-intern-event-row fn-intern-event fn-scka-intern-one)))))

(local
 (defthm o1l-intern-arena-is-append
   (implies (and (fn-arena-p fn-arena) (not (equal (fn-scka-intern-one w keyring generation (len fn-arena)) :bad)))
            (equal (mv-nth 1 (fn-intern-event w keyring generation fn-arena))
                   (if (fn-scka-sealsp w) (append fn-arena (list (fn-scka-payload-of w))) fn-arena)))
   :hints (("Goal" :in-theory (e/d (fn-scka-sealsp fn-scka-payload-of fn-scka-intern-one fn-scka-seal-list-is-append) (fn-intern-event fn-arena-seal-list))
            :use (fn-intern-event-arena)))))

(local
 (defthm o1l-fold-step-row
   (implies (and (fn-arena-p fn-arena) (natp generation)
                 (fn-o1-records-filed-or-reclaimedp (list (fn-bpr-event-article w)))
                 (not (equal (fn-scka-intern-one w keyring generation (len fn-arena)) :bad)))
            (fn-o1-rows-invp (list (fn-scka-intern-one w keyring generation (len fn-arena)))
                             (if (fn-scka-sealsp w) (append fn-arena (list (fn-scka-payload-of w))) fn-arena)))
   :hints (("Goal" :use ((:instance o1l-intern-row-invp2 (keyring keyring) (generation generation) (w w) (fn-arena fn-arena))
                         (:instance o1l-scka-intern-row-len)
                         (:instance o1l-intern-arena-is-append))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm o1l-sealed-arena-p
   (implies (and (fn-arena-p fn-arena)
                 (not (equal (fn-scka-intern-one w keyring generation h) :bad)))
            (fn-arena-p (if (fn-scka-sealsp w) (append fn-arena (list (fn-scka-payload-of w))) fn-arena)))
   :hints (("Goal" :in-theory (e/d (fn-scka-sealsp fn-scka-payload-of fn-scka-intern-one fn-scka-seal-list-is-append)
                                   (fn-arena-seal-list))
            :use ((:instance o1l-seal-arena-p (xs (fn-record-payload w)))
                  (:instance o1l-seal-arena-p (xs (fn-record-payload (fn-replay-composite-record w)))))))))

(local
 (defthm o1l-rows-invp-sealed
   (implies (and (fn-arena-p fn-arena) (fn-o1-rows-invp rows fn-arena))
            (fn-o1-rows-invp rows (if (fn-scka-sealsp w) (append fn-arena (list (fn-scka-payload-of w))) fn-arena)))
   :hints (("Goal" :in-theory (e/d (fn-scka-sealsp fn-scka-payload-of fn-scka-seal-list-is-append)
                                   (fn-arena-seal-list fn-o1-rows-invp))
            :use ((:instance o1l-seal-invp (xs (fn-record-payload w)))
                  (:instance o1l-seal-invp (xs (fn-record-payload (fn-replay-composite-record w)))))))))

(local
 (defthm o1l-rev-onto (equal (fn-ag-rev-onto x acc) (revappend x acc))))

(local
 (defthm o1l-revappend-append (equal (revappend x y) (append (revappend x nil) y)) :rule-classes nil))

(local
 (defthm o1l-revappend-snoc (equal (revappend x (list r)) (append (revappend x nil) (list r)))
   :hints (("Goal" :use (:instance o1l-revappend-append (y (list r)))))))

(local
 (defthm o1l-rows-of-publish
   (equal (fn-ssr-rows (fn-ssr-publish acc row wire id))
          (append (fn-ssr-rows acc) (list row)))
   :hints (("Goal" :in-theory (enable fn-ssr-publish fn-ssr-rows fn-ssr-state fn-ssr-at o1l-rev-onto o1l-revappend-snoc)))))

(local
 (defthm o1l-statep-natp-gen (implies (fn-ssr-statep acc) (natp (fn-ssr-at 2 acc)))
   :hints (("Goal" :in-theory (enable fn-ssr-statep)))))

(local
 (defthm o1l-len-sealed
   (equal (len (if (fn-scka-sealsp w) (append a (list x)) a)) (if (fn-scka-sealsp w) (+ 1 (len a)) (len a)))))

(local
 (defthm o1l-fold-step-rows
   (implies (and (fn-ssr-statep acc) (fn-arena-p fn-arena) (equal h (len fn-arena))
                 (fn-o1-rows-invp (fn-ssr-rows acc) fn-arena)
                 (fn-o1-records-filed-or-reclaimedp (list (fn-bpr-event-article w)))
                 (not (equal (fn-scka-intern-one w (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) h) :bad)))
            (fn-o1-rows-invp (fn-ssr-rows (fn-ssr-publish acc (fn-scka-intern-one w (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) h) w id))
                             (if (fn-scka-sealsp w) (append fn-arena (list (fn-scka-payload-of w))) fn-arena)))
   :hints (("Goal" :in-theory (theory 'minimal-theory)
            :use ((:instance o1l-rows-of-publish (row (fn-scka-intern-one w (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) h)) (wire w))
                  (:instance o1l-fold-step-row (keyring (fn-ssr-at 1 acc)) (generation (fn-ssr-at 2 acc)))
                  (:instance o1l-rows-invp-sealed (rows (fn-ssr-rows acc)))
                  (:instance o1l-statep-natp-gen)
                  (:instance fn-o1-rows-invp-append (a (fn-ssr-rows acc)) (b (list (fn-scka-intern-one w (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) h)))
                             (fn-arena (if (fn-scka-sealsp w) (append fn-arena (list (fn-scka-payload-of w))) fn-arena))))))))

(local
 (defthm o1l-fold-not-bad-row
   (implies (and (consp ws) (not (equal (fn-scka-fold-at acc ws h) :bad)))
            (not (equal (fn-scka-intern-one (car ws) (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) h) :bad)))
   :hints (("Goal" :expand ((fn-scka-fold-at acc ws h)) :in-theory (disable fn-replay-identity-step fn-stxk-context-kind fn-ssr-publish)))))

(local
 (defthm o1l-fold-at-step
   (implies (and (consp ws) (not (equal (fn-scka-fold-at acc ws h) :bad)))
            (equal (fn-scka-fold-at acc ws h)
                   (fn-scka-fold-at (fn-ssr-publish acc (fn-scka-intern-one (car ws) (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) h) (car ws)
                                                    (fn-replay-identity-step (fn-ssr-at 3 acc)
                                                                             (fn-scka-intern-one (car ws) (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) h)))
                                    (cdr ws) (if (fn-scka-sealsp (car ws)) (+ 1 h) h))))
   :hints (("Goal" :expand ((fn-scka-fold-at acc ws h)) :in-theory (disable fn-replay-identity-step fn-stxk-context-kind fn-ssr-publish)))))

(local
 (defthm o1l-payloads-cons
   (equal (fn-scka-payloads (cons w ws))
          (if (fn-scka-sealsp w) (cons (fn-scka-payload-of w) (fn-scka-payloads ws)) (fn-scka-payloads ws)))
   :hints (("Goal" :in-theory (enable fn-scka-payloads)))))

(local
 (defthm o1l-append-cons (equal (append a (cons p r)) (append (append a (list p)) r)) :rule-classes nil))

(local
 (defthm o1l-fold-invp-step
   (implies (and (consp ws) (fn-ssr-statep acc) (fn-arena-p fn-arena) (equal h (len fn-arena))
                 (fn-o1-rows-invp (fn-ssr-rows acc) fn-arena)
                 (fn-o1-records-filed-or-reclaimedp (fn-bpr-article-records ws))
                 (not (equal (fn-scka-fold-at acc ws h) :bad))
                 (let* ((row (fn-scka-intern-one (car ws) (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) h))
                        (acc2 (fn-ssr-publish acc row (car ws) (fn-replay-identity-step (fn-ssr-at 3 acc) row)))
                        (a2 (if (fn-scka-sealsp (car ws)) (append fn-arena (list (fn-scka-payload-of (car ws)))) fn-arena))
                        (h2 (if (fn-scka-sealsp (car ws)) (+ 1 h) h)))
                   (implies (and (fn-ssr-statep acc2) (fn-arena-p a2) (equal h2 (len a2))
                                 (fn-o1-rows-invp (fn-ssr-rows acc2) a2)
                                 (fn-o1-records-filed-or-reclaimedp (fn-bpr-article-records (cdr ws)))
                                 (not (equal (fn-scka-fold-at acc2 (cdr ws) h2) :bad)))
                            (fn-o1-rows-invp (fn-ssr-rows (fn-scka-fold-at acc2 (cdr ws) h2))
                                             (append a2 (fn-scka-payloads (cdr ws)))))))
            (fn-o1-rows-invp (fn-ssr-rows (fn-scka-fold-at acc ws h)) (append fn-arena (fn-scka-payloads ws))))
   :hints (("Goal" :in-theory (disable fn-o1-rows-invp fn-o1-records-filed-or-reclaimedp fn-ssr-publish fn-ssr-rows fn-ssr-statep fn-ssr-at
                                       fn-scka-intern-one fn-scka-sealsp fn-scka-payload-of fn-replay-identity-step fn-stxk-context-kind
                                       fn-bpr-article-records fn-bpr-event-article fn-scka-payloads fn-arena-p fn-scka-fold-at
                                       o1l-fold-step-rows o1l-sealed-arena-p o1l-fold-at-step o1l-fold-not-bad-row)
            :use (o1l-fold-at-step o1l-fold-not-bad-row o1l-payloads-cons (:instance o1l-append-cons (a fn-arena) (p (fn-scka-payload-of (car ws))) (r (fn-scka-payloads (cdr ws))))
                  (:instance o1l-fold-step-rows (w (car ws)) (id (fn-replay-identity-step (fn-ssr-at 3 acc)
                                                        (fn-scka-intern-one (car ws) (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) h))))
                  (:instance o1l-sealed-arena-p (w (car ws)) (keyring (fn-ssr-at 1 acc)) (generation (fn-ssr-at 2 acc)))
                  (:instance fn-ssr-publish-preserves-statep (row (fn-scka-intern-one (car ws) (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) h))
                             (wire (car ws)) (identity (fn-replay-identity-step (fn-ssr-at 3 acc)
                                                        (fn-scka-intern-one (car ws) (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) h))))
                  (:instance o1l-len-sealed (w (car ws)) (a fn-arena) (x (fn-scka-payload-of (car ws))))
                  (:instance o1l-article-records-cons (w (car ws)) (ws (cdr ws)))
                  (:instance o1l-fr-cons-fwd (x (fn-bpr-event-article (car ws))) (y (fn-bpr-article-records (cdr ws)))))))))

(local
 (defun o1l-fold-ind (acc ws h a)
   (declare (xargs :measure (len ws)))
   (if (atom ws)
       (list acc h a)
     (o1l-fold-ind (fn-ssr-publish acc (fn-scka-intern-one (car ws) (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) h) (car ws)
                                   (fn-replay-identity-step (fn-ssr-at 3 acc)
                                                            (fn-scka-intern-one (car ws) (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) h)))
                   (cdr ws) (if (fn-scka-sealsp (car ws)) (+ 1 h) h)
                   (if (fn-scka-sealsp (car ws)) (append a (list (fn-scka-payload-of (car ws)))) a)))))

(local
 (defthm o1l-fold-base
   (implies (and (atom ws) (not (equal (fn-scka-fold-at acc ws h) :bad)))
            (and (equal ws nil) (equal (fn-scka-fold-at acc ws h) acc)))
   :rule-classes nil
   :hints (("Goal" :expand ((fn-scka-fold-at acc ws h))))))

(local
 (defthm o1l-fold-invp
   (implies (and (fn-ssr-statep acc) (fn-arena-p fn-arena) (equal h (len fn-arena))
                 (fn-o1-rows-invp (fn-ssr-rows acc) fn-arena)
                 (fn-o1-records-filed-or-reclaimedp (fn-bpr-article-records ws))
                 (not (equal (fn-scka-fold-at acc ws h) :bad)))
            (fn-o1-rows-invp (fn-ssr-rows (fn-scka-fold-at acc ws h)) (append fn-arena (fn-scka-payloads ws))))
   :hints (("Goal" :induct (o1l-fold-ind acc ws h fn-arena)
            :in-theory (disable fn-o1-rows-invp fn-o1-records-filed-or-reclaimedp fn-ssr-publish fn-ssr-rows fn-ssr-statep fn-ssr-at
                                fn-scka-intern-one fn-scka-sealsp fn-scka-payload-of fn-replay-identity-step fn-stxk-context-kind
                                fn-bpr-article-records fn-bpr-event-article fn-scka-payloads fn-arena-p fn-scka-fold-at o1l-fold-invp-step)
            :do-not-induct nil)
           ("Subgoal *1/2" :use o1l-fold-invp-step)
           ("Subgoal *1/1" :use o1l-fold-base :expand ((fn-scka-payloads ws))))))

(local
 (defthm o1l-full-recover-rows-invp
   (implies (fn-o1-records-filed-or-reclaimedp (fn-bpr-article-records ws))
            (fn-o1-rows-invp (fn-sco-records (car (fn-scka-full-recover configs ws)))
                             (cadr (fn-scka-full-recover configs ws))))
   :hints (("Goal" :cases ((equal (fn-scka-fold-at (fn-ssr-seed (fn-stxk-initial-context 0)) ws 0) :bad))
            :in-theory (e/d (fn-scka-full-recover fn-hpo-sco-records-of-extend o1l-capture-records-nil o1l-sco-records-bad)
                            (fn-sco-records fn-sco-capture fn-sco-extend fn-scka-fold-at fn-ssr-seed fn-o1-rows-invp fn-o1-records-filed-or-reclaimedp fn-bpr-article-records fn-ssr-rows fn-ssr-statep fn-scka-payloads))
            :use ((:instance o1l-fold-invp (acc (fn-ssr-seed (fn-stxk-initial-context 0))) (h 0) (fn-arena nil))
                  (:instance fn-ssr-seed-establishes-statep (identity (fn-stxk-initial-context 0)))
                  (:instance fn-scka-rows-of-seed (id (fn-stxk-initial-context 0)))
                  o1l-nil-invp)))))

(defthm fn-o1-reopen-keeps-the-history
  (let* ((fr (fn-scka-full-recover configs ws))
         (oc (fn-ock-recover-extended (car fr) configs frontier max-conns)))
    (implies (fn-o1-records-filed-or-reclaimedp (fn-bpr-article-records ws))
             (fn-o1-files-invp (fn-sn-files (fn-own-store (fn-ocfg-owner oc))) (cadr fr))))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use (o1l-full-recover-rows-invp
                 (:instance o1l-ocfg-files-invp
                            (rows2 (fn-sco-records (car (fn-scka-full-recover configs ws))))
                            (arena2 (cadr (fn-scka-full-recover configs ws)))
                            (oc (fn-ock-recover-extended (car (fn-scka-full-recover configs ws)) configs frontier max-conns)))
                 (:instance o1l-recover-extended-files (e (car (fn-scka-full-recover configs ws))) (mc max-conns))))))

(defthm fn-o1-checkpoint-reopen-keeps-the-history
  (let* ((c (fn-sco-capture configs (fn-scka-intern-at ws (fn-stxk-initial-context 0) 0)))
         (r (fn-scka-recover-rows c configs vs (fn-scka-payloads ws)))
         (oc (fn-ock-recover-extended (mv-nth 0 r) configs frontier max-conns)))
    (implies (and (true-listp ws)
                  (not (equal (fn-scka-intern-at (append ws vs) (fn-stxk-initial-context 0) 0) :bad))
                  (fn-o1-records-filed-or-reclaimedp (fn-bpr-article-records (append ws vs))))
             (fn-o1-files-invp (fn-sn-files (fn-own-store (fn-ocfg-owner oc))) (mv-nth 1 r))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d () (fn-scka-recover-rows fn-scka-intern-at fn-sco-capture fn-scka-full-recover fn-o1-files-invp fn-o1-records-filed-or-reclaimedp fn-bpr-article-records fn-ock-recover-extended fn-own-store fn-ocfg-owner fn-sn-files))
           :use ((:instance fn-scka-recover-from-checkpoint-is-full-recover-with-arena (fn-arena (fn-scka-payloads ws)))
                 (:instance fn-o1-reopen-keeps-the-history (ws (append ws vs)))))))

(local
 (defthm o1l-composites-car-cdr
   (implies (and (consp rows) (fn-rows-composites-okp rows fn-arena))
            (and (fn-row-composite-okp (car rows) fn-arena) (fn-rows-composites-okp (cdr rows) fn-arena)))
   :hints (("Goal" :expand ((fn-rows-composites-okp rows fn-arena))))))

(local
 (defthm o1l-wire-of-articles-is-history-articles
   (implies (fn-rows-composites-okp rows fn-arena)
            (equal (fn-rows-wire-of (fn-bpr-article-records rows) fn-arena)
                   (fn-cat-history-articles rows fn-arena)))
   :hints (("Goal" :induct (len rows)
            :in-theory (e/d (fn-rows-wire-of fn-cat-history-articles o1l-article-records-cons)
                            (fn-row-wire-of fn-bpr-event-article fn-cat-history-article fn-row-composite-okp fn-rows-composites-okp
                             o1l-composites-car-cdr o1l-article-alpha2 fn-bpr-event-article-over-alpha)))
           ("Subgoal *1/1" :use (o1l-composites-car-cdr
                                 (:instance o1l-article-alpha2 (row (car rows)))
                                 (:instance fn-bpr-event-article-over-alpha (row (car rows))))))))

(defthm fn-o1-journal-of-the-history
  (implies (fn-o1-rows-invp rows fn-arena)
           (fn-o1-records-filed-or-reclaimedp
            (fn-bpr-article-records (fn-rows-wire-of rows fn-arena))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-o1-rows-invp) (fn-bpr-article-records fn-rows-wire-of fn-cat-history-articles fn-rows-composites-okp fn-o1-records-filed-or-reclaimedp o1l-wire-of-articles-is-history-articles))
           :use ((:instance fn-bpr-article-records-over-alpha) o1l-wire-of-articles-is-history-articles))))

(local
 (defthm o1l-load-held-row-positional
   (implies (fn-o1-cat-positionalp fn-cat)
            (fn-o1-cat-positionalp (fn-sca-load-held-row r view-index fn-cat)))
   :hints (("Goal" :in-theory (disable fn-o1-cat-positionalp fn-cat-commit fn-midx-lookup fn-held-with-withdrawn)
            :use ((:instance fn-o1-commit-keeps-the-catalog-positional (h r))
                  (:instance fn-o1-commit-keeps-the-catalog-positional (h (fn-hstxa-held r)))
                  (:instance fn-o1-commit-keeps-the-catalog-positional (h (fn-held-with-withdrawn r (cons (fn-cat-count fn-cat) 0))))
                  (:instance fn-o1-commit-keeps-the-catalog-positional (h (fn-held-with-withdrawn (fn-hstxa-held r) (cons (fn-cat-count fn-cat) 0)))))))))

(local
 (defthm o1l-load-available-row-positional
   (implies (fn-o1-cat-positionalp fn-cat)
            (fn-o1-cat-positionalp (fn-sca-load-held-available-row r view-index fn-arena fn-cat)))
   :hints (("Goal" :in-theory (disable fn-o1-cat-positionalp fn-sca-load-held-row)
            :use ((:instance o1l-load-held-row-positional (r (fn-cat-prepare-row-availability r fn-arena)))
                  (:instance o1l-load-held-row-positional (r (fn-cat-prepare-row-availability (fn-hstxa-held r) fn-arena))))))))

(local
 (defthm o1l-load-available-from-positional
   (implies (fn-o1-cat-positionalp fn-cat)
            (fn-o1-cat-positionalp (fn-sca-load-held-available-from rows view-index fn-arena fn-cat)))
   :hints (("Goal" :induct (fn-sca-load-held-available-from rows view-index fn-arena fn-cat)
            :in-theory (disable fn-o1-cat-positionalp fn-sca-load-held-available-row))
           ("Subgoal *1/2" :use ((:instance o1l-load-available-row-positional (r (car rows))))))))

(defthm fn-o1-load-makes-the-catalog-positional
  (fn-o1-cat-positionalp (fn-sca-load-held-rows rows view-index fn-arena fn-cat))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-o1-cat-positionalp fn-sca-load-held-available-from fn-cat-clear)
           :use ((:instance o1l-load-available-from-positional (fn-cat (fn-cat-clear fn-cat)))
                 fn-o1-clear-makes-the-catalog-positional))))

(defthm fn-o1-installed-catalog-rows-are-reclaimed-or-within-header
  (implies (and (fn-arena-p fn-arena)
                (fn-sf-record-valuesp rows)
                (fn-o1-rows-invp rows fn-arena))
           (let ((article (fn-cat-row-article
                           i fn-arena (fn-sca-load-held-rows rows view-index fn-arena fn-cat))))
             (or (fn-nntp-article-tombstonep article fn-arena)
                 (fn-o1-article-within-headerp
                  article (fn-nntp-article-bytes article fn-arena)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-o1-rows-invp) (fn-cat-row-article fn-o1-article-within-headerp fn-nntp-article-bytes fn-nntp-article-tombstonep
                                                   fn-sca-load-held-rows fn-cat-history-articles fn-rows-composites-okp fn-rows-handles-inp
                                                   fn-o1-records-filed-or-reclaimedp fn-o1-cat-positionalp fn-cat-history-relation))
           :use ((:instance fn-o1-catalog-rows-are-reclaimed-or-within-header
                            (records (fn-cat-history-articles rows fn-arena))
                            (fn-cat (fn-sca-load-held-rows rows view-index fn-arena fn-cat)))
                 (:instance fn-sca-load-held-rows-establishes-relation)
                 fn-o1-load-makes-the-catalog-positional))))
