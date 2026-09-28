; post-identity-catalog.lisp -- a POST's duplicate-versus-conflict test read
; from the catalog, not the owner's Message-ID trie (lane join-f2-midx, the
; fn-midx retirement; PRF-191's test with the lookup moved).
;
; books/post-identity-index.lisp answers the test the host asks before a
; prepare (fn-pidx-existing-action) through the view's trie, when the article
; list asked about is the view's raw list and no withdrawal record targets
; the Message-ID; otherwise it walks.  This book answers the same branch from
; the catalog's Message-ID column at its count (fn-scat-msgid-article,
; books/served-catalog.lisp), which the join (fn-scj-joinp, carried by the
; host's owner as a conjunct of fn-scj-invp inside fn-sjh-okp) makes the walk
; of the view's visible list.  An untargeted Message-ID is found alike in the
; visible list and the raw one (fn-pidx-find-in-visible-is-find), so the
; column answers the raw walk.
;
; KEYSTONE fn-pidx-existing-action-cat-is-store-existing-action: the host's
; call (host/owner-host.lisp fn-owner-existing-action-buffer and the
; pre-check of fn-owner-prepare-buffer) is the Store's duplicate entry,
; fn-store-existing-action, under the visible-list relation (fn-ocl-relation
; carries it) and the join; no trie hypothesis.

(in-package "ACL2")

(include-book "post-identity-index")
(include-book "served-catalog-join-conns")

(local (in-theory (enable (:definition fn-ctl-visible-articles))))

; fn-find-article MSGID ARTS through the catalog's Message-ID column when
; ARTS is the view's raw list and no withdrawal targets MSGID.
(defun fn-pidx-find-article-cat (msgid arts view fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)))
  (if (and (stringp msgid)
           (< 0 (length msgid))
           (equal arts (fn-own-view-raw view))
           (not (fn-pidx-targetedp msgid (fn-own-view-withdrawals view))))
      (fn-scat-msgid-article msgid (fn-cat-count fn-cat) fn-arena fn-cat)
    (fn-find-article msgid arts)))

; KEYSTONE (the lookup).
(defthm fn-pidx-find-article-cat-is-find-article
  (implies (and (fn-ocl-view-visiblep view)
                (fn-scj-joinp view fn-arena fn-cat))
           (equal (fn-pidx-find-article-cat msgid arts view fn-arena fn-cat)
                  (fn-find-article msgid arts)))
  :hints (("Goal" :in-theory (e/d (fn-pidx-find-article-cat fn-ocl-view-visiblep
                                   fn-scj-joinp fn-scat-msgid-article-is-find-article)
                                  (fn-scat-msgid-article fn-find-article fn-cat-view-articles
                                   fn-ctl-visible-filter fn-pidx-targetedp
                                   fn-scj-marks-below fn-scj-seqs-below))
           :use ((:instance fn-pidx-find-in-visible-is-find
                            (withdrawals (fn-own-view-withdrawals view))
                            (xs (fn-own-view-raw view)) (articles (fn-own-view-raw view))
                            (verdicts (fn-own-view-verdicts view)))))))

(in-theory (disable fn-pidx-find-article-cat))

(defun fn-pidx-existing-action-cat (msgid fn-octets groups o fn-arena fn-cat)
  ; fn-pidx-existing-action with the article found through the catalog.
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat)
                  :guard (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)))
  (let ((article (fn-pidx-find-article-cat
                  msgid
                  (fn-state-articles
                   (fn-node-acceptance (fn-sn-node (fn-own-store o))))
                  (fn-own-view o) fn-arena fn-cat)))
    (if article
        (if (and (fn-rclb-same-articlep (fn-record-string-octets msgid) fn-octets
                                        (fn-handle-bytes (fn-article-payload article)
                                                         fn-arena))
                 (equal groups (fn-article-groups article)))
            :duplicate
          :conflict)
      nil)))

; KEYSTONE.  The host's call is the Store's duplicate entry (as
; fn-pidx-existing-action-is-store-existing-action, with the join for the
; trie's correspondence).
(defthm fn-pidx-existing-action-cat-is-store-existing-action
  (implies (and (fn-ocl-view-visiblep (fn-own-view o))
                (fn-scj-joinp (fn-own-view o) fn-arena fn-cat)
                (fn-octets-p fn-octets))
           (equal (fn-pidx-existing-action-cat msgid fn-octets groups o fn-arena fn-cat)
                  (fn-store-existing-action msgid fn-octets groups
                                            (fn-own-store o) fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-pidx-existing-action-cat
                                   fn-store-existing-action
                                   fn-rclb-same-articlep fn-rcl-same-articlep)
                                  (fn-ocl-view-visiblep fn-scj-joinp
                                   fn-find-article
                                   fn-rclb-same-as-tombstonep fn-rcl-same-as-tombstonep
                                   fn-rcl-tombstonep fn-pbb-same-articlep fn-pb-same-articlep
                                   fn-octets-p fn-handle-bytes))
           :use ((:instance fn-pbb-same-articlep-is-pb-same-articlep
                            (msgid (fn-record-string-octets msgid))
                            (held-payload (fn-handle-bytes
                                           (fn-article-payload
                                            (fn-find-article msgid (fn-state-articles
                                                                    (fn-node-acceptance
                                                                     (fn-sn-node (fn-own-store o))))))
                                           fn-arena)))
                 (:instance fn-rclb-same-as-tombstonep-is-rcl
                            (msgid (fn-record-string-octets msgid))
                            (tomb (fn-handle-bytes
                                   (fn-article-payload
                                    (fn-find-article msgid (fn-state-articles
                                                            (fn-node-acceptance
                                                             (fn-sn-node (fn-own-store o))))))
                                   fn-arena)))))))

; The host's owner: fn-ocl-relation carries the visible list and
; fn-scj-invp the join.
(defthm fn-pidx-existing-action-cat-of-live-owner
  (implies (and (fn-ocl-relation oc)
                (fn-scj-invp (fn-ocfg-owner oc) fn-arena fn-cat)
                (fn-octets-p fn-octets))
           (equal (fn-pidx-existing-action-cat msgid fn-octets groups (fn-ocfg-owner oc)
                                               fn-arena fn-cat)
                  (fn-store-existing-action msgid fn-octets groups
                                            (fn-own-store (fn-ocfg-owner oc)) fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-ocl-relation fn-scj-invp)
                                  (fn-ocl-view-historyp fn-ocl-view-visiblep fn-scj-joinp
                                   fn-scj-rows-invp fn-scj-vvp fn-scj-live-okp fn-scj-conns-pinp
                                   fn-pidx-existing-action-cat fn-store-existing-action))
           :use ((:instance fn-ocl-view-historyp-is-visible (o (fn-ocfg-owner oc)))
                 (:instance fn-pidx-existing-action-cat-is-store-existing-action
                            (o (fn-ocfg-owner oc)))))))
