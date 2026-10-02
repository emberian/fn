;; fn: the relay transfer decision (IHAVE, TAKETHIS, BP transit) with its two
;; store-wide tests answered by the owner's indexes (lane served-incremental-1,
;; audit-incremental-2026-10-02 I1).
;;
;; fn-peer-decide-transfer (books/peer-inbound.lisp) asks, per transferred
;; article, fn-peer-history-hasp -- fn-acceptedp over every accepted article
;; plus fn-node-find-binding over every binding -- and fn-retain-admissiblep,
;; whose known-id test walks every pin and release: O(N + P + R) per article,
;; so a feed of N articles is O(N^2) to ingest.  The owner already carries
;; both indexes for POST: the catalog's Message-ID column read at the owner's
;; view (books/post-identity-catalog.lisp fn-pidx-find-article-cat, KEYSTONE
;; fn-pidx-find-article-cat-is-find-article) and the carried id trie
;; (books/post-retain-carried.lisp fn-prc-admissiblep, KEYSTONE
;; fn-prc-admissiblep-is-admissiblep).  This book is the decision with those
;; two calls replaced, and its equation with the reference.  Under the node
;; invariant a binding names an accepted article
;; (books/peer-offer-indexed.lisp fn-pix-peer-history-hasp-is-acceptedp), so
;; the history is the article list's Message-ID test alone.
;;
;; GEN: a twin of fn-peer-decide-transfer with two calls replaced; when the
;; reference takes its history and admission tests as arguments the twin
;; goes (NEXT in the lane dump).
(in-package "ACL2")
(include-book "peer-offer-indexed")
(include-book "post-identity-catalog")
(include-book "post-retain-carried")

(local (in-theory (disable (tau-system))))

(local
 (defthm fn-pti-nil-article-has-no-string-msgid
   (not (stringp (fn-article-msgid nil)))
   :hints (("Goal" :in-theory (enable fn-article-msgid)))))

(local
 (defthm fn-pti-find-article-iff-accepted
   (implies (stringp m)
            (iff (fn-find-article m as) (fn-acceptedp m as)))
   :hints (("Goal" :in-theory (enable fn-find-article fn-acceptedp)))))

;; The history test: one Message-ID column probe at the owner's view.
(defun fn-peer-history-hasp-cat (msgid node view fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (fn-node-statep node)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))))
  (if (stringp msgid)
      (if (fn-pidx-find-article-cat msgid (fn-state-articles (fn-node-acceptance node))
                                    view fn-arena fn-cat)
          t
        nil)
    (fn-peer-history-hasp msgid node)))

(defthm fn-peer-history-hasp-cat-is-history-hasp
  (implies (and (fn-node-statep node)
                (fn-ocl-view-visiblep view)
                (fn-scj-joinp view fn-arena fn-cat))
           (equal (fn-peer-history-hasp-cat msgid node view fn-arena fn-cat)
                  (fn-peer-history-hasp msgid node)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-peer-history-hasp-cat fn-pix-peer-history-hasp-is-acceptedp)
                           (fn-peer-history-hasp fn-node-statep fn-acceptedp fn-find-article
                            fn-pidx-find-article-cat fn-ocl-view-visiblep fn-scj-joinp))
           :use ((:instance fn-pidx-find-article-cat-is-find-article
                            (arts (fn-state-articles (fn-node-acceptance node))))
                 (:instance fn-pti-find-article-iff-accepted
                            (m msgid) (as (fn-state-articles (fn-node-acceptance node))))))))

(in-theory (disable fn-peer-history-hasp-cat))

(defun fn-peer-decide-transfer-cat (node cfg peer msgid octets clock id subject
                                         view carry fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (fn-node-statep node)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :verify-guards nil))
  (let* ((record (fn-cfg-peer-find peer (fn-cfg-peers (fn-cfg-value cfg))))
         (parsed (fn-article-parse octets))
         (article (if (and (fn-article-result-okp parsed)
                           (true-listp parsed))
                      (fn-article-result-article parsed)
                    nil))
         (okp (and article (fn-article-syntax-p article)))
         ; RFC 5537 section 3.6 step 1 is the RELAYING agent's check, and
         ; that is what this is. The injecting agent's check of section
         ; 3.4.1 refuses an article carrying Injection-Info, which every
         ; injected article carries, so applying it here refused EVERY offer
         ; of an article any node had posted -- `:refuse :proto-article` on
         ; the first transfer between two fn nodes, every time.
         (check (if okp (fn-af-relayed-article-check article) nil)))
    (cond ((not record) (fn-peer-decision :refuse :not-a-peer))
          ((null (fn-cfg-peer-inbound record))
           (fn-peer-decision :refuse :no-inbound))
          ((not (fn-af-message-idp msgid))
           (fn-peer-decision :refuse :message-id-syntax))
          ((< (fn-cfg-peer-inbound-max-octets record) (len octets))
           (fn-peer-decision :refuse :oversize))
          ; 3.6 steps 1 and 4 and the proto-article check: the refusals the
          ; octets decide (PRF-235, PRF-236; the arms are
          ; fn-peer-intrinsic-refusal-of's).
          ((fn-peer-intrinsic-refusal-of msgid okp article check
                                         (fn-peer-parse-limitp parsed octets))
           (fn-peer-decision :refuse
                             (fn-peer-intrinsic-refusal-of msgid okp article
                                                           check
                                                           (fn-peer-parse-limitp parsed octets))))
          ; 3.6 step 2: more than the operator's margin (at most 24 hours)
          ; into the future (PRF-236).
          ((fn-peer-date-futurep article cfg clock)
           (fn-peer-decision :refuse :date-future))
          ; 3.6 step 4: Path, when the operator requires it (PRF-236).
          ((fn-peer-path-missingp article cfg)
           (fn-peer-decision :refuse :no-path))
          ; 3.6 step 3 / 3.7 step 3: already accepted.  Re-checked here
          ; because the offer may be stale (RFC 4644 section 2.4.2).
          ((fn-peer-history-hasp-cat (fn-record-octets-string msgid) node view fn-arena fn-cat)
           (fn-peer-decision :have :history))
          ; Loop: our own path identity already in Path (section 2.3).
          ((fn-path-names-p (fn-af-path-field-value article)
                            (fn-peer-local-identity cfg))
           (fn-peer-decision :refuse :loop))
          ; Scope: at least one Newsgroups name accepted from this peer and
          ; live now.
          ((null (fn-peer-scope-groups (fn-peer-check-groups check) record cfg))
           (fn-peer-decision :refuse :out-of-scope))
          ; P3: a group it would be stored under is moderated here and the
          ; article carries no Approved header field (RFC 5537 sections
          ; 3.6 item 6 and 3.7 item 5): refused by name, never stored.
          ((and (fn-peer-moderated-namesp
                 (fn-peer-scope-groups (fn-peer-check-groups check) record cfg)
                 (fn-cfg-value cfg) (fn-cfg-generation cfg))
                (fn-inj-absentp article *fn-mod-approved-name*))
           (fn-peer-decision :refuse :unapproved-moderated))
          ; RFC 5537 section 3.6 step 7: the Path update is part of
          ; accepting the article.  If the updated article no longer fits
          ; the article bounds (books/article.lisp: a header line, the
          ; header block or the article grew past its limit), the article
          ; "MUST be rejected rather than modified" (section 3.6, last
          ; paragraph) -- it is refused, never stored without the update.
          ((not (fn-article-result-okp
                 (fn-article-parse (fn-peer-relayed-octets cfg peer octets))))
           (fn-peer-decision :refuse :oversize))
          ((fn-peer-stagedp (fn-record-octets-string msgid) node)
           (fn-peer-decision :defer :staged))
          ((consp (fn-node-stage node)) (fn-peer-decision :defer :busy))
          ((equal (fn-state-fenced (fn-node-acceptance node)) t)
           (fn-peer-decision :defer :fenced))
          ; Local policy: capacity at transfer time, the bytes having
          ; arrived, is a refusal (RFC 3977 section 6.3.2.2 lists disc space).
          ; The charge is the stored payload's: the updated article.
          ((not (fn-prc-admissiblep
                 (fn-node-retention node) id subject
                 :archive (fn-peer-evidence peer cfg)
                 (fn-charge-for-payload
                  (len (fn-peer-relayed-octets cfg peer octets)))
                 carry))
           (fn-peer-decision :refuse :capacity))
          (t (fn-peer-decision :want nil)))))

(defthm fn-peer-decide-transfer-cat-is-decide-transfer
  (implies (and (fn-node-statep node)
                (fn-ocl-view-visiblep view)
                (fn-scj-joinp view fn-arena fn-cat)
                (fn-prc-carryp carry))
           (equal (fn-peer-decide-transfer-cat node cfg peer msgid octets clock id subject
                                               view carry fn-arena fn-cat)
                  (fn-peer-decide-transfer node cfg peer msgid octets clock id subject)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-peer-decide-transfer-cat fn-peer-decide-transfer)
                           (fn-node-statep fn-ocl-view-visiblep fn-scj-joinp fn-prc-carryp
                            fn-peer-history-hasp fn-retain-admissiblep fn-prc-admissiblep
                            fn-article-parse fn-peer-relayed-octets fn-peer-intrinsic-refusal-of
                            fn-peer-scope-groups fn-peer-date-futurep fn-peer-path-missingp
                            fn-af-relayed-article-check fn-peer-decision)))))

;; The host-called form (host/owner-host.lisp fn-owner-transit-decide through
;; fn-pta-decide; the owner's BP transit): under the store profile's header
;; limits, as fn-peer-decide-transfer-under.
(defun fn-peer-decide-transfer-under-cat
    (node cfg peer msgid octets clock id subject limits view carry fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (fn-node-statep node)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :verify-guards nil))
  (let ((d (fn-peer-decide-transfer-cat node cfg peer msgid octets clock id
                                        subject view carry fn-arena fn-cat)))
    (if (member-equal (fn-peer-decision-kind d) '(:want :defer))
        (let ((limit (fn-peer-header-limit-refusal cfg peer octets limits)))
          (if limit (fn-peer-decision :refuse limit) d))
      d)))

(defthm fn-peer-decide-transfer-under-cat-is-under
  (implies (and (fn-node-statep node)
                (fn-ocl-view-visiblep view)
                (fn-scj-joinp view fn-arena fn-cat)
                (fn-prc-carryp carry))
           (equal (fn-peer-decide-transfer-under-cat node cfg peer msgid octets clock id
                                                     subject limits view carry fn-arena fn-cat)
                  (fn-peer-decide-transfer-under node cfg peer msgid octets clock id
                                                 subject limits)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-peer-decide-transfer-under-cat fn-peer-decide-transfer-under)
                           (fn-peer-decide-transfer-cat fn-peer-decide-transfer
                            fn-node-statep fn-ocl-view-visiblep fn-scj-joinp fn-prc-carryp
                            fn-peer-header-limit-refusal fn-peer-decision)))))

(in-theory (disable fn-peer-decide-transfer-cat fn-peer-decide-transfer-under-cat))
