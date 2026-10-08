; fn: the IHAVE/CHECK duplicate test.
;
; fn-peer-decide-offer (books/peer-inbound.lisp) decides "already have it"
; with fn-peer-history-hasp: fn-acceptedp, a scan of the node's article list,
; then fn-node-find-binding, a scan of its bindings -- O((N + B) * L) per
; offer.  fn-pix-history-hasp is the test with the article list it is asked
; of passed alongside: when the session's node holds exactly that list the
; answer is the specification's lookup, fn-find-article (the served step
; answers it from the catalog's Message-ID column, books/served-catalog-chain
; fn-scr-history-hasp).  Otherwise it is the scan, unchanged.
;
; The keystone is fn-pix-history-hasp-is-peer-history-hasp: under
; fn-node-statep of the node, the test is the scan, for every Message-ID.  The
; node premise is used once, for the bindings: every binding's Message-ID is
; an article's (fn-node-statep's fn-subsetp conjunct), so the binding scan
; adds nothing the article scan has not answered.

(in-package "ACL2")
(include-book "peer-inbound")
(include-book "protocol-table") ; reply texts: (fn-proto-text ROW KEY)
(include-book "msgid-index")

; -----------------------------------------------------------------------------
; The history test

; The fast path is taken only when the session node's article list IS the
; list the answer is asked of (ARTS).  The owner's fn-own-refresh stores the
; store node's own acceptance in the view, so after a refresh the two are the
; same object and Common Lisp's EQUAL answers on its first pointer
; comparison.  The answer there is the specification's lookup,
; fn-find-article (the served step reads the catalog's column for it:
; books/served-catalog-chain.lisp fn-scr-history-hasp).
(defun fn-pix-history-hasp (msgid node arts)
  (declare (xargs :guard t))
  (if (and (stringp msgid)
           (< 0 (length msgid))
           (equal (fn-state-articles (fn-node-acceptance node)) arts))
      (if (fn-find-article msgid arts) t nil)
    (fn-peer-history-hasp msgid node)))

(local (defthm fn-pix-binding-found-is-member
  (implies (consp (fn-node-find-binding m bs))
           (member-equal m (fn-node-binding-msgids bs)))
  :hints (("Goal" :in-theory (enable fn-node-find-binding
                                     fn-node-binding-msgids)))))

(local (defthm fn-pix-member-of-subset
  (implies (and (member-equal m xs) (fn-subsetp xs ys))
           (member-equal m ys))
  :hints (("Goal" :in-theory (enable fn-subsetp)))))

(local (defthm fn-pix-member-msgids-is-accepted
  (iff (member-equal m (fn-article-msgids as))
       (fn-acceptedp m as))
  :hints (("Goal" :in-theory (enable fn-article-msgids fn-acceptedp)))))

(local (defthm fn-pix-nil-article-has-no-string-msgid
  (not (stringp (fn-article-msgid nil)))
  :hints (("Goal" :in-theory (enable fn-article-msgid)))))

(local (defthm fn-pix-find-article-iff-accepted
  (implies (stringp m)
           (iff (fn-find-article m as)
                (fn-acceptedp m as)))
  :hints (("Goal" :in-theory (enable fn-find-article fn-acceptedp)))))

; Under the node invariant the history is the article list: a binding names
; an accepted article.  (fn-node-statep's bindings conjunct.)
(defthm fn-pix-peer-history-hasp-is-acceptedp
  (implies (fn-node-statep node)
           (equal (fn-peer-history-hasp msgid node)
                  (fn-acceptedp msgid (fn-state-articles
                                       (fn-node-acceptance node)))))
  :hints (("Goal" :in-theory (e/d (fn-peer-history-hasp fn-node-statep)
                                  (fn-node-binding-listp fn-statep
                                   fn-retain-statep
                                   fn-node-articles-have-archive-bindingsp
                                   fn-node-stagep))
           :use ((:instance fn-pix-binding-found-is-member
                            (m msgid) (bs (fn-node-bindings node)))
                 (:instance fn-pix-member-of-subset
                            (m msgid)
                            (xs (fn-node-binding-msgids (fn-node-bindings node)))
                            (ys (fn-article-msgids
                                 (fn-state-articles (fn-node-acceptance node)))))
                 (:instance fn-pix-member-msgids-is-accepted
                            (m msgid)
                            (as (fn-state-articles (fn-node-acceptance node))))))))

; KEYSTONE.  The history test with the specification's lookup is the scan,
; for every Message-ID.
(defthm fn-pix-history-hasp-is-peer-history-hasp
  (implies (fn-node-statep node)
           (equal (fn-pix-history-hasp msgid node arts)
                  (fn-peer-history-hasp msgid node)))
  :hints (("Goal" :in-theory (e/d (fn-pix-history-hasp)
                                  (fn-peer-history-hasp fn-node-statep fn-find-article))
           :use ((:instance fn-pix-find-article-iff-accepted
                            (m msgid) (as arts))))))

; -----------------------------------------------------------------------------
; The offer decision, the transit commands and the pinned peer step that
; used this test are fn-pgc-decide-offer, fn-pgc-peer-command and
; fn-pgc-peer-arm (books/peer-guard-carried.lisp), which the served step
; reaches (books/served-carried.lisp fn-scar-peer-step-pinned).  The fn-pix-
; copies no caller reached were deleted (assurance-hygiene-6, PKT-075).

(in-theory (disable fn-pix-history-hasp))
