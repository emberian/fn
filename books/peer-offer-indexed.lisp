; fn: the IHAVE/CHECK duplicate test answered from the Message-ID trie.
;
; fn-peer-decide-offer (books/peer-inbound.lisp) decides "already have it"
; with fn-peer-history-hasp: fn-acceptedp, a scan of the node's article list,
; then fn-node-find-binding, a scan of its bindings -- O((N + B) * L) per
; offer.  The owner already maintains a trie over its committed view's
; articles (fn-own-view-index, refreshed by fn-own-refresh through
; fn-midx-refresh; books/msgid-index.lisp).  This book is the peer step with
; that trie and the article list it was built from passed alongside, and the
; history test answered by one fn-midx-lookup when the session's node holds
; exactly that article list.  Otherwise it is the scan, unchanged.
;
; The keystone is fn-pix-history-hasp-is-peer-history-hasp: under the trie's
; correspondence to the list and fn-node-statep of the node, the indexed test
; is the scan, for every Message-ID.  The node premise is used once, for the
; bindings: every binding's Message-ID is an article's (fn-node-statep's
; fn-subsetp conjunct), so the binding scan adds nothing the article scan
; has not answered.  Each copy below is proved EQUAL to its reference under
; the correspondence alone; the peer step's own fn-peer-sessionp test
; supplies fn-node-statep, exactly as the reference's guard needs it.

(in-package "ACL2")
(include-book "peer-inbound")
(include-book "msgid-index")

; -----------------------------------------------------------------------------
; The history test

; The fast path is taken only when the session node's article list IS the
; list the trie was built from.  The owner's fn-own-refresh stores the store
; node's own acceptance in the view, so after a refresh the two are the same
; object and Common Lisp's EQUAL answers on its first pointer comparison.
(defun fn-pix-history-hasp (msgid node trie arts)
  (declare (xargs :guard t))
  (if (and (stringp msgid)
           (consp (fn-midx-key-chars msgid))
           (equal (fn-state-articles (fn-node-acceptance node)) arts))
      (if (fn-midx-lookup msgid trie) t nil)
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

; KEYSTONE.  The indexed history test is the scan, for every Message-ID,
; whenever the trie is the one built from the list it is keyed to.
(defthm fn-pix-history-hasp-is-peer-history-hasp
  (implies (and (fn-node-statep node)
                (fn-midx-correspondencep trie arts))
           (equal (fn-pix-history-hasp msgid node trie arts)
                  (fn-peer-history-hasp msgid node)))
  :hints (("Goal" :in-theory (e/d (fn-pix-history-hasp
                                   fn-midx-correspondencep)
                                  (fn-peer-history-hasp fn-node-statep
                                   fn-midx-lookup fn-midx-build
                                   fn-midx-key-chars))
           :use ((:instance fn-midx-lookup-of-build-is-find-article-for-nonempty
                            (articles arts))))))

; -----------------------------------------------------------------------------
; The offer decision, the transit commands and the pinned peer step, each the
; reference with the history test above.

(defun fn-pix-decide-offer (node cfg peer session msgid clock inflight trie arts)
  (declare (xargs :guard (fn-node-statep node) :verify-guards nil)
           (ignorable session clock))
  (let ((record (fn-cfg-peer-find peer (fn-cfg-peers (fn-cfg-value cfg)))))
    (cond ((not record) (fn-peer-decision :refuse :not-a-peer))
          ((null (fn-cfg-peer-inbound record))
           (fn-peer-decision :refuse :no-inbound))
          ((not (fn-af-message-idp msgid))
           (fn-peer-decision :refuse :message-id-syntax))
          ((fn-pix-history-hasp (fn-record-octets-string msgid) node trie arts)
           (fn-peer-decision :have :history))
          ((fn-peer-stagedp (fn-record-octets-string msgid) node)
           (fn-peer-decision :defer :staged))
          ((equal (fn-state-fenced (fn-node-acceptance node)) t)
           (fn-peer-decision :defer :fenced))
          ((<= (fn-cfg-peer-inbound-max-inflight record) (nfix inflight))
           (fn-peer-decision :defer :inflight-limit))
          ((not (fn-retain-admissiblep (fn-node-retention node)
                                       (fn-peer-probe-obligation-id msgid)
                                       (fn-peer-probe-subject) :archive
                                       (fn-peer-evidence peer cfg)
                                       (fn-charge-for-payload 0)))
           (fn-peer-decision :defer :capacity))
          (t (fn-peer-decision :want nil)))))

(defthm fn-pix-decide-offer-is-peer-decide-offer
  (implies (and (fn-node-statep node)
                (fn-midx-correspondencep trie arts))
           (equal (fn-pix-decide-offer node cfg peer session msgid clock
                                       inflight trie arts)
                  (fn-peer-decide-offer node cfg peer session msgid clock
                                        inflight)))
  :hints (("Goal" :in-theory (e/d (fn-pix-decide-offer fn-peer-decide-offer)
                                  (fn-pix-history-hasp fn-peer-history-hasp
                                   fn-node-statep fn-midx-correspondencep
                                   fn-peer-stagedp fn-retain-admissiblep
                                   fn-cfg-peer-find fn-af-message-idp
                                   fn-record-octets-string)))))

(local (defthm fn-pix-transferp-forward
  (implies (and (fn-peer-transferp x) x)
           (and (consp x) (consp (cdr x))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d ((:d fn-peer-transferp))
                                  ((:d fn-nntp-printable-tokenp)
                                   (:d fn-af-message-idp)))))))

(verify-guards fn-pix-decide-offer
  :hints (("Goal" :in-theory (disable (:d fn-node-statep) (:d fn-statep)
                                      (:d fn-retain-statep)
                                      (:d fn-node-state-shapep)
                                      (:d fn-cfgp) (:d fn-cfg-peer-find)
                                      (:d fn-af-message-idp)
                                      (:d fn-pix-history-hasp)
                                      (:d fn-peer-stagedp)
                                      (:d fn-retain-admissiblep)
                                      (:d fn-peer-evidence)
                                      (:d fn-record-octets-string)
                                      (:d fn-cfg-peer-inbound)
                                      (:d fn-cfg-peer-inbound-groups)
                                      (:d fn-cfg-peer-inbound-max-octets)
                                      (:d fn-cfg-peer-inbound-max-inflight)
                                      (:d fn-cfg-ag-car) (:d fn-cfg-ag-cdr)))))

(defun fn-pix-peer-command (ps keyword args trie arts)
  (declare (xargs :guard (and (fn-peer-sessionp ps) (fn-peer-session-peer ps))
                  :verify-guards nil))
  (let ((node (fn-peer-session-node ps))
        (cfg (fn-peer-session-cfg ps))
        (peer (fn-peer-session-peer ps))
        (inflight (fn-peer-session-inflight ps)))
    (cond
     ((fn-nntp-keywordp keyword "IHAVE")
      (if (not (fn-peer-msgid-argp args))
          (fn-post-make-result ps (fn-peer-single ps "501 syntax error") nil)
        (let ((d (fn-pix-decide-offer node cfg peer ps (car args) nil inflight
                                      trie arts)))
          (if (equal (fn-peer-decision-kind d) :want)
              (fn-post-make-result
               (fn-peer-with-transfer ps (list :ihave (car args)) inflight)
               (append (fn-peer-single ps (fn-peer-ihave-offer-line d))
                       (list (fn-nntp-begin-article-effect)))
               nil)
            (fn-post-make-result ps (fn-peer-single ps (fn-peer-ihave-offer-line d))
                                 nil)))))
     ((fn-nntp-keywordp keyword "CHECK")
      (if (not (fn-peer-msgid-argp args))
          (fn-post-make-result ps (fn-peer-single ps "501 syntax error") nil)
        (let ((d (fn-pix-decide-offer node cfg peer ps (car args) nil inflight
                                      trie arts)))
          (fn-post-make-result
           (if (equal (fn-peer-decision-kind d) :want)
               (fn-peer-with-transfer ps nil (+ 1 (nfix inflight)))
             ps)
           (fn-peer-echo-reply (fn-peer-check-code d) (car args))
           nil))))
     (t (fn-peer-command ps keyword args)))))

; The IHAVE and CHECK arms are the only ones that decide an offer; every
; other keyword is the reference's own arm, reached by the fall-through.
(defthm fn-pix-peer-command-is-peer-command
  (implies (and (fn-peer-sessionp ps)
                (fn-peer-session-peer ps)
                (fn-midx-correspondencep trie arts))
           (equal (fn-pix-peer-command ps keyword args trie arts)
                  (fn-peer-command ps keyword args)))
  :hints (("Goal" :in-theory (e/d (fn-pix-peer-command fn-peer-command)
                                  (fn-pix-decide-offer fn-peer-decide-offer
                                   fn-peer-sessionp fn-midx-correspondencep
                                   fn-nntp-keywordp fn-peer-msgid-argp
                                   fn-peer-single fn-peer-echo-reply
                                   fn-peer-ihave-offer-line fn-peer-check-code
                                   fn-peer-with-transfer fn-peer-capability-lines))
           :use ((:instance fn-pix-decide-offer-is-peer-decide-offer
                            (node (fn-peer-session-node ps))
                            (cfg (fn-peer-session-cfg ps))
                            (peer (fn-peer-session-peer ps))
                            (session ps) (msgid (car args)) (clock nil)
                            (inflight (fn-peer-session-inflight ps)))))))

(local (defthm fn-pix-msgid-argp-forward
  (implies (fn-peer-msgid-argp args)
           (and (consp args) (null (cdr args))
                (fn-nntp-printable-tokenp (car args))
                (fn-af-message-idp (car args))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-peer-msgid-argp)))))

(local (defthm fn-pix-peer-single-true-listp
  (true-listp (fn-peer-single ps text))
  :hints (("Goal" :in-theory (enable fn-peer-single fn-nntp-result-effects
                                     fn-nntp-single fn-nntp-make-result)))))

(verify-guards fn-pix-peer-command
  :hints (("Goal" :in-theory (disable fn-pix-decide-offer fn-peer-command
                                      fn-peer-single fn-peer-msgid-argp))))

(defun fn-pix-peer-step-pinned
    (ps trie arts archive index verdicts config observation injection wire-event)
  (declare (xargs :guard t :verify-guards nil))
  (cond
   ((not (fn-peer-sessionp ps)) (fn-post-make-result ps nil nil))
   ((null (fn-peer-session-peer ps))
    (fn-peer-delegate-pinned ps archive index verdicts config observation
                             injection wire-event))
   ((not (equal (fn-nntp-session-openp (fn-peer-reader-session ps)) t))
    (fn-peer-delegate-pinned ps archive index verdicts config observation
                             injection wire-event))
   ((fn-peer-session-transfer ps)
    (fn-peer-step ps archive config observation injection wire-event))
   ((and (consp wire-event)
         (equal (car wire-event) :command)
         (consp (cdr wire-event))
         (null (cdr (cdr wire-event)))
         (fn-nntp-command-inputp (car (cdr wire-event))))
    (let ((tokens (fn-nntp-tokenize (car (cdr wire-event)))))
      (if (and (consp tokens)
               (fn-nntp-keyword-tokenp (car tokens))
               (fn-nntp-command-arguments-at-mostp tokens))
          (let ((r (fn-pix-peer-command ps (car tokens) (cdr tokens) trie arts)))
            (if r r
              (fn-peer-delegate-pinned ps archive index verdicts config
                                       observation injection wire-event)))
        (fn-peer-delegate-pinned ps archive index verdicts config observation
                                 injection wire-event))))
   (t (fn-peer-delegate-pinned ps archive index verdicts config observation
                               injection wire-event))))

(defthm fn-pix-peer-step-pinned-is-peer-step-pinned
  (implies (fn-midx-correspondencep trie arts)
           (equal (fn-pix-peer-step-pinned ps trie arts archive index verdicts
                                           config observation injection
                                           wire-event)
                  (fn-peer-step-pinned ps archive index verdicts config
                                       observation injection wire-event)))
  :hints (("Goal" :in-theory (e/d (fn-pix-peer-step-pinned fn-peer-step-pinned)
                                  (fn-pix-peer-command fn-peer-command
                                   fn-peer-sessionp fn-midx-correspondencep
                                   fn-peer-delegate-pinned fn-peer-step
                                   fn-nntp-tokenize fn-nntp-command-inputp)))))

(verify-guards fn-pix-peer-step-pinned
  :hints (("Goal" :in-theory (disable fn-pix-peer-command fn-peer-command
                                      fn-peer-delegate-pinned fn-peer-step))))

(in-theory (disable fn-pix-history-hasp fn-pix-decide-offer
                    fn-pix-peer-command fn-pix-peer-step-pinned))
