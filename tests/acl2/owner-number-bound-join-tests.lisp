; Teeth for books/owner-number-bound-join.lisp (lane join-f2-8, PRF-958,
; PKT-615's follow-up, NNT-057).  The fixtures are owner-number-bound-tests'
; (the composite of acceptance-stamp-tests finished to :ready, and the same
; Store with a watermark past RFC 3977 section 6's bound).  onbjt- is this
; book's prefix.
(in-package "ACL2")
(include-book "owner-number-bound-tests")
(include-book "../../books/owner-number-bound-join")

; fn-onb-boundp is proof vocabulary (defun-nx); its executable body, proved
; equal to it, is what the witnesses evaluate.
(defun onbjt-boundp (o)
  (and (onbt-node-boundp (fn-sn-node (fn-own-store o)))
       (onbt-inflight-fitp (fn-own-store o))
       (fn-nntp-nexts-boundedp (fn-state-nexts (fn-own-view-archive (fn-own-view o))))))

(defthm onbjt-boundp-is-onb-boundp
  (equal (onbjt-boundp o) (fn-onb-boundp o))
  :hints (("Goal" :in-theory (e/d (fn-onb-boundp fn-onb-store-boundp)
                                  (onbt-node-boundp onbt-inflight-fitp fn-nntp-nexts-boundedp)))))

; KEYSTONE fn-onbj-open-okp-is-boundp-when-idle.  Reachable positive
; witness: the finished Store (:ready, idle) as an owner: its premise holds,
; and the open's check and the bound both hold.  The damaged Store (idle):
; both fail -- the open refuses exactly it.
(assert-event (fn-own-store-idlep (fn-own-store *onbt-open-owner*)))
(assert-event (fn-onb-open-okp *onbt-open-owner*))
(assert-event (onbjt-boundp *onbt-open-owner*))
(assert-event (fn-own-store-idlep (fn-own-store *onbt-open-owner-over*)))
(assert-event (not (fn-onb-open-okp *onbt-open-owner-over*)))
(assert-event (not (onbjt-boundp *onbt-open-owner-over*)))
; Hypothesis removal (the idle store): the composite's Store at :completing
; as an owner is not idle; it is bound (the composite in flight fits), yet
; the open's check refuses it -- without the premise the equation fails.
(snbt-defconst *onbjt-completing-owner*
  (fn-own-make *ast-composite-completing* nil nil 0 0 nil nil 0 nil nil nil nil nil nil nil))
(assert-event (not (fn-own-store-idlep (fn-own-store *onbjt-completing-owner*))))
(assert-event (onbjt-boundp *onbjt-completing-owner*))
(assert-event (not (fn-onb-open-okp *onbjt-completing-owner*)))

; fn-onbj-extend-nexts-bounded (the configure keystone's node step,
; fn-onbj-boundp-at-owner-reconfigure-complete).  Reachable positive
; witness: a grown domain keeps the watermark a group has and starts a new
; group at 1, within the bound.  Hypothesis removal: a watermark past the
; bound stays past it.
(defconst *onbjt-nexts* (list (cons "stamp.test" 5)))
(assert-event (fn-nntp-nexts-boundedp *onbjt-nexts*))
(assert-event (equal (fn-cnode-extend-nexts '("stamp.test" "new.group") *onbjt-nexts*)
                     '(("stamp.test" . 5) ("new.group" . 1))))
(assert-event (fn-nntp-nexts-boundedp (fn-cnode-extend-nexts '("stamp.test" "new.group") *onbjt-nexts*)))
(defconst *onbjt-nexts-over* (list (cons "stamp.test" (+ 1 *fn-nntp-max-article-number*))))
(assert-event (not (fn-nntp-nexts-boundedp *onbjt-nexts-over*)))
(assert-event (not (fn-nntp-nexts-boundedp (fn-cnode-extend-nexts '("stamp.test" "new.group") *onbjt-nexts-over*))))

; fn-onbj-store-boundp-of-known-abort (fn-onbj-boundp-at-owner-known-abort):
; the store after the abort is at :ready, where nothing is in flight
; (fn-onbj-inflight-fitp-when-ready): the finished Store.
(assert-event (onbt-inflight-fitp *onbt-ready*))
