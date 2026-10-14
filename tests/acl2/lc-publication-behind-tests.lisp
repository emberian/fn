; Publication backpressure vocabulary and per-member release witnesses.
(in-package "ACL2")
(include-book "../../books/nntp-post")
(include-book "../../books/peer-inbound")
(include-book "../../books/owner-commit-steps")
(defconst *fn-lc-behind-text*
 "the log's publication is behind, nothing was stored (publication-behind); try again shortly")
(defconst *fn-lc-behind-peer*
 (fn-peer-make-session (fn-post-make-session (fn-nntp-make-session t nil nil t) nil)
                       "lc-peer" nil 0 nil nil nil))
(defconst *fn-lc-behind-id* (fn-nntp-string-octets "<lc@fn.test>"))
(assert-event (fn-post-store-refusalp :publication-behind))
(assert-event (equal (fn-post-store-refusal-text :publication-behind) *fn-lc-behind-text*))
(assert-event (equal (fn-post-store-refusal-line :publication-behind)
                    (string-append "441 posting failed; " *fn-lc-behind-text*)))
; Both commands are transient 436, even when the admission decision refused.
(assert-event
 (and (equal (fn-peer-transit-code :ihave (fn-peer-decision :refuse :loop) :publication-behind) 436)
      (equal (fn-peer-transit-code :takethis (fn-peer-decision :refuse :loop) :publication-behind) 436)
      (not (member-equal (fn-peer-transit-code :ihave (fn-peer-decision :want nil) :publication-behind) '(437 439)))
      (not (member-equal (fn-peer-transit-code :takethis (fn-peer-decision :want nil) :publication-behind) '(437 439)))))
(with-guard-checking-event nil
 (assert-event
  (equal (fn-peer-transit-outcome-effects *fn-lc-behind-peer*
           (fn-peer-make-submission "lc-peer" :ihave *fn-lc-behind-id* nil)
           (fn-peer-decision :want nil) :publication-behind)
         (list (fn-nntp-reply-effect
                (fn-nntp-crlf (fn-nntp-string-octets
                              (string-append "436 retry later; " *fn-lc-behind-text*))))))))
(with-guard-checking-event nil
 (assert-event
  (equal (fn-peer-transit-outcome-effects *fn-lc-behind-peer*
           (fn-peer-make-submission "lc-peer" :takethis *fn-lc-behind-id* nil)
           (fn-peer-decision :want nil) :publication-behind)
         (fn-peer-echo-reply "436 " *fn-lc-behind-id*))))
(defun fn-lc-behind-outcomes (n)
 (declare (xargs :guard (natp n)))
 (if (zp n) nil
  (cons (list :publication-behind (if (equal (mod n 2) 0) t nil))
        (fn-lc-behind-outcomes (1- n)))))
(defun fn-lc-all-renderedp (xs)
 (declare (xargs :guard t))
 (if (consp xs) (and (equal (car xs) :rendered) (fn-lc-all-renderedp (cdr xs))) t))
(defun fn-lc-behind-release-check (n)
 (declare (xargs :guard (natp n) :verify-guards nil))
 (let ((releases (fn-ocs-member-releases :complete (fn-lc-behind-outcomes n))))
  (and (equal (len releases) n) (fn-lc-all-renderedp releases))))
(with-guard-checking-event nil
 (assert-event
  (and (fn-lc-behind-release-check 0)
       (fn-lc-behind-release-check 1)
       (fn-lc-behind-release-check 2)
       (fn-lc-behind-release-check 3)
       (fn-lc-behind-release-check 4)
       (fn-lc-behind-release-check 5)
       (fn-lc-behind-release-check 6)
       (fn-lc-behind-release-check 7)
       (fn-lc-behind-release-check 8))))
; P13 (condition (b)): the default arm releases a refused member. A batch
; refused at START completes each member with the word, so :complete gives
; :rendered (its refusal line); a stopped batch keeps the existing policy.
(assert-event
 (and (equal (fn-ocs-member-release :complete :publication-behind t) :rendered)
      (equal (fn-ocs-member-release :complete :publication-behind nil) :rendered)
      (equal (fn-ocs-member-release :stop :publication-behind t) :uncertain-reply)
      (equal (fn-ocs-member-release :stop :publication-behind nil) :close)))
; Existing release policy is preserved for every action/word/renderability.
(defthm fn-lc-publication-behind-release-preserves-the-policy
 (equal (fn-ocs-member-release action word renderable)
        (cond ((eq word :uncertain) :own-uncertain)
              ((eq action :complete) :rendered)
              (renderable :uncertain-reply) (t :close)))
 :hints (("Goal" :in-theory (enable fn-ocs-member-release))))
