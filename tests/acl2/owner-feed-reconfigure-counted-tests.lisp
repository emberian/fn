(in-package "ACL2")
(include-book "../../books/owner-feed-reconfigure-counted")
(defconst *ofrc-peer*
  (fn-cfg-peer-make "p" "p.fn.test" '(:nntp "127.0.0.1" 1120)
                    '("fn.*" 32768 16) '("fn.*" t 256 1000)
                    '(:source-address "127.0.0.2")))
(defconst *ofrc-peers* (fn-cfg-peer-rows *ofrc-peer*))
(defconst *ofrc-empty* (fn-own-feed-install-one "p" *ofrc-peers* nil))
(defconst *ofrc-enqueued*
  (fn-own-feed-enqueue-all-counted '("p") *ofrc-empty* '(60 97 62) 0 0))
(defconst *ofrc-live* (car *ofrc-enqueued*))
(assert-event
 (and (fn-own-feed-tablep *ofrc-live*) (fn-ofct-table-relationp *ofrc-live*)
      (equal (cdr *ofrc-enqueued*) 1)
      (equal (fn-own-feed-reconfigure-counted *ofrc-live* nil 1) (cons *ofrc-live* 1))
      (equal (car (fn-own-feed-reconfigure-counted *ofrc-live* nil 1))
             (fn-own-feed-reconfigure *ofrc-live* nil))))
(defconst *ofrc-other-drop*
  (fn-own-feed-put "p" *ofrc-peer*
   (fn-feed-give-up (fn-own-feed-find "p" *ofrc-live*) '(60 97 62) :operator)
   *ofrc-live*))
; A non-retry-bound drop remains pending while its feed exists. The existing
; idle/no-outbound policy removes that feed; the same retire fold subtracts it.
(assert-event
 (and (fn-own-feed-tablep *ofrc-other-drop*)
      (fn-ofct-table-relationp *ofrc-other-drop*)
      (equal (fn-own-feed-table-pending-model *ofrc-other-drop*) 1)
      (equal (fn-own-feed-reconfigure-counted *ofrc-other-drop* nil 1) (cons nil 0))
      (equal (car (fn-own-feed-reconfigure-counted *ofrc-other-drop* nil 1))
             (fn-own-feed-reconfigure *ofrc-other-drop* nil))))
; Hypothesis removal: wrong starting aggregate retains a numeric scalar but
; fails both the model relation and the output relation after the same removal.
(assert-event
 (and (acl2-numberp 42)
      (not (equal 42 (fn-own-feed-table-pending-model *ofrc-other-drop*)))
      (not (equal (cdr (fn-own-feed-reconfigure-counted *ofrc-other-drop* nil 42))
                   (fn-own-feed-table-pending-model
                    (car (fn-own-feed-reconfigure-counted *ofrc-other-drop* nil 42)))))))
(assert-event
 (and (equal 0 (fn-own-feed-table-pending-model nil))
      (equal (cdr (fn-own-feed-reconfigure-counted nil *ofrc-peers* 0)) 0)
      (equal (car (fn-own-feed-reconfigure-counted nil *ofrc-peers* 0)) *ofrc-empty*)
      (fn-ofct-table-relationp (car (fn-own-feed-reconfigure-counted nil *ofrc-peers* 0)))))
