;; fn: the owner read the host calls, with the live node's invariant carried.
;
; books/served-carried.lisp is the served fold parameterized by a node known
; to satisfy fn-node-statep.  This book closes it at the owner: the node is
; the store's own (fn-sn-node (fn-own-store o)), which the configured
; owner's relation fn-ocl-relation (books/config-owner-live.lisp) carries
; through fn-cst-relation (fn-scar-ocl-relation-carries-node-statep), as the
; static owner's fn-own-relation does through fn-snt-relation
; (fn-scar-relation-carries-node-statep), and the read never changes
; the store (fn-scar-ocfg-read-keeps-store), so the premise is carried from
; open through every read without being evaluated on it.
; host/owner-host.lisp fn-owner-chunk calls fn-scar-ocfg-read-tls-prefix.

(in-package "ACL2")
(include-book "served-carried")
(include-book "owner-tls-prefix")
(include-book "config-owner-live")

(defun fn-scar-conn-boundedp (conn groups live)
  (declare (xargs :guard t))
  (let ((as (fn-own-conn-session conn)))
    (and (fn-scar-auth-sessionp as live)
         (let ((session (fn-auth-reader-session as)))
           (and (or (null (fn-nntp-session-group session))
                    (fn-ag-member (fn-nntp-session-group session) groups))
                (or (null (fn-nntp-session-current session))
                    (and (posp (fn-nntp-session-current session))
                         (<= (fn-nntp-session-current session)
                             *fn-nntp-max-article-number*))))))))

(defthm fn-scar-conn-boundedp-is-own-conn-boundedp
  (implies (fn-node-statep live)
           (equal (fn-scar-conn-boundedp conn groups live)
                  (fn-own-conn-boundedp conn groups)))
  :hints (("Goal" :in-theory (e/d (fn-scar-conn-boundedp fn-own-conn-boundedp)
                                  (fn-scar-auth-sessionp fn-auth-sessionp
                                   fn-node-statep)))))

(defun fn-scar-finish-read (o conn result live)
  (declare (xargs :guard t))
  (let* ((effects (fn-served-result-effects result))
         (sconn (fn-served-result-conn result))
         (id (fn-own-conn-id conn))
         (next (fn-own-conn-make-group-indexed id
                                 (fn-own-conn-version conn)
                                 (fn-own-conn-frontier conn)
                                 (fn-served-conn-wire sconn)
                                 (fn-served-conn-session sconn)
                                 (fn-own-conn-archive conn)
                                 (fn-own-conn-config conn)
                                 (fn-own-conn-observation conn)
                                 (fn-own-conn-verdicts conn)
                                 (fn-own-conn-index conn)
                                       (fn-own-conn-group-index conn)))
         (decision (fn-served-submission effects)))
    (cons effects
          (if (and (fn-scar-conn-boundedp
                    next (fn-sn-groups (fn-own-store o)) live)
                   (fn-scar-conn-boundedp
                    next (fn-state-groups (fn-own-conn-archive next)) live))
              (let ((o2 (fn-own-set-conns
                         o (fn-own-replace-conn next (fn-own-conns o)))))
                (if decision
                    (fn-own-enqueue
                     o2 (fn-own-sub-make id (fn-own-conn-version conn)
                                         nil decision))
                  o2))
            (fn-own-set-conns o (fn-own-remove-conn id (fn-own-conns o)))))))

(defthm fn-scar-finish-read-is-own-finish-read
  (implies (fn-node-statep live)
           (equal (fn-scar-finish-read o conn result live)
                  (fn-own-finish-read o conn result)))
  :hints (("Goal" :in-theory (e/d (fn-scar-finish-read fn-own-finish-read)
                                  (fn-scar-conn-boundedp fn-own-conn-boundedp
                                   fn-node-statep)))))

; The owner's view trie and the article list it indexes, carried (not
; evaluated) the way the node premise is.  fn-own-relation carries it in
; fn-own-view-okp; for the configured owner it is carried by every
; fn-ocfg-step event, fn-ocfg-observe and the carried read
; (books/owner-offer-indexed.lisp).
(defun fn-scar-view-indexedp (o)
  (declare (xargs :guard t))
  (fn-midx-correspondencep
   (fn-own-view-index (fn-own-view o))
   (fn-state-articles (fn-own-view-archive (fn-own-view o)))))

; fn-own-read-tls-prefix (books/owner-tls-prefix.lisp) with the store's node
; passed as `live', and the view's trie and articles as `trie' and `arts'
; for the IHAVE/CHECK history test (books/peer-offer-indexed.lisp).
(defun fn-scar-own-read-tls-prefix (o id octets)
  (declare (xargs :guard t))
  (let ((conn (fn-own-find-conn id (fn-own-conns o)))
        (live (fn-sn-node (fn-own-store o)))
        (trie (fn-own-view-index (fn-own-view o)))
        (arts (fn-state-articles (fn-own-view-archive (fn-own-view o)))))
    (if conn
        (let* ((counted
                 (fn-scar-step-counted-fast
                  (fn-own-tls-served-conn o conn) octets live trie arts))
               (result
                 (fn-scar-finish-read
                  o conn (fn-served-counted-result counted) live)))
          (fn-own-tls-make-result
           (fn-served-counted-consumed counted) (car result) (cdr result)))
      (fn-own-tls-make-result (len octets) nil o))))

(defthm fn-scar-own-read-tls-prefix-is-own-read-tls-prefix
  (implies (and (fn-node-statep (fn-sn-node (fn-own-store o)))
                (fn-scar-view-indexedp o))
           (equal (fn-scar-own-read-tls-prefix o id octets)
                  (fn-own-read-tls-prefix o id octets)))
  :hints (("Goal" :in-theory (e/d (fn-scar-own-read-tls-prefix
                                   fn-own-read-tls-prefix)
                                  (fn-scar-step-counted-fast
                                   fn-served-step-counted-fast
                                   fn-scar-finish-read fn-own-finish-read
                                   fn-own-tls-served-conn fn-node-statep
                                   fn-midx-correspondencep)))))

; The function host/owner-host.lisp fn-owner-chunk calls.
(defun fn-scar-ocfg-read-tls-prefix (oc id octets)
  (declare (xargs :guard (fn-wire-octet-listp octets)))
  (let ((result (fn-scar-own-read-tls-prefix (fn-ocfg-owner oc) id octets)))
    (fn-own-tls-make-result
     (fn-own-tls-result-consumed result)
     (fn-own-tls-result-effects result)
     (fn-ocfg-with-read-owner oc id (fn-own-tls-result-owner result)))))

(defthm fn-scar-ocfg-read-tls-prefix-is-ocfg-read-tls-prefix
  (implies (and (fn-node-statep (fn-sn-node (fn-own-store (fn-ocfg-owner oc))))
                (fn-scar-view-indexedp (fn-ocfg-owner oc)))
           (equal (fn-scar-ocfg-read-tls-prefix oc id octets)
                  (fn-ocfg-read-tls-prefix oc id octets)))
  :hints (("Goal" :in-theory (e/d (fn-scar-ocfg-read-tls-prefix
                                   fn-ocfg-read-tls-prefix)
                                  (fn-scar-own-read-tls-prefix
                                   fn-own-read-tls-prefix fn-node-statep
                                   fn-scar-view-indexedp)))))

; The premise is the owner's: fn-own-relation conjoins fn-snt-relation,
; which conjoins fn-sn-statep, which conjoins fn-node-statep of the node.
(defthm fn-scar-relation-carries-node-statep
  (implies (fn-own-relation o)
           (fn-node-statep (fn-sn-node (fn-own-store o))))
  :hints (("Goal" :in-theory (e/d (fn-own-relation fn-snt-relation fn-sn-statep)
                                  (fn-node-statep)))))

(defthm fn-scar-relation-carries-view-indexedp
  (implies (fn-own-relation o)
           (fn-scar-view-indexedp o))
  :hints (("Goal" :in-theory (e/d (fn-own-relation fn-own-view-okp
                                   fn-scar-view-indexedp)
                                  (fn-midx-correspondencep)))))

; KEYSTONE for the host line.  Under the owner relation, the carried read is
; the reference read, whatever the connection, the octets and the session.
(defthm fn-scar-ocfg-read-tls-prefix-is-reference-under-relation
  (implies (fn-own-relation (fn-ocfg-owner oc))
           (equal (fn-scar-ocfg-read-tls-prefix oc id octets)
                  (fn-ocfg-read-tls-prefix oc id octets)))
  :hints (("Goal" :in-theory (disable fn-scar-ocfg-read-tls-prefix
                                      fn-ocfg-read-tls-prefix fn-own-relation
                                      fn-scar-view-indexedp))))

; Preservation: a served read leaves the store, hence its node and the
; premise, exactly as it found them.  No hypothesis.
(defthm fn-scar-own-read-keeps-store
  (equal (fn-own-store
          (fn-own-tls-result-owner (fn-scar-own-read-tls-prefix o id octets)))
         (fn-own-store o))
  :hints (("Goal" :in-theory (e/d (fn-scar-own-read-tls-prefix
                                   fn-scar-finish-read fn-own-tls-make-result
                                   fn-own-tls-result-owner fn-own-set-conns
                                   fn-own-enqueue)
                                  (fn-scar-step-counted-fast
                                   fn-scar-conn-boundedp)))))

(defthm fn-scar-ocfg-read-keeps-store
  (equal (fn-own-store
          (fn-ocfg-owner
           (fn-own-tls-result-owner (fn-scar-ocfg-read-tls-prefix oc id octets))))
         (fn-own-store (fn-ocfg-owner oc)))
  :hints (("Goal" :in-theory (e/d (fn-scar-ocfg-read-tls-prefix
                                   fn-ocfg-with-read-owner fn-own-tls-make-result
                                   fn-own-tls-result-owner)
                                  (fn-scar-own-read-tls-prefix
                                   fn-scar-own-read-keeps-store))
           :use ((:instance fn-scar-own-read-keeps-store
                            (o (fn-ocfg-owner oc)))))))

(defthm fn-scar-ocfg-read-preserves-node-premise
  (implies (fn-node-statep (fn-sn-node (fn-own-store (fn-ocfg-owner oc))))
           (fn-node-statep
            (fn-sn-node
             (fn-own-store
              (fn-ocfg-owner
               (fn-own-tls-result-owner
                (fn-scar-ocfg-read-tls-prefix oc id octets)))))))
  :hints (("Goal" :in-theory (disable fn-scar-ocfg-read-tls-prefix
                                      fn-node-statep))))

; The configured owner the host runs carries fn-ocl-relation
; (books/config-owner-live.lisp; fn-ocl-open-, -close-, -observe-, -read-,
; -advance- and -complete-preserves-historical-relation keep it).  Its store
; conjunct is fn-cst-relation, which conjoins fn-sn-statep.
(defthm fn-scar-ocl-relation-carries-node-statep
  (implies (fn-ocl-relation oc)
           (fn-node-statep (fn-sn-node (fn-own-store (fn-ocfg-owner oc)))))
  :hints (("Goal" :in-theory (e/d (fn-ocl-relation fn-cst-relation fn-sn-statep)
                                  (fn-node-statep)))))

; KEYSTONE for host/owner-host.lisp fn-owner-chunk: under the configured
; owner's relation and its view trie's correspondence, the carried read is
; the reference read, for every connection identifier, every observed octet
; list and every session.  books/owner-offer-indexed.lisp carries the second
; premise across every configured-owner transition.
(defthm fn-scar-ocfg-read-tls-prefix-is-reference-under-ocl-relation
  (implies (and (fn-ocl-relation oc)
                (fn-scar-view-indexedp (fn-ocfg-owner oc)))
           (equal (fn-scar-ocfg-read-tls-prefix oc id octets)
                  (fn-ocfg-read-tls-prefix oc id octets)))
  :hints (("Goal" :in-theory (disable fn-scar-ocfg-read-tls-prefix
                                      fn-ocfg-read-tls-prefix fn-ocl-relation
                                      fn-scar-view-indexedp))))

(in-theory (disable fn-scar-view-indexedp fn-scar-conn-boundedp fn-scar-finish-read
                    fn-scar-own-read-tls-prefix fn-scar-ocfg-read-tls-prefix))
