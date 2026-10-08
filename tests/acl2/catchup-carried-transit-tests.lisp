; Durable catch-up witnesses through the configured owner, not the absent arm.
(in-package "ACL2")
(include-book "../../books/owner-outcome-counted")
(include-book "../../books/owner-config-observe")
(include-book "../../books/defkeystone")
(include-book "owner-advance-carried-tests")
(include-book "peer-inbound-tests")
(bpr-lift fn-ocfg-read 3)
(bpr-lift fn-ocfg-step 2)

; Extend the real configured recovery fixture with an admitted peer record.
(defconst *sck-config-record*
  (fn-cfg-record-make
   2 8 3 (list (fn-cfg-set-capacity 1048576)
               (fn-cfg-set-peer-delta *pt-peer*))
   *fn-cfg-default-stamp*))
(defconst *sck-configured*
  (fn-ocl-complete
   (fn-ocfg-make (fn-own-start *cpo-t-ready* 4) *ocl-t-cfg*
                 nil *sck-config-record*)))
(assert-event (and (fn-ocl-relation *sck-configured*)
                   (null (fn-ocfg-staged *sck-configured*))))
(defconst *sck-start*
  (fn-ocfg-observe
   (fn-ocfg-with-owner *sck-configured*
                       (fn-own-configure (fn-ocfg-owner *sck-configured*)
                                         *own-config*))
   *pt-obs*))
(defconst *sck-open* (cdr (fn-ocfg-open-peer *sck-start* "innA" nil)))
(defconst *sck-offered*
  (cdr (in-arena-fn-ocfg-read
        *sr-arena* *sck-open* 0
        (append (fn-nntp-string-octets "IHAVE <loop@example.invalid>")
                '(13 10)))))
(defconst *sck-read*
  (cdr (in-arena-fn-ocfg-read
        *sr-arena* *sck-offered* 0 (append *pt-noloop* '(46 13 10)))))
(defconst *sck-taken* (in-arena-fn-ocfg-step *sr-arena* *sck-read* '(:take)))
(assert-event
 (and (fn-ocl-relation *sck-taken*)
      (fn-own-transit-subp (fn-own-inflight (fn-ocfg-owner *sck-taken*)))
      (equal (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *sck-taken*))) 0)))
(defconst *sck-completing*
  (in-arena-acar-t-ocfg-run
   *sr-arena* *sck-taken*
   (osi-drop-last
    (own-post-events
     (osi-sub-record 2 8 (fn-own-inflight (fn-ocfg-owner *sck-taken*)))))))
(defconst *sck-durable*
  (fn-ocfg-with-owner
   *sck-completing* (fn-ccar-own-complete (fn-ocfg-owner *sck-completing*))))
(assert-event
 (let* ((oc *sck-durable*)
        (o (fn-ocfg-owner oc))
        (sub (fn-own-inflight o)))
   (and (fn-ocl-relation oc)
        (fn-own-find-conn 0 (fn-own-conns o))
        sub (equal (fn-own-sub-id sub) 0) (fn-own-transit-subp sub)
        (equal (fn-own-outcome-completion o :durable) :durable)
        (equal (fn-own-view-version (fn-own-view o)) 3)
        (equal (fn-own-conn-version (fn-own-find-conn 0 (fn-own-conns o))) 2))))

(defconst *sck-result* (fn-oop-transit-outcome *sck-durable* 0 :want nil :durable))
(assert-event
 (and (equal (fn-own-take 4 (fn-served-reply-octets (car *sck-result*)))
             (fn-nntp-string-octets "235 "))
      (equal (fn-own-conn-version
              (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner (cdr *sck-result*)))))
             3)
      (fn-ocl-relation (cdr *sck-result*))))

; Corrupt only the view archive: the carried projection flag differs from
; the reference, even though the real durable transit trigger remains.
(defconst *sck-bad-view*
  (let* ((oc *sck-durable*) (o (fn-ocfg-owner oc))
         (view (fn-own-view o)) (a (fn-own-view-archive view))
         (bad (fn-make-state (fn-state-groups a) (fn-state-nexts a)
                             (cons 'junk (fn-state-articles a))
                             (fn-state-next-txid a) (fn-state-pending a)
                             (fn-state-fenced a))))
    (fn-ocfg-with-owner
     oc (fn-own-make (fn-own-store o) (update-nth 2 bad view) (fn-own-conns o)
                     (fn-own-next-id o) (fn-own-max-conns o) (fn-own-pending o)
                     (fn-own-ledger-field o) (fn-own-clock o) (fn-own-facts o)
                     (fn-own-config o) (fn-own-queue o) (fn-own-inflight o)
                     (fn-own-feeds o) (fn-own-node-secret o) (fn-own-refused o)))))

; Independent corruption: retain the good archive, corrupt the held node.
(defconst *sck-bad-session*
  (let* ((oc *sck-durable*) (o (fn-ocfg-owner oc))
         (conn (fn-own-find-conn 0 (fn-own-conns o)))
         (as (fn-own-conn-session conn))
         (bad (fn-auth-with-base
               as (fn-peer-with-node (fn-auth-session-base as) *scar-t-bad-node*))))
    (fn-ocfg-with-owner
     oc (fn-own-set-conns o (fn-own-replace-conn (update-nth 4 bad conn)
                                                (fn-own-conns o))))))

(defteeth fn-oop-transit-outcome-is-own-transit-outcome
  :subject fn-oop-transit-outcome
  :claim
  (((ocl (fn-ocl-relation oc)))
   (and (equal (car (fn-oop-transit-outcome oc id kind reason word))
               (car (fn-own-transit-outcome (fn-ocfg-owner oc) id kind reason word)))
        (equal (fn-ocfg-owner (cdr (fn-oop-transit-outcome oc id kind reason word)))
               (cdr (fn-own-transit-outcome (fn-ocfg-owner oc) id kind reason word)))))
  :witness ((oc *sck-durable*) (id 0) (kind :want) (reason nil) (word :durable))
  :breaks ((ocl ((oc *sck-bad-view*) (id 0) (kind :want) (reason nil) (word :durable))))
  :corrupt ((held-node ((oc *sck-bad-session*) (id 0) (kind :want)
                        (reason nil) (word :durable))))
  :mutations
  ((no-advance
    (:conclusion (equal (fn-ocfg-owner (cdr (fn-oop-transit-outcome oc id kind reason word)))
                        (fn-ocfg-owner oc)))
    ((oc *sck-durable*) (id 0) (kind :want) (reason nil) (word :durable))
    :fault "A durable transit leaves the connection at its old view.")))

(defteeth fn-oct-transit-is-own-transit-outcome-under-ocl-relation
  :subject fn-oct-transit
  :claim
  (((ocl (fn-ocl-relation oc)))
   (and (equal (car (car (fn-oct-transit oc id kind reason word pending)))
               (car (fn-own-transit-outcome (fn-ocfg-owner oc) id kind reason word)))
        (equal (fn-ocfg-owner (cdr (car (fn-oct-transit oc id kind reason word pending))))
               (cdr (fn-own-transit-outcome (fn-ocfg-owner oc) id kind reason word)))))
  :witness ((oc *sck-durable*) (id 0) (kind :want) (reason nil) (word :durable) (pending 0))
  :breaks ((ocl ((oc *sck-bad-view*) (id 0) (kind :want) (reason nil)
                 (word :durable) (pending 0))))
  :corrupt ((held-node ((oc *sck-bad-session*) (id 0) (kind :want)
                        (reason nil) (word :durable) (pending 0))))
  :mutations
  ((no-advance
    (:conclusion (equal (fn-ocfg-owner (cdr (car (fn-oct-transit oc id kind reason word pending))))
                        (fn-ocfg-owner oc)))
    ((oc *sck-durable*) (id 0) (kind :want) (reason nil) (word :durable) (pending 0))
    :fault "The counted durable outcome leaves the connection at its old view.")))

(defteeth-check (fn-oop-transit-outcome-is-own-transit-outcome
                 fn-oct-transit-is-own-transit-outcome-under-ocl-relation))
