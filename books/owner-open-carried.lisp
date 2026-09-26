;; fn: the connection open (the greeting) the host calls, with the owner's invariant carried.
;
; host/owner-host.lisp fn-owner-exposure-open calls fn-exp-open
; (books/public-exposure.lisp), whose reader arm is fn-ocfg-open
; (books/owner-config.lisp); admin.lisp's fn-owner-open calls fn-ocfg-open.
; A reader open evaluated three whole-archive recognizers under the owner
; mutex, all over values the configured owner's relation already describes:
;
; - fn-own-open -> fn-served-open-group-indexed -> fn-auth-open-session ->
;   fn-peer-open-session -> fn-post-open-session -> fn-nntp-open-session,
;   which records fn-nntp-projectionp of the pinned view's archive, whose
;   first conjunct is fn-statep of the whole archive;
; - fn-own-reader-context -> fn-peer-open-session over the same archive
;   (fn-statep again), fn-node-statep of the store's node, and fn-cfgp of
;   the configuration.
;
; At N = 20,000 that is 369 ms per greeting (planning/evidence/
; served-path-scale-2026-09-26.md), and the envelope's greeting p95 at N =
; 10,000 is 1.3 s (PKT-455 (1), PKT-190).
;
; The carried open below is the reference with each recognizer taken from
; fn-ocl-relation instead of evaluated:
; - the projection flag by fn-acar-open-session
;   (books/owner-advance-carried.lisp), the recognizer without its fn-statep
;   conjunct, equal to it when the archive is an acceptance state
;   (fn-acar-open-session-is-open-session); the relation carries that of the
;   view archive (fn-acar-ocl-relation-carries-view-statep);
; - fn-node-statep of the store node from the relation
;   (fn-scar-ocl-relation-carries-node-statep);
; - fn-cfgp of the configuration, a conjunct of fn-ocl-relation.
; What a greeting still evaluates: the connection bound (len of the
; connections), the group list and next-number table (O(groups)), the
; article count (len of the view's articles: pointer steps, no recognizer)
; and the authentication policy.  The served bytes are the reference's by
; the keystones.  The relation itself is established at every host-called
; open and preserved by every configured-owner transition the host installs
; (books/config-owner-live.lisp, books/owner-recover-ocl.lisp); this book
; restates none of that.

(in-package "ACL2")
(include-book "owner-advance-carried")
(include-book "public-exposure")

; -----------------------------------------------------------------------------
; The sessions a reader open builds.

; fn-auth-open-session ARCHIVE NIL NIL NIL ACFG NIL, the reader session
; fn-served-open-indexed opens: the peer arm of fn-peer-open-session is the
; unpinned one, since (fn-node-statep nil) is false.
(defun fn-ocar-auth-open-reader (archive acfg)
  (declare (xargs :guard t))
  (fn-auth-make-session
   (fn-peer-make-session (fn-post-make-session (fn-acar-open-session archive)
                                               nil)
                         nil nil 0 nil nil)
   (if (fn-auth-configp acfg) acfg (fn-auth-open-config))
   nil nil nil nil))

(defthm fn-ocar-auth-open-reader-is-auth-open-session
  (implies (fn-statep archive)
           (equal (fn-ocar-auth-open-reader archive acfg)
                  (fn-auth-open-session archive nil nil nil acfg nil)))
  :hints (("Goal" :use ((:instance fn-acar-open-session-is-open-session))
           :in-theory (e/d (fn-auth-open-session fn-peer-open-session
                            fn-post-open-session)
                           (fn-acar-open-session fn-nntp-open-session
                            fn-acar-open-session-is-open-session
                            fn-statep fn-auth-configp)))))

; fn-peer-open-session ARCHIVE NIL NODE CFG, the reader context's session,
; with the node and configuration recognizers carried.
(defun fn-ocar-peer-open-reader (archive node cfg)
  (declare (xargs :guard t))
  (fn-peer-make-session (fn-post-make-session (fn-acar-open-session archive)
                                              nil)
                        nil nil 0 node cfg))

(defthm fn-ocar-peer-open-reader-is-peer-open-session
  (implies (and (fn-statep archive)
                (fn-node-statep node)
                (fn-cfgp cfg))
           (equal (fn-ocar-peer-open-reader archive node cfg)
                  (fn-peer-open-session archive nil node cfg)))
  :hints (("Goal" :use ((:instance fn-acar-open-session-is-open-session))
           :in-theory (e/d (fn-peer-open-session fn-post-open-session)
                           (fn-acar-open-session fn-nntp-open-session
                            fn-acar-open-session-is-open-session
                            fn-statep fn-node-statep fn-cfgp)))))

; -----------------------------------------------------------------------------
; The owner's open, carried.

(defun fn-ocar-served-open-group-indexed
    (archive index buckets verdicts line-limit body-limit config
             observation injection acfg)
  (declare (xargs :guard t))
  (fn-served-pin-group-index
   (fn-served-make-result
    (fn-served-make-conn-indexed
     (fn-wire-initial-state line-limit body-limit)
     (fn-ocar-auth-open-reader archive acfg)
     archive config observation injection verdicts index)
    (list (fn-nntp-reply-effect
           (fn-served-greeting config (fn-ocar-auth-open-reader archive acfg)))))
   buckets))

(defthm fn-ocar-served-open-group-indexed-is-reference
  (implies (fn-statep archive)
           (equal (fn-ocar-served-open-group-indexed
                   archive index buckets verdicts line-limit body-limit config
                   observation injection acfg)
                  (fn-served-open-group-indexed
                   archive index buckets verdicts line-limit body-limit config
                   observation injection acfg)))
  :hints (("Goal" :in-theory (e/d (fn-served-open-group-indexed
                                   fn-served-open-indexed)
                                  (fn-ocar-auth-open-reader fn-auth-open-session
                                   fn-statep fn-served-pin-group-index
                                   fn-served-greeting)))))

(defun fn-ocar-own-open (o acfg)
  (declare (xargs :guard t))
  (if (< (len (fn-own-conns o)) (nfix (fn-own-max-conns o)))
      (let* ((view (fn-own-view o))
             (archive (fn-own-view-archive view))
             (id (fn-own-next-id o))
             (opened (fn-ocar-served-open-group-indexed
                      archive (fn-own-view-index view)
                      (fn-own-view-group-index view)
                      (fn-own-view-verdicts view)
                      *fn-nntp-max-initial-line-octets*
                      (fn-own-body-limit o) (fn-own-config o)
                      (fn-own-clock o) (fn-own-clock o) acfg))
             (sconn (fn-served-result-conn opened))
             (conn (fn-own-conn-make-group-indexed id (fn-own-view-version view)
                                     (fn-own-view-frontier view)
                                     (fn-served-conn-wire sconn)
                                     (fn-served-conn-session sconn)
                                     archive (fn-own-config o) (fn-own-clock o)
                                     (fn-own-view-verdicts view)
                                     (fn-own-view-index view)
                                     (fn-own-view-group-index view) (fn-own-view-control view))))
        (cons (fn-served-result-effects opened)
              (fn-own-make (fn-own-store o) view (cons conn (fn-own-conns o))
                           (1+ (nfix id)) (fn-own-max-conns o) (fn-own-pending o)
                           (fn-own-ledger o) (fn-own-clock o) (fn-own-facts o) (fn-own-config o) (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o))))
    (cons nil o)))

(defthm fn-ocar-own-open-is-own-open
  (implies (fn-acar-view-statep o)
           (equal (fn-ocar-own-open o acfg)
                  (fn-own-open o acfg)))
  :hints (("Goal" :in-theory (e/d (fn-own-open fn-acar-view-statep)
                                  (fn-ocar-served-open-group-indexed
                                   fn-served-open-group-indexed fn-statep)))))

(defun fn-ocar-own-reader-context (o id cfg)
  (declare (xargs :guard t))
  (let ((conn (fn-own-find-conn id (fn-own-conns o))))
    (if conn
        (let* ((as (fn-own-conn-session conn))
               (next-as
                (fn-auth-with-base
                 as (fn-ocar-peer-open-reader (fn-own-conn-archive conn)
                                              (fn-sn-node (fn-own-store o))
                                              cfg)))
               (next (fn-own-conn-make-group-indexed
                      (fn-own-conn-id conn) (fn-own-conn-version conn)
                      (fn-own-conn-frontier conn) (fn-own-conn-wire conn) next-as
                      (fn-own-conn-archive conn) (fn-own-conn-config conn)
                      (fn-own-conn-observation conn)
                      (fn-own-conn-verdicts conn)
                      (fn-own-conn-index conn)
                      (fn-own-conn-group-index conn) (fn-own-conn-control conn))))
          (fn-own-set-conns o (fn-own-replace-conn next (fn-own-conns o))))
      o)))

(defthm fn-ocar-own-reader-context-is-reference
  (implies (and (fn-statep (fn-own-conn-archive
                            (fn-own-find-conn id (fn-own-conns o))))
                (fn-node-statep (fn-sn-node (fn-own-store o)))
                (fn-cfgp cfg))
           (equal (fn-ocar-own-reader-context o id cfg)
                  (fn-own-reader-context o id cfg)))
  :hints (("Goal" :in-theory (e/d (fn-own-reader-context)
                                  (fn-ocar-peer-open-reader fn-peer-open-session
                                   fn-statep fn-node-statep fn-cfgp)))))

(defun fn-ocar-ocfg-open (oc acfg)
  (declare (xargs :guard t))
  (let* ((o (fn-ocfg-owner oc))
         (id (fn-own-next-id o))
         (opened (fn-ocar-own-open o (fn-auth-config-with-accounts
                                      acfg (fn-cfg-value (fn-ocfg-config oc)))))
         (raw (cdr opened))
         (o2 (if (fn-own-find-conn id (fn-own-conns raw))
                 (fn-ocar-own-reader-context raw id (fn-ocfg-config oc))
               raw)))
    (cons (car opened)
          (fn-ocfg-make o2 (fn-ocfg-config oc)
                        (if (fn-own-find-conn id (fn-own-conns o2))
                            (fn-ocfg-pin-add id (fn-ocfg-config oc)
                                             (fn-ocfg-pins oc))
                          (fn-ocfg-pins oc))
                        (fn-ocfg-staged oc)))))

; -----------------------------------------------------------------------------
; The premises at the opened owner, from the relation.

(local
 (defthm fn-ocar-find-conn-at-next-id-absent
   (implies (and (fn-own-ids-below-next-p conns n)
                 (natp n))
            (not (fn-own-find-conn n conns)))
   :hints (("Goal" :use ((:instance fn-own-find-conn-id-below-next
                                    (id n)))))))

; The connection the open finds at the old next id is the new one, whose
; archive is the view's; if the open was refused, the owner is unchanged
; and holds no connection at that id.
(local
 (defthm fn-ocar-own-open-found-archive
   (implies (and (fn-own-ids-below-next-p (fn-own-conns o) (fn-own-next-id o))
                 (natp (fn-own-next-id o))
                 (fn-own-find-conn (fn-own-next-id o)
                                   (fn-own-conns (cdr (fn-own-open o acfg)))))
            (equal (fn-own-conn-archive
                    (fn-own-find-conn (fn-own-next-id o)
                                      (fn-own-conns (cdr (fn-own-open o acfg)))))
                   (fn-own-view-archive (fn-own-view o))))
   :hints (("Goal" :in-theory (e/d (fn-own-open)
                                   (fn-served-open-group-indexed))))))

(local
 (defthm fn-ocar-ref-own-open-keeps-store
   (equal (fn-own-store (cdr (fn-own-open o acfg)))
          (fn-own-store o))
   :hints (("Goal" :in-theory (e/d (fn-own-open)
                                   (fn-served-open-group-indexed))))))

(local
 (defthm fn-ocar-ocl-relation-carries-open-premises
   (implies (fn-ocl-relation oc)
            (and (fn-cfgp (fn-ocfg-config oc))
                 (fn-own-ids-below-next-p (fn-own-conns (fn-ocfg-owner oc))
                                          (fn-own-next-id (fn-ocfg-owner oc)))
                 (natp (fn-own-next-id (fn-ocfg-owner oc)))))
   :hints (("Goal" :in-theory (e/d (fn-ocl-relation)
                                   (fn-ocl-view-historyp fn-auth-sessionp
                                    fn-ocl-conns-historyp fn-cst-relation
                                    fn-ocl-config-historyp fn-ocl-view-configp
                                    fn-cfgp fn-own-ids-below-next-p))))))

; KEYSTONE for the host lines (host/owner-host.lisp fn-owner-open, and
; fn-owner-exposure-open through fn-ocar-exp-open below): under the
; configured owner's relation the carried open is the reference open, the
; greeting effects and the owner alike, for every authentication policy.
(defthm fn-ocar-ocfg-open-is-ocfg-open-under-ocl-relation
  (implies (fn-ocl-relation oc)
           (equal (fn-ocar-ocfg-open oc acfg)
                  (fn-ocfg-open oc acfg)))
  :hints (("Goal"
           :use ((:instance fn-acar-ocl-relation-carries-view-statep)
                 (:instance fn-scar-ocl-relation-carries-node-statep)
                 (:instance fn-ocar-ocl-relation-carries-open-premises)
                 (:instance fn-ocar-own-open-is-own-open
                            (o (fn-ocfg-owner oc))
                            (acfg (fn-auth-config-with-accounts
                                   acfg (fn-cfg-value (fn-ocfg-config oc)))))
                 (:instance fn-ocar-own-reader-context-is-reference
                            (o (cdr (fn-own-open
                                     (fn-ocfg-owner oc)
                                     (fn-auth-config-with-accounts
                                      acfg (fn-cfg-value (fn-ocfg-config oc))))))
                            (id (fn-own-next-id (fn-ocfg-owner oc)))
                            (cfg (fn-ocfg-config oc))))
           :in-theory (e/d (fn-ocfg-open fn-acar-view-statep)
                           (fn-ocar-own-open fn-own-open
                            fn-ocar-own-reader-context fn-own-reader-context
                            fn-ocl-relation fn-statep fn-node-statep fn-cfgp
                            fn-own-ids-below-next-p
                            fn-acar-ocl-relation-carries-view-statep
                            fn-scar-ocl-relation-carries-node-statep
                            fn-ocar-ocl-relation-carries-open-premises
                            fn-ocar-own-open-is-own-open
                            fn-ocar-own-reader-context-is-reference)))))

; -----------------------------------------------------------------------------
; The exposure open the native accept calls (host/owner-host.lisp
; fn-owner-exposure-open): fn-exp-open with its reader arm carried.  The
; peer arm (fn-ocfg-open-peer) is unchanged.

(defun fn-ocar-exp-open (oc xs lim acfg peer address now)
  (declare (xargs :guard t))
  (let* ((o (fn-ocfg-owner oc))
         (decision (fn-exp-admit-decision xs lim (len (fn-own-conns o))
                                          address now)))
    (if (equal (car decision) :admit)
        (let* ((id (fn-own-next-id o))
               (pinned (fn-exp-pinned-acfg acfg lim))
               (opened (if peer
                           (fn-ocfg-open-peer oc peer pinned)
                         (fn-ocar-ocfg-open oc pinned)))
               (oc2 (cdr opened))
               (openedp (and (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc2)))
                             t)))
          (list (car opened) oc2
                (if openedp (fn-exp-register xs id address now) xs)
                (if openedp id nil)
                nil))
      (list nil oc
            (fn-exp-with xs (fn-exp-conns xs) (fn-exp-rates xs)
                         (fn-exp-fails xs) (fn-exp-posts xs)
                         (fn-exp-counters-bump (nfix (fn-exp-at 2 decision)) now
                                               (fn-exp-counters xs)))
            nil
            (fn-exp-line (fn-exp-at 1 decision))))))

; KEYSTONE for host/owner-host.lisp fn-owner-exposure-open.
(defthm fn-ocar-exp-open-is-exp-open-under-ocl-relation
  (implies (fn-ocl-relation oc)
           (equal (fn-ocar-exp-open oc xs lim acfg peer address now)
                  (fn-exp-open oc xs lim acfg peer address now)))
  :hints (("Goal" :in-theory (e/d (fn-exp-open)
                                  (fn-ocar-ocfg-open fn-ocfg-open
                                   fn-ocfg-open-peer fn-ocl-relation
                                   fn-exp-admit-decision fn-exp-register
                                   fn-exp-pinned-acfg)))))
;
; The Store is untouched by the carried open, with no hypothesis: what
; books/owner-store-indexed.lisp's host-step model needs for the :open and
; :exposure-open arms (fn-osi-host-step), which name these functions because
; the host installs their results (fn-osi-ocar-exp-open-keeps-store there
; adds the peer arm).
(defthm fn-ocar-own-open-keeps-store
  (equal (fn-own-store (cdr (fn-ocar-own-open o acfg)))
         (fn-own-store o))
  :hints (("Goal" :in-theory (e/d (fn-ocar-own-open)
                                  (fn-ocar-served-open-group-indexed)))))

(defthm fn-ocar-own-reader-context-keeps-store
  (equal (fn-own-store (fn-ocar-own-reader-context o id cfg))
         (fn-own-store o))
  :hints (("Goal" :in-theory (e/d (fn-ocar-own-reader-context fn-own-set-conns)
                                  (fn-ocar-peer-open-reader)))))

(defthm fn-ocar-ocfg-open-keeps-store
  (equal (fn-own-store (fn-ocfg-owner (cdr (fn-ocar-ocfg-open oc acfg))))
         (fn-own-store (fn-ocfg-owner oc)))
  :hints (("Goal" :in-theory (e/d (fn-ocar-ocfg-open)
                                  (fn-ocar-own-open fn-ocar-own-reader-context)))))

(in-theory (disable fn-ocar-auth-open-reader fn-ocar-peer-open-reader
                    fn-ocar-served-open-group-indexed fn-ocar-own-open
                    fn-ocar-own-reader-context fn-ocar-ocfg-open
                    fn-ocar-exp-open))
