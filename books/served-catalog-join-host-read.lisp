; served-catalog-join-host-read.lisp -- the catalog join carried across the
; host's served read (lane join-f2-2, 2026-09-29; PRF-302).
;
; host/owner-host.lisp fn-owner-chunk-span-at installs the owner of
; fn-mca-read-span's result: the credit layer (books/owner-credits.lisp) over
; the article-slot layer (books/owner-article-slots.lisp) over the disk
; admission (books/owner-time-admission.lisp) over the reader-view read
; (books/owner-reader-read.lisp) over the carried catalog read.  Every layer
; above the reader-view read changes one connection's posting bit or closes
; its wire, which no pin reads; the reader-view read keeps the store and puts
; the working view back (sca-join-4's fn-scj-invp-of-orr-read-span and
; fn-scj-versions-atmost-of-orr-read-span).  So fn-sjh-okp holds after with
; the same pending row.
;
; Two premises stay NAMED here and are not carried by fn-sjh-okp: the arena
; rows' column facts (fn-scol-okp, the catalog read's own premise) and the
; captured reader view's liveness over the catalog at a version no newer than
; the working view's (fn-sjh-views-okp) -- open obligations of row J1's
; carried state, see planning/evidence/sca-join-2026-09-28-join-f2.md.

(in-package "ACL2")

(include-book "served-catalog-join-host-complete")
(include-book "owner-credits") ; fn-mca-read-span: the read the host calls

(local (in-theory (disable (tau-system))))

(defun-nx fn-sjh-views-okp (views o fn-arena fn-cat)
  (implies (consp views)
           (and (fn-scj-live-okp (car views) fn-arena fn-cat)
                (<= (nfix (fn-own-view-version (car views)))
                    (nfix (fn-own-view-version (fn-own-view o)))))))

(defthm fn-sjh-rd-orr-keeps
  (implies (and (fn-scol-okp fn-arena fn-cat)
                (fn-scj-invp (fn-ocfg-owner oc) fn-arena fn-cat)
                (fn-sjh-views-okp views (fn-ocfg-owner oc) fn-arena fn-cat))
           (let ((o2 (fn-ocfg-owner (fn-own-tls-result-owner
                                     (fn-orr-read-span oc views id i end cache fn-octets fn-arena fn-cat)))))
             (and (equal (fn-own-store o2) (fn-own-store (fn-ocfg-owner oc)))
                  (equal (fn-own-view o2) (fn-own-view (fn-ocfg-owner oc))))))
  :hints (("Goal" :in-theory (union-theories '(fn-scj-orr-read-span-owner fn-sjh-views-okp)
                                             (theory 'minimal-theory))
           :cases ((consp views)))
          ("Subgoal 2" :use ((:instance fn-scj-scr-own-read-span-keeps (o (fn-ocfg-owner oc)))
                             (:instance fn-scj-invp-conns (o (fn-ocfg-owner oc)))
                             (:instance fn-scj-invp-gives-live-okp (o (fn-ocfg-owner oc)))))
          ("Subgoal 1"
           :use ((:instance fn-scj-invp-conns (o (fn-ocfg-owner oc)))
                 (:instance fn-scj-read-at-view-keeps (v (car views)) (w (fn-own-view (fn-ocfg-owner oc))))))))

(defthm fn-sjh-rd-okp-of-orr
  (implies (and (fn-scol-okp fn-arena fn-cat)
                (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
                (fn-sjh-views-okp views (fn-ocfg-owner oc) fn-arena fn-cat))
           (fn-sjh-okp (fn-ocfg-owner (fn-own-tls-result-owner
                                       (fn-orr-read-span oc views id i end cache fn-octets fn-arena fn-cat)))
                       pending fn-arena fn-cat))
  :hints (("Goal" :in-theory '(fn-sjh-views-okp)
           :use ((:instance fn-sjh-okp-unfolds (o (fn-ocfg-owner oc)))
                 (:instance fn-sjh-rd-orr-keeps)
                 (:instance fn-scj-invp-of-orr-read-span)
                 (:instance fn-scj-versions-atmost-of-orr-read-span)
                 (:instance fn-sjh-okp-of-same-store-and-view
                            (o (fn-ocfg-owner oc))
                            (o2 (fn-ocfg-owner (fn-own-tls-result-owner
                                                (fn-orr-read-span oc views id i end cache fn-octets fn-arena fn-cat)))))))))

(defthm fn-sjh-rd-with-allow-fields
  (let ((o2 (fn-ocfg-owner (fn-otm-owner-with-allow oc id allow)))
        (o (fn-ocfg-owner oc)))
    (and (equal (fn-own-store o2) (fn-own-store o))
         (equal (fn-own-view o2) (fn-own-view o))))
  :hints (("Goal" :in-theory (e/d (fn-otm-owner-with-allow fn-own-set-conns fn-sjh-ocfg-owner-of-with-owner)
                                  (fn-otm-conn-with-allow fn-own-replace-conn fn-own-find-conn)))))

(defthm fn-sjh-rd-conn-with-allow-version
  (equal (fn-own-conn-version (fn-otm-conn-with-allow c allow)) (fn-own-conn-version c))
  :hints (("Goal" :in-theory (e/d (fn-otm-conn-with-allow) (fn-own-conn-version))
           :use ((:instance fn-scj-conn-pin-fields-of-update-6
                            (v (fn-otm-cfg-with-allow (fn-own-conn-config c) allow)))))))

(defthm fn-sjh-rd-with-allow-versions
  (implies (fn-scj-versions-okp (fn-ocfg-owner oc))
           (fn-scj-versions-okp (fn-ocfg-owner (fn-otm-owner-with-allow oc id allow))))
  :hints (("Goal" :in-theory (e/d (fn-otm-owner-with-allow fn-own-set-conns fn-sjh-ocfg-owner-of-with-owner
                                   fn-scj-versions-okp)
                                  (fn-otm-conn-with-allow fn-own-replace-conn fn-own-find-conn
                                   fn-scj-conns-versions-atmostp))
           :use ((:instance fn-scj-versions-atmost-of-replace-conn
                            (conn (fn-otm-conn-with-allow (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))) allow))
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (n (fn-own-view-version (fn-own-view (fn-ocfg-owner oc)))))
                 (:instance fn-scj-versions-atmost-find-conn
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (n (fn-own-view-version (fn-own-view (fn-ocfg-owner oc)))))))))

(defthm fn-sjh-rd-okp-of-with-allow
  (implies (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
           (fn-sjh-okp (fn-ocfg-owner (fn-otm-owner-with-allow oc id allow)) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-sjh-okp-unfolds (o (fn-ocfg-owner oc)))
                 (:instance fn-sjh-rd-with-allow-fields)
                 (:instance fn-scj-invp-of-otm-owner-with-allow)
                 (:instance fn-sjh-rd-with-allow-versions)
                 (:instance fn-sjh-okp-of-same-store-and-view
                            (o (fn-ocfg-owner oc))
                            (o2 (fn-ocfg-owner (fn-otm-owner-with-allow oc id allow))))))))

(defthm fn-sjh-rd-with-refused-fields
  (let ((o2 (fn-ocfg-owner (fn-otm-ocfg-with-refused oc mem)))
        (o (fn-ocfg-owner oc)))
    (and (equal (fn-own-store o2) (fn-own-store o))
         (equal (fn-own-view o2) (fn-own-view o))
         (equal (fn-own-conns o2) (fn-own-conns o))))
  :hints (("Goal" :in-theory (e/d (fn-otm-ocfg-with-refused fn-sjh-ocfg-owner-of-with-owner) ()))))

(local
 (defthm fn-sjh-rd-okp-of-same-fields
   (implies (and (fn-sjh-okp o pending fn-arena fn-cat)
                 (equal (fn-own-store o2) (fn-own-store o))
                 (equal (fn-own-view o2) (fn-own-view o))
                 (equal (fn-own-conns o2) (fn-own-conns o)))
            (fn-sjh-okp o2 pending fn-arena fn-cat))
   :rule-classes nil
   :hints (("Goal" :in-theory '(fn-sjh-okp-of-same-store-and-view fn-sjh-versionsp-is-versions-okp)
            :use ((:instance fn-scjs-invp-of-same-fields)
                  (:instance fn-scjs-versionsp-of-same-fields)
                  (:instance fn-sjh-okp-unfolds))))))

(defthm fn-sjh-rd-okp-of-with-refused
  (implies (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
           (fn-sjh-okp (fn-ocfg-owner (fn-otm-ocfg-with-refused oc mem)) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-sjh-rd-with-refused-fields)
                 (:instance fn-sjh-rd-okp-of-same-fields (o (fn-ocfg-owner oc))
                            (o2 (fn-ocfg-owner (fn-otm-ocfg-with-refused oc mem))))))))

(defthm fn-sjh-rd-okp-of-shed
  (implies (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
           (fn-sjh-okp (fn-ocfg-owner (fn-otm-shed-ocfg oc id)) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory '(fn-otm-shed-ocfg fn-sjh-rd-okp-of-with-refused fn-sjh-rd-okp-of-with-allow))))

(defthm fn-sjh-rd-okp-of-unshed
  (implies (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
           (fn-sjh-okp (fn-ocfg-owner (fn-otm-unshed-ocfg oc id allow)) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory '(fn-otm-unshed-ocfg fn-sjh-rd-okp-of-with-refused fn-sjh-rd-okp-of-with-allow))))

(defthm fn-sjh-rd-shed-view
  (equal (fn-own-view (fn-ocfg-owner (fn-otm-shed-ocfg oc id))) (fn-own-view (fn-ocfg-owner oc)))
  :hints (("Goal" :in-theory '(fn-otm-shed-ocfg fn-sjh-rd-with-refused-fields fn-sjh-rd-with-allow-fields))))

(defthm fn-sjh-rd-views-okp-of-same-view
  (implies (equal (fn-own-view o2) (fn-own-view o))
           (equal (fn-sjh-views-okp views o2 fn-arena fn-cat) (fn-sjh-views-okp views o fn-arena fn-cat)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-sjh-views-okp))))

(defthm fn-sjh-rd-okp-of-otm
  (implies (and (fn-scol-okp fn-arena fn-cat)
                (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
                (fn-sjh-views-okp views (fn-ocfg-owner oc) fn-arena fn-cat))
           (fn-sjh-okp (fn-ocfg-owner (fn-own-tls-result-owner
                                       (fn-otm-read-span oc views id i end cache s fn-octets fn-arena fn-cat)))
                       pending fn-arena fn-cat))
  :hints (("Goal" :in-theory (union-theories '(fn-scj-otm-read-span-owner fn-sjh-rd-okp-of-unshed)
                                             (theory 'minimal-theory))
           :use ((:instance fn-sjh-rd-okp-of-orr)
                 (:instance fn-sjh-rd-okp-of-orr (oc (fn-otm-shed-ocfg oc id)))
                 (:instance fn-sjh-rd-okp-of-shed)
                 (:instance fn-sjh-rd-shed-view)
                 (:instance fn-sjh-rd-views-okp-of-same-view (o (fn-ocfg-owner oc))
                            (o2 (fn-ocfg-owner (fn-otm-shed-ocfg oc id))))))))

(defthm fn-sjh-rd-conn-closed-fields
  (let ((c2 (fn-oas-conn-closed c)))
    (and (equal (fn-own-conn-id c2) (fn-own-conn-id c))
         (equal (fn-own-conn-version c2) (fn-own-conn-version c))
         (equal (fn-own-conn-archive c2) (fn-own-conn-archive c))
         (equal (fn-own-conn-index c2) (fn-own-conn-index c))
         (equal (fn-own-conn-group-index c2) (fn-own-conn-group-index c))
         (equal (fn-own-conn-control c2) (fn-own-conn-control c))))
  :hints (("Goal" :in-theory (e/d (fn-oas-conn-closed update-nth true-list-fix fn-own-conn-id fn-own-conn-version
                                   fn-own-conn-archive fn-own-conn-index fn-own-conn-group-index
                                   fn-own-conn-control fn-ag-car fn-ag-cdr)
                                  (fn-wire-make-state fn-wire-make-result fn-wire-result-state)))))

(defthm fn-sjh-rd-conn-closed-pinp
  (equal (fn-scj-conn-pinp (fn-oas-conn-closed c) fn-arena fn-cat)
         (fn-scj-conn-pinp c fn-arena fn-cat))
  :hints (("Goal" :in-theory (union-theories '(fn-scj-conn-pinp fn-scj-conn-pinned-index fn-sjh-rd-conn-closed-fields)
                                             (theory 'minimal-theory)))))


(defthm fn-sjh-rd-owner-closed-owner
  (equal (fn-ocfg-owner (fn-oas-owner-closed oc id))
         (if (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))
             (fn-own-set-conns (fn-ocfg-owner oc)
                               (fn-own-replace-conn
                                (fn-oas-conn-closed (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))
                                (fn-own-conns (fn-ocfg-owner oc))))
           (fn-ocfg-owner oc)))
  :hints (("Goal" :in-theory '(fn-oas-owner-closed fn-sjh-ocfg-owner-of-with-owner))))

(defthm fn-sjh-rd-set-conns-fields
  (and (equal (fn-own-store (fn-own-set-conns o conns)) (fn-own-store o))
       (equal (fn-own-view (fn-own-set-conns o conns)) (fn-own-view o))
       (equal (fn-own-conns (fn-own-set-conns o conns)) conns))
  :hints (("Goal" :in-theory (enable fn-own-set-conns))))

(defthm fn-sjh-rd-owner-closed-okp
  (implies (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
           (fn-sjh-okp (fn-ocfg-owner (fn-oas-owner-closed oc id)) pending fn-arena fn-cat))
  :hints (("Goal" :cases ((fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))
           :in-theory (union-theories '(fn-sjh-rd-owner-closed-owner fn-sjh-rd-set-conns-fields
                                             fn-sjh-rd-conn-closed-pinp fn-sjh-rd-conn-closed-fields)
                                           (theory 'minimal-theory)))
          ("Subgoal 1"
           :use ((:instance fn-sjh-okp-unfolds (o (fn-ocfg-owner oc)))
                 (:instance fn-scj-versions-okp (o (fn-ocfg-owner oc)))
                 (:instance fn-scj-versions-okp (o (fn-own-set-conns (fn-ocfg-owner oc)
                                                  (fn-own-replace-conn
                                                   (fn-oas-conn-closed (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))
                                                   (fn-own-conns (fn-ocfg-owner oc))))))
                 (:instance fn-scj-invp-conns (o (fn-ocfg-owner oc)))
                 (:instance fn-scj-conns-pinp-find (conns (fn-own-conns (fn-ocfg-owner oc))))
                 (:instance fn-scjs-conns-pinp-of-replace
                            (conn (fn-oas-conn-closed (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))))
                            (conns (fn-own-conns (fn-ocfg-owner oc))))
                 (:instance fn-scj-invp-by-parts (o (fn-ocfg-owner oc))
                            (o2 (fn-own-set-conns (fn-ocfg-owner oc)
                                                  (fn-own-replace-conn
                                                   (fn-oas-conn-closed (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))
                                                   (fn-own-conns (fn-ocfg-owner oc))))))
                 (:instance fn-scjs-versions-of-replace
                            (conn (fn-oas-conn-closed (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))))
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (n (fn-own-view-version (fn-own-view (fn-ocfg-owner oc)))))
                 (:instance fn-scj-versions-atmost-find-conn
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (n (fn-own-view-version (fn-own-view (fn-ocfg-owner oc)))))
                 (:instance fn-sjh-okp-of-same-store-and-view
                            (o (fn-ocfg-owner oc))
                            (o2 (fn-own-set-conns (fn-ocfg-owner oc)
                                                  (fn-own-replace-conn
                                                   (fn-oas-conn-closed (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))
                                                   (fn-own-conns (fn-ocfg-owner oc))))))))))

(defun-nx fn-sjh-rd-result-okp (r pending fn-arena fn-cat)
  (fn-sjh-okp (fn-ocfg-owner (fn-own-tls-result-owner r)) pending fn-arena fn-cat))

(defthm fn-sjh-rd-close-result-okp
  (implies (fn-sjh-rd-result-okp r pending fn-arena fn-cat)
           (fn-sjh-rd-result-okp (fn-oas-close-result r id) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory '(fn-sjh-rd-result-okp fn-oas-close-result fn-scj-tls-result-owner-of-make
                               fn-sjh-rd-owner-closed-okp))))

(defthm fn-sjh-rd-whole-refusal-okp
  (implies (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
           (fn-sjh-rd-result-okp (fn-oas-whole-refusal oc id i end) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory '(fn-sjh-rd-result-okp fn-oas-whole-refusal fn-scj-tls-result-owner-of-make
                               fn-sjh-rd-owner-closed-okp))))

(defthm fn-sjh-rd-tiers-okp
  (implies (and (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
                (fn-sjh-rd-result-okp r1 pending fn-arena fn-cat))
           (fn-sjh-rd-result-okp (fn-oas-tiers oc r1 id i end slots) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory '(fn-oas-tiers fn-sjh-rd-close-result-okp fn-sjh-rd-whole-refusal-okp))))

(defthm fn-sjh-rd-with-allow-view
  (equal (fn-own-view (fn-ocfg-owner (fn-otm-owner-with-allow oc id allow))) (fn-own-view (fn-ocfg-owner oc)))
  :hints (("Goal" :in-theory '(fn-sjh-rd-with-allow-fields))))

(defthm fn-sjh-rd-otm-okp
  (implies (and (fn-scol-okp fn-arena fn-cat)
                (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
                (fn-sjh-views-okp views (fn-ocfg-owner oc) fn-arena fn-cat))
           (fn-sjh-rd-result-okp (fn-otm-read-span oc views id i end cache s fn-octets fn-arena fn-cat)
                                 pending fn-arena fn-cat))
  :hints (("Goal" :in-theory '(fn-sjh-rd-result-okp fn-sjh-rd-okp-of-otm))))

(defthm fn-sjh-rd-posting-off-okp
  (implies (and (fn-scol-okp fn-arena fn-cat)
                (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
                (fn-sjh-views-okp views (fn-ocfg-owner oc) fn-arena fn-cat))
           (fn-sjh-rd-result-okp (fn-oas-posting-off-read oc views id i end cache s fn-octets fn-arena fn-cat)
                                 pending fn-arena fn-cat))
  :hints (("Goal" :in-theory '(fn-sjh-rd-result-okp fn-oas-posting-off-read fn-scj-tls-result-owner-of-make
                               fn-sjh-rd-okp-of-with-allow)
           :use ((:instance fn-sjh-rd-okp-of-otm (oc (fn-otm-owner-with-allow oc id nil)))
                 (:instance fn-sjh-rd-okp-of-with-allow (allow nil))
                 (:instance fn-sjh-rd-with-allow-view (allow nil))
                 (:instance fn-sjh-rd-views-okp-of-same-view (o (fn-ocfg-owner oc))
                            (o2 (fn-ocfg-owner (fn-otm-owner-with-allow oc id nil))))))))

(defthm fn-sjh-rd-oas-okp
  (implies (and (fn-scol-okp fn-arena fn-cat)
                (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
                (fn-sjh-views-okp views (fn-ocfg-owner oc) fn-arena fn-cat))
           (fn-sjh-rd-result-okp (fn-oas-read-span oc views id i end cache s slots fn-octets fn-arena fn-cat)
                                 pending fn-arena fn-cat))
  :hints (("Goal" :in-theory '(fn-oas-read-span fn-sjh-rd-otm-okp fn-sjh-rd-posting-off-okp fn-sjh-rd-tiers-okp))))


(defthm fn-sjh-rd-shut-read-okp
  (implies (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
           (fn-sjh-rd-result-okp (fn-mca-shut-read oc id i end) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory '(fn-sjh-rd-result-okp fn-mca-shut-read fn-scj-tls-result-owner-of-make
                               fn-sjh-rd-owner-closed-okp))))

(defthm fn-sjh-rd-refused-read-okp
  (implies (and (fn-scol-okp fn-arena fn-cat)
                (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
                (fn-sjh-views-okp views (fn-ocfg-owner oc) fn-arena fn-cat))
           (fn-sjh-rd-result-okp (fn-mca-refused-read oc views id i end cache s fn-octets fn-arena fn-cat)
                                 pending fn-arena fn-cat))
  :hints (("Goal" :in-theory '(fn-mca-refused-read fn-sjh-rd-posting-off-okp fn-sjh-rd-close-result-okp))))

; The read the host calls (host/owner-host.lisp fn-owner-chunk-span-at):
; fn-mca-read-span's result, whichever credit branch it takes.
(defthm fn-sjh-rd-mca-okp
  (implies (and (fn-scol-okp fn-arena fn-cat)
                (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
                (fn-sjh-views-okp views (fn-ocfg-owner oc) fn-arena fn-cat))
           (fn-sjh-rd-result-okp (car (fn-mca-read-span credits oc views id i end s slots reserve
                                                        fn-octets fn-arena fn-cat))
                                 pending fn-arena fn-cat))
  :hints (("Goal" :in-theory '(fn-mca-read-span car-cons fn-sjh-rd-oas-okp fn-sjh-rd-refused-read-okp
                               fn-sjh-rd-shut-read-okp))))

; KEYSTONE (the join carried across the host's served read).
; host/owner-host.lisp fn-owner-chunk-span-at installs the owner of
; (car (fn-mca-read-span CREDITS OC VIEWS ID START END cache SCHED SLOTS RESERVE
; ...)); fn-sjh-okp with the same pending row, under the two named premises
; above.
(defthm fn-sjh-okp-at-owner-chunk-span
  (implies (and (fn-scol-okp fn-arena fn-cat)
                (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
                (fn-sjh-views-okp views (fn-ocfg-owner oc) fn-arena fn-cat))
           (fn-sjh-okp (fn-ocfg-owner
                        (fn-own-tls-result-owner
                         (car (fn-mca-read-span credits oc views id i end s slots reserve
                                                fn-octets fn-arena fn-cat))))
                       pending fn-arena fn-cat))
  :hints (("Goal" :in-theory '(fn-sjh-rd-result-okp)
           :use ((:instance fn-sjh-rd-mca-okp)))))
