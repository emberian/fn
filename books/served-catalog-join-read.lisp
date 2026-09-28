; served-catalog-join-read.lisp -- the host's served read keeps the catalog
; invariant (lane sca-join-4, 2026-09-27; PRF-302, step 5 of the join's
; discharge).
;
; host/owner-host.lisp fn-owner-chunk-span runs fn-scr-ocfg-read-span for a
; socket region.  Under fn-scj-invp it is the carried read (the chain's
; equation), which changes only the connection it serves: the store, the
; view and the catalog are untouched, and the connection record it writes
; back is built from the served connection after the span, which keeps the
; chain's catalog fact byte by byte (fn-scr-conn-okp-of-scar-feed-byte) and
; so across the span.

(in-package "ACL2")

(include-book "served-catalog-join-conns")
(include-book "owner-reader-read")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-scr-conn-okp))))

(local (in-theory (disable fn-nntp-article-idp-is-consp fn-scat-article-idp-is-msgid-idp
                           fn-scat-msgid-idp fn-nntp-index-msgid-okp-stringp
                           fn-nntp-index-msgid-okp fn-cp-id-length-bound)))

(local (defthm fn-scj-counted-result-of-make
  (equal (fn-served-counted-result (fn-served-counted-make n r)) r)
  :hints (("Goal" :in-theory (enable fn-served-counted-result fn-served-counted-make fn-ag-car fn-ag-cdr)))))

(local (defthm fn-scj-result-conn-of-make-result
  (equal (fn-served-result-conn (fn-served-make-result conn effects)) conn)))

(defthm fn-scj-conn-okp-of-scar-feed-span
  (implies (fn-scr-conn-okp conn fn-arena fn-cat)
           (fn-scr-conn-okp (fn-served-result-conn
                             (fn-served-counted-result
                              (fn-scar-feed-span conn i end live trie arts fn-octets fn-arena)))
                            fn-arena fn-cat))
  :hints (("Goal" :induct (fn-scar-feed-span conn i end live trie arts fn-octets fn-arena)
           :in-theory (e/d (fn-scar-feed-span fn-served-counted-result fn-served-counted-make)
                           (fn-scr-conn-okp fn-scar-feed-byte fn-served-submission fn-scar-feed-span-is-feed-counted
                            fn-served-closed-wirep fn-served-haltedp)))))

(defthm fn-scj-conn-okp-of-scar-step-span-fast
  (implies (fn-scr-conn-okp conn fn-arena fn-cat)
           (fn-scr-conn-okp (fn-served-result-conn
                             (fn-served-counted-result
                              (fn-scar-step-span-fast conn i end live trie arts fn-octets fn-arena)))
                            fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-scar-step-span-fast fn-scar-step-span-core)
                                  (fn-scr-conn-okp fn-scar-feed-span fn-served-closed-wirep fn-scar-feed-span-is-feed-counted fn-scar-step-span-core-is-step-counted-core fn-scar-step-span-fast-is-step-counted-fast
                                   fn-wire-fast-statep)))))

; -----------------------------------------------------------------------------
; The owner after the read.

(defthm fn-scjr-conns-pinp-of-replace
  (implies (and (fn-scj-conns-pinp conns fn-arena fn-cat)
                (fn-scj-conn-pinp next fn-arena fn-cat))
           (fn-scj-conns-pinp (fn-own-replace-conn next conns) fn-arena fn-cat))
  :hints (("Goal" :induct (fn-own-replace-conn next conns)
           :in-theory (enable fn-scj-conns-pinp))))

(defthm fn-scjr-conns-pinp-of-remove
  (implies (fn-scj-conns-pinp conns fn-arena fn-cat)
           (fn-scj-conns-pinp (fn-own-remove-conn id conns) fn-arena fn-cat))
  :hints (("Goal" :induct (fn-own-remove-conn id conns)
           :in-theory (enable fn-scj-conns-pinp))))

; The record the read writes back is the served connection's pin.
(defthm fn-scj-conn-pinp-of-written-back
  (equal (fn-scj-conn-pinp
          (fn-own-conn-make-group-indexed
           id (fn-served-pinned-version (fn-served-conn-pinned sconn))
           frontier wire session (fn-served-conn-archive sconn) config observation verdicts
           (fn-served-conn-index sconn) (fn-served-conn-group-index sconn)
           (fn-served-conn-control sconn))
          fn-arena fn-cat)
         (fn-scr-conn-catalogp sconn fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-scj-conn-pinp fn-scj-conn-pinned-index
                                   fn-scr-conn-catalogp fn-scr-fields-catalogp)
                                  (fn-scr-catalogp fn-own-conn-make-group-indexed)))))

(defthm fn-scj-served-conn-okp-of-pins
  (implies (and (fn-scj-conns-pinp (fn-own-conns o) fn-arena fn-cat)
                (fn-scj-live-okp (fn-own-view o) fn-arena fn-cat)
                (fn-own-find-conn id (fn-own-conns o)))
           (fn-scr-conn-okp (fn-own-tls-served-conn o (fn-own-find-conn id (fn-own-conns o)))
                            fn-arena fn-cat))
  :hints (("Goal" :use ((:instance fn-scj-owner-catalogp-of-conns-and-live))
           :in-theory (e/d (fn-scr-owner-catalogp) (fn-scj-owner-catalogp-of-conns-and-live
                                                    fn-scr-conn-okp fn-own-tls-served-conn)))))

(defthm fn-scj-finish-read-fields
  (let ((o2 (cdr (fn-scar-finish-read o conn result live))))
    (and (equal (fn-own-view o2) (fn-own-view o))
         (equal (fn-own-store o2) (fn-own-store o))))
  :hints (("Goal" :in-theory (e/d (fn-scar-finish-read fn-own-set-conns fn-own-enqueue)
                                  (fn-scar-conn-boundedp fn-own-conn-make-group-indexed)))))

(defthm fn-scj-conns-pinp-of-scar-finish-read
  (implies (and (fn-scj-conns-pinp (fn-own-conns o) fn-arena fn-cat)
                (fn-scr-conn-okp (fn-served-result-conn result) fn-arena fn-cat))
           (fn-scj-conns-pinp (fn-own-conns (cdr (fn-scar-finish-read o conn result live)))
                              fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-scar-finish-read fn-scr-conn-okp fn-own-set-conns
                                   fn-own-enqueue)
                                  (fn-scr-conn-catalogp fn-scr-live-catalogp
                                   fn-scar-conn-boundedp
                                   fn-own-conn-make-group-indexed fn-scj-conn-pinp)))))

(defthm fn-scj-scar-own-read-span-keeps
  (implies (and (fn-scj-conns-pinp (fn-own-conns o) fn-arena fn-cat)
                (fn-scj-live-okp (fn-own-view o) fn-arena fn-cat))
           (let ((o2 (fn-own-tls-result-owner (fn-scar-own-read-span o id i end fn-octets fn-arena))))
             (and (fn-scj-conns-pinp (fn-own-conns o2) fn-arena fn-cat)
                  (equal (fn-own-view o2) (fn-own-view o))
                  (equal (fn-own-store o2) (fn-own-store o)))))
  :hints (("Goal" :cases ((fn-own-find-conn id (fn-own-conns o)))
           :in-theory (e/d (fn-scar-own-read-span fn-own-tls-result-owner fn-own-tls-make-result)
                           (fn-scar-step-span-fast-is-step-counted-fast
                            fn-scar-own-read-span-is-own-read-tls-prefix
                            fn-scar-finish-read fn-scar-step-span-fast
                            fn-own-tls-served-conn fn-scr-conn-okp)))
          ("Subgoal 1" :use ((:instance fn-scj-conns-pinp-of-scar-finish-read
                                        (conn (fn-own-find-conn id (fn-own-conns o)))
                                        (live (fn-sn-node (fn-own-store o)))
                                        (result (fn-served-counted-result
                                                 (fn-scar-step-span-fast
                                                  (fn-own-tls-served-conn o (fn-own-find-conn id (fn-own-conns o)))
                                                  i end (fn-sn-node (fn-own-store o))
                                                  (fn-own-view-index (fn-own-view o))
                                                  (fn-state-articles (fn-own-view-archive (fn-own-view o)))
                                                  fn-octets fn-arena))))
                             (:instance fn-scj-served-conn-okp-of-pins)
                             (:instance fn-scj-conn-okp-of-scar-step-span-fast
                                        (conn (fn-own-tls-served-conn o (fn-own-find-conn id (fn-own-conns o))))
                                        (live (fn-sn-node (fn-own-store o)))
                                        (trie (fn-own-view-index (fn-own-view o)))
                                        (arts (fn-state-articles (fn-own-view-archive (fn-own-view o)))))))))

(defthm fn-scj-scr-own-read-span-keeps
  (implies (and (fn-scol-okp fn-arena fn-cat)
                (fn-scj-conns-pinp (fn-own-conns o) fn-arena fn-cat)
                (fn-scj-live-okp (fn-own-view o) fn-arena fn-cat))
           (let ((o2 (fn-own-tls-result-owner (fn-scr-own-read-span o id i end fn-octets fn-arena fn-cat))))
             (and (fn-scj-conns-pinp (fn-own-conns o2) fn-arena fn-cat)
                  (equal (fn-own-view o2) (fn-own-view o))
                  (equal (fn-own-store o2) (fn-own-store o)))))
  :hints (("Goal" :use ((:instance fn-scr-own-read-span-is-scar-own-read-span)
                        (:instance fn-scj-owner-catalogp-of-conns-and-live)
                        (:instance fn-scj-scar-own-read-span-keeps))
           :in-theory (union-theories '() (theory 'minimal-theory)))))

(defthm fn-scj-invp-by-parts
  (implies (and (fn-scj-invp o fn-arena fn-cat)
                (equal (fn-own-view o2) (fn-own-view o))
                (equal (fn-own-store o2) (fn-own-store o))
                (fn-scj-conns-pinp (fn-own-conns o2) fn-arena fn-cat))
           (fn-scj-invp o2 fn-arena fn-cat))
  :hints (("Goal" :in-theory (enable fn-scj-invp fn-scj-vvp))))

; KEYSTONE (the host's served read keeps the invariant).  The owner
; fn-scr-own-read-span leaves satisfies fn-scj-invp whenever the owner it
; read satisfied it.
(defthm fn-scj-invp-of-scr-own-read-span
  (implies (and (fn-scol-okp fn-arena fn-cat) (fn-scj-invp o fn-arena fn-cat))
           (fn-scj-invp (fn-own-tls-result-owner
                         (fn-scr-own-read-span o id i end fn-octets fn-arena fn-cat))
                        fn-arena fn-cat))
  :hints (("Goal" :use ((:instance fn-scj-scr-own-read-span-keeps)
                        (:instance fn-scj-invp-by-parts
                                   (o2 (fn-own-tls-result-owner
                                        (fn-scr-own-read-span o id i end fn-octets fn-arena fn-cat)))))
           :in-theory (e/d (fn-scj-invp) (fn-scj-scr-own-read-span-keeps fn-scj-invp-by-parts
                                          fn-scr-own-read-span)))))

(defthm fn-scj-scr-ocfg-read-span-owner
  (equal (fn-ocfg-owner (fn-own-tls-result-owner (fn-scr-ocfg-read-span oc id i end fn-octets fn-arena fn-cat)))
         (fn-own-tls-result-owner (fn-scr-own-read-span (fn-ocfg-owner oc) id i end fn-octets fn-arena fn-cat)))
  :hints (("Goal" :in-theory (e/d (fn-scr-ocfg-read-span fn-ocfg-with-read-owner
                                   fn-own-tls-result-owner fn-own-tls-make-result)
                                  (fn-scr-own-read-span)))))

(defthm fn-scj-invp-conns
  (implies (fn-scj-invp o fn-arena fn-cat)
           (fn-scj-conns-pinp (fn-own-conns o) fn-arena fn-cat))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-scj-invp))))


(defthm fn-scj-tls-result-owner-of-make
  (equal (fn-own-tls-result-owner (fn-own-tls-make-result c e o r)) o)
  :hints (("Goal" :in-theory (enable fn-own-tls-result-owner fn-own-tls-make-result))))

(defthm fn-scj-orr-read-span-owner
  (equal (fn-ocfg-owner (fn-own-tls-result-owner
                         (fn-orr-read-span oc views id i end fn-octets fn-arena fn-cat)))
         (if (consp views)
             (fn-ocfg-owner
              (fn-ocfg-with-view
               (fn-own-tls-result-owner
                (fn-scr-ocfg-read-span (fn-ocfg-with-view oc (car views)) id i end fn-octets fn-arena fn-cat))
               (fn-own-view (fn-ocfg-owner oc))))
           (fn-own-tls-result-owner
            (fn-scr-own-read-span (fn-ocfg-owner oc) id i end fn-octets fn-arena fn-cat))))
  :hints (("Goal" :in-theory (union-theories '(fn-orr-read-span fn-ocfg-at-reader-view fn-ocv-reader-view
                                               fn-scj-tls-result-owner-of-make
                                               fn-scj-scr-ocfg-read-span-owner)
                                             (theory 'minimal-theory)))))

; A read at any view V the pins and V are live over keeps the pins, V and
; the store (the captured owner's store is the working owner's).
(defthm fn-scj-read-at-view-keeps
  (implies (and (fn-scol-okp fn-arena fn-cat)
                (fn-scj-conns-pinp (fn-own-conns (fn-ocfg-owner oc)) fn-arena fn-cat)
                (fn-scj-live-okp v fn-arena fn-cat))
           (let ((o2 (fn-ocfg-owner
                      (fn-ocfg-with-view
                       (fn-own-tls-result-owner
                        (fn-scr-ocfg-read-span (fn-ocfg-with-view oc v) id i end fn-octets fn-arena fn-cat))
                       w))))
             (and (fn-scj-conns-pinp (fn-own-conns o2) fn-arena fn-cat)
                  (equal (fn-own-view o2) w)
                  (equal (fn-own-store o2) (fn-own-store (fn-ocfg-owner oc))))))
  :hints (("Goal" :in-theory (union-theories '(fn-scj-scr-ocfg-read-span-owner)
                                             (theory 'minimal-theory))
           :use ((:instance fn-orr-with-view-fields)
                 (:instance fn-orr-with-view-fields
                            (oc (fn-own-tls-result-owner
                                 (fn-scr-ocfg-read-span (fn-ocfg-with-view oc v) id i end fn-octets fn-arena fn-cat)))
                            (v w))
                 (:instance fn-scj-scr-own-read-span-keeps
                            (o (fn-ocfg-owner (fn-ocfg-with-view oc v))))))))

; KEYSTONE (step 5, the read entry).  host/owner-host.lisp fn-owner-chunk-span
; calls fn-orr-read-span (books/owner-reader-read.lisp): with a capture held
; it reads at the captured reader view and puts the working view back.  The
; owner it leaves satisfies fn-scj-invp when the working owner did and the
; captured view (when there is one) is live over the catalog, as every
; pinned view is (a capture is a view the owner held, pinned like a
; connection).
(defthm fn-scj-invp-of-orr-read-span
  (implies (and (fn-scol-okp fn-arena fn-cat)
                (fn-scj-invp (fn-ocfg-owner oc) fn-arena fn-cat)
                (implies (consp views) (fn-scj-live-okp (car views) fn-arena fn-cat)))
           (fn-scj-invp (fn-ocfg-owner (fn-own-tls-result-owner
                                        (fn-orr-read-span oc views id i end fn-octets fn-arena fn-cat)))
                        fn-arena fn-cat))
  :hints (("Goal" :in-theory (union-theories '(fn-scj-orr-read-span-owner)
                                             (theory 'minimal-theory))
           :cases ((consp views)))
          ("Subgoal 2" :use ((:instance fn-scj-invp-of-scr-own-read-span (o (fn-ocfg-owner oc)))))
          ("Subgoal 1"
           :use ((:instance fn-scj-invp-conns (o (fn-ocfg-owner oc)))
                 (:instance fn-scj-read-at-view-keeps (v (car views)) (w (fn-own-view (fn-ocfg-owner oc))))
                 (:instance fn-scj-invp-by-parts
                            (o (fn-ocfg-owner oc))
                            (o2 (fn-ocfg-owner
                                 (fn-ocfg-with-view
                                  (fn-own-tls-result-owner
                                   (fn-scr-ocfg-read-span (fn-ocfg-with-view oc (car views))
                                                          id i end fn-octets fn-arena fn-cat))
                                  (fn-own-view (fn-ocfg-owner oc))))))))))

; KEYSTONE (the chain, with the catalog premise discharged by the carried
; invariant).  fn-scr-ocfg-read-span-is-reference-under-ocl-relation
; (books/served-catalog-chain.lisp) with fn-scr-owner-catalogp replaced by
; fn-scj-invp, which the owner's entries establish and its steps keep
; (this book's read keystones; books/served-catalog-join-frame*.lisp).
(defthm fn-scj-ocfg-read-span-is-reference-under-invp
  (implies (and (fn-scol-okp fn-arena fn-cat)
                (fn-ocl-relation oc)
                (fn-scar-view-indexedp (fn-ocfg-owner oc))
                (fn-scj-invp (fn-ocfg-owner oc) fn-arena fn-cat)
                (natp i) (natp end))
           (equal (fn-scr-ocfg-read-span oc id i end fn-octets fn-arena fn-cat)
                  (fn-ocfg-read-tls-prefix oc id (fn-oct-slice-list i end fn-octets) fn-arena)))
  :hints (("Goal" :in-theory (union-theories '() (theory 'minimal-theory))
           :use ((:instance fn-scj-invp-gives-owner-catalogp (o (fn-ocfg-owner oc)))
                 (:instance fn-scr-ocfg-read-span-is-reference-under-ocl-relation)))))
