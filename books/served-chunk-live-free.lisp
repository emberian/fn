;; served-chunk-live-free.lisp -- a served chunk that selects nothing does not
;; read the committed view (lane join-f2-2/-3, 2026-09-29; PKT-731, the P3
;; chunk form).
;;
;; The live view a served connection carries (fn-served-conn-live) is read
;; only by fn-served-repin, which only a GROUP or LISTGROUP command reaches
;; (books/served.lisp fn-served-dispatch).  So a chunk that frames no such
;; command -- the counted read the host runs per socket read,
;; fn-served-step-counted-fast -- consumes the same octets and answers the
;; same effects whatever the live view (the served keystone below).  Lifted to
;; the owner's reference read (fn-own-read-tls-prefix), to another
;; connection's post (with fn-own-pinned-view-survives-other-post) and to the
;; host's catalog read (fn-scr-ocfg-read-span, through
;; fn-scr-ocfg-read-span-is-reference-under-ocl-relation).
;;
;; Scope: both sides are read over the same arena and catalog, as the
;; per-event form (fn-own-other-post-keeps-a-non-selecting-read-step) is; that
;; the post's own arena and catalog appends leave a pinned read unchanged is
;; the store's frame, not this book's.

(in-package "ACL2")

(include-book "owner-served-invariants")
(include-book "served-catalog-chain")

(local (in-theory (disable (tau-system))))

(defun fn-scl-with-live (conn live)
  (declare (xargs :guard t))
  (fn-served-make-conn-live (fn-served-conn-wire conn)
                            (fn-served-conn-session conn)
                            (fn-served-conn-archive conn)
                            (fn-served-conn-config conn)
                            (fn-served-conn-observation conn)
                            (fn-served-conn-injection conn)
                            (fn-served-conn-verdicts conn)
                            (fn-served-conn-index conn)
                            (fn-served-conn-group-index conn)
                            (fn-served-conn-control conn)
                            (fn-served-conn-pinned conn)
                            live))

(defun fn-scl-events-select-nothing-p (events)
  (declare (xargs :guard t))
  (if (consp events)
      (and (not (fn-served-advance-eventp (car events)))
           (fn-scl-events-select-nothing-p (cdr events)))
    t))

(defthm fn-scl-with-live-fields
  (and (equal (fn-served-conn-wire (fn-scl-with-live conn live)) (fn-served-conn-wire conn))
       (equal (fn-served-conn-session (fn-scl-with-live conn live)) (fn-served-conn-session conn))
       (equal (fn-served-conn-archive (fn-scl-with-live conn live)) (fn-served-conn-archive conn))
       (equal (fn-served-conn-config (fn-scl-with-live conn live)) (fn-served-conn-config conn))
       (equal (fn-served-conn-observation (fn-scl-with-live conn live)) (fn-served-conn-observation conn))
       (equal (fn-served-conn-injection (fn-scl-with-live conn live)) (fn-served-conn-injection conn))
       (equal (fn-served-conn-verdicts (fn-scl-with-live conn live)) (fn-served-conn-verdicts conn))
       (equal (fn-served-conn-index (fn-scl-with-live conn live)) (fn-served-conn-index conn))
       (equal (fn-served-conn-group-index (fn-scl-with-live conn live)) (fn-served-conn-group-index conn))
       (equal (fn-served-conn-control (fn-scl-with-live conn live)) (fn-served-conn-control conn))
       (equal (fn-served-conn-pinned (fn-scl-with-live conn live)) (fn-served-conn-pinned conn))
       (equal (fn-served-conn-live (fn-scl-with-live conn live)) live))
  :hints (("Goal" :in-theory (enable fn-scl-with-live))))

(defthm fn-scl-with-live-of-make-conn-live
  (equal (fn-scl-with-live (fn-served-make-conn-live wire session archive config observation
                                                     injection verdicts index buckets
                                                     control pinned live0)
                           live)
         (fn-served-make-conn-live wire session archive config observation
                                   injection verdicts index buckets
                                   control pinned live))
  :hints (("Goal" :in-theory (enable fn-scl-with-live))))

(defthm fn-scl-with-live-of-conn-with-wire
  (equal (fn-served-conn-with-wire (fn-scl-with-live conn live) wire)
         (fn-scl-with-live (fn-served-conn-with-wire conn wire) live))
  :hints (("Goal" :in-theory (enable fn-scl-with-live fn-served-conn-with-wire))))

(defthm fn-scl-dispatch-core-of-with-live
  (equal (fn-served-dispatch-core (fn-scl-with-live conn live) event fn-arena)
         (fn-served-make-result
          (fn-scl-with-live (fn-served-result-conn (fn-served-dispatch-core conn event fn-arena))
                            live)
          (fn-served-result-effects (fn-served-dispatch-core conn event fn-arena))))
  :hints (("Goal" :in-theory (union-theories
    '(fn-served-dispatch-core fn-served-conn-pinned-index fn-scl-with-live-fields
      fn-scl-with-live-of-make-conn-live fn-served-result-conn fn-served-result-effects
      fn-served-make-result fn-ag-car fn-ag-cdr car-cons cdr-cons)
    (theory 'minimal-theory)))))

(defthm fn-scl-dispatch-of-with-live-selecting-nothing
  (implies (not (fn-served-advance-eventp event))
           (equal (fn-served-dispatch (fn-scl-with-live conn live) event fn-arena)
                  (fn-served-make-result
                   (fn-scl-with-live (fn-served-result-conn (fn-served-dispatch conn event fn-arena))
                                     live)
                   (fn-served-result-effects (fn-served-dispatch conn event fn-arena)))))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-served-dispatch-without-advance-is-core
                                fn-scl-dispatch-core-of-with-live)
                              (theory 'minimal-theory)))))

(defthm fn-scl-dispatch-events-of-with-live-selecting-nothing
  (implies (fn-scl-events-select-nothing-p events)
           (equal (fn-served-dispatch-events (fn-scl-with-live conn live) events fn-arena)
                  (fn-served-make-result
                   (fn-scl-with-live (fn-served-result-conn
                                      (fn-served-dispatch-events conn events fn-arena))
                                     live)
                   (fn-served-result-effects (fn-served-dispatch-events conn events fn-arena)))))
  :hints (("Goal" :induct (fn-served-dispatch-events conn events fn-arena)
           :in-theory (disable fn-served-dispatch fn-scl-with-live fn-served-advance-eventp))))

(defthm fn-scl-haltedp-of-with-live
  (equal (fn-served-haltedp (fn-scl-with-live conn live)) (fn-served-haltedp conn))
  :hints (("Goal" :in-theory (enable fn-served-haltedp fn-served-quitp
                                     fn-served-tls-handshakingp))))

(in-theory (disable fn-scl-with-live))

(defthm fn-scl-feed-byte-of-with-live-selecting-nothing
  (implies (fn-scl-events-select-nothing-p
            (fn-wire-result-events (fn-wire-feed-byte (fn-served-conn-wire conn) byte)))
           (equal (fn-served-feed-byte (fn-scl-with-live conn live) byte fn-arena)
                  (fn-served-make-result
                   (fn-scl-with-live (fn-served-result-conn
                                      (fn-served-feed-byte conn byte fn-arena))
                                     live)
                   (fn-served-result-effects (fn-served-feed-byte conn byte fn-arena)))))
  :hints (("Goal" :in-theory (e/d (fn-served-feed-byte)
                                  (fn-served-dispatch-events fn-wire-feed-byte)))))

; A chunk selects nothing: no event the counted read frames before it stops
; (the octets run out, the wire closes, the connection halts, or a
; submission yields) is a GROUP or LISTGROUP command.
(defun fn-scl-counted-selects-nothing-p (conn octets fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (fn-wire-fast-statep (fn-served-conn-wire conn))
                  :verify-guards nil
                  :measure (len octets)))
  (if (or (not (consp octets))
          (fn-served-closed-wirep (fn-served-conn-wire conn))
          (fn-served-haltedp conn))
      t
    (and (fn-scl-events-select-nothing-p
          (fn-wire-result-events (fn-wire-feed-byte (fn-served-conn-wire conn) (car octets))))
         (let ((here (fn-served-feed-byte conn (car octets) fn-arena)))
           (or (and (fn-served-submission (fn-served-result-effects here)) t)
               (fn-scl-counted-selects-nothing-p (fn-served-result-conn here)
                                                 (cdr octets) fn-arena))))))

(verify-guards fn-scl-counted-selects-nothing-p
  :hints (("Goal"
           :in-theory (disable fn-served-feed-byte fn-wire-fast-statep fn-wire-feed-byte
                               fn-served-feed-byte-preserves-fast-statep)
           :use ((:instance fn-served-feed-byte-preserves-fast-statep
                            (byte (car octets)))))))

(defthm fn-scl-feed-counted-of-with-live-selecting-nothing
  (implies (fn-scl-counted-selects-nothing-p conn octets fn-arena)
           (let ((fed (fn-served-feed-counted conn octets fn-arena)))
             (equal (fn-served-feed-counted (fn-scl-with-live conn live) octets fn-arena)
                    (fn-served-counted-make
                     (fn-served-counted-consumed fed)
                     (fn-served-make-result
                      (fn-scl-with-live (fn-served-result-conn (fn-served-counted-result fed))
                                        live)
                      (fn-served-result-effects (fn-served-counted-result fed)))))))
  :hints (("Goal" :induct (fn-scl-counted-selects-nothing-p conn octets fn-arena)
           :in-theory (e/d (fn-served-feed-counted fn-served-counted-make
                            fn-served-counted-consumed fn-served-counted-result
                            fn-served-make-result fn-served-result-conn
                            fn-served-result-effects fn-ag-car fn-ag-cdr)
                           (fn-served-feed-byte fn-wire-feed-byte
                               fn-served-haltedp fn-served-closed-wirep
                               fn-scl-events-select-nothing-p
                               fn-served-feed-counted-result-is-feed-of-consumed-prefix)))))

; KEYSTONE (PKT-731, served level).  A chunk that selects nothing answers
; the same whatever the connection's live view: the consumed count and the
; effects are equal, and the connection after is the one after the chunk
; with the other live view.  The live view is read only by fn-served-repin,
; which only a GROUP or LISTGROUP command reaches (fn-served-dispatch).
(defthm fn-scl-step-counted-fast-of-with-live-selecting-nothing
  (implies (fn-scl-counted-selects-nothing-p conn octets fn-arena)
           (let ((c (fn-served-step-counted-fast conn octets fn-arena)))
             (equal (fn-served-step-counted-fast (fn-scl-with-live conn live) octets fn-arena)
                    (fn-served-counted-make
                     (fn-served-counted-consumed c)
                     (fn-served-make-result
                      (fn-scl-with-live (fn-served-result-conn (fn-served-counted-result c))
                                        live)
                      (fn-served-result-effects (fn-served-counted-result c)))))))
  :hints (("Goal" :in-theory (e/d (fn-served-step-counted-fast fn-served-step-counted-core
                                   fn-served-counted-make
                                   fn-served-counted-consumed fn-served-counted-result
                                   fn-served-make-result fn-served-result-conn
                                   fn-served-result-effects fn-ag-car fn-ag-cdr)
                                  (fn-served-feed-counted fn-served-closed-wirep
                                   fn-scl-counted-selects-nothing-p fn-wire-fast-statep
                                   fn-served-feed-counted-result-is-feed-of-consumed-prefix
                                   fn-served-step-counted-result-is-step-of-consumed-prefix)))))

(defthm fn-scl-own-served-conn-is-with-live
  (implies (equal (fn-own-clock o2) (fn-own-clock o))
           (equal (fn-own-served-conn o2 conn session)
                  (fn-scl-with-live (fn-own-served-conn o conn session)
                                    (fn-own-view-live (fn-own-view o2)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-own-served-conn fn-scl-with-live))))

(defthm fn-scl-reader-live-session-is-its-own-by-definition
  (implies (not (fn-peer-session-cfg (fn-auth-session-base (fn-own-conn-session conn))))
           (equal (fn-own-conn-live-session o conn) (fn-own-conn-session conn)))
  :hints (("Goal" :in-theory (enable fn-own-conn-live-session))))

; The reference read's consumed count and effects are the counted served
; step's over the connection's served view.
(defthm fn-scl-own-read-tls-prefix-answer-unfolds
  (let ((conn (fn-own-find-conn id (fn-own-conns o))))
    (and (equal (fn-own-tls-result-consumed (fn-own-read-tls-prefix o id octets fn-arena))
                (if conn
                    (fn-served-counted-consumed
                     (fn-served-step-counted-fast (fn-own-tls-served-conn o conn) octets fn-arena))
                  (len octets)))
         (equal (fn-own-tls-result-effects (fn-own-read-tls-prefix o id octets fn-arena))
                (if conn
                    (fn-served-result-effects
                     (fn-served-counted-result
                      (fn-served-step-counted-fast (fn-own-tls-served-conn o conn) octets fn-arena)))
                  nil))))
  :hints (("Goal" :in-theory (e/d (fn-own-read-tls-prefix fn-own-tls-make-result
                                   fn-own-tls-result-consumed fn-own-tls-result-effects
                                   fn-own-finish-read)
                                  (fn-served-step-counted-fast fn-own-tls-served-conn
                                   fn-own-set-conns fn-own-enqueue fn-own-replace-conn
                                   fn-own-remove-conn fn-own-conn-boundedp
                                   fn-own-conn-make-group-indexed fn-own-sub-make-author)))))

; KEYSTONE (PKT-731, the owner's reference read).  Two owners that agree on
; connection ID's record, the clock and the connection's live session
; answer a chunk that selects nothing with the same consumed count and the
; same effects, whatever their committed views.
(defthm fn-scl-own-read-tls-prefix-selecting-nothing-ignores-the-view
  (let ((conn (fn-own-find-conn id (fn-own-conns o))))
    (implies (and (equal (fn-own-find-conn id (fn-own-conns o2)) conn)
                  (equal (fn-own-clock o2) (fn-own-clock o))
                  (equal (fn-own-conn-live-session o2 conn)
                         (fn-own-conn-live-session o conn))
                  (fn-scl-counted-selects-nothing-p (fn-own-tls-served-conn o conn)
                                                    octets fn-arena))
             (and (equal (fn-own-tls-result-consumed (fn-own-read-tls-prefix o2 id octets fn-arena))
                         (fn-own-tls-result-consumed (fn-own-read-tls-prefix o id octets fn-arena)))
                  (equal (fn-own-tls-result-effects (fn-own-read-tls-prefix o2 id octets fn-arena))
                         (fn-own-tls-result-effects (fn-own-read-tls-prefix o id octets fn-arena))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-own-tls-served-conn fn-served-counted-make
                                   fn-served-counted-consumed fn-served-counted-result
                                   fn-served-make-result fn-served-result-effects
                                   fn-ag-car fn-ag-cdr)
                                  (fn-served-step-counted-fast fn-own-served-conn
                                   fn-own-conn-live-session fn-scl-counted-selects-nothing-p
                                   fn-own-read-tls-prefix))
           :use ((:instance fn-scl-step-counted-fast-of-with-live-selecting-nothing
                            (conn (fn-own-tls-served-conn o (fn-own-find-conn id (fn-own-conns o))))
                            (live (fn-own-view-live (fn-own-view o2))))
                 (:instance fn-scl-own-served-conn-is-with-live
                            (conn (fn-own-find-conn id (fn-own-conns o)))
                            (session (fn-own-conn-live-session o (fn-own-find-conn id (fn-own-conns o)))))))))

; The configured owner's reference read answers what its owner's does.
(defthm fn-scl-ocfg-read-tls-prefix-answer-unfolds
  (and (equal (fn-own-tls-result-consumed (fn-ocfg-read-tls-prefix oc id octets fn-arena))
              (fn-own-tls-result-consumed (fn-own-read-tls-prefix (fn-ocfg-owner oc) id octets fn-arena)))
       (equal (fn-own-tls-result-effects (fn-ocfg-read-tls-prefix oc id octets fn-arena))
              (fn-own-tls-result-effects (fn-own-read-tls-prefix (fn-ocfg-owner oc) id octets fn-arena))))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-ocfg-read-tls-prefix fn-own-tls-make-result
                                fn-own-tls-result-consumed fn-own-tls-result-effects
                                fn-ag-car fn-ag-cdr car-cons cdr-cons)
                              (theory 'minimal-theory)))))

; KEYSTONE (PKT-731, P3's chunk form over the reference read).  After any
; writer events and another connection's outcome, a reader's chunk that
; selects nothing consumes the same octets and answers the same effects as
; before (the per-event form is fn-own-other-post-keeps-a-non-selecting-
; read-step).  A reader: its session carries no peer configuration, so its
; live session is its own (a peer's reads the store's node).
(defthm fn-scl-other-post-keeps-a-chunk-selecting-nothing
  (let ((conn (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))))
    (implies (and (fn-ocfg-writer-eventsp events)
                  (not (equal id sub-id))
                  (not (fn-peer-session-cfg (fn-auth-session-base (fn-own-conn-session conn))))
                  (fn-scl-counted-selects-nothing-p
                   (fn-own-tls-served-conn (fn-ocfg-owner oc) conn) octets fn-arena))
             (let* ((oc1 (fn-ocfg-run oc events fn-arena))
                    (oc2 (fn-ocfg-with-owner
                          oc1 (cdr (fn-own-outcome (fn-ocfg-owner oc1) sub-id word)))))
               (and (equal (fn-own-tls-result-consumed (fn-ocfg-read-tls-prefix oc2 id octets fn-arena))
                           (fn-own-tls-result-consumed (fn-ocfg-read-tls-prefix oc id octets fn-arena)))
                    (equal (fn-own-tls-result-effects (fn-ocfg-read-tls-prefix oc2 id octets fn-arena))
                           (fn-own-tls-result-effects (fn-ocfg-read-tls-prefix oc id octets fn-arena)))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-own-pinned-view-survives-other-post)
                 (:instance fn-scl-own-read-tls-prefix-selecting-nothing-ignores-the-view
                            (o (fn-ocfg-owner oc))
                            (o2 (fn-ocfg-owner
                                 (fn-ocfg-with-owner
                                  (fn-ocfg-run oc events fn-arena)
                                  (cdr (fn-own-outcome (fn-ocfg-owner (fn-ocfg-run oc events fn-arena))
                                                       sub-id word)))))))
           :in-theory (e/d (fn-scl-reader-live-session-is-its-own-by-definition)
                           (fn-ocfg-read-tls-prefix fn-own-read-tls-prefix fn-ocfg-with-owner
                            fn-ocfg-run fn-own-outcome fn-own-conn-live-session
                            fn-scl-counted-selects-nothing-p fn-own-tls-served-conn)))))

; P3's chunk form at the host's catalog read (host/owner-host.lisp
; fn-owner-chunk-span-at: fn-mca-read-span, through fn-oas-read-span,
; fn-otm-read-span and fn-orr-read-span, reads by fn-scr-ocfg-read-span).
; Each side is the reference read of the chunk's octets by
; fn-scr-ocfg-read-span-is-reference-under-ocl-relation, over the one arena
; and catalog (the book's scope, above).
(defthm fn-scl-host-chunk-selecting-nothing-survives-other-post
  (let* ((conn (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))
         (oc1 (fn-ocfg-run oc events fn-arena))
         (oc2 (fn-ocfg-with-owner
               oc1 (cdr (fn-own-outcome (fn-ocfg-owner oc1) sub-id word)))))
    (implies (and (fn-gacc-okp cache) (fn-ocfg-writer-eventsp events)
                  (not (equal id sub-id))
                  (not (fn-peer-session-cfg (fn-auth-session-base (fn-own-conn-session conn))))
                  (fn-scl-counted-selects-nothing-p
                   (fn-own-tls-served-conn (fn-ocfg-owner oc) conn)
                   (fn-oct-slice-list i end fn-octets) fn-arena)
                  (fn-ocl-relation oc)
                  (fn-scar-view-indexedp (fn-ocfg-owner oc))
                  (fn-scr-owner-catalogp (fn-ocfg-owner oc) id fn-arena fn-cat)
                  (fn-ocl-relation oc2)
                  (fn-scar-view-indexedp (fn-ocfg-owner oc2))
                  (fn-scr-owner-catalogp (fn-ocfg-owner oc2) id fn-arena fn-cat)
                  (fn-scol-okp fn-arena fn-cat)
                  (natp i) (natp end))
             (and (equal (fn-own-tls-result-consumed
                          (fn-scr-ocfg-read-span oc2 id i end cache fn-octets fn-arena fn-cat))
                         (fn-own-tls-result-consumed
                          (fn-scr-ocfg-read-span oc id i end cache fn-octets fn-arena fn-cat)))
                  (equal (fn-own-tls-result-effects
                          (fn-scr-ocfg-read-span oc2 id i end cache fn-octets fn-arena fn-cat))
                         (fn-own-tls-result-effects
                          (fn-scr-ocfg-read-span oc id i end cache fn-octets fn-arena fn-cat))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-scl-other-post-keeps-a-chunk-selecting-nothing
                            (octets (fn-oct-slice-list i end fn-octets)))
                 (:instance fn-scr-ocfg-read-span-is-reference-under-ocl-relation)
                 (:instance fn-scr-ocfg-read-span-is-reference-under-ocl-relation
                            (oc (fn-ocfg-with-owner
                                 (fn-ocfg-run oc events fn-arena)
                                 (cdr (fn-own-outcome (fn-ocfg-owner (fn-ocfg-run oc events fn-arena))
                                                      sub-id word))))))
           :in-theory (union-theories '() (theory 'minimal-theory)))))
