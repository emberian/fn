; served-catalog-join-conns.lisp -- the chain premise fn-scr-owner-catalogp
; split into what each connection pins and what the owner's live view
; carries (lane sca-join-4, 2026-09-27; PRF-302, steps 3 to 5 of the
; join's discharge).
;
; fn-scr-owner-catalogp (books/served-catalog-chain.lisp) asks, of the
; connection a read names, the -cat keystone's hypothesis at the connection's
; pin and at the live view it may re-pin to.  The served connection the
; owner builds (fn-own-tls-served-conn) takes its archive, index, group
; index, control and pin from the owner's connection record and its live
; view from the owner's view (fn-own-view-live), so the premise is two
; facts that live in different places and change at different steps:
;
;   fn-scj-conn-pinp  -- one connection record, at its pinned version: its
;     archive is the catalog's view at fn-scr-view-of of that version, with
;     its pin correspondences and the number table fresh.  Only the
;     connection's own fields and the catalog enter; a step that keeps both
;     keeps it.
;   fn-scj-live-okp   -- the owner's view, as the live view a GROUP or
;     LISTGROUP re-pins to.
;
; fn-scj-conns-pinp is the first over every open connection; with the
; second it gives the chain premise at every connection identifier
; (fn-scj-owner-catalogp-of-conns-and-live).

(in-package "ACL2")

(include-book "served-catalog-join-finish")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-scr-conn-okp))))

(defun-nx fn-scj-conn-pinned-index (conn)
  (if (fn-own-conn-group-index conn)
      (fn-gidx-pin-with-control (fn-own-conn-index conn)
                                (fn-own-conn-group-index conn)
                                (fn-own-conn-control conn))
    (fn-own-conn-index conn)))

(defun-nx fn-scj-conn-pinp (conn fn-arena fn-cat)
  (fn-scr-catalogp (fn-own-conn-archive conn)
                   (fn-scj-conn-pinned-index conn)
                   (fn-scr-view-of (fn-own-conn-version conn) fn-cat)
                   fn-arena fn-cat))

(defun-nx fn-scj-conns-pinp (conns fn-arena fn-cat)
  (if (consp conns)
      (and (fn-scj-conn-pinp (car conns) fn-arena fn-cat)
           (fn-scj-conns-pinp (cdr conns) fn-arena fn-cat))
    t))

(defun-nx fn-scj-live-okp (view fn-arena fn-cat)
  (fn-scr-live-catalogp (fn-own-view-live view) fn-arena fn-cat))

; The served connection's catalog fact is its record's.
(defthm fn-scj-conn-catalogp-of-served-conn
  (equal (fn-scr-conn-catalogp (fn-own-served-conn o conn session) fn-arena fn-cat)
         (fn-scj-conn-pinp conn fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-own-served-conn fn-scj-conn-pinp fn-scj-conn-pinned-index
                                   fn-scr-conn-catalogp-of-make-conn-live fn-scr-fields-catalogp
                                   fn-served-pinned-version fn-served-pinned-make)
                                  (fn-scr-catalogp fn-scr-view-of fn-served-make-conn-live)))))

(defthm fn-scj-conns-pinp-find
  (implies (and (fn-scj-conns-pinp conns fn-arena fn-cat)
                (fn-own-find-conn id conns))
           (fn-scj-conn-pinp (fn-own-find-conn id conns) fn-arena fn-cat))
  :hints (("Goal" :induct (fn-own-find-conn id conns)
           :in-theory (e/d (fn-own-find-conn fn-scj-conns-pinp) (fn-scj-conn-pinp)))))

(defthm fn-scj-served-conn-live
  (equal (fn-served-conn-live (fn-own-served-conn o conn session))
         (fn-own-view-live (fn-own-view o)))
  :hints (("Goal" :in-theory (e/d (fn-own-served-conn) (fn-served-make-conn-live fn-own-view-live)))))

; The chain premise from the two.
(defthm fn-scj-owner-catalogp-of-conns-and-live
  (implies (and (fn-scj-conns-pinp (fn-own-conns o) fn-arena fn-cat)
                (fn-scj-live-okp (fn-own-view o) fn-arena fn-cat))
           (fn-scr-owner-catalogp o id fn-arena fn-cat))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scr-owner-catalogp fn-scr-conn-okp fn-own-tls-served-conn
                                fn-scj-live-okp fn-scj-conn-catalogp-of-served-conn
                                fn-scj-served-conn-live fn-scj-conns-pinp-find)
                              (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; VV: the view carries the store's acceptance articles and verdicts.  Every
; refresh at an idle store installs both (fn-scj-vvp-of-idle-refresh), and
; under it the refresh takes fn-ctl-refresh-visible's first arm: the visible
; list, the raw list, the verdicts and the withdrawals stay as they were
; (fn-scj-refresh-under-vvp).  So the view's articles move only when the
; store's acceptance articles or verdicts move, which only a finish does.

(defun-nx fn-scj-vvp (o)
  (and (equal (fn-own-view-raw (fn-own-view o))
              (fn-state-articles (fn-node-acceptance (fn-sn-node (fn-own-store o)))))
       (equal (fn-own-view-verdicts (fn-own-view o))
              (fn-sn-verdicts (fn-own-store o)))))

(defthm fn-scj-vvp-of-idle-refresh
  (implies (fn-own-store-idlep (fn-own-store o))
           (fn-scj-vvp (fn-own-refresh o)))
  :hints (("Goal" :in-theory (e/d (fn-own-refresh fn-scj-vvp)
                                  (fn-own-store-idlep fn-ctl-refresh-visible fn-ctl-refresh-withdrawals
                                   fn-ctl-refresh-withdrawn fn-midx-refresh fn-gidx-refresh
                                   fn-ctl-visible-state-of)))))

(defthm fn-scj-refresh-not-idle
  (implies (not (fn-own-store-idlep (fn-own-store o)))
           (equal (fn-own-refresh o) o))
  :hints (("Goal" :in-theory (e/d (fn-own-refresh) (fn-own-store-idlep)))))

(defthm fn-scj-refresh-under-vvp
  (implies (fn-scj-vvp o)
           (let ((view (fn-own-view o)) (view2 (fn-own-view (fn-own-refresh o))))
             (and (equal (fn-state-articles (fn-own-view-archive view2))
                         (fn-state-articles (fn-own-view-archive view)))
                  (equal (fn-own-view-raw view2) (fn-own-view-raw view))
                  (equal (fn-own-view-verdicts view2) (fn-own-view-verdicts view))
                  (equal (fn-own-view-withdrawals view2) (fn-own-view-withdrawals view)))))
  :hints (("Goal" :in-theory (e/d (fn-own-refresh fn-scj-vvp fn-ctl-refresh-visible
                                   fn-ctl-refresh-withdrawals)
                                  (fn-own-store-idlep fn-ctl-refresh-withdrawn fn-midx-refresh
                                   fn-gidx-refresh fn-ctl-visible-articles fn-ctl-visible-add
                                   fn-ctl-articles-withdrawals fn-ctl-prepend)))))

; -----------------------------------------------------------------------------
; Records that load no catalog row (every event but a plain article row and a
; signed composite): appending them keeps the rows invariant.

(defun fn-scj-no-rowsp (events)
  (declare (xargs :guard t))
  (if (consp events)
      (and (not (fn-scj-load-h (car events)))
           (fn-scj-no-rowsp (cdr events)))
    t))

(defthm fn-scj-load-from-of-append
  (equal (fn-sca-load-held-rows-from (append a b) idx c)
         (fn-sca-load-held-rows-from b idx (fn-sca-load-held-rows-from a idx c)))
  :hints (("Goal" :induct (fn-sca-load-held-rows-from a idx c)
           :in-theory (disable fn-sca-load-held-row fn-scj-load-held-row-is))))

(defthm fn-scj-load-from-of-no-rows-alone
  (implies (fn-scj-no-rowsp extra)
           (equal (fn-sca-load-held-rows-from extra idx c) c))
  :hints (("Goal" :induct (fn-sca-load-held-rows-from extra idx c))))

(defthm fn-scj-load-from-of-no-rows
  (implies (fn-scj-no-rowsp extra)
           (equal (fn-sca-load-held-rows-from (append events extra) idx c)
                  (fn-sca-load-held-rows-from events idx c)))
  :hints (("Goal" :in-theory (disable fn-sca-load-held-rows-from))))

(defthm fn-scj-rows-invp-of-no-rows
  (implies (fn-scj-no-rowsp extra)
           (equal (fn-scj-rows-invp c (append events extra))
                  (fn-scj-rows-invp c events)))
  :hints (("Goal" :in-theory (e/d (fn-scj-rows-invp) (fn-sca-load-held-rows-from fn-scj-arts-map)))))

; -----------------------------------------------------------------------------
; THE INVARIANT the host's catalog carries with the owner (step 5): the join
; at the view, the rows as the load of the history the view has seen (a
; transaction in flight has appended its record to the store's history but
; not yet to the view's: fn-own-take of the view's version), VV, the live
; view and every pinned connection over the catalog.

(defun-nx fn-scj-invp (o fn-arena fn-cat)
  (let ((view (fn-own-view o)))
    (and (fn-scj-joinp view fn-arena fn-cat)
         (fn-scj-rows-invp fn-cat (fn-own-take (fn-own-view-version view)
                                               (fn-sf-records (fn-sn-files (fn-own-store o)))))
         (fn-scj-vvp o)
         (fn-scj-live-okp view fn-arena fn-cat)
         (fn-scj-conns-pinp (fn-own-conns o) fn-arena fn-cat))))

(defthm fn-scj-invp-gives-owner-catalogp
  (implies (fn-scj-invp o fn-arena fn-cat)
           (fn-scr-owner-catalogp o id fn-arena fn-cat))
  :hints (("Goal" :in-theory (union-theories '(fn-scj-invp fn-scj-owner-catalogp-of-conns-and-live)
                                             (theory 'minimal-theory)))))

(in-theory (disable fn-scj-invp fn-scj-vvp fn-scj-live-okp fn-scj-conn-pinp fn-scj-conns-pinp
                    fn-scj-conn-pinned-index))
