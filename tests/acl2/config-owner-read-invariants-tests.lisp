; A live-created group gives old and new connections different historical
; archives.  The host TLS adapter refines the full owner read for both.
(in-package "ACL2")
(include-book "../../books/config-owner-read-invariants")
(include-book "config-owner-live-tests")
(include-book "served-tls-prefix-tests")
(include-book "std/testing/must-fail" :dir :system)

(defconst *ocri-live* *ocl-t-new-open*)
(defconst *ocri-new-group*
  (append (fn-nntp-string-octets "GROUP fn.live") '(13 10)))
(assert-event (fn-ocri-relation *ocri-live*))
(defconst *ocri-third-open* (cdr (fn-ocfg-open *ocri-live* nil)))
(assert-event (fn-ocri-relation *ocri-third-open*))
(assert-event
 (equal (fn-own-conn-index
         (fn-own-find-conn 2
                           (fn-own-conns (fn-ocfg-owner *ocri-third-open*))))
        (fn-own-view-index (fn-own-view (fn-ocfg-owner *ocri-live*)))))
(assert-event
 (not (equal (fn-own-conn-archive
              (fn-own-find-conn 0
                                (fn-own-conns (fn-ocfg-owner *ocri-live*))))
             (fn-own-conn-archive
              (fn-own-find-conn 1
                                (fn-own-conns (fn-ocfg-owner *ocri-live*)))))))
(include-book "arena-lift")
;; The payloads the arena holds at handles 0, 1, ...: none (no byte is read here).
(defconst *sr-arena* nil)
(bpr-lift fn-ocfg-read 3)
(bpr-lift fn-ocfg-read-tls-prefix 3)
(defconst *ocri-old-tls*
  (in-arena-fn-ocfg-read-tls-prefix *sr-arena* *ocri-live* 0 *ocri-new-group*))
(defconst *ocri-new-tls*
  (in-arena-fn-ocfg-read-tls-prefix *sr-arena* *ocri-live* 1 *ocri-new-group*))
(assert-event
 (equal (fn-own-tls-result-effects *ocri-old-tls*)
        (car (in-arena-fn-ocfg-read *sr-arena* *ocri-live* 0 *ocri-new-group*))))
(assert-event
 (equal (fn-own-tls-result-effects *ocri-new-tls*)
        (car (in-arena-fn-ocfg-read *sr-arena* *ocri-live* 1 *ocri-new-group*))))
; BY SPECIFICATION (NNT-042, 2026-09-27): a successful GROUP acquires the
; committed view, so the old connection (pinned before the new group) and the
; new one answer GROUP fn.live alike; before NNT-042 the old one answered 411.
; The two pins still differ through a read that is not a selection.
(assert-event
 (equal (fn-own-tls-result-effects *ocri-old-tls*)
        (fn-own-tls-result-effects *ocri-new-tls*)))
(defconst *ocri-stat-command*
  (append (fn-nntp-string-octets "STAT 1") '(13 10)))
(assert-event
 (not (equal (fn-state-groups
              (fn-own-conn-archive
               (fn-own-find-conn 0
                (fn-own-conns (fn-ocfg-owner (cdr (in-arena-fn-ocfg-read *sr-arena* *ocri-live* 0 *ocri-stat-command*)))))))
             (fn-state-groups
              (fn-own-conn-archive
               (fn-own-find-conn 1
                (fn-own-conns (fn-ocfg-owner (cdr (in-arena-fn-ocfg-read *sr-arena* *ocri-live* 1 *ocri-stat-command*))))))))))
(assert-event
 (fn-ocri-conns-p
  (fn-own-conns (fn-ocfg-owner
                 (cdr (in-arena-fn-ocfg-read *sr-arena* *ocri-live* 0 *ocri-new-group*))))))
(assert-event
 (fn-ocri-relation
  (cdr (in-arena-fn-ocfg-read *sr-arena* *ocri-live* 0 *ocri-new-group*))))
(assert-event
 (fn-ocri-relation
  (cdr (in-arena-fn-ocfg-read *sr-arena* *ocri-live* 1 *ocri-new-group*))))
; The full read theorem needs the incoming historical reader relation.  A
; forged old pin survives a read as a forged pin; the result is still outside
; that relation.
(assert-event (not (fn-ocri-relation *ocl-t-forged-old-pin*)))
; A read that is not a selection keeps the forged pin (the corrupted-state
; witness); BY SPECIFICATION (NNT-042, 2026-09-27) a successful GROUP re-pins
; the connection to the committed view, replacing the forged pin, so the
; relation holds again after it.
(assert-event
 (not (fn-ocri-relation
       (cdr (in-arena-fn-ocfg-read *sr-arena* *ocl-t-forged-old-pin* 0 *ocl-t-stat-command*)))))
(assert-event
 (fn-ocri-relation
  (cdr (in-arena-fn-ocfg-read *sr-arena* *ocl-t-forged-old-pin* 0 *ocri-new-group*))))
(local
 (must-fail
  (defthm ocri-read-without-relation-is-not-preserved
    (fn-ocri-relation (cdr (fn-ocfg-read oc id octets fn-arena)))
    :rule-classes nil)))

; The selected wire hypothesis has a real separator.  The forged wire has
; the fast spine but an invalid retained octet; the full read refuses it.
(defconst *ocri-old-conn*
  (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *ocri-live*))))
(defconst *ocri-bad-conn*
  (fn-own-conn-make-indexed
   0 (fn-own-conn-version *ocri-old-conn*)
   (fn-own-conn-frontier *ocri-old-conn*)
   *stp-cheap-only-wire*
   (fn-own-conn-session *ocri-old-conn*)
   (fn-own-conn-archive *ocri-old-conn*)
   (fn-own-conn-config *ocri-old-conn*)
   (fn-own-conn-observation *ocri-old-conn*)
   (fn-own-conn-verdicts *ocri-old-conn*)
   (fn-own-conn-index *ocri-old-conn*)))
(defconst *ocri-bad-oc*
  (fn-ocfg-with-owner
   *ocri-live*
   (fn-own-set-conns
    (fn-ocfg-owner *ocri-live*)
    (fn-own-replace-conn
     *ocri-bad-conn* (fn-own-conns (fn-ocfg-owner *ocri-live*))))))
(assert-event (not (fn-ocri-relation *ocri-bad-oc*)))
(assert-event
 (not (fn-ocri-relation (cdr (fn-ocfg-open *ocri-bad-oc* nil)))))
(must-fail
 (defthm ocri-open-without-carried-wire-and-index
   (fn-ocri-relation (cdr (fn-ocfg-open *ocri-bad-oc* nil)))))
(assert-event
 (not (equal
       (fn-own-tls-result-owner
        (in-arena-fn-ocfg-read-tls-prefix *sr-arena* *ocri-bad-oc* 0 '(65)))
       (cdr (in-arena-fn-ocfg-read *sr-arena* *ocri-bad-oc* 0 '(65))))))
(must-fail
 (defthm ocri-host-read-without-carried-wire
   (equal
    (fn-own-tls-result-owner
     (fn-ocfg-read-tls-prefix *ocri-bad-oc* 0 '(65) fn-arena))
    (cdr (fn-ocfg-read *ocri-bad-oc* 0 '(65) fn-arena)))))
