; Teeth for books/owner-recover-ocl.lisp.
(in-package "ACL2")
(include-book "../../books/owner-recover-ocl")
(include-book "std/testing/must-fail" :dir :system)
(include-book "config-owner-publish-tests")

; The owner host/owner-host.lisp fn-owner-recover installs (:186-201),
; written out term for term as the keystone states it.
(defmacro orec-t-install (configs frontier events max-conns)
  `(let* ((replayed (fn-cpr-replay ,configs ,events))
          (cfg (fn-cnode-config (fn-replay-result-node replayed)))
          (opened (fn-cpo-open-observed ,configs ,frontier ,events)))
     (fn-ocfg-make (fn-own-configure
                    (fn-own-start (fn-sn-open-state opened) ,max-conns)
                    (fn-oag-post-config cfg *fn-record-max-payload*))
                   cfg nil nil)))

; -----------------------------------------------------------------------------
; Witness: the journal the live publication wrote.  config-owner-publish-tests'
; *ocp-published* is the served owner after fn-ocl-publish installed the
; third configuration record over the ground store; its store's two journals
; (three configuration records, two Store events, frontier 8) are what a
; crash right after that publication leaves on disk.

(defconst *orec-t-st* (fn-own-store (fn-ocfg-owner *ocp-published*)))
(defconst *orec-t-configs* (fn-sn-config-history *orec-t-st*))
(defconst *orec-t-events* (fn-sf-records (fn-sn-files *orec-t-st*)))
(defconst *orec-t-frontier* (fn-sf-frontier (fn-sn-files *orec-t-st*)))
(defconst *orec-t-oc*
  (orec-t-install *orec-t-configs* *orec-t-frontier* *orec-t-events* 4))

(assert-event (equal (len *orec-t-configs*) 3))
(assert-event (equal (len *orec-t-events*) 2))
(assert-event (equal *orec-t-frontier* 8))
; Both hypotheses and every host check hold.
(assert-event (equal (fn-replay-result-kind
                      (fn-cpr-replay *orec-t-configs* *orec-t-events*))
                     :ok))
(assert-event (equal (fn-sn-open-kind
                      (fn-cpo-open-observed *orec-t-configs* *orec-t-frontier*
                                            *orec-t-events*))
                     :ok))
; The installed owner: store at :recovering, the view the whole journal.
(assert-event (equal (fn-sf-phase (fn-sn-files (fn-own-store
                                                (fn-ocfg-owner *orec-t-oc*))))
                     :recovering))
(assert-event (equal (fn-own-view-version (fn-own-view (fn-ocfg-owner *orec-t-oc*)))
                     2))
; The conclusion.
(assert-event (fn-ocl-relation *orec-t-oc*))
(assert-event (fn-scar-view-indexedp (fn-ocfg-owner *orec-t-oc*)))
; Recovery answers the generation the live owner had published.
(assert-event (equal (fn-ocfg-config *orec-t-oc*) (fn-ocfg-config *ocp-published*)))
(assert-event (equal (fn-cfg-generation (fn-ocfg-config *orec-t-oc*)) 3))
; The admin open after recovery (fn-owner-open, owner-host.lisp:1337) pins
; connection 0 and keeps both premises.
(defconst *orec-t-admin* (cdr (fn-ocfg-open *orec-t-oc* nil)))
(assert-event (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *orec-t-admin*))))
(assert-event (fn-ocl-relation *orec-t-admin*))
(assert-event (fn-scar-view-indexedp (fn-ocfg-owner *orec-t-admin*)))

; The ground journal under the same fixtures (config-observed-tests'
; *cpo-t-configs*, *cpo-t-events*, frontier 8), with a zero connection bound.
(assert-event (fn-ocl-relation (orec-t-install *cpo-t-configs* 8 *cpo-t-events* 0)))

; -----------------------------------------------------------------------------
; One must-fail per hypothesis: the others hold, the conclusion is false.

; Without (natp max-conns): the same journal opens, a bound of -1.
(assert-event (equal (fn-sn-open-kind
                      (fn-cpo-open-observed *orec-t-configs* *orec-t-frontier*
                                            *orec-t-events*))
                     :ok))
(must-fail
 (defthm orec-t-without-natp-max-conns
   (fn-ocl-relation
    (orec-t-install *orec-t-configs* *orec-t-frontier* *orec-t-events* -1))))

; Without the open's kind :ok, the replay still :ok: frontier 1 is below the
; journal's transactions.  The host's replay check (:187) passes and its open
; check (:192) refuses; installing anyway would break the relation.
(assert-event (equal (fn-replay-result-kind
                      (fn-cpr-replay *orec-t-configs* *orec-t-events*))
                     :ok))
(assert-event (equal (fn-sn-open-kind
                      (fn-cpo-open-observed *orec-t-configs* 1 *orec-t-events*))
                     :error))
(must-fail
 (defthm orec-t-without-open-ok-frontier
   (fn-ocl-relation (orec-t-install *orec-t-configs* 1 *orec-t-events* 4))))

; A journal that replays :fault: the first configuration record lost.  The
; host installs nothing (:187 answers :fault before :191), and the owner the
; composition would build is not related.
(assert-event (equal (fn-replay-result-kind
                      (fn-cpr-replay (cdr *orec-t-configs*) *orec-t-events*))
                     :fault))
(assert-event (equal (fn-sn-open-kind
                      (fn-cpo-open-observed (cdr *orec-t-configs*)
                                            *orec-t-frontier* *orec-t-events*))
                     :error))
(must-fail
 (defthm orec-t-without-open-ok-fault
   (fn-ocl-relation
    (orec-t-install (cdr *orec-t-configs*) *orec-t-frontier* *orec-t-events* 4))))

; The proper-list fact is derived, not assumed: an improper configuration
; journal replays :fault.
(assert-event (equal (fn-replay-result-kind
                      (fn-cpr-replay (append *orec-t-configs* 7) *orec-t-events*))
                     :fault))
