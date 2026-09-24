; Administrative completion changes the actual owner Store together with the
; live configuration; a prior physical capacity decrease remains recoverable.
(in-package "ACL2")
(include-book "../../books/config-owner-live")
(include-book "std/testing/must-fail" :dir :system)
(include-book "config-observed-tests")

(defconst *ocl-t-cfg*
  (fn-cnode-config
   (fn-replay-result-node
    (fn-cpr-replay *cpo-t-configs* *cpo-t-events*))))
(defconst *ocl-t-open*
  (cdr (fn-ocfg-open
        (fn-ocfg-make (fn-own-start *cpo-t-ready* 3)
                      *ocl-t-cfg* nil nil) nil)))
(defconst *ocl-t-before*
  (fn-ocfg-make (fn-ocfg-owner *ocl-t-open*)
                *ocl-t-cfg* (fn-ocfg-pins *ocl-t-open*)
                *cpo-t-increase*))
(defconst *ocl-t-after* (fn-ocl-complete *ocl-t-before*))

(assert-event (fn-cst-relation *cpo-t-ready*))
(assert-event (fn-ocl-relation *ocl-t-before*))
(assert-event (fn-ocl-view-configp *ocl-t-before*))
(assert-event
 (fn-ocl-conns-historyp *ocl-t-before*
                        (fn-own-conns (fn-ocfg-owner *ocl-t-before*))))
(assert-event (null (fn-ocfg-staged *ocl-t-after*)))
(assert-event (fn-ocl-relation *ocl-t-after*))
(assert-event (fn-ocl-view-configp *ocl-t-after*))
(assert-event
 (equal (fn-sn-capacity (fn-own-store (fn-ocfg-owner *ocl-t-after*))) 20))
(assert-event
 (equal (fn-sn-config-history (fn-own-store (fn-ocfg-owner *ocl-t-after*)))
        (append *cpo-t-configs* (list *cpo-t-increase*))))
(assert-event
 (fn-cst-relation (fn-own-store (fn-ocfg-owner *ocl-t-after*))))
(assert-event
 (equal (fn-cfg-generation (fn-ocfg-config *ocl-t-after*)) 3))
(assert-event
 (equal (fn-ocfg-pins *ocl-t-after*) (fn-ocfg-pins *ocl-t-before*)))
(assert-event (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *ocl-t-after*))))
(assert-event (equal (fn-ocfg-conn-generation *ocl-t-after* 0) 2))
(assert-event (equal (fn-ocfg-served *ocl-t-after* 0)
                     (fn-ocfg-served *ocl-t-before* 0)))
(assert-event
 (fn-ocl-conns-historyp *ocl-t-after*
                        (fn-own-conns (fn-ocfg-owner *ocl-t-after*))))

; A second durable change creates a group in the Store allocation domain.
; The old connection still serves its pinned generation, while a connection
; opened afterwards pins the new served table and can name the new group.
(defconst *ocl-t-create-before*
  (fn-ocfg-make (fn-ocfg-owner *ocl-t-after*)
                (fn-ocfg-config *ocl-t-after*)
                (fn-ocfg-pins *ocl-t-after*) *cpo-t-create*))
(defconst *ocl-t-created* (fn-ocl-complete *ocl-t-create-before*))
(defconst *ocl-t-new-open* (cdr (fn-ocfg-open *ocl-t-created* nil)))
(assert-event (null (fn-ocfg-staged *ocl-t-created*)))
(assert-event (fn-ocl-relation *ocl-t-created*))
(assert-event (fn-ocl-view-configp *ocl-t-created*))
(assert-event
 (member-equal "fn.live"
               (fn-sn-groups (fn-own-store (fn-ocfg-owner *ocl-t-created*)))))
(assert-event
 (member-equal
  "fn.live"
  (fn-state-groups
   (fn-own-view-archive (fn-own-view (fn-ocfg-owner *ocl-t-created*))))))
(assert-event
 (not (member-equal
       "fn.live"
       (fn-state-groups
        (fn-own-conn-archive
         (fn-own-find-conn 0
          (fn-own-conns (fn-ocfg-owner *ocl-t-new-open*))))))))
(assert-event (not (member-equal "fn.live" (fn-ocfg-served *ocl-t-new-open* 0))))
(assert-event (member-equal "fn.live" (fn-ocfg-served *ocl-t-new-open* 1)))
(assert-event
 (equal
  (fn-state-groups
   (fn-own-conn-archive
    (fn-own-find-conn 0
     (fn-own-conns (fn-ocfg-owner *ocl-t-new-open*)))))
  (fn-cnode-domain-of (fn-ocfg-conn-config *ocl-t-new-open* 0))))
(assert-event
 (equal
  (fn-state-groups
   (fn-own-conn-archive
    (fn-own-find-conn 1
     (fn-own-conns (fn-ocfg-owner *ocl-t-new-open*)))))
  (fn-cnode-domain-of (fn-ocfg-conn-config *ocl-t-new-open* 1))))
(defconst *ocl-t-live-group-command*
  (append (fn-nntp-string-octets "GROUP fn.live") '(13 10)))
(defconst *ocl-t-old-read*
  (cdr (fn-ocfg-read *ocl-t-new-open* 0 *ocl-t-live-group-command*)))
(defconst *ocl-t-new-read*
  (cdr (fn-ocfg-read *ocl-t-new-open* 1 *ocl-t-live-group-command*)))
(assert-event (fn-ocl-relation *ocl-t-old-read*))
(assert-event (fn-ocl-relation *ocl-t-new-read*))
(assert-event
 (null (fn-nntp-session-group
        (fn-auth-reader-session
         (fn-own-conn-session
          (fn-own-find-conn 0
           (fn-own-conns (fn-ocfg-owner *ocl-t-old-read*))))))))
(assert-event
 (equal (fn-nntp-session-group
         (fn-auth-reader-session
          (fn-own-conn-session
           (fn-own-find-conn 1
            (fn-own-conns (fn-ocfg-owner *ocl-t-new-read*))))))
        "fn.live"))
(defconst *ocl-t-forged-old-pin*
  (fn-ocfg-make
   (fn-ocfg-owner *ocl-t-new-open*)
   (fn-ocfg-config *ocl-t-new-open*)
   (fn-ocfg-pin-set 0 (fn-ocfg-config *ocl-t-new-open*)
                    (fn-ocfg-pins *ocl-t-new-open*))
   nil))
(assert-event
 (not (equal
       (fn-state-groups
        (fn-own-conn-archive
         (fn-own-find-conn 0
          (fn-own-conns (fn-ocfg-owner *ocl-t-forged-old-pin*)))))
       (fn-cnode-domain-of
        (fn-ocfg-conn-config *ocl-t-forged-old-pin* 0)))))
; The read theorem needs the incoming historical relation: a forged newer
; pin remains wrong after the old connection reads its pinned archive.
(assert-event (not (fn-ocl-relation *ocl-t-forged-old-pin*)))
(assert-event
 (not (fn-ocl-relation
       (cdr (fn-ocfg-read *ocl-t-forged-old-pin*
                          0 *ocl-t-live-group-command*)))))
(local
 (must-fail
  (defthm fn-ocl-read-without-historical-input-is-not-preserved
    (fn-ocl-relation (cdr (fn-ocfg-read oc id octets)))
    :rule-classes nil)))
(assert-event
 (equal (fn-ocfg-conn-config *ocl-t-new-open* 1)
        (fn-ocfg-config *ocl-t-created*)))
; Without the historical owner's exact pin-table domain, a forged pin at
; the not-yet-open identifier survives pin-add and makes a new open stale.
(defconst *ocl-t-stale-next-pin*
  (fn-ocfg-make (fn-ocfg-owner *ocl-t-created*)
                (fn-ocfg-config *ocl-t-created*)
                (cons (cons 1 *ocl-t-cfg*) (fn-ocfg-pins *ocl-t-created*))
                nil))
(assert-event (not (fn-ocl-relation *ocl-t-stale-next-pin*)))
(assert-event
 (not (fn-ocl-relation
       (cdr (fn-ocfg-open *ocl-t-stale-next-pin* nil)))))
(assert-event
 (not (equal (fn-ocfg-conn-config
              (cdr (fn-ocfg-open *ocl-t-stale-next-pin* nil)) 1)
             (fn-ocfg-config *ocl-t-stale-next-pin*))))
(assert-event
 (member-equal
  "fn.live"
  (fn-state-groups
   (fn-own-conn-archive
    (fn-own-find-conn 1
     (fn-own-conns (fn-ocfg-owner *ocl-t-new-open*)))))))
(assert-event
 (fn-ocl-conn-historyp
  *ocl-t-new-open*
  (fn-own-find-conn 1
   (fn-own-conns (fn-ocfg-owner *ocl-t-new-open*)))))
(assert-event
 (fn-ocl-conns-historyp *ocl-t-new-open*
                        (fn-own-conns (fn-ocfg-owner *ocl-t-new-open*))))
(assert-event (fn-ocl-relation *ocl-t-new-open*))
; The old invariant replays this pinned archive at the newly created Store
; domain and capacity, so it cannot express the same historical connection.
(assert-event
 (not (fn-own-conn-okp
       (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *ocl-t-new-open*)))
       (fn-sn-groups (fn-own-store (fn-ocfg-owner *ocl-t-new-open*)))
       (fn-sn-capacity (fn-own-store (fn-ocfg-owner *ocl-t-new-open*)))
       (fn-sf-records
        (fn-sn-files (fn-own-store (fn-ocfg-owner *ocl-t-new-open*)))))))

; A record below the live reservation total remains staged after durable
; publication; the host must fence and reopen rather than report acceptance.
(defconst *ocl-t-refused-record*
  (fn-cfg-record-make 2 8 3 (list (fn-cfg-set-capacity 0))
                      *fn-cfg-default-stamp*))
(defconst *ocl-t-refused*
  (fn-ocfg-make (fn-ocfg-owner *ocl-t-before*)
                *ocl-t-cfg* nil *ocl-t-refused-record*))
(assert-event (equal (fn-ocl-complete *ocl-t-refused*) *ocl-t-refused*))
