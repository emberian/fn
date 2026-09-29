; owner-host-relation-tests.lisp -- teeth for books/owner-host-relation.lisp
; (ohrt-).  Fixtures: the served owner *ocp-admin* of config-owner-publish-tests
; (reader 0 and admin 1 open, :ready) and *lgt-oc0* of owner-log-ocl-tests (the
; carried relation).  A removal witness per hypothesis: the stale-pin owner
; *ohrt-stale* (a pin that names no connection) fails fn-ocl-relation before
; and after the entry.

(in-package "ACL2")
(include-book "../../books/owner-host-relation")
(include-book "owner-log-ocl-tests")

(defconst *ohrt-oc* *ocp-admin*)
(assert-event (fn-ocl-relation *ohrt-oc*))
(assert-event (and (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *ohrt-oc*)))
                   (fn-own-find-conn 1 (fn-own-conns (fn-ocfg-owner *ohrt-oc*)))
                   (null (fn-ocfg-staged *ohrt-oc*))))

; The stale-pin owner: the relation's fn-ocfg-pins-pin-conns-only fails.
(defconst *ohrt-stale*
  (fn-ocfg-make (fn-ocfg-owner *ohrt-oc*) (fn-ocfg-config *ohrt-oc*)
                (cons (cons 77 (fn-ocfg-config *ohrt-oc*)) (fn-ocfg-pins *ohrt-oc*))
                (fn-ocfg-staged *ohrt-oc*)))
(assert-event (not (fn-ocl-relation *ohrt-stale*)))

; HOST-FAULT (fn-ohr-fault-preserves-ocl-relation): positive witness, complete
; antecedent and conclusion; the faulted connection is gone and the effects close it.
(defconst *ohrt-faulted* (fn-ocfg-fault *ohrt-oc* 1))
(assert-event (fn-ocl-relation (cdr *ohrt-faulted*)))
(assert-event (and (car *ohrt-faulted*)
                   (not (fn-own-find-conn 1 (fn-own-conns (fn-ocfg-owner (cdr *ohrt-faulted*)))))
                   (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner (cdr *ohrt-faulted*))))
                   (not (fn-ocfg-pin-find 1 (fn-ocfg-pins (cdr *ohrt-faulted*))))))
; An unknown connection: no effect, the owner unchanged, the relation kept.
(assert-event (and (null (car (fn-ocfg-fault *ohrt-oc* 9)))
                   (fn-ocl-relation (cdr (fn-ocfg-fault *ohrt-oc* 9)))))
; Removal witness (the one hypothesis): without the relation before, none after.
(assert-event (not (fn-ocl-relation (cdr (fn-ocfg-fault *ohrt-stale* 1)))))

; STAGING (fn-ohr-reconfigure-preserves-ocl-relation): the admin's request is
; admitted and staged at the next generation; a reader's request is refused
; and changes nothing.  *ocp-staged* is fn-ocfg-step of (:reconfigure 1 deltas).
(assert-event (equal *ocp-staged* (fn-ocfg-reconfigure *ohrt-oc* 1 *ocp-deltas*)))
(assert-event (and (fn-ocl-relation *ocp-staged*)
                   (fn-ocfg-staged *ocp-staged*)
                   (equal (fn-cfg-record-generation (fn-ocfg-staged *ocp-staged*))
                          (+ 1 (fn-cfg-generation (fn-ocfg-config *ohrt-oc*))))))
(assert-event (and (equal (fn-ocfg-reconfigure *ohrt-oc* 9 *ocp-deltas*) *ohrt-oc*)
                   (fn-ocl-relation (fn-ocfg-reconfigure *ohrt-oc* 9 *ocp-deltas*))))
; Removal witness: the stale owner stages the same record and still fails.
(assert-event (and (fn-ocfg-staged (fn-ocfg-reconfigure *ohrt-stale* 1 *ocp-deltas*))
                   (not (fn-ocl-relation (fn-ocfg-reconfigure *ohrt-stale* 1 *ocp-deltas*)))))

; The host-shaped step (fn-ohr-step-*): the events fn-owner-step sends.
(assert-event (fn-ocl-relation (in-arena-fn-ocfg-step *sr-arena* *ohrt-oc* (list :reconfigure 1 *ocp-deltas*))))
(assert-event (fn-ocl-relation (in-arena-fn-ocfg-step *sr-arena* *ohrt-oc* (list :close 0))))
(assert-event (fn-ocl-relation (in-arena-fn-ocfg-step *sr-arena* *ohrt-oc* (list :advance 0))))
(assert-event (fn-ocl-relation (in-arena-fn-ocfg-step *sr-arena* *ohrt-oc* (list :take))))
(assert-event (fn-ocl-relation (in-arena-fn-ocfg-step *sr-arena* *ohrt-oc* (list :feeds (fn-ocfg-config *ohrt-oc*)))))
(assert-event (not (fn-ocl-relation (in-arena-fn-ocfg-step *sr-arena* *ohrt-stale* (list :take)))))

; The carried relation (fn-ohr-*-preserves-carried-relation) on the carried
; fixture: fault, staging refused, a feed reconfiguration.
(assert-event (fn-lgoc-invariantp *lgt-oc0*))
(assert-event (fn-lgoc-invariantp (cdr (fn-ocfg-fault *lgt-oc0* 1))))
(assert-event (fn-lgoc-invariantp (in-arena-fn-ocfg-step *sr-arena* *lgt-oc0* (list :take))))
(assert-event (fn-lgoc-invariantp
               (fn-ocfg-with-owner *lgt-oc0* (fn-own-configure (fn-ocfg-owner *lgt-oc0*)
                                                               (fn-own-config (fn-ocfg-owner *lgt-oc0*))))))
; Removal witness for the carried half: *lgt-bad-oc0* keeps fn-ocl-relation and
; not the Store companion; the fault keeps that failure.
(assert-event (and (fn-ocl-relation (cdr (fn-ocfg-fault *lgt-bad-oc0* 1)))
                   (not (fn-lgoc-invariantp (cdr (fn-ocfg-fault *lgt-bad-oc0* 1))))))

; BEGIN and DECLARE-GROUP (fn-ohr-step-begin-, fn-ohr-step-declare-group-preserves-ocl-relation).
(defconst *ohrt-begun* (in-arena-fn-ocfg-step *sr-arena* *ohrt-oc* (list :begin 0)))
(assert-event (and (fn-ocl-relation *ohrt-begun*)
                   (equal (fn-own-pending (fn-ocfg-owner *ohrt-begun*)) 0)))
(assert-event (not (fn-ocl-relation (in-arena-fn-ocfg-step *sr-arena* *ohrt-stale* (list :begin 0)))))
(defconst *ohrt-declared* (in-arena-fn-ocfg-step *sr-arena* *ohrt-oc* (list :declare-group "fn.declared")))
(assert-event (and (fn-ocl-relation *ohrt-declared*)
                   (member-equal "fn.declared"
                                 (fn-own-replay-facts (fn-own-facts (fn-ocfg-owner *ohrt-declared*))))))
(assert-event (not (fn-ocl-relation (in-arena-fn-ocfg-step *sr-arena* *ohrt-stale* (list :declare-group "fn.declared")))))
