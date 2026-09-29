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

; =============================================================================
; PEER OPEN (fn-ohr-open-peer-preserves-ocl-relation, PRF-931; PKT-888).
; Positive witness, complete antecedent and conclusion: the served owner opens
; a transit connection for peer "p" (a name its configuration does not carry:
; the open does not ask the record); the connection is installed and pinned at
; the live configuration; the relation and the carried relation hold after.
(defconst *ohrt-peer-id* (fn-own-next-id (fn-ocfg-owner *ohrt-oc*)))
(defconst *ohrt-peered* (fn-ocfg-open-peer *ohrt-oc* "p" nil))
(assert-event (fn-ocl-relation (cdr *ohrt-peered*)))
(assert-event (and (car *ohrt-peered*)
                   (fn-own-find-conn *ohrt-peer-id* (fn-own-conns (fn-ocfg-owner (cdr *ohrt-peered*))))
                   (equal (fn-ocfg-conn-config (cdr *ohrt-peered*) *ohrt-peer-id*)
                          (fn-ocfg-config *ohrt-oc*))
                   (equal (fn-own-store (fn-ocfg-owner (cdr *ohrt-peered*)))
                          (fn-own-store (fn-ocfg-owner *ohrt-oc*)))))
(assert-event (fn-lgoc-invariantp (cdr (fn-ocfg-open-peer *lgt-oc0* "p" nil))))
; Removal witness (the hypothesis): the stale-pin owner fails the relation
; before and after the peer open.
(assert-event (not (fn-ocl-relation (cdr (fn-ocfg-open-peer *ohrt-stale* "p" nil)))))
; MUTATION witness (PKT-888 as it was): the peer open's owner installed with the
; pin table untouched (what fn-ocfg-with-owner does, and fn-ocfg-open-peer did)
; fails the relation: the new connection has no pin.
(assert-event (not (fn-ocl-relation (fn-ocfg-with-owner *ohrt-oc* (fn-ocfg-owner (cdr *ohrt-peered*))))))
(assert-event (not (fn-ocfg-pin-find *ohrt-peer-id*
                                     (fn-ocfg-pins (fn-ocfg-with-owner *ohrt-oc* (fn-ocfg-owner (cdr *ohrt-peered*)))))))
; The exposure open's peer arm (fn-ohr-exposure-open-preserves-ocl-relation,
; both arms): the host-called open with a resolved peer keeps the relation.
(assert-event (fn-ocl-relation
               (fn-exp-open-ocfg (fn-ocar-exp-open *ohrt-oc* (fn-exp-initial) (fn-exp-lim-make 8 4 1000 600 600 3 8 nil)
                                                   nil "p" '(:inet 127 0 0 1) 0))))

; =============================================================================
; OUTCOME (fn-ohr-outcome-preserves-ocl-relation, PRF-932; PKT-889): the bite.
; A configured owner with a posting configuration and a clock (owner-tests'
; *own-config*, *own-post-obs*) opens reader 0 at generation 2 (config-owner-live-
; tests' *ocl-t-cfg*), then completes a capacity increase (*cpo-t-increase*): the
; live configuration is generation 3, connection 0 still pinned at 2.  Reader 0
; POSTs owner-tests' article; the submission is taken and the log route's store
; events (owner-served-invariants-tests) reach :completing; the commit
; (fn-ccar-own-complete) reaches :ready with the completion :durable.
(defconst *ohrt-b0* (fn-ocfg-make (fn-own-start *cpo-t-ready* 3) *ocl-t-cfg* nil nil))
(defconst *ohrt-b1* (fn-ocfg-observe (fn-ocfg-with-owner *ohrt-b0* (fn-own-configure (fn-ocfg-owner *ohrt-b0*) *own-config*))
                                     *own-post-obs*))
(defconst *ohrt-b2* (cdr (fn-ocfg-open *ohrt-b1* nil)))
(defconst *ohrt-b4* (fn-ocl-complete (fn-ocfg-make (fn-ocfg-owner *ohrt-b2*) *ocl-t-cfg* (fn-ocfg-pins *ohrt-b2*) *cpo-t-increase*)))
(assert-event (and (fn-ocl-relation *ohrt-b4*)
                   (equal (fn-ocfg-conn-generation *ohrt-b4* 0) 2)
                   (equal (fn-cfg-generation (fn-ocfg-config *ohrt-b4*)) 3)))
(defconst *ohrt-b5* (in-arena-fn-ocfg-read *sr-arena* *ohrt-b4* 0 *own-post-command*))
(assert-event (equal (fn-own-take 4 (fn-served-reply-octets (car *ohrt-b5*))) (fn-nntp-string-octets "340 ")))
(defconst *ohrt-b6* (in-arena-fn-ocfg-read *sr-arena* (cdr *ohrt-b5*) 0 *own-article*))
(defconst *ohrt-b7* (in-arena-fn-ocfg-step *sr-arena* (cdr *ohrt-b6*) '(:take)))
(assert-event (equal (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *ohrt-b7*))) 0))
(defconst *ohrt-b8* (in-arena-acar-t-ocfg-run *sr-arena* *ohrt-b7*
                                              (osi-drop-last (own-post-events (osi-sub-record 2 8 (fn-own-inflight (fn-ocfg-owner *ohrt-b7*)))))))
(defconst *ohrt-b9* (fn-ocfg-with-owner *ohrt-b8* (fn-ccar-own-complete (fn-ocfg-owner *ohrt-b8*))))
(assert-event (and (equal (fn-sf-phase (fn-sn-files (fn-own-store (fn-ocfg-owner *ohrt-b8*)))) :completing)
                   (equal (fn-sf-phase (fn-sn-files (fn-own-store (fn-ocfg-owner *ohrt-b9*)))) :ready)
                   (fn-ocl-relation *ohrt-b9*)
                   (fn-lgoc-invariantp *ohrt-b9*)
                   (equal (fn-own-outcome-completion (fn-ocfg-owner *ohrt-b9*) :durable) :durable)
                   (equal (fn-ocfg-conn-generation *ohrt-b9* 0) 2)
                   (equal (fn-own-conn-version (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *ohrt-b9*)))) 2)
                   (equal (fn-own-view-version (fn-own-view (fn-ocfg-owner *ohrt-b9*))) 3)))
; Positive witness: the configured outcome answers 240, keeps the relation and
; the carried relation, advances connection 0 to the view (version 3) and moves
; its pin to the live generation (3); its owner and effects are
; fn-apc-own-outcome's (fn-oop-outcome-is-apc-own-outcome).
(defconst *ohrt-b10* (fn-oop-outcome *ohrt-b9* 0 :durable nil nil))
(assert-event (and (equal (fn-own-take 4 (fn-served-reply-octets (car *ohrt-b10*))) (fn-nntp-string-octets "240 "))
                   (fn-ocl-relation (cdr *ohrt-b10*))
                   (fn-lgoc-invariantp (cdr *ohrt-b10*))
                   (equal (fn-own-conn-version (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner (cdr *ohrt-b10*))))) 3)
                   (equal (fn-ocfg-conn-generation (cdr *ohrt-b10*) 0) 3)
                   (equal (fn-ocfg-owner (cdr *ohrt-b10*))
                          (cdr (fn-apc-own-outcome (fn-ocfg-owner *ohrt-b9*) 0 :durable nil nil)))
                   (equal (car *ohrt-b10*)
                          (car (fn-apc-own-outcome (fn-ocfg-owner *ohrt-b9*) 0 :durable nil nil)))))
; MUTATION witness (PKT-889 as it was): the same owner installed by
; fn-owner-replace-core's fn-ocfg-with-owner keeps the opening pin (2) on a
; connection now at version 3, and the relation fails.
(assert-event (not (fn-ocl-relation
                    (fn-ocfg-with-owner *ohrt-b9* (cdr (fn-apc-own-outcome (fn-ocfg-owner *ohrt-b9*) 0 :durable nil nil))))))
; Removal witness (the hypothesis): the stale-pin owner fails before and after.
(assert-event (not (fn-ocl-relation (cdr (fn-oop-outcome *ohrt-stale* 0 :durable nil nil)))))
; The refused word on the same owner: no advance, no pin moved, the relation kept.
(defconst *ohrt-b11* (fn-oop-outcome *ohrt-b9* 0 :refused nil nil))
(assert-event (and (fn-ocl-relation (cdr *ohrt-b11*))
                   (equal (fn-ocfg-pins (cdr *ohrt-b11*)) (fn-ocfg-pins *ohrt-b9*))
                   (equal (fn-own-take 4 (fn-served-reply-octets (car *ohrt-b11*))) (fn-nntp-string-octets "441 "))))

; TRANSIT OUTCOME (fn-ohr-transit-outcome-preserves-ocl-relation, PRF-932): on
; the same durable owner the in-flight submission is a POST, not a transit one,
; so the transit outcome is the absent branch: nothing changes and the relation
; holds; the transit arm's own durable witness is owed (no configured owner with
; a transit submission in flight is under fn-ocl-relation in tests/acl2 yet).
(assert-event (and (equal (cdr (fn-oop-transit-outcome *ohrt-b9* 0 :want nil :durable)) *ohrt-b9*)
                   (null (car (fn-oop-transit-outcome *ohrt-b9* 0 :want nil :durable)))
                   (fn-ocl-relation (cdr (fn-oop-transit-outcome *ohrt-b9* 0 :want nil :durable)))))
