; Teeth for books/config-owner-carried.lisp (PRF-274): the live configuration
; completion from the owner's carried node, as the host calls it
; (host/owner-host.lisp fn-owner-reconfigure-complete -> fn-oclc-publish).
; The witness is config-owner-publish-tests' native live arm: a reader
; mid-command, a group request staged by a second connection, the admin
; connection closed.
(in-package "ACL2")
(include-book "../../books/config-owner-carried")
(include-book "std/testing/must-fail" :dir :system)
(include-book "config-owner-publish-tests")

; -----------------------------------------------------------------------------
; fn-oclc-publish-is-publish.  Reachable witness: the recovered owner's
; staged group request satisfies the invariant, and the carried completion
; answers exactly what fn-ocl-publish answers: :durable, the record's
; generation, the history one record longer.
(defconst *oclct-pub* (mv-list 2 (fn-oclc-publish *ocp-closed* 3 *ocp-max*)))
(assert-event (fn-ocl-relation *ocp-closed*))
(assert-event (fn-ocfg-staged *ocp-closed*))
(assert-event (equal *oclct-pub* (mv-list 2 (fn-ocl-publish *ocp-closed* 3 *ocp-max*))))
(assert-event (equal (car *oclct-pub*) :durable))
(assert-event (equal (fn-cfg-generation (fn-ocfg-config (cadr *oclct-pub*))) 3))
(assert-event (equal (fn-sn-config-history (fn-own-store (fn-ocfg-owner (cadr *oclct-pub*))))
                     (append (fn-sn-config-history
                              (fn-own-store (fn-ocfg-owner *ocp-closed*)))
                             (list (fn-ocfg-staged *ocp-closed*)))))
; The refusals agree too: the wrong generation.
(assert-event (equal (mv-list 2 (fn-oclc-publish *ocp-closed* 4 *ocp-max*))
                     (mv-list 2 (fn-ocl-publish *ocp-closed* 4 *ocp-max*))))
(assert-event (equal (car (mv-list 2 (fn-oclc-publish *ocp-closed* 4 *ocp-max*))) :refused))

; Hypothesis fn-ocl-relation.  *ocp-forged* claims the initial configuration
; while its store replays to generation 2: the invariant fails (its
; configuration is not the replayed one).  The carried completion trusts the
; owner's configuration: the staged record (generation 3) does not follow the
; claimed generation, so it answers :recovery-required, while fn-ocl-publish,
; which replays the history, answers :durable.  The conclusion fails.
(defconst *oclct-forged-carried* (mv-list 2 (fn-oclc-publish *ocp-forged* 3 *ocp-max*)))
(defconst *oclct-forged-full* (mv-list 2 (fn-ocl-publish *ocp-forged* 3 *ocp-max*)))
(assert-event (not (fn-ocl-relation *ocp-forged*)))
(assert-event (equal (car *oclct-forged-carried*) :recovery-required))
(assert-event (equal (car *oclct-forged-full*) :durable))
(assert-event (not (equal *oclct-forged-carried* *oclct-forged-full*)))
(local
 (must-fail
  (defthm fn-oclc-publish-is-publish-without-the-invariant
    (equal (fn-oclc-publish oc generation max-octets)
           (fn-ocl-publish oc generation max-octets))
    :rule-classes nil
    :hints (("Goal" :do-not-induct t)))))

; -----------------------------------------------------------------------------
; fn-oclc-publish-carries-ocl-relation.  Reachable witness: the published
; owner satisfies the invariant again, so the next completion's hypothesis
; holds.
(assert-event (fn-ocl-relation (cadr *oclct-pub*)))
; Hypothesis fn-ocl-relation: from the forged owner the carried completion
; answers :recovery-required and keeps that owner, which does not satisfy it.
(assert-event (not (fn-ocl-relation (cadr *oclct-forged-carried*))))
(local
 (must-fail
  (defthm fn-oclc-publish-carries-ocl-relation-without-the-invariant
    (fn-ocl-relation (mv-nth 1 (fn-oclc-publish oc generation max-octets)))
    :rule-classes nil
    :hints (("Goal" :do-not-induct t)))))
