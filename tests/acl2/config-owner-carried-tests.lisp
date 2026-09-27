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

; -----------------------------------------------------------------------------
; The steps fn-oclc-publish-is-publish is proved through, each a registry
; event of PRF-274 (keystone-audit 2026-09-27: none had a witness).  The
; store is the recovered owner's (*ocp-closed*), ready, with the group request
; staged; *ocp-forged* is the same store under an owner claiming the initial
; configuration (a CORRUPTED owner: its configuration is not the replayed one).
(defconst *oclct-st* (fn-own-store (fn-ocfg-owner *ocp-closed*)))
(defconst *oclct-rec* (fn-ocfg-staged *ocp-closed*))
(defconst *oclct-cfg*
  (mv-list 2 (fn-oclc-configure *oclct-st* (fn-ocfg-config *ocp-closed*) *oclct-rec*)))
(assert-event (equal (fn-own-store (fn-ocfg-owner *ocp-forged*)) *oclct-st*))

; fn-oclc-ready-cst-relation-is-history-relation: both hypotheses (the carried
; relation, the ready phase) and the conclusion.  No removal witness here: an
; unready store and a store outside fn-cst-relation were not constructed.
(assert-event (and (fn-cst-relation *oclct-st*)
                   (equal (fn-sf-phase (fn-sn-files *oclct-st*)) :ready)
                   (fn-cpo-history-relation *oclct-st*)))

; fn-oclc-configure-is-configure-durable: the history relation, the owner's
; configuration the replayed one, and the carried configure is
; fn-cpo-configure-durable's store (non-vacuous: the history grows).
(assert-event (and (fn-cpo-history-relation *oclct-st*)
                   (equal (fn-ocfg-config *ocp-closed*)
                          (fn-cnode-config (fn-oclc-replayed *oclct-st*)))
                   (equal (car *oclct-cfg*) (fn-cpo-configure-durable *oclct-st* *oclct-rec*))
                   (not (equal (fn-sn-config-history (car *oclct-cfg*))
                               (fn-sn-config-history *oclct-st*)))))
; Hypothesis removal (configuration): the forged owner's configuration on the
; same store (the history relation holds) is not the replayed one, and the
; carried configure is not fn-cpo-configure-durable's.
(assert-event
 (let ((c (mv-list 2 (fn-oclc-configure *oclct-st* (fn-ocfg-config *ocp-forged*) *oclct-rec*))))
   (and (fn-cpo-history-relation *oclct-st*)
        (not (equal (fn-ocfg-config *ocp-forged*)
                    (fn-cnode-config (fn-oclc-replayed *oclct-st*))))
        (not (equal (car c) (fn-cpo-configure-durable *oclct-st* *oclct-rec*))))))

; fn-oclc-configure-config-is-store-config: every hypothesis (the history
; grew) and the conclusion.  The history-changed hypothesis has no removal
; witness: with the configuration the replayed one an unchanged configure
; answers that configuration, which is the store's (the refused record nil
; below), so it may be redundant; the weakened theorem is NOT proved here.
(assert-event (equal (cadr *oclct-cfg*) (fn-ocl-store-config (car *oclct-cfg*))))
(assert-event
 (let ((c (mv-list 2 (fn-oclc-configure *oclct-st* (fn-ocfg-config *ocp-closed*) nil))))
   (and (equal (car c) *oclct-st*)
        (equal (cadr c) (fn-ocl-store-config (car c))))))

; fn-oclc-complete-is-complete: staged, the store in fn-cst-relation, the
; owner's configuration history (fn-ocl-config-historyp), and the carried
; completion is fn-ocl-complete's (non-vacuous: the owner changes).
(assert-event (and (fn-ocfg-staged *ocp-closed*)
                   (fn-cst-relation *oclct-st*)
                   (fn-ocl-config-historyp *ocp-closed*)
                   (equal (fn-oclc-complete *ocp-closed*) (fn-ocl-complete *ocp-closed*))
                   (not (equal (fn-oclc-complete *ocp-closed*) *ocp-closed*))))
; Hypothesis removal (fn-ocl-config-historyp), CORRUPTED owner: staged and
; the store's relation hold, the forged configuration fails it, and the two
; completions differ.
(assert-event (and (fn-ocfg-staged *ocp-forged*)
                   (fn-cst-relation (fn-own-store (fn-ocfg-owner *ocp-forged*)))
                   (not (fn-ocl-config-historyp *ocp-forged*))
                   (not (equal (fn-oclc-complete *ocp-forged*)
                               (fn-ocl-complete *ocp-forged*)))))
