; Teeth for books/config-owner-live-authorize.lisp (PKT-837): the live
; owner's administrative authorization from its carried state, as the host
; calls it (host/owner-host.lisp fn-owner-cfg-native-admin-authorize, from
; host/native/admin.lisp fnn-admin-authorize-owner).  The witness is
; config-owner-publish-tests' native live arm: a reader mid-command, a group
; request staged by a second connection, the admin connection closed.
(in-package "ACL2")
(include-book "../../books/config-owner-live-authorize")
(include-book "../../books/owner-log-ocl")
(include-book "must-fail-checked")
(include-book "config-owner-publish-tests")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-sob-identity-typedp))))

(defconst *olaut-st* (fn-own-store (fn-ocfg-owner *ocp-closed*)))
(defconst *olaut-files* (fn-sn-files *olaut-st*))
(defconst *olaut-configs* (fn-sn-config-history *olaut-st*))
(defconst *olaut-record* (fn-ocfg-staged *ocp-closed*))
(defconst *olaut-profile* *fn-bs-profile-defaults*)

; -----------------------------------------------------------------------------
; fn-olau-authorize-is-the-replayed-authorization.  Reachable witness: the
; recovered owner's staged group request (generation 3) with the config/
; history it carries, a live lock, no occupied name: every hypothesis holds
; (the owner's full invariant fn-lgoc-invariantp included), and the carried
; authorization answers exactly what the replay answers, :accepted at
; generation 3 under the name 00000003.cfg with the initial publication state.
(defconst *olaut-carried*
  (fn-olau-authorize *ocp-closed* *olaut-configs* *olaut-record* t nil *olaut-profile*))
(defconst *olaut-replayed*
  (fn-cvec-native-admin-authorize (fn-sf-records *olaut-files*) (fn-sf-frontier *olaut-files*)
                                  *olaut-configs* *olaut-record* t nil *olaut-profile*))
(assert-event (fn-lgoc-invariantp *ocp-closed*))
(assert-event (fn-ocl-relation *ocp-closed*))
(assert-event (equal (fn-sf-phase *olaut-files*) :ready))
(assert-event (equal (fn-cfg-record-txid *olaut-record*) (fn-sf-frontier *olaut-files*)))
(assert-event (fn-olau-events-reopenp (fn-sf-records *olaut-files*)))
(assert-event (consp (fn-sf-records *olaut-files*)))
(assert-event (equal *olaut-carried* *olaut-replayed*))
(assert-event (equal *olaut-carried*
                     (fn-native-admin-publication-result
                      :accepted nil 3 "00000003.cfg" (fn-jpub-initial t))))
; The refusals agree too: no lock, and an occupied name.
(assert-event (equal (fn-olau-authorize *ocp-closed* *olaut-configs* *olaut-record* nil nil
                                        *olaut-profile*)
                     (fn-cvec-native-admin-authorize
                      (fn-sf-records *olaut-files*) (fn-sf-frontier *olaut-files*)
                      *olaut-configs* *olaut-record* nil nil *olaut-profile*)))
(assert-event (equal (car (fn-olau-authorize *ocp-closed* *olaut-configs* *olaut-record* t
                                             '("00000003.cfg") *olaut-profile*))
                     :refused))
(assert-event (equal (fn-olau-authorize *ocp-closed* *olaut-configs* *olaut-record* t
                                        '("00000003.cfg") *olaut-profile*)
                     (fn-cvec-native-admin-authorize
                      (fn-sf-records *olaut-files*) (fn-sf-frontier *olaut-files*)
                      *olaut-configs* *olaut-record* t '("00000003.cfg") *olaut-profile*)))

; A record like the staged one at another transaction id.
(defun olaut-record-at (txid)
  (fn-cfg-record-make (fn-cfg-record-sequence *olaut-record*) txid
                      (fn-cfg-record-generation *olaut-record*)
                      (fn-cfg-record-change *olaut-record*)
                      (fn-cfg-record-stamp *olaut-record*)))

; Hypothesis fn-ocl-relation.  *ocp-forged* claims the initial configuration
; while its store replays to generation 2; everything else holds.  The
; carried authorization applies the record to the claimed configuration and
; refuses :candidate; the replay accepts.
(defconst *olaut-forged-files* (fn-sn-files (fn-own-store (fn-ocfg-owner *ocp-forged*))))
(assert-event (not (fn-ocl-relation *ocp-forged*)))
(assert-event (equal (fn-sf-phase *olaut-forged-files*) :ready))
(assert-event (equal (fn-sn-config-history (fn-own-store (fn-ocfg-owner *ocp-forged*)))
                     *olaut-configs*))
(assert-event (equal (fn-cfg-record-txid *olaut-record*) (fn-sf-frontier *olaut-forged-files*)))
(assert-event (fn-olau-events-reopenp (fn-sf-records *olaut-forged-files*)))
(assert-event (equal (car (fn-olau-authorize *ocp-forged* *olaut-configs* *olaut-record* t nil
                                             *olaut-profile*))
                     :refused))
(assert-event (equal (car (fn-cvec-native-admin-authorize
                           (fn-sf-records *olaut-forged-files*)
                           (fn-sf-frontier *olaut-forged-files*)
                           *olaut-configs* *olaut-record* t nil *olaut-profile*))
                     :accepted))

; Hypothesis :ready.  The owner mid-POST (its log reservation taken,
; fn-olr-ocfg-reserve, which keeps fn-lgoc-invariantp) at :reserved, the
; record at the reserved frontier 9.  The carried authorization refuses; the
; replay, which never looks at the phase, accepts.
(defconst *olaut-reserved* (fn-olr-ocfg-reserve *ocp-closed*))
(defconst *olaut-rfiles* (fn-sn-files (fn-own-store (fn-ocfg-owner *olaut-reserved*))))
(assert-event (fn-lgoc-invariantp *olaut-reserved*))
(assert-event (equal (fn-sf-phase *olaut-rfiles*) :reserved))
(assert-event (equal (fn-sn-config-history (fn-own-store (fn-ocfg-owner *olaut-reserved*)))
                     *olaut-configs*))
(assert-event (equal (fn-sf-frontier *olaut-rfiles*) 9))
(assert-event (fn-olau-events-reopenp (fn-sf-records *olaut-rfiles*)))
(assert-event (equal (car (fn-olau-authorize *olaut-reserved* *olaut-configs* (olaut-record-at 9)
                                             t nil *olaut-profile*))
                     :refused))
(assert-event (equal (car (fn-cvec-native-admin-authorize
                           (fn-sf-records *olaut-rfiles*) (fn-sf-frontier *olaut-rfiles*)
                           *olaut-configs* (olaut-record-at 9) t nil *olaut-profile*))
                     :accepted))

; Hypothesis: the observed configuration history is the carried one.  A disk
; history whose last record differs from the carried one only in its stamp
; (the same generations and changes): the replay accepts over it; the
; carried authorization refuses.
(defconst *olaut-other-configs*
  (let ((a (car (last *olaut-configs*))))
    (append (butlast *olaut-configs* 1)
            (list (fn-cfg-record-make (fn-cfg-record-sequence a) (fn-cfg-record-txid a)
                                      (fn-cfg-record-generation a) (fn-cfg-record-change a)
                                      (fn-cfg-record-stamp *olaut-record*))))))
(assert-event (not (equal *olaut-other-configs* *olaut-configs*)))
(assert-event (equal (car (fn-olau-authorize *ocp-closed* *olaut-other-configs* *olaut-record*
                                             t nil *olaut-profile*))
                     :refused))
(assert-event (equal (car (fn-cvec-native-admin-authorize
                           (fn-sf-records *olaut-files*) (fn-sf-frontier *olaut-files*)
                           *olaut-other-configs* *olaut-record* t nil *olaut-profile*))
                     :accepted))

; Hypothesis: the record is at the frontier.  The staged record at txid 7,
; below the frontier 8: the replay files it before the last Store event and
; accepts; the carried authorization refuses.
(assert-event (equal (car (fn-olau-authorize *ocp-closed* *olaut-configs* (olaut-record-at 7)
                                             t nil *olaut-profile*))
                     :refused))
(assert-event (equal (car (fn-cvec-native-admin-authorize
                           (fn-sf-records *olaut-files*) (fn-sf-frontier *olaut-files*)
                           *olaut-configs* (olaut-record-at 7) t nil *olaut-profile*))
                     :accepted))

; Each hypothesis's removal, as the theorem it would be (the witnesses above
; are its counterexamples).
(local
 (must-fail-checked
  (with-prover-step-limit 1000000
  (defthm olaut-without-the-invariant
    (let* ((st (fn-own-store (fn-ocfg-owner oc))) (files (fn-sn-files st)))
      (implies (and (equal (fn-sf-phase files) :ready)
                    (equal config-records (fn-sn-config-history st))
                    (equal (fn-cfg-record-txid record) (fn-sf-frontier files))
                    (fn-olau-events-reopenp (fn-sf-records files)))
               (equal (fn-olau-authorize oc config-records record lock-owned
                                         observed-names profile)
                      (fn-cvec-native-admin-authorize
                       (fn-sf-records files) (fn-sf-frontier files)
                       config-records record lock-owned observed-names profile))))
    :rule-classes nil
    :hints (("Goal" :do-not-induct t :in-theory (disable fn-olau-authorize
                                                         fn-cvec-native-admin-authorize)))))))
(local
 (must-fail-checked
  (with-prover-step-limit 1000000
  (defthm olaut-without-ready
    (let* ((st (fn-own-store (fn-ocfg-owner oc))) (files (fn-sn-files st)))
      (implies (and (fn-ocl-relation oc)
                    (equal config-records (fn-sn-config-history st))
                    (equal (fn-cfg-record-txid record) (fn-sf-frontier files))
                    (fn-olau-events-reopenp (fn-sf-records files)))
               (equal (fn-olau-authorize oc config-records record lock-owned
                                         observed-names profile)
                      (fn-cvec-native-admin-authorize
                       (fn-sf-records files) (fn-sf-frontier files)
                       config-records record lock-owned observed-names profile))))
    :rule-classes nil
    :hints (("Goal" :do-not-induct t :in-theory (disable fn-olau-authorize
                                                         fn-cvec-native-admin-authorize
                                                         fn-ocl-relation)))))))
(local
 (must-fail-checked
  (with-prover-step-limit 1000000
  (defthm olaut-without-the-carried-history
    (let* ((st (fn-own-store (fn-ocfg-owner oc))) (files (fn-sn-files st)))
      (implies (and (fn-ocl-relation oc)
                    (equal (fn-sf-phase files) :ready)
                    (equal (fn-cfg-record-txid record) (fn-sf-frontier files))
                    (fn-olau-events-reopenp (fn-sf-records files)))
               (equal (fn-olau-authorize oc config-records record lock-owned
                                         observed-names profile)
                      (fn-cvec-native-admin-authorize
                       (fn-sf-records files) (fn-sf-frontier files)
                       config-records record lock-owned observed-names profile))))
    :rule-classes nil
    :hints (("Goal" :do-not-induct t :in-theory (disable fn-olau-authorize
                                                         fn-cvec-native-admin-authorize
                                                         fn-ocl-relation)))))))
(local
 (must-fail-checked
  (with-prover-step-limit 1000000
  (defthm olaut-without-the-frontier-txid
    (let* ((st (fn-own-store (fn-ocfg-owner oc))) (files (fn-sn-files st)))
      (implies (and (fn-ocl-relation oc)
                    (equal (fn-sf-phase files) :ready)
                    (equal config-records (fn-sn-config-history st))
                    (fn-olau-events-reopenp (fn-sf-records files)))
               (equal (fn-olau-authorize oc config-records record lock-owned
                                         observed-names profile)
                      (fn-cvec-native-admin-authorize
                       (fn-sf-records files) (fn-sf-frontier files)
                       config-records record lock-owned observed-names profile))))
    :rule-classes nil
    :hints (("Goal" :do-not-induct t :in-theory (disable fn-olau-authorize
                                                         fn-cvec-native-admin-authorize
                                                         fn-ocl-relation)))))))
