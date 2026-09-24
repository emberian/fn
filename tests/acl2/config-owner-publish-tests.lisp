; Teeth for books/config-owner-publish.lisp: the live reconfiguration as the
; host calls it.  One reachable witness (a reader mid-command, a group request
; staged by a second connection, the admin connection closed, a durable
; publication), then for every hypothesis of a keystone a value that meets
; the other hypotheses, breaks that one and breaks the conclusion, asserted
; positively and then as a must-fail.
(in-package "ACL2")
(include-book "../../books/config-owner-publish")
(include-book "std/testing/must-fail" :dir :system)
(include-book "config-owner-live-tests")

(defconst *ocp-max* 32768)

; The recovered owner over the replayed ground store, a clock observed.
(defconst *ocp-0*
  (fn-ocfg-make (fn-own-start *cpo-t-ready* 4) *ocl-t-cfg* nil nil))
(defconst *ocp-clocked*
  (fn-ocfg-step *ocp-0*
                (list :observe (fn-clock-observation 5000000 1790000000000 0 t))))
(defconst *ocp-open0* (cdr (fn-ocfg-open *ocp-clocked* nil)))

; Reader 0 is mid-command: half of `GROUP fn.test' has arrived, no reply yet.
(defconst *ocp-half* (fn-nntp-string-octets "GROUP fn.te"))
(defconst *ocp-rest* (append (fn-nntp-string-octets "st") '(13 10)))
(defconst *ocp-reading* (cdr (fn-ocfg-read *ocp-open0* 0 *ocp-half*)))
(assert-event (null (car (fn-ocfg-read *ocp-open0* 0 *ocp-half*))))
(assert-event (not (equal (fn-own-conns (fn-ocfg-owner *ocp-reading*))
                          (fn-own-conns (fn-ocfg-owner *ocp-open0*)))))

; Connection 1 asks for a new group; ACL2 builds the delta and stages it.
(defconst *ocp-admin* (cdr (fn-ocfg-open *ocp-reading* nil)))
(defconst *ocp-deltas* (fn-ocl-request-deltas :create-group "fn.live"))
(defconst *ocp-staged*
  (fn-ocfg-step *ocp-admin* (list :reconfigure 1 *ocp-deltas*)))
(assert-event (fn-ocfg-staged *ocp-staged*))
(assert-event (equal (fn-cfg-record-generation (fn-ocfg-staged *ocp-staged*)) 3))

; The headline directly: publication right after staging.
(defconst *ocp-direct* (mv-list 2 (fn-ocl-publish *ocp-staged* 3 *ocp-max*)))
(assert-event (equal (car *ocp-direct*) :durable))
(assert-event (equal (fn-own-conns (fn-ocfg-owner (cadr *ocp-direct*)))
                     (fn-own-conns (fn-ocfg-owner *ocp-admin*))))
(assert-event (equal (fn-ocfg-pins (cadr *ocp-direct*)) (fn-ocfg-pins *ocp-admin*)))
(assert-event (equal (fn-ocfg-served (cadr *ocp-direct*) 0)
                     (fn-ocfg-served *ocp-admin* 0)))
(assert-event (equal (fn-cfg-generation (fn-ocfg-config (cadr *ocp-direct*))) 3))
(assert-event (null (fn-ocfg-staged (cadr *ocp-direct*))))

; The native live arm's sequence: stage, close the admin connection, publish.
(defconst *ocp-closed* (fn-ocfg-step *ocp-staged* (list :close 1)))
(defconst *ocp-pub* (mv-list 2 (fn-ocl-publish *ocp-closed* 3 *ocp-max*)))
(defconst *ocp-published* (cadr *ocp-pub*))
(assert-event (equal (car *ocp-pub*) :durable))
(assert-event (equal (fn-cfg-generation (fn-ocfg-config *ocp-closed*)) 2))
(assert-event (equal (fn-cfg-generation (fn-ocfg-config *ocp-published*)) 3))
(assert-event (equal (fn-sn-config-history (fn-own-store (fn-ocfg-owner *ocp-published*)))
                     (append (fn-sn-config-history
                              (fn-own-store (fn-ocfg-owner *ocp-closed*)))
                             (list (fn-ocfg-staged *ocp-closed*)))))
(assert-event (equal (fn-own-config (fn-ocfg-owner *ocp-published*))
                     (fn-oag-post-config (fn-ocfg-config *ocp-published*) *ocp-max*)))
; The reader's record, pin and served table are the ones it had mid-command.
(assert-event (equal (fn-own-conns (fn-ocfg-owner *ocp-published*))
                     (fn-own-conns (fn-ocfg-owner *ocp-reading*))))
(assert-event (equal (fn-ocfg-served *ocp-published* 0)
                     (fn-ocfg-served *ocp-reading* 0)))
(assert-event (not (member-equal "fn.live" (fn-ocfg-served *ocp-published* 0))))
; The rest of its command gets the reply it would have got with no change.
(assert-event (equal (car (fn-ocfg-read *ocp-published* 0 *ocp-rest*))
                     (car (fn-ocfg-read *ocp-reading* 0 *ocp-rest*))))
(assert-event (consp (car (fn-ocfg-read *ocp-reading* 0 *ocp-rest*))))
; A connection opened after publication serves the new group.
(defconst *ocp-new* (cdr (fn-ocfg-open *ocp-published* nil)))
(assert-event (member-equal "fn.live" (fn-ocfg-served *ocp-new* 2)))
; The owner itself moved (store and posting configuration): the old
; headline's "owner unchanged" conjunct is false of the called path, which is
; why the restatement is over connection records, pins and served tables.
(assert-event (not (equal (fn-ocfg-owner *ocp-published*)
                          (fn-ocfg-owner *ocp-closed*))))
(local
 (must-fail
  (defthm fn-ocl-publish-keeps-the-owner-is-false
    (implies (equal (mv-nth 0 (fn-ocl-publish oc generation max-octets)) :durable)
             (equal (fn-ocfg-owner (mv-nth 1 (fn-ocl-publish oc generation max-octets)))
                    (fn-ocfg-owner oc)))
    :rule-classes nil
    :hints (("Goal" :do-not-induct t)))))

; A durable write of another generation publishes nothing.
(defconst *ocp-wrong* (mv-list 2 (fn-ocl-publish *ocp-closed* 4 *ocp-max*)))
(assert-event (equal *ocp-wrong* (list :refused *ocp-closed*)))

; -----------------------------------------------------------------------------
; fn-ocl-publish-installs-the-whole-staged-record.  Witness: the live owner
; replays to its configuration and publishes the whole record.
(assert-event (fn-ocl-config-historyp *ocp-closed*))
(assert-event (equal (fn-ocfg-config *ocp-published*)
                     (fn-cfg-apply-record (fn-ocfg-config *ocp-closed*)
                                          (fn-ocfg-staged *ocp-closed*))))
(assert-event (not (equal (fn-ocfg-config *ocp-published*)
                          (fn-ocfg-config *ocp-closed*))))
; Hypothesis, the live configuration is what the durable history replays
; to: an owner claiming the initial configuration still publishes what its
; store replays to, which is not the record applied to its claim.
(defconst *ocp-forged*
  (fn-ocfg-make (fn-ocfg-owner *ocp-closed*) (fn-cfg-initial)
                (fn-ocfg-pins *ocp-closed*) (fn-ocfg-staged *ocp-closed*)))
(defconst *ocp-forged-pub* (mv-list 2 (fn-ocl-publish *ocp-forged* 3 *ocp-max*)))
(assert-event (not (fn-ocl-config-historyp *ocp-forged*)))
(assert-event (equal (car *ocp-forged-pub*) :durable))
(assert-event (not (equal (fn-ocfg-config (cadr *ocp-forged-pub*))
                          (fn-cfg-apply-record (fn-ocfg-config *ocp-forged*)
                                               (fn-ocfg-staged *ocp-forged*)))))
(local
 (must-fail
  (defthm fn-ocl-publish-installs-the-whole-record-without-history
    (implies (equal (mv-nth 0 (fn-ocl-publish oc generation max-octets)) :durable)
             (equal (fn-ocfg-config (mv-nth 1 (fn-ocl-publish oc generation max-octets)))
                    (fn-cfg-apply-record (fn-ocfg-config oc) (fn-ocfg-staged oc))))
    :rule-classes nil
    :hints (("Goal" :do-not-induct t)))))

; -----------------------------------------------------------------------------
; fn-ocl-publish-agrees-with-ocfg-complete-on-readers, hypothesis :durable.
; At the wrong generation the stage is kept, while `(:complete)' clears it.
(assert-event (not (equal (car *ocp-wrong*) :durable)))
(assert-event (not (equal (fn-ocfg-staged (cadr *ocp-wrong*))
                          (fn-ocfg-staged (fn-ocfg-step *ocp-closed* '(:complete))))))
(local
 (must-fail
  (defthm fn-ocl-publish-agrees-with-complete-without-durable
    (equal (fn-ocfg-staged (mv-nth 1 (fn-ocl-publish oc generation max-octets)))
           (fn-ocfg-staged (fn-ocfg-step oc (list :complete))))
    :rule-classes nil
    :hints (("Goal" :do-not-induct t)))))

; -----------------------------------------------------------------------------
; fn-ocl-request-refused-over-a-reader-in-the-group.  Witness: reader 0
; finishes `GROUP fn.test'; retiring fn.test is then refused.
(defconst *ocp-selected* (cdr (fn-ocfg-read *ocp-admin* 0 *ocp-rest*)))
(defconst *ocp-reader*
  (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *ocp-selected*))))
(assert-event (member-equal *ocp-reader* (fn-own-conns (fn-ocfg-owner *ocp-selected*))))
(assert-event (equal (fn-nntp-session-group
                      (fn-auth-reader-session (fn-own-conn-session *ocp-reader*)))
                     "fn.test"))
(assert-event
 (equal (fn-ocfg-step *ocp-selected*
                      (list :reconfigure 1 (fn-ocl-request-deltas :remove-group "fn.test")))
        *ocp-selected*))

; Hypothesis 1, the reader is open: the same reader record against the owner
; in which connection 0 has not yet selected the group; retiring stages.
(assert-event (not (member-equal *ocp-reader* (fn-own-conns (fn-ocfg-owner *ocp-admin*)))))
(assert-event
 (fn-ocfg-staged
  (fn-ocfg-step *ocp-admin*
                (list :reconfigure 1 (fn-ocl-request-deltas :remove-group "fn.test")))))
(local
 (must-fail
  (defthm fn-ocl-request-refused-without-an-open-reader
    (implies (equal (fn-nntp-session-group
                     (fn-auth-reader-session (fn-own-conn-session conn)))
                    name)
             (equal (fn-ocfg-step oc (list :reconfigure id
                                           (fn-ocl-request-deltas kind name)))
                    oc))
    :rule-classes nil
    :hints (("Goal" :do-not-induct t)))))

; Hypothesis 2, the reader stands in the requested group: a request for
; another group stages over the same reader.
(assert-event
 (fn-ocfg-staged
  (fn-ocfg-step *ocp-selected*
                (list :reconfigure 1 (fn-ocl-request-deltas :create-group "fn.live")))))
(local
 (must-fail
  (defthm fn-ocl-request-refused-without-the-reader-group
    (implies (member-equal conn (fn-own-conns (fn-ocfg-owner oc)))
             (equal (fn-ocfg-step oc (list :reconfigure id
                                           (fn-ocl-request-deltas kind name)))
                    oc))
    :rule-classes nil
    :hints (("Goal" :do-not-induct t)))))

; -----------------------------------------------------------------------------
; fn-ocl-request-deltas-name-only-the-requested-group.  A kind outside the
; two has no delta; a name that is no label gives an untyped delta.
(assert-event (null (fn-ocl-request-deltas :set-capacity "fn.test")))
(assert-event (not (fn-cfg-delta-listp (fn-ocl-request-deltas :create-group 7))))
(local
 (must-fail
  (defthm fn-ocl-request-deltas-of-any-kind-are-nonempty
    (consp (fn-ocl-request-deltas kind name))
    :rule-classes nil
    :hints (("Goal" :do-not-induct t)))))
(local
 (must-fail
  (defthm fn-ocl-request-deltas-of-any-name-are-typed
    (implies (member-equal kind '(:create-group :remove-group))
             (fn-cfg-delta-listp (fn-ocl-request-deltas kind name)))
    :rule-classes nil
    :hints (("Goal" :do-not-induct t)))))
