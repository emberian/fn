; Teeth for books/config-owner-live-authorize-carried.lisp (sweep S033): the
; live owner's administrative authorization over its carried configuration
; history, with the host's one observation of the next generation's name
; (host/owner-host.lisp fn-owner-cfg-native-admin-authorize-carried, from
; host/native/admin.lisp fnn-admin-authorize-owner).  The fixture is
; config-owner-live-authorize-tests' (config-owner-publish-tests' native live
; arm: a recovered owner at generation 2 with a group request staged).
(in-package "ACL2")
(include-book "../../books/config-owner-live-authorize-carried")
(include-book "config-owner-live-authorize-tests")

(defconst *olact-configs* (fn-sn-config-history (fn-own-store (fn-ocfg-owner *ocp-closed*))))

; The guard-verified entries.
(assert-event
 (and (eq (symbol-class 'fn-olau-next-name (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-olau-authorize-carried (w state)) :common-lisp-compliant)))

; KEYSTONE fn-olau-authorize-carried-is-the-observed-authorization.
; Positive witnesses: the full antecedent (the owner's invariant; OCCUPIED is
; the next name's membership in the names on disk) and the conclusion, on
; the accepted arm (the two names on disk, the next one free) and on the
; occupied arm (the next name already on disk).
(assert-event (fn-ocl-relation *ocp-closed*))
(assert-event (equal (fn-olau-next-name *ocp-closed*) "00000003.cfg"))
(defconst *olact-free* '("00000001.cfg" "00000002.cfg"))
(defconst *olact-taken* '("00000001.cfg" "00000002.cfg" "00000003.cfg"))
(assert-event
 (and (not (fn-native-admin-name-memberp (fn-olau-next-name *ocp-closed*) *olact-free*))
      (equal (fn-olau-authorize-carried *ocp-closed* *olaut-record* t nil *olaut-profile*)
             (fn-olau-authorize *ocp-closed* *olact-configs* *olaut-record* t
                                *olact-free* *olaut-profile*))
      (equal (fn-olau-authorize-carried *ocp-closed* *olaut-record* t nil *olaut-profile*)
             (fn-native-admin-publication-result
              :accepted nil 3 "00000003.cfg" (fn-jpub-initial t)))))
(assert-event
 (and (fn-native-admin-name-memberp (fn-olau-next-name *ocp-closed*) *olact-taken*)
      (equal (fn-olau-authorize-carried *ocp-closed* *olaut-record* t t *olaut-profile*)
             (fn-olau-authorize *ocp-closed* *olact-configs* *olaut-record* t
                                *olact-taken* *olaut-profile*))
      (equal (fn-olau-authorize-carried *ocp-closed* *olaut-record* t t *olaut-profile*)
             (fn-native-admin-publication-result :refused :occupied nil nil nil))))

; Hypothesis removal: fn-ocl-relation.  *ocp-forged* claims the initial
; configuration while its history replays to generation 2: the carried
; next name is the claimed one's, not the fold's.  The retained hypothesis
; holds (OCCUPIED is that name's membership: nil), the omitted one fails, and
; the conclusion fails: the carried call does not see the fold's name on
; disk and goes on to refuse :candidate, the observed call refuses :occupied.
(defconst *olact-forged-configs*
  (fn-sn-config-history (fn-own-store (fn-ocfg-owner *ocp-forged*))))
(assert-event
 (let ((names '("00000003.cfg")))
   (and (not (fn-ocl-relation *ocp-forged*))
        (equal nil (fn-native-admin-name-memberp (fn-olau-next-name *ocp-forged*) names))
        (not (equal (fn-olau-authorize-carried *ocp-forged* *olaut-record* t nil
                                               *olaut-profile*)
                    (fn-olau-authorize *ocp-forged* *olact-forged-configs* *olaut-record* t
                                       names *olaut-profile*))))))

; Hypothesis removal: OCCUPIED is the next name's membership.  The owner's
; invariant holds; OCCUPIED says taken while the disk has the name free:
; the carried call refuses :occupied, the observed call accepts.
(assert-event
 (and (fn-ocl-relation *ocp-closed*)
      (not (equal t (fn-native-admin-name-memberp (fn-olau-next-name *ocp-closed*)
                                                  *olact-free*)))
      (equal (car (fn-olau-authorize-carried *ocp-closed* *olaut-record* t t
                                             *olaut-profile*))
             :refused)
      (equal (car (fn-olau-authorize *ocp-closed* *olact-configs* *olaut-record* t
                                     *olact-free* *olaut-profile*))
             :accepted)))

; Mutation witnesses (labelled): a record staged for a stale generation (the
; staged record's generation one back) is refused :generation by the carried
; call and by the observed one alike; without the lock, :lock alike.
(defconst *olact-stale*
  (fn-cfg-record-make (fn-cfg-record-sequence *olaut-record*)
                      (fn-cfg-record-txid *olaut-record*)
                      (- (fn-cfg-record-generation *olaut-record*) 1)
                      (fn-cfg-record-change *olaut-record*)
                      (fn-cfg-record-stamp *olaut-record*)))
(assert-event
 (and (equal (fn-olau-authorize-carried *ocp-closed* *olact-stale* t nil *olaut-profile*)
             (fn-native-admin-publication-result :refused :generation nil nil nil))
      (equal (fn-olau-authorize-carried *ocp-closed* *olact-stale* t nil *olaut-profile*)
             (fn-olau-authorize *ocp-closed* *olact-configs* *olact-stale* t
                                *olact-free* *olaut-profile*))
      (equal (fn-olau-authorize-carried *ocp-closed* *olaut-record* nil nil *olaut-profile*)
             (fn-native-admin-publication-result :refused :lock nil nil nil))))


(include-book "../../books/defkeystone")
(defconst *olact-octets* (fn-cfg-encode *olaut-record*))
(assert-event
 (and (eq (symbol-class 'fn-olau-authorize-observed (w state)) :common-lisp-compliant)
      (equal (fn-record-parse-value (fn-cfg-decode-exact *olact-octets*)) *olaut-record*)
      (equal (fn-olau-authorize-observed *ocp-closed* nil t :absent *olaut-profile*)
             (fn-native-admin-publication-result :refused :decode nil nil nil))
      (equal (fn-olau-authorize-observed *ocp-closed* nil t :error *olaut-profile*)
             (fn-native-admin-publication-result :fault :observation nil nil nil))))

(defteeth fn-olau-authorize-observed-is-the-carried-authorization
  :claim (((observed (member-equal observation '(:present :absent)))
           (parsed (fn-record-parse-okp (fn-cfg-decode-exact record-octets))))
          (equal (fn-olau-authorize-observed oc record-octets lock-owned observation profile)
                 (fn-olau-authorize-carried
                  oc (fn-record-parse-value (fn-cfg-decode-exact record-octets))
                  lock-owned (equal observation :present) profile)))
  :subject fn-olau-authorize-observed
  :witness ((oc *ocp-closed*) (record-octets *olact-octets*)
            (lock-owned t) (observation :absent) (profile *olaut-profile*))
  :breaks ((observed ((observation :error)))
           (parsed ((record-octets nil))))
  :mutations ((inverted-observation
               (:conclusion
                (equal (fn-olau-authorize-observed oc record-octets lock-owned observation profile)
                       (fn-olau-authorize-carried
                        oc (fn-record-parse-value (fn-cfg-decode-exact record-octets))
                        lock-owned (equal observation :absent) profile)))
               ((observation :present))
               :fault "Treating a present next-generation name as free")))

(local
 (defthm olact-reader-arms-keep-the-configuration
   (implies (member-equal (car event) '(:open :close :read :octets :fault))
            (equal (fn-ocfg-config (fn-ocfg-step oc event fn-arena))
                   (fn-ocfg-config oc)))
   :rule-classes nil
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(car-cons cdr-cons member-equal fn-ocfg-config-of-fn-ocfg-make
               fn-ocfg-step fn-ocfg-open fn-ocfg-close fn-ocfg-read
               fn-ocfg-read-step fn-ocfg-fault fn-ocfg-with-read-owner))))))

; A2 preserves the decision, not the stage or pending slot.  The three
; lifecycle conditions are redundant for this projection: reader arms
; always retain the store and configuration, even :close NIL.  Label the
; complete supplied window premise together; do not fabricate separate
; counterexamples for redundant conjuncts.  The :store mutation breaks the
; event restriction while retaining all three lifecycle conditions.
(defteeth fn-olau-authorize-carried-across-reader-events
  :claim (((reader-window
            (and (fn-ocfg-staged oc)
                 (not (fn-own-pending (fn-ocfg-owner oc)))
                 (member-equal (car event) '(:open :close :read :octets :fault))
                 (implies (equal (car event) :close) (natp (cadr event))))))
          (equal (fn-olau-authorize-carried (fn-ocfg-step oc event fn-arena)
                                            record lock-owned occupied profile)
                 (fn-olau-authorize-carried oc record lock-owned occupied profile)))
  :subject fn-olau-authorize-carried
  :witness ((oc *ocp-closed*) (event '(:close 0)) (record *olaut-record*)
            (lock-owned t) (occupied nil) (profile *olaut-profile*))
  :breaks ((reader-window ((event '(:store (:io :start-frontier nil))))))
  :mutations ((store-in-reader-window
               (:hypothesis reader-window
                (and (fn-ocfg-staged oc)
                     (not (fn-own-pending (fn-ocfg-owner oc)))
                     (member-equal (car event) '(:open :close :read :octets :fault :store))
                     (implies (equal (car event) :close) (natp (cadr event)))))
               ((event '(:store (:io :start-frontier nil))))
               :fault "Admitting a frontier reservation while authorizing a captured owner")))
