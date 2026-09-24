; Teeth for the bounded native administrative command plan.
(in-package "ACL2")
(include-book "../../books/native-admin")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defun fn-na-test-argv (words)
  (if (consp words)
      (cons (fn-record-string-octets (car words))
            (fn-na-test-argv (cdr words)))
    nil))

(defconst *fn-na-create*
  (fn-native-admin-plan (fn-na-test-argv '("group" "create" "fn.admin"))))
(assert-event (equal (fn-native-admin-result-status *fn-na-create*) :accepted))
(assert-event (equal (fn-native-admin-result-kind *fn-na-create*) :create-group))
(assert-event (equal (fn-native-admin-result-name *fn-na-create*)
                     (fn-record-string-octets "fn.admin")))

(defconst *fn-na-retire*
  (fn-native-admin-plan (fn-na-test-argv '("group" "retire" "fn.admin"))))
(assert-event (equal (fn-native-admin-result-status *fn-na-retire*) :accepted))
(assert-event (equal (fn-native-admin-result-kind *fn-na-retire*) :remove-group))

(defconst *fn-na-capacity*
  (fn-native-admin-plan (fn-na-test-argv '("capacity" "1048576"))))
(assert-event (equal (fn-native-admin-result-status *fn-na-capacity*) :accepted))
(assert-event (equal (fn-native-admin-result-capacity *fn-na-capacity*) 1048576))

(defconst *fn-na-peer-add*
  (fn-native-admin-plan
   (list (fn-record-string-octets "peer")
         (fn-record-string-octets "add")
         (fn-record-string-octets "far")
         (fn-record-string-octets "far.example")
         (fn-record-string-octets "192.0.2.44")
         (fn-record-string-octets "1119")
         (fn-record-string-octets "fn.*")
         (fn-record-string-octets "fn.*")
         (fn-record-string-octets "192.0.2.44")
         (fn-record-string-octets "true")
         (fn-record-string-octets "starttls")
         (fn-record-string-octets "news.example")
         (fn-record-string-octets "/etc/fn/peer-ca.pem"))))
(assert-event (equal (fn-native-admin-result-status *fn-na-peer-add*) :accepted))
(assert-event (equal (fn-native-admin-result-kind *fn-na-peer-add*) :set-peer))
(assert-event (fn-cfg-peerp (fn-native-admin-result-peer *fn-na-peer-add*)))
(assert-event
 (equal (fn-cfg-peer-transport (fn-native-admin-result-peer *fn-na-peer-add*))
        '(:nntp 1 "192.0.2.44" 1119
                (:tls :starttls "news.example" "/etc/fn/peer-ca.pem"))))
(assert-event
 (equal (fn-cfg-peer-auth (fn-native-admin-result-peer *fn-na-peer-add*))
        '(:source-address "192.0.2.44")))
(defconst *fn-na-principal-hex*
  "0707070707070707070707070707070707070707070707070707070707070707")
(defconst *fn-na-peer-principal*
  (fn-native-admin-plan
   (fn-na-test-argv
    (list "peer" "add" "principal-peer" "principal.example"
          "192.0.2.45" "1119" "fn.*" "-" "principal"
          *fn-na-principal-hex* "false" "implicit" "news.example"
          "/etc/fn/peer-ca.pem"))))
(assert-event
 (equal (fn-native-admin-result-status *fn-na-peer-principal*) :accepted))
(assert-event
 (equal (fn-cfg-peer-auth
         (fn-native-admin-result-peer *fn-na-peer-principal*))
        (list :principal *fn-na-principal-hex*)))
(defconst *fn-na-peer-principal-out-auth*
  (fn-native-admin-plan
   (fn-na-test-argv
    (list "peer" "add" "principal-peer" "principal.example"
          "192.0.2.45" "1119" "fn.*" "fn.*" "principal"
          *fn-na-principal-hex* "/etc/fn/outbound.auth" "false" "true"
          "starttls" "news.example" "/etc/fn/peer-ca.pem"))))
(assert-event
 (equal (fn-cfg-peer-outbound-auth
         (fn-native-admin-result-peer *fn-na-peer-principal-out-auth*))
        '(:authinfo "/etc/fn/outbound.auth" nil)))
(assert-event
 (let ((peer (fn-native-admin-result-peer *fn-na-peer-principal-out-auth*)))
   (equal (fn-cfg-peer-of-rows (fn-cfg-peer-name peer)
                               (fn-cfg-peer-rows peer))
          peer)))
; Principal ids are the canonical 32-octet lowercase hex projection.
(assert-event
 (equal (fn-native-admin-result-status
         (fn-native-admin-plan
          (fn-na-test-argv
           '("peer" "add" "bad-principal" "bad.example" "192.0.2.45"
             "1119" "fn.*" "-" "principal" "07" "false"))))
        :refused))
(assert-event
 (equal (fn-native-admin-result-status
         (fn-native-admin-plan
          (list (fn-record-string-octets "peer")
                (fn-record-string-octets "add")
                (fn-record-string-octets "far")
                (fn-record-string-octets "far.example")
                (fn-record-string-octets "192.0.2.44")
                (fn-record-string-octets "70000")
                (fn-record-string-octets "fn.*")
                (fn-record-string-octets "fn.*")
                (fn-record-string-octets "192.0.2.44")
                (fn-record-string-octets "true"))))
        :refused))
(assert-event
 (equal (fn-native-admin-result-status
         (fn-native-admin-plan
          (list (fn-record-string-octets "peer")
                (fn-record-string-octets "add")
                (fn-record-string-octets "far")
                (fn-record-string-octets "far.example")
                (fn-record-string-octets "192.0.2.44")
                (fn-record-string-octets "1119")
                (fn-record-string-octets "fn.*")
                (fn-record-string-octets "fn.*")
                (fn-record-string-octets "192.000.2.44")
                (fn-record-string-octets "true"))))
        :refused))
(defconst *fn-na-peer-remove*
  (fn-native-admin-plan
   (list (fn-record-string-octets "peer")
         (fn-record-string-octets "remove")
         (fn-record-string-octets "far"))))
(assert-event (equal (fn-native-admin-result-kind *fn-na-peer-remove*) :remove-peer))

; Leading zeroes, signs, overflow, malformed verbs, and non-group labels are
; all refusals before the physical adapter acquires a writable store.
(assert-event (equal (fn-native-admin-result-status
                      (fn-native-admin-plan (fn-na-test-argv '("capacity" "01"))))
                     :refused))
(assert-event (equal (fn-native-admin-result-status
                      (fn-native-admin-plan (fn-na-test-argv '("capacity" "+1"))))
                     :refused))
(assert-event (equal (fn-native-admin-result-status
                      (fn-native-admin-plan (fn-na-test-argv '("capacity" "4294967296"))))
                     :refused))
(assert-event (equal (fn-native-admin-result-status
                      (fn-native-admin-plan (fn-na-test-argv '("group" "create" ""))))
                     :refused))
(assert-event (equal (fn-native-admin-result-status
                      (fn-native-admin-plan (fn-na-test-argv '("group" "remove" "fn.admin"))))
                     :refused))

; The persistent generation namespace uses byte-store's ACL2 digit renderer;
; a raw `format' implementation cannot pass these fixed-name witnesses.
(assert-event (equal (fn-native-admin-config-name 1) "00000001.cfg"))
(assert-event (equal (fn-native-admin-config-name 99999999) "99999999.cfg"))
(assert-event (equal (fn-native-admin-config-name 100000000) nil))

; Candidate validation is the logical replay/open predicate the host wrapper
; calls after byte decoding.  The default durable record opens an empty image;
; an out-of-range frontier is a reachable differing observation and refuses.
(assert-event (fn-native-admin-candidate-openp nil 0 (list *fn-cfg-default-record*)))
(assert-event (not (fn-native-admin-candidate-openp nil 4294967296
                                                 (list *fn-cfg-default-record*))))

; Physical replay must admit a capacity decrease after an undertaking is
; released. Replaying both article events at the final capacity would reject
; this valid image; moving the decrease before release must still be refused.
(defconst *fn-na-historical-events*
  (list (fn-store-retention-event-make :undertake 0 0 0
                                        "admin-history" "subject" "evidence" 10)
        (fn-store-retention-event-make :release 1 1 1
                                        "admin-history" "subject" "evidence" 0)))
(assert-event
 (fn-native-admin-candidate-openp
  *fn-na-historical-events* 8
  (list *fn-cfg-default-record*
        (fn-cfg-record-make 1 7 2 (list (fn-cfg-set-capacity 1))
                            *fn-cfg-default-stamp*))))
(assert-event
 (not (fn-native-admin-candidate-openp
       *fn-na-historical-events* 8
       (list *fn-cfg-default-record*
             (fn-cfg-record-make 1 1 2 (list (fn-cfg-set-capacity 1))
                                 *fn-cfg-default-stamp*)))))

; Raw clocks are observations only.  ACL2 accepts a schema-representable pair
; and refuses an out-of-domain value without wrapping it.
(assert-event (equal (fn-native-admin-clock-status
                      (fn-native-admin-clock-observation 7 9)) :accepted))
(assert-event (equal (fn-native-admin-clock-status
                      (fn-native-admin-clock-observation -1 9)) :refused))

; Publication authorization cannot be reached without the observed exclusive
; lock.  This separates the raw lock observation from the ACL2 authority it
; must satisfy before a fn-jpub state is returned.
(assert-event (equal (fn-native-admin-publication-status
                      (fn-native-admin-publication-authorize nil 0 nil nil nil nil))
                     :refused))

; A second, admissible configuration record is authorized only for the exact
; next ACL2-rendered name.  An observed collision for that name refuses before
; any shared immutable-publisher state is exposed to the raw adapter.
(defconst *fn-na-second-record*
  (fn-cfg-record-make
   1 0 2 (list (fn-cfg-set-capacity 1048576))
   (fn-clock-observation 7 9 0 t)))
(defconst *fn-na-publication*
  (fn-native-admin-publication-authorize
   nil 0 (list *fn-cfg-default-record*) *fn-na-second-record* t nil))
(assert-event (equal (fn-native-admin-publication-status *fn-na-publication*)
                     :accepted))
(assert-event (equal (fn-native-admin-publication-generation *fn-na-publication*) 2))
(assert-event (equal (fn-native-admin-publication-name *fn-na-publication*)
                     "00000002.cfg"))
(assert-event (equal (fn-jpub-phase
                      (fn-native-admin-publication-jpub *fn-na-publication*))
                     :staging))
(assert-event
 (equal (fn-native-admin-publication-status
         (fn-native-admin-publication-authorize
          nil 0 (list *fn-cfg-default-record*) *fn-na-second-record* t
          '("00000002.cfg")))
        :refused))

; Teeth for `fn-native-admin-publication-is-authorized-only-under-the-lock'.
; The witness: an admissible second record, the next name free, the lock
; observed -- accepted, with a publication state raw Lisp may execute.
(assert-event (fn-native-admin-publication-jpub *fn-na-publication*))
; The separating value: the SAME inputs with the lock not observed are refused
; `:lock' and carry no publication state.  The lock is what decides here, not
; the record, the generation or the namespace.
(defconst *fn-na-unlocked-publication*
  (fn-native-admin-publication-authorize
   nil 0 (list *fn-cfg-default-record*) *fn-na-second-record* nil nil))
(assert-event (equal (fn-native-admin-publication-status *fn-na-unlocked-publication*)
                     :refused))
(assert-event (equal (fn-native-admin-publication-reason *fn-na-unlocked-publication*)
                     :lock))
(assert-event (null (fn-native-admin-publication-jpub *fn-na-unlocked-publication*)))
; The witness's publication state is the one the immutable executor admits
; (`fn-jpub-host-authorized-initialp', host/journal-publish-host.lisp).
(assert-event (equal (fn-native-admin-publication-jpub *fn-na-publication*)
                     (fn-jpub-initial t)))
; One `must-fail' per hypothesis, the hints kept.  Each is refuted by the
; unlocked value above (lock-owned = NIL, status :refused, jpub NIL).
; (1) The acceptance hypothesis dropped: a refused result says nothing of
; the lock.
(must-fail
 (defthm fn-na-lock-without-acceptance
   (let ((result (fn-native-admin-publication-authorize
                  records frontier config-records record lock-owned observed-names)))
     (declare (ignorable result))
     lock-owned)
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-native-admin-publication-authorize)
                                   (fn-cnode-config-replay fn-native-admin-candidate-openp
                                    fn-native-admin-config-name fn-cfg-recordp))))))
; (2) The publication-state hypothesis replaced by its negation: a result
; with no jpub, which the executor never runs, may come from an unlocked
; process.
(must-fail
 (defthm fn-na-lock-without-a-publication-state
   (let ((result (fn-native-admin-publication-authorize
                  records frontier config-records record lock-owned observed-names)))
     (implies (not (fn-native-admin-publication-jpub result))
              lock-owned))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-native-admin-publication-authorize)
                                   (fn-cnode-config-replay fn-native-admin-candidate-openp
                                    fn-native-admin-config-name fn-cfg-recordp))))))

; Length alone does not establish a proper argument vector.
(assert-event
 (equal (fn-native-admin-result-status
         (fn-native-admin-peer-plan
          '("peer" "add" "near" "near" "localhost" "119"
            "*" "*" "127.0.0.1" "true" . improper-tail)))
        :refused))

; The node's own <path-identity>: a `:set-policy' plan whose slot and value
; are the exact argv octets, and whose value must itself be a path identity.
(defconst *fn-na-policy*
  (fn-native-admin-plan
   (fn-na-test-argv '("policy" "set" "path-identity" "a.gate.example.invalid"))))
(assert-event (equal (fn-native-admin-result-status *fn-na-policy*) :accepted))
(assert-event (equal (fn-native-admin-result-kind *fn-na-policy*) :set-policy))
(assert-event (equal (fn-native-admin-result-name *fn-na-policy*)
                     (fn-record-string-octets "path-identity")))
(assert-event (equal (fn-native-admin-result-value *fn-na-policy*)
                     (fn-record-string-octets "a.gate.example.invalid")))
(assert-event (fn-path-identityp (fn-native-admin-result-value *fn-na-policy*)))
; Teeth: each hypothesis of the accepting arm, removed, refuses.
(assert-event
 (equal (fn-native-admin-result-reason
         (fn-native-admin-plan
          (fn-na-test-argv '("policy" "set" "path-identity" ".leading-dot"))))
        :policy))
(assert-event
 (equal (fn-native-admin-result-reason
         (fn-native-admin-plan
          (fn-na-test-argv '("policy" "set" "path-identity" "trailing-dot."))))
        :policy))
(assert-event
 (equal (fn-native-admin-result-reason
         (fn-native-admin-plan
          (fn-na-test-argv '("policy" "set" "other-slot" "a.gate.example.invalid"))))
        :policy))
(assert-event
 (equal (fn-native-admin-result-reason
         (fn-native-admin-plan
          (fn-na-test-argv '("policy" "get" "path-identity"))))
        :policy))
(assert-event
 (equal (fn-native-admin-result-reason
         (fn-native-admin-plan
          (fn-na-test-argv '("policy" "set" "path-identity"))))
        :policy))
; The other kinds carry no value.
(assert-event (null (fn-native-admin-result-value *fn-na-create*)))
(assert-event (null (fn-native-admin-result-value *fn-na-capacity*)))

; -----------------------------------------------------------------------------
; `peer list': the read side of the same table, and what keeps it read-only.

(defconst *fn-na-peer-list*
  (fn-native-admin-plan (fn-na-test-argv '("peer" "list"))))
(assert-event (equal (fn-native-admin-result-status *fn-na-peer-list*) :accepted))
(assert-event (equal (fn-native-admin-result-kind *fn-na-peer-list*) :list-peers))
(assert-event (fn-native-admin-result-queryp *fn-na-peer-list*))
; A query carries no label, no number and no record: there is nothing for an
; executor to publish even if it tried.
(assert-event (null (fn-native-admin-result-name *fn-na-peer-list*)))
(assert-event (null (fn-native-admin-result-peer *fn-na-peer-list*)))
(assert-event (null (fn-native-admin-result-value *fn-na-peer-list*)))

; Teeth: every mutation this grammar admits fails the query test, so the
; read-only executor cannot be reached by a plan that writes a record.
(assert-event (not (fn-native-admin-result-queryp *fn-na-create*)))
(assert-event (not (fn-native-admin-result-queryp *fn-na-retire*)))
(assert-event (not (fn-native-admin-result-queryp *fn-na-capacity*)))
(assert-event (not (fn-native-admin-result-queryp *fn-na-peer-add*)))
(assert-event (not (fn-native-admin-result-queryp *fn-na-policy*)))
(assert-event
 (not (fn-native-admin-result-queryp
       (fn-native-admin-plan (fn-na-test-argv '("peer" "remove" "far"))))))
; And a refused plan is not a query either, however it is spelled.
(assert-event
 (not (fn-native-admin-result-queryp
       (fn-native-admin-plan (fn-na-test-argv '("peer" "list" "far"))))))

; Teeth: `list' takes no argument, and `peer' alone is not a listing.
(assert-event (equal (fn-native-admin-result-status
                      (fn-native-admin-plan
                       (fn-na-test-argv '("peer" "list" "far"))))
                     :refused))
(assert-event (equal (fn-native-admin-result-status
                      (fn-native-admin-plan (fn-na-test-argv '("peer"))))
                     :refused))
(assert-event (equal (fn-native-admin-result-status
                      (fn-native-admin-plan (fn-na-test-argv '("peer" "show")))
                      )
                     :refused))

; The report: the record `peer add` wrote, read back in the order `peer add`
; takes its arguments.  The rows are the codec's own.
(defconst *fn-na-peer-rows*
  (fn-cfg-peer-rows (fn-native-admin-result-peer *fn-na-peer-add*)))
(assert-event (equal (fn-cfg-peer-names *fn-na-peer-rows*) (list "far")))
(assert-event
 (equal (fn-native-admin-peer-report *fn-na-peer-rows*)
        (append (fn-record-string-octets
                 "far path-identity=far.example address=192.0.2.44 port=1119 security=starttls inbound=fn.* outbound=fn.* auth=source-address:192.0.2.44")
                (list 10))))

; A record whose outbound half is absent and whose auth is a principal: the
; absent half is `-`, and the principal id is the exact configured label.
(defconst *fn-na-peer-principal-rows*
  (fn-cfg-peer-rows (fn-native-admin-result-peer *fn-na-peer-principal*)))
(assert-event
 (equal (fn-native-admin-peer-report *fn-na-peer-principal-rows*)
        (append (fn-record-string-octets
                 (string-append
                  "principal-peer path-identity=principal.example address=192.0.2.45 port=1119 security=implicit inbound=fn.* outbound=- auth=principal:"
                  *fn-na-principal-hex*))
                (list 10))))

; Two peers are two lines, in the table's row order; an empty table is no
; output at all, not a header and not a placeholder row.
(assert-event
 (equal (fn-native-admin-peer-report
         (append *fn-na-peer-rows* *fn-na-peer-principal-rows*))
        (append (fn-native-admin-peer-report *fn-na-peer-rows*)
                (fn-native-admin-peer-report *fn-na-peer-principal-rows*))))
(assert-event (equal (fn-native-admin-peer-report nil) nil))
; Rows that denote no well-formed record contribute no line rather than a
; half-rendered one: the name is enumerated, the record is not found.
(assert-event
 (equal (fn-cfg-peer-names
         (list (fn-cfg-row-make "ghost" "path-identity" "ghost.example" 0)))
        (list "ghost")))
(assert-event
 (equal (fn-native-admin-peer-report
         (list (fn-cfg-row-make "ghost" "path-identity" "ghost.example" 0)))
        nil))

; -----------------------------------------------------------------------------
; The LIVE arm's delta labels (plan T8; `fn-native-admin-plan-deltas').
;
; The finding, evaluated.  A plan carries the name the operator typed as argv
; OCTETS.  The delta the live arm used to build from it -- the octets passed
; straight to the constructor -- is not a `fn-cfg-deltap', because a
; configuration label is a string; `fn-ocfg-reconfig-refusal' refused every
; such request `:malformed-delta'.  The same name as a string is a typed delta.
(assert-event (not (fn-cfg-deltap
                    (fn-cfg-create-group (fn-native-admin-result-name *fn-na-create*)
                                         *fn-cfg-default-policy-id*))))
(assert-event (not (fn-cfg-deltap
                    (fn-cfg-remove-group (fn-native-admin-result-name *fn-na-retire*)))))
(assert-event (not (fn-cfg-deltap
                    (fn-cfg-remove-peer-delta
                     (fn-native-admin-result-name *fn-na-peer-remove*)))))

; What the live arm stages now, kind by kind: one typed delta whose label is
; the admitted word.
(assert-event (equal (fn-native-admin-plan-deltas *fn-na-create*)
                     (list (fn-cfg-create-group "fn.admin" *fn-cfg-default-policy-id*))))
(assert-event (fn-cfg-delta-listp (fn-native-admin-plan-deltas *fn-na-create*)))
(assert-event (equal (fn-native-admin-plan-deltas *fn-na-retire*)
                     (list (fn-cfg-remove-group "fn.admin"))))
(assert-event (fn-cfg-delta-listp (fn-native-admin-plan-deltas *fn-na-retire*)))
(assert-event (equal (fn-native-admin-plan-deltas *fn-na-peer-remove*)
                     (list (fn-cfg-remove-peer-delta "far"))))
(assert-event (fn-cfg-delta-listp (fn-native-admin-plan-deltas *fn-na-peer-remove*)))
(assert-event (equal (fn-native-admin-plan-deltas *fn-na-capacity*)
                     (list (fn-cfg-set-capacity 1048576))))
(assert-event (fn-cfg-delta-listp (fn-native-admin-plan-deltas *fn-na-capacity*)))
(assert-event (equal (fn-native-admin-plan-deltas *fn-na-policy*)
                     (list (fn-cfg-set-policy "path-identity" "a.gate.example.invalid"))))
(assert-event (fn-cfg-delta-listp (fn-native-admin-plan-deltas *fn-na-policy*)))
(assert-event (fn-cfg-delta-listp (fn-native-admin-plan-deltas *fn-na-peer-add*)))
(assert-event (equal (len (fn-native-admin-plan-deltas *fn-na-peer-add*)) 1))
; A query stages nothing.
(assert-event (null (fn-native-admin-plan-deltas *fn-na-peer-list*)))

; fn-native-admin-live-group-delta-is-a-typed-delta: the two witnesses are
; the create and retire assertions above.  One violating value per
; hypothesis.
;
; Hypothesis 1, the plan was accepted: a refused `group create' (a 200-octet
; name, over the 128-octet group-name bound) stages nothing, so the
; conclusion's `consp' fails.
(defconst *fn-na-create-overlong*
  (fn-native-admin-plan
   (fn-na-test-argv (list "group" "create"
                          (coerce (make-list 200 :initial-element #\g) 'string)))))
(assert-event (member-equal (fn-native-admin-result-kind *fn-na-create-overlong*)
                            '(nil)))
(assert-event (not (equal (fn-native-admin-result-status *fn-na-create-overlong*) :accepted)))
(assert-event (not (consp (fn-native-admin-plan-deltas *fn-na-create-overlong*))))
; Hypothesis 2, the kind is a group kind: an ACCEPTED `peer remove' whose
; name is 300 octets.  The plan admits any non-empty word up to 512 octets
; there, the configuration label holds 256, and the staged delta is not
; typed -- so the theorem is about the group kinds and says so.
(defconst *fn-na-long-name*
  (coerce (make-list 300 :initial-element #\p) 'string))
(defconst *fn-na-peer-remove-long*
  (fn-native-admin-plan (fn-na-test-argv (list "peer" "remove" *fn-na-long-name*))))
(assert-event (equal (fn-native-admin-result-status *fn-na-peer-remove-long*) :accepted))
(assert-event (equal (fn-native-admin-result-kind *fn-na-peer-remove-long*) :remove-peer))
(assert-event (not (fn-cfg-delta-listp (fn-native-admin-plan-deltas *fn-na-peer-remove-long*))))

; The BP boundary is a durable peer delta with every originator in the
; loopback process boundary named; no received EID can create these rows.
(defconst *fn-na-bp-boundary*
  (fn-native-admin-plan
   (fn-na-test-argv '("bp-boundary" "add" "dtn-peer"
                       "peer.example.invalid" "dtn://peer/" "4556"))))
(assert-event (equal (fn-native-admin-result-status *fn-na-bp-boundary*)
                     :accepted))
(assert-event
 (and (fn-cfg-delta-listp (fn-native-admin-plan-deltas *fn-na-bp-boundary*))
      (fn-cfg-peer-find "dtn-peer"
        (fn-cfg-delta-rows (car (fn-native-admin-plan-deltas
                                 *fn-na-bp-boundary*))))
      (member-equal
       (fn-cfg-row-make "dtn-peer" "bp-boundary-originators"
                        "all-co-resident" 0)
       (fn-cfg-delta-rows (car (fn-native-admin-plan-deltas
                                *fn-na-bp-boundary*))))))
(assert-event
 (equal (fn-native-admin-result-status
         (fn-native-admin-plan
          (fn-na-test-argv '("bp-boundary" "add" "dtn-peer"
                              "peer.example.invalid" "dtn://peer/"
                              "999999999999999999999999"))))
        :refused))

; The short form admits a channel principal but grants no article ingress.
; An operator must supply an explicit inbound scope and finite limits.
(assert-event
 (not (member-equal
       (fn-cfg-row-make "dtn-peer" "inbound-groups" "fn.*" 32768)
       (fn-cfg-delta-rows (car (fn-native-admin-plan-deltas
                                *fn-na-bp-boundary*))))))
(defconst *fn-na-bp-inbound*
  (fn-native-admin-plan
   (fn-na-test-argv '("bp-boundary" "add" "dtn-peer"
                       "peer.example.invalid" "dtn://peer/" "4556"
                       "fn.*" "32768" "16"))))
(assert-event (equal (fn-native-admin-result-status *fn-na-bp-inbound*)
                     :accepted))
(assert-event
 (member-equal
  (fn-cfg-row-make "dtn-peer" "inbound-groups" "fn.*" 32768)
  (fn-cfg-delta-rows (car (fn-native-admin-plan-deltas
                           *fn-na-bp-inbound*)))))
(assert-event
 (equal (fn-native-admin-result-status
         (fn-native-admin-plan
          (fn-na-test-argv '("bp-boundary" "add" "dtn-peer"
                              "peer.example.invalid" "dtn://peer/" "4556"
                              "fn.*" "0" "16"))))
        :refused))

; -----------------------------------------------------------------------------
; RFC 5536 s3.1.4 reserved names at `group create'
; (`fn-native-admin-group-name-reservedp', `fn-native-admin-plan').
; The first (or only) component "example" and the whole name "poster" are
; reserved; the comparison folds ASCII case, so "Example.a" and "POSTER" are
; refused as well.  Every reserved witness is a valid group name, so the
; refusal is the reservation, not the grammar.
(defun fn-na-test-reserved-refusedp (names)
  (if (consp names)
      (let ((plan (fn-native-admin-plan
                   (fn-na-test-argv (list "group" "create" (car names))))))
        (and (fn-record-group-namep (car names))
             (fn-native-admin-group-name-reservedp (car names))
             (not (fn-native-admin-group-name-creatablep (car names)))
             (equal (fn-native-admin-result-status plan) :refused)
             (equal (fn-native-admin-result-reason plan) :reserved-group-name)
             (null (fn-native-admin-plan-deltas plan))
             (fn-na-test-reserved-refusedp (cdr names))))
    t))
(defconst *fn-na-reserved-names*
  '("example" "example.test" "example.a.b" "Example.a" "EXAMPLE.test"
    "poster" "POSTER" "Poster"))
(assert-event (fn-na-test-reserved-refusedp *fn-na-reserved-names*))

; Near misses are creatable: the rule is the first component and the whole
; name, not a substring.
(defun fn-na-test-creatable-acceptedp (names)
  (if (consp names)
      (let ((plan (fn-native-admin-plan
                   (fn-na-test-argv (list "group" "create" (car names))))))
        (and (fn-native-admin-group-name-creatablep (car names))
             (equal (fn-native-admin-result-status plan) :accepted)
             (equal (fn-native-admin-result-kind plan) :create-group)
             (consp (fn-native-admin-plan-deltas plan))
             (fn-na-test-creatable-acceptedp (cdr names))))
    t))
(defconst *fn-na-creatable-names*
  '("fn.example" "examples.test" "exampl" "example_a" "xexample.a"
    "poster.x" "posters" "fn.poster" "fn.test"))
(assert-event (fn-na-test-creatable-acceptedp *fn-na-creatable-names*))

; An invalid name is still the grammar's refusal, and `group retire' of a
; reserved name a store already carries stays admitted.
(assert-event (not (fn-native-admin-group-name-creatablep "fn..test")))
(assert-event (equal (fn-native-admin-result-reason
                      (fn-native-admin-plan
                       (fn-na-test-argv '("group" "create" "fn..test"))))
                     :syntax))
(defconst *fn-na-retire-reserved*
  (fn-native-admin-plan (fn-na-test-argv '("group" "retire" "example.test"))))
(assert-event (equal (fn-native-admin-result-status *fn-na-retire-reserved*)
                     :accepted))
(assert-event (equal (fn-native-admin-result-kind *fn-na-retire-reserved*)
                     :remove-group))

; Teeth for `fn-native-admin-plan-refuses-a-reserved-group-create', one
; `must-fail' per hypothesis, each refuted by a ground value.
; (1) Without `fn-native-admin-argvp': an improper argv of the same three
; words is refused :argv, not :reserved-group-name.
(defconst *fn-na-improper-reserved-argv*
  (list* (fn-record-string-octets "group") (fn-record-string-octets "create")
         (fn-record-string-octets "poster") 'tail))
(assert-event (not (fn-native-admin-argvp *fn-na-improper-reserved-argv*)))
(assert-event (equal (fn-native-admin-words *fn-na-improper-reserved-argv*)
                     '("group" "create" "poster")))
(assert-event (equal (fn-native-admin-result-reason
                      (fn-native-admin-plan *fn-na-improper-reserved-argv*))
                     :argv))
(must-fail
 (defthm fn-na-reserved-create-without-argvp
   (implies (and (equal (fn-native-admin-words argv) (list "group" "create" name))
                 (fn-native-admin-group-name-reservedp name))
            (equal (fn-native-admin-result-reason (fn-native-admin-plan argv))
                   :reserved-group-name))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-native-admin-plan)
                                   (fn-native-admin-group-name-reservedp
                                    fn-native-admin-words fn-native-admin-argvp
                                    fn-native-admin-peer-plan
                                    fn-native-admin-bp-boundary-plan
                                    fn-record-group-namep fn-path-identityp
                                    fn-native-admin-decimalp
                                    fn-native-admin-decimal-value))))))
; (2) Without the `group create' words: `group retire example.test' is
; accepted (the witness above).
(must-fail
 (defthm fn-na-reserved-without-create
   (implies (and (fn-native-admin-argvp argv)
                 (fn-native-admin-group-name-reservedp name))
            (equal (fn-native-admin-result-status (fn-native-admin-plan argv))
                   :refused))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-native-admin-plan)
                                   (fn-native-admin-group-name-reservedp
                                    fn-native-admin-words fn-native-admin-argvp
                                    fn-native-admin-peer-plan
                                    fn-native-admin-bp-boundary-plan
                                    fn-record-group-namep fn-path-identityp
                                    fn-native-admin-decimalp
                                    fn-native-admin-decimal-value))))))
; (3) Without the reservation: `group create fn.test' is accepted.
(must-fail
 (defthm fn-na-create-refused-without-reservation
   (implies (and (fn-native-admin-argvp argv)
                 (equal (fn-native-admin-words argv) (list "group" "create" name)))
            (equal (fn-native-admin-result-status (fn-native-admin-plan argv))
                   :refused))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-native-admin-plan)
                                   (fn-native-admin-group-name-reservedp
                                    fn-native-admin-words fn-native-admin-argvp
                                    fn-native-admin-peer-plan
                                    fn-native-admin-bp-boundary-plan
                                    fn-record-group-namep fn-path-identityp
                                    fn-native-admin-decimalp
                                    fn-native-admin-decimal-value))))))

; Teeth for `fn-native-admin-group-name-creatablep-is-the-rfc-5536-rule':
; each disjunct of the reading is needed.  Without the case fold,
; "Example.a" would be creatable; without the whole-name "example" disjunct,
; "example" would; without the "example." prefix, "example.test" would.
(assert-event (not (fn-native-admin-group-name-creatablep "Example.a")))
(must-fail
 (defthm fn-na-creatable-without-case-fold
   (equal (fn-native-admin-group-name-creatablep text)
          (and (fn-record-group-namep text)
               (let ((xs (fn-record-string-octets text)))
                 (not (or (equal xs *fn-native-admin-reserved-example*)
                          (and (<= 8 (len xs))
                               (equal (take 8 xs)
                                      (append *fn-native-admin-reserved-example*
                                              '(46))))
                          (equal xs *fn-native-admin-reserved-poster*))))))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable fn-record-group-namep
                                       fn-native-admin-fold-octets
                                       fn-record-string-octets)))))
(must-fail
 (defthm fn-na-creatable-without-only-component
   (equal (fn-native-admin-group-name-creatablep text)
          (and (fn-record-group-namep text)
               (let ((xs (fn-native-admin-fold-octets
                          (fn-record-string-octets text))))
                 (not (or (and (<= 8 (len xs))
                               (equal (take 8 xs)
                                      (append *fn-native-admin-reserved-example*
                                              '(46))))
                          (equal xs *fn-native-admin-reserved-poster*))))))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable fn-record-group-namep
                                       fn-native-admin-fold-octets
                                       fn-record-string-octets)))))
(must-fail
 (defthm fn-na-creatable-without-example-prefix
   (equal (fn-native-admin-group-name-creatablep text)
          (and (fn-record-group-namep text)
               (let ((xs (fn-native-admin-fold-octets
                          (fn-record-string-octets text))))
                 (not (or (equal xs *fn-native-admin-reserved-example*)
                          (equal xs *fn-native-admin-reserved-poster*))))))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable fn-record-group-namep
                                       fn-native-admin-fold-octets
                                       fn-record-string-octets)))))

; D23: `peer add ... carries HEX' adds carries-principal rows to the peer's
; set-peer delta; a peer without `carries' is the base plan unchanged.
(defconst *fn-na-carry-hex*
  "0707070707070707070707070707070707070707070707070707070707070707")
(defconst *fn-na-base-words*
  '("peer" "add" "near" "near" "localhost" "119" "*" "*" "127.0.0.1" "true"))
(defconst *fn-na-carry-plan*
  (fn-native-admin-peer-plan (append *fn-na-base-words*
                                     (list "carries" *fn-na-carry-hex*))))
(assert-event (equal (fn-native-admin-result-status *fn-na-carry-plan*) :accepted))
(assert-event (equal (fn-native-admin-result-kind *fn-na-carry-plan*) :set-peer))
(assert-event (equal (fn-native-admin-result-peer *fn-na-carry-plan*)
                     (fn-native-admin-result-peer
                      (fn-native-admin-peer-plan *fn-na-base-words*))))
(assert-event
 (equal (fn-native-admin-plan-deltas *fn-na-carry-plan*)
        (list (fn-cfg-set-peer
               "near"
               (append (fn-cfg-peer-rows
                        (fn-native-admin-result-peer *fn-na-carry-plan*))
                       (list (list "near" "carries-principal" *fn-na-carry-hex* 0)))))))
(assert-event
 (equal (fn-native-admin-plan-deltas (fn-native-admin-peer-plan *fn-na-base-words*))
        (list (fn-cfg-set-peer-delta
               (fn-native-admin-result-peer
                (fn-native-admin-peer-plan *fn-na-base-words*))))))
; Uppercase hex, or no principal after `carries', is refused.
(assert-event
 (equal (fn-native-admin-result-reason
         (fn-native-admin-peer-plan
          (append *fn-na-base-words*
                  (list "carries"
                        "0A0A0A0A0A0A0A0A0A0A0A0A0A0A0A0A0A0A0A0A0A0A0A0A0A0A0A0A0A0A0A0A"))))
        :carries))
(assert-event
 (equal (fn-native-admin-result-reason
         (fn-native-admin-peer-plan (append *fn-na-base-words* (list "carries"))))
        :carries))
