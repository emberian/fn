; Receiver-local selection for a portable signed carrier at a protected peer
; ingress.  A portable signature by itself is not a B-local enrollment or a
; historical Store verdict.  The latter exists only after kind-4 publication.
(in-package "ACL2")
(include-book "hybrid-lifecycle")
(include-book "hybrid-carrier")
(include-book "config")
(include-book "control-classify")

; The classifier prevents a malformed or unauthorized FN-Authorship field
; from falling through to the legacy article-only Store path.  An article
; that cannot be parsed is invalid here too, never carrier-absent.
(defun fn-pa-carrier-kind (received)
  (declare (xargs :guard t))
  (let ((parsed (fn-article-parse received)))
    (if (not (fn-article-result-okp parsed))
        :invalid
      (let ((article (fn-article-result-article parsed)))
        (if (not (true-listp article)) :invalid
          (if (equal (fn-hc-count-name
                      *fn-hc-name* (fn-article-fields article)) 0)
              :absent
            :present))))))

; Syntax and exact-source projection before any current local key policy.
; This allows byte-identical already-stored bytes to report the Store's
; historical duplicate outcome after a later key rotation or tombstone.
; If the old record was legacy fn-r, this does not upgrade it or create a
; historical verdict.  A present but malformed field has no such path.
(defun fn-pa-carrier-form (received)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory
                                 (disable fn-pa-carrier-kind
                                          fn-hc-received-plan)))))
  (let ((kind (fn-pa-carrier-kind received)))
    (if (eq kind :absent) :absent
      (if (eq kind :invalid) (list :refused :article)
        (let ((parsed (fn-hc-received-plan received)))
          (if (not (fn-hc-okp parsed))
              (list :refused :carrier)
            (let ((value (fn-hc-value parsed)))
              (if (not (and (true-listp value) (equal (len value) 2)))
                  (list :refused :carrier-shape)
                (let ((carrier (cadr value)))
                  (if (not (and (true-listp carrier)
                                (equal (len carrier) 3)))
                      (list :refused :carrier-shape)
                    (list :ok (car value) (car carrier) (cadr carrier)
                          (caddr carrier))))))))))))

; D23 (planning/decisions.md, 2026-09-24).  A peer boundary's carried-source
; list: the principals whose signed articles this node holds and relays for
; that neighbour without an enrollment of its own.  It is rows of the peer's
; configuration group (books/peer-config.lisp keeps its typed record and
; ignores other slots; books/config.lisp admits any rows keyed by the peer),
;
;   (name "carries-principal" HEX 0)       ; repeatable, one per principal
;
; HEX the 64 lowercase hexadecimal characters of the 32-octet principal, the
; spelling the HDR :fn-verified line and `auth-principal' use.  The list is
; compared as rendered octets, so no hex is parsed here.
(defconst *fn-pa-carries-slot* "carries-principal")

(defun fn-pa-carried-sources (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (let ((rest (fn-pa-carried-sources (cdr rows))))
        (if (and (equal (fn-cfg-row-b (car rows)) *fn-pa-carries-slot*)
                 (stringp (fn-cfg-row-c (car rows))))
            (cons (fn-record-string-octets (fn-cfg-row-c (car rows))) rest)
          rest))
    nil))

; The list for the peer that delivered: its rows in the configured table.
(defun fn-pa-peer-carried-sources (peer peers)
  (declare (xargs :guard t))
  (fn-pa-carried-sources (fn-cfg-rows-with-key peers peer)))

(defun fn-pa-carriesp (principal carried)
  (declare (xargs :guard t))
  (and (fn-hsig-exact-octets-p principal 32)
       (true-listp carried)
       (member-equal (fn-stx-hex-octets principal) carried)
       t))

; The one acceptance decision for a present carrier (served POST, bound local
; submission, NNTP transit).  Five outcomes:
;   (:ok source principal keys signatures exact-current-snapshot generation)
;     this node's current enrollment of the principal names the carried keys;
;   (:carried source principal keys signatures)
;     D23: this node has no snapshot of the principal at all (never enrolled,
;     never revoked) and CARRIED, the delivering boundary's list, names it;
;   (:revoked source principal keys signatures tombstone generation)
;     PRF-098: NNTP transit only (TRANSITP), this node's newest snapshot of the
;     principal is its revocation tombstone at GENERATION, that tombstone is
;     the snapshot the generation names, and the carried keys are keys this
;     node enrolled for the principal before: evidence of an article signed
;     before the revocation, stored as :revoked, never :verified;
;   (:refused REASON), carrier-form's refusals and :local-enrollment;
;   :absent, the unsigned arm.
; CARRIED is nil and TRANSITP nil on every path without a delivering peer
; (served POST, bound submission, BP transit), where the decision is the D02
; one unchanged (fn-pa-current-plan-off-the-transit-arms-is-the-d02-plan).
; A principal enrolled under other keys is refused whatever the list.
(defun fn-pa-revoked-tombstonep (current generation principal keys snapshots)
  (declare (xargs :guard t))
  (and (fn-stxk-p current)
       (equal (fn-stxk-profile current) *fn-hl-revoked-profile*)
       (posp generation)
       (equal (fn-stxk-find generation snapshots) current)
       (fn-hsig-enrolled-keys-of-principalp principal keys snapshots)))

(defun fn-pa-current-plan (received snapshots carried transitp)
  (declare (xargs :guard t))
  (let ((form (fn-pa-carrier-form received)))
    (if (not (and (consp form) (eq (car form) :ok))) form
            (let* ((source (nth 1 form))
                   (principal (nth 2 form))
                   (keys (nth 3 form))
                   (signatures (nth 4 form))
                   (current (fn-hl-current-for-principal
                             principal snapshots))
                   (generation (if (fn-stxk-p current)
                                   (fn-stxk-keyring-generation current) nil))
                   (enrolled (fn-hl-current-enrollment
                              generation snapshots)))
              (cond ((and (true-listp enrolled)
                          (equal (len enrolled) 3)
                          (equal (car enrolled) current)
                          (equal (cadr enrolled) principal)
                          (equal (caddr enrolled) keys))
                     (list :ok source principal keys signatures
                           current generation))
                    ((and (null current)
                          (fn-pa-carriesp principal carried))
                     (list :carried source principal keys signatures))
                    ((and transitp
                          (fn-pa-revoked-tombstonep current generation
                                                    principal keys snapshots))
                     (list :revoked source principal keys signatures
                           current generation))
                    (t (list :refused :local-enrollment)))))))

; The caller supplies primitive observations, not an authorization Boolean.
; This constructor reselects the exact carrier and current enrollment itself,
; and retains B's relayed payload and peer-derived evidence in the article
; record.  Store publication is the separate durable acceptance decision.
(defun fn-pa-authorized-event
    (sequence txid generation msgid received groups obligation-id
              content-subject release-evidence charge snapshots
              observed-ml-key ed-observation ml-observation clock-observation)
  (declare (xargs :guard t))
  (let ((plan (fn-pa-current-plan received snapshots nil nil)))
    (if (not (and (consp plan) (eq (car plan) :ok))) nil
      (fn-hsig-authorized-carried-submission-event-base
       sequence txid generation (nth 6 plan)
       (fn-stxk-snapshot (nth 5 plan))
       msgid (nth 1 plan) received groups obligation-id content-subject
       release-evidence charge (nth 2 plan) (nth 3 plan) (nth 4 plan)
       observed-ml-key ed-observation ml-observation clock-observation
       (fn-hc-okp (fn-hc-received-plan received))))))

;; D23: the carried arm's Store event.  The same article record, authored
;; source and carrier the schema-1 constructor binds
;; (fn-hsig-authorized-carried-submission-event-base), with no enrolled
;; snapshot, no primitive observation, and a verdict whose token is :carried,
;; whose detail is the carrier's principal and whose keyring generation is 0.
;; It is returned only when replay's carried branch admits it
;; (fn-hsig-article-event-carried-bindsp), so the host has nothing to commit
;; otherwise.  Host: host/owner-host.lisp fn-owner-peer-carried-relay-event.
(defun fn-pa-carried-event
    (sequence txid generation msgid received groups obligation-id
              content-subject release-evidence charge snapshots carried
              clock-observation)
  (declare (xargs :guard t))
  (let ((plan (fn-pa-current-plan received snapshots carried t)))
    (if (not (and (consp plan) (eq (car plan) :carried))) nil
      (let* ((source (nth 1 plan))
             (principal (nth 2 plan))
             (fields (fn-hsig-authored-source-fields source))
             (stamp (fn-record-stamp-of-observation clock-observation))
             (record (fn-record-make sequence txid generation msgid received
                                     groups obligation-id content-subject
                                     release-evidence charge stamp))
             (source-id (fn-hsig-authored-source-id source)))
        (if (and (natp stamp) fields source-id
                 (equal msgid (car fields))
                 (equal groups (cadr fields))
                 (equal charge (fn-charge-for-payload (len received)))
                 (fn-hsig-carried-record-metadatap source received record))
            (let* ((verdict (fn-stxe-make sequence txid generation msgid
                                          :carried principal 0
                                          (fn-hsig-evidence-tag source)))
                   (event (fn-stxa-make-carried
                           sequence txid generation 0
                           (fn-hsig-evidence-tag source)
                           (fn-record-string-octets content-subject)
                           (fn-record-encode record)
                           (fn-stxe-encode verdict)
                           source source-id)))
              (if (fn-hsig-article-event-carried-bindsp event) event nil))
          nil)))))

;; ---------------------------------------------------------------------------
;; D23 keystones over fn-pa-current-plan, the function
;; host/owner-host.lisp fn-owner-peer-carrier-plan calls for every present
;; carrier (served POST, bound submission and transit).

; The carrier's own form is :absent, (:refused REASON) or (:ok ...): the
; carried arm is only ever the plan's.
(defthm fn-pa-carrier-form-is-never-carried
  (not (equal (car (fn-pa-carrier-form received)) :carried))
  :hints (("Goal" :in-theory (e/d (fn-pa-carrier-form)
                                  (fn-pa-carrier-kind fn-hc-received-plan)))))

(defthm fn-pa-carrier-form-is-never-revoked
  (not (equal (car (fn-pa-carrier-form received)) :revoked))
  :hints (("Goal" :in-theory (e/d (fn-pa-carrier-form)
                                  (fn-pa-carrier-kind fn-hc-received-plan)))))

; Five outcomes and no sixth: accepted under this node's enrollment, carried
; for the delivering boundary, revoked evidence on transit, refused with a
; reason, or the unsigned arm.
(defthm fn-pa-current-plan-outcomes
  (let ((plan (fn-pa-current-plan received snapshots carried transitp)))
    (or (equal plan :absent)
        (equal (car plan) :ok)
        (equal (car plan) :carried)
        (equal (car plan) :revoked)
        (equal (car plan) :refused)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-pa-current-plan fn-pa-carrier-form)
                                  (fn-pa-carrier-kind fn-hc-received-plan
                                   fn-hl-current-for-principal
                                   fn-hl-current-enrollment fn-pa-carriesp
                                   fn-pa-revoked-tombstonep)))))

; The carried arm needs both: the delivering boundary lists the principal,
; and this node has no snapshot of it (never enrolled, never revoked).
(defthm fn-pa-carried-arm-needs-the-list-and-no-local-snapshot
  (let ((plan (fn-pa-current-plan received snapshots carried transitp)))
    (implies (equal (car plan) :carried)
             (and (fn-pa-carriesp (nth 2 plan) carried)
                  (null (fn-hl-current-for-principal (nth 2 plan) snapshots))
                  (equal (nth 1 plan) (nth 1 (fn-pa-carrier-form received)))
                  (equal (nth 2 plan) (nth 2 (fn-pa-carrier-form received))))))
  :hints (("Goal" :in-theory (e/d (fn-pa-current-plan fn-pa-carrier-form)
                                  (fn-pa-carrier-kind fn-hc-received-plan
                                   fn-hl-current-for-principal
                                   fn-hl-current-enrollment fn-pa-carriesp
                                   fn-pa-revoked-tombstonep)))))

; Off the two transit arms the decision is the D02 one: an enrolled receiver
; accepts exactly as before and an unlisted, unenrolled principal is refused
; with :local-enrollment, whatever list the boundary carries and whatever
; the path.
(defthm fn-pa-current-plan-off-the-transit-arms-is-the-d02-plan
  (implies (and (not (equal (car (fn-pa-current-plan received snapshots
                                                     carried transitp))
                            :carried))
                (not (equal (car (fn-pa-current-plan received snapshots
                                                     carried transitp))
                            :revoked)))
           (equal (fn-pa-current-plan received snapshots carried transitp)
                  (fn-pa-current-plan received snapshots nil nil)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-pa-current-plan fn-pa-carriesp)
                                  (fn-pa-carrier-form
                                   fn-hl-current-for-principal
                                   fn-hl-current-enrollment
                                   fn-pa-revoked-tombstonep)))))

; Every path without a delivering peer passes nil: it never carries.
(defthm fn-pa-current-plan-without-carried-list-never-carries
  (not (equal (car (fn-pa-current-plan received snapshots nil transitp))
              :carried))
  :hints (("Goal" :in-theory (e/d (fn-pa-current-plan fn-pa-carriesp)
                                  (fn-pa-carrier-form
                                   fn-hl-current-for-principal
                                   fn-hl-current-enrollment
                                   fn-pa-revoked-tombstonep)))))

; Every path but NNTP transit passes TRANSITP nil: it never reports
; :revoked (a served POST under a revoked key is refused :local-enrollment).
(defthm fn-pa-current-plan-off-transit-never-revoked
  (not (equal (car (fn-pa-current-plan received snapshots carried nil))
              :revoked))
  :hints (("Goal" :in-theory (e/d (fn-pa-current-plan)
                                  (fn-pa-carrier-form fn-pa-carriesp
                                   fn-hl-current-for-principal
                                   fn-hl-current-enrollment
                                   fn-pa-revoked-tombstonep)))))

(defthm fn-pa-carried-event-requires-the-carried-arm
  (implies (fn-pa-carried-event
            sequence txid generation msgid received groups obligation-id
            content-subject release-evidence charge snapshots carried
            clock-observation)
           (equal (car (fn-pa-current-plan received snapshots carried t))
                  :carried))
  :hints (("Goal" :in-theory
           (e/d (fn-pa-carried-event)
                (fn-pa-current-plan fn-hsig-article-event-carried-bindsp
                 fn-stxa-make-carried fn-stxe-encode 
                 fn-record-make fn-hsig-carried-record-metadatap)))))

; The carried event is what replay's carried branch admits, and its verdict
; is :carried naming the carrier's principal: never :verified.
(defthm fn-pa-carried-event-is-a-carried-record
  (let ((e (fn-pa-carried-event
            sequence txid generation msgid received groups obligation-id
            content-subject release-evidence charge snapshots carried
            clock-observation)))
    (implies e
             (and (fn-hsig-article-event-carried-bindsp e)
                  (equal (fn-stxa-keyring-generation e) 0)
                  (equal (fn-stxe-token
                          (fn-stmt-value
                           (fn-stxe-decode-exact (fn-stxa-verdict-event e))))
                         :carried))))
  :hints (("Goal" :in-theory
           (e/d (fn-pa-carried-event)
                (fn-pa-current-plan fn-hsig-article-event-carried-bindsp
                 fn-stxa-bindsp fn-stxa-p
                 fn-stxa-make-carried fn-stxe-encode 
                 fn-record-make fn-hsig-carried-record-metadatap
                 fn-stxe-decode-exact
                 fn-hc-received-plan fn-hsig-authored-source-id)))))

(defthm fn-pa-absent-is-only-parser-confirmed-absence
  (implies (equal (fn-pa-current-plan received snapshots carried transitp)
                  :absent)
           (equal (fn-pa-carrier-kind received) :absent))
  :hints (("Goal" :in-theory (enable fn-pa-current-plan
                                     fn-pa-carrier-form))))

(defthm fn-pa-authorized-event-requires-current-plan-by-definition
  (implies (fn-pa-authorized-event
            sequence txid generation msgid received groups obligation-id
            content-subject release-evidence charge snapshots
            observed-ml-key ed-observation ml-observation clock-observation)
           (equal (car (fn-pa-current-plan received snapshots nil nil)) :ok))
  :hints (("Goal" :in-theory
           (e/d (fn-pa-authorized-event)
                (fn-pa-current-plan fn-hc-received-plan
                 fn-hsig-authorized-carried-submission-event-base)))))

;; ---------------------------------------------------------------------------
;; PRF-098: the revoked arm's Store event.  The same article record, authored
;; source and carrier the carried arm binds, a verdict whose token is
;; :revoked, whose detail is the carrier's principal and whose keyring
;; generation is the tombstone's, and BOTH primitive observations: the
;; caller supplies them over the carrier's keys (the keys this node once
;; enrolled for the principal) and this constructor requires
;; fn-hsig-authorize-at of them, exactly as the :ok arm does.  It is
;; returned only when replay's revoked branch admits it at these snapshots
;; (fn-hsig-article-event-revoked-bindsp, fn-hsig-revoked-tombstone-bindsp),
;; so the host has nothing to commit otherwise.  NNTP transit only (the plan
;; is asked with TRANSITP t).  Host: host/owner-host.lisp
;; fn-owner-peer-revoked-event, called from host/native/owner.lisp
;; fnn-owner-attempt-transit on the plan's :revoked arm.
(defun fn-pa-revoked-event
    (sequence txid generation msgid received groups obligation-id
              content-subject release-evidence charge snapshots
              observed-ml-key ed-observation ml-observation clock-observation)
  (declare (xargs :guard t))
  (let ((plan (fn-pa-current-plan received snapshots nil t)))
    (if (not (and (consp plan) (eq (car plan) :revoked))) nil
      (let* ((source (nth 1 plan))
             (principal (nth 2 plan))
             (keys (nth 3 plan))
             (signatures (nth 4 plan))
             (tombstone (nth 6 plan))
             (fields (fn-hsig-authored-source-fields source))
             (stamp (fn-record-stamp-of-observation clock-observation))
             (record (fn-record-make sequence txid generation msgid received
                                     groups obligation-id content-subject
                                     release-evidence charge stamp))
             (source-id (fn-hsig-authored-source-id source)))
        (if (and (natp stamp) fields source-id
                 (equal msgid (car fields))
                 (equal groups (cadr fields))
                 (equal charge (fn-charge-for-payload (len received)))
                 (fn-hsig-carried-record-metadatap source received record)
                 (fn-hsig-authorize-at (fn-hsig-source-version source)
                                       principal keys source signatures
                                       observed-ml-key ed-observation
                                       ml-observation))
            (let* ((verdict (fn-stxe-make sequence txid generation msgid
                                          :revoked principal tombstone
                                          (fn-hsig-evidence-tag source)))
                   (event (fn-stxa-make-carried
                           sequence txid generation tombstone
                           (fn-hsig-evidence-tag source)
                           (fn-record-string-octets content-subject)
                           (fn-record-encode record)
                           (fn-stxe-encode verdict)
                           source source-id)))
              (if (and (fn-hsig-article-event-revoked-bindsp event)
                       (fn-hsig-revoked-tombstone-bindsp
                        (fn-stmt-value
                         (fn-stxe-decode-exact (fn-stxa-verdict-event event)))
                        (fn-hsig-article-event-carrier-keys event)
                        snapshots))
                  event
                nil))
          nil)))))

;; Keystones over fn-pa-current-plan's revoked arm and the event.

; The revoked arm is taken only on NNTP transit, only for a principal whose
; newest snapshot here is its tombstone at the plan's generation, and only
; for keys this node enrolled for that principal.
(defthm fn-pa-revoked-arm-needs-transit-a-tombstone-and-once-enrolled-keys
  (let ((plan (fn-pa-current-plan received snapshots carried transitp)))
    (implies (equal (car plan) :revoked)
             (and (not (null transitp))
                  (equal (nth 5 plan)
                         (fn-hl-current-for-principal (nth 2 plan) snapshots))
                  (fn-stxk-p (nth 5 plan))
                  (equal (fn-stxk-profile (nth 5 plan)) *fn-hl-revoked-profile*)
                  (equal (nth 6 plan) (fn-stxk-keyring-generation (nth 5 plan)))
                  (posp (nth 6 plan))
                  (equal (fn-stxk-find (nth 6 plan) snapshots) (nth 5 plan))
                  (fn-hsig-enrolled-keys-of-principalp (nth 2 plan) (nth 3 plan)
                                                       snapshots)
                  (equal (nth 1 plan) (nth 1 (fn-pa-carrier-form received)))
                  (equal (nth 2 plan) (nth 2 (fn-pa-carrier-form received)))
                  (equal (nth 3 plan) (nth 3 (fn-pa-carrier-form received))))))
  :hints (("Goal" :in-theory (e/d (fn-pa-current-plan fn-pa-revoked-tombstonep)
                                  (fn-pa-carrier-form fn-pa-carriesp
                                   fn-hl-current-for-principal
                                   fn-hl-current-enrollment
                                   fn-hsig-enrolled-keys-of-principalp)))))

; KEYSTONE (theorem 3 of the spike record, first half).  While a principal's
; newest snapshot here is a revocation tombstone, no plan for a carrier
; naming that principal is :ok, on any path, whatever the boundary carries.
(defthm fn-pa-no-ok-plan-for-a-revoked-principal
  (implies (and (equal (nth 2 (fn-pa-carrier-form received)) principal)
                (equal (fn-stxk-profile
                        (fn-hl-current-for-principal principal snapshots))
                       *fn-hl-revoked-profile*))
           (not (equal (car (fn-pa-current-plan received snapshots carried
                                                transitp))
                       :ok)))
  :hints (("Goal" :in-theory (e/d (fn-pa-current-plan)
                                  (fn-pa-carrier-form fn-pa-carriesp
                                   fn-hl-current-for-principal
                                   fn-hl-current-enrollment
                                   fn-hsig-keyring-snapshot-value
                                   fn-pa-revoked-tombstonep))
           :use ((:instance fn-hl-current-enrollment-selects-an-enrolled-snapshot
                            (requested (fn-stxk-keyring-generation
                                        (fn-hl-current-for-principal
                                         principal snapshots))))
                 (:instance fn-hsig-keyring-snapshot-value-requires-the-key-profile
                            (snapshot (fn-hl-current-for-principal
                                       principal snapshots)))))))

; KEYSTONE (theorem 3, over the revocation the owner commits).  After the
; tombstone fn-hl-revoke-event builds for P at G is the newest snapshot, no
; plan for P is :ok; on NNTP transit a carrier under keys this node enrolled
; for P before is :revoked at G, and on every other path it is refused
; :local-enrollment.
(defthm fn-pa-revocation-leaves-no-ok-plan
  (let ((tomb (fn-hl-revoke-event sequence txid store-generation g
                                  principal snapshots)))
    (implies (and tomb
                  (equal (nth 2 (fn-pa-carrier-form received)) principal))
             (not (equal (car (fn-pa-current-plan received (cons tomb snapshots)
                                                  carried transitp))
                         :ok))))
  :hints (("Goal" :in-theory (disable fn-hl-revoke-event fn-pa-carrier-form
                                      fn-hl-current-for-principal)
           :use ((:instance fn-hl-revoke-event-is-the-principals-tombstone
                            (keyring-generation g))
                 (:instance fn-pa-no-ok-plan-for-a-revoked-principal
                            (snapshots
                             (cons (fn-hl-revoke-event sequence txid
                                                       store-generation g
                                                       principal snapshots)
                                   snapshots)))))))

(defthm fn-pa-revoked-principal-on-transit-is-revoked-at-its-tombstone
  (let ((tomb (fn-hl-revoke-event sequence txid store-generation g
                                  principal snapshots))
        (form (fn-pa-carrier-form received)))
    (implies (and tomb
                  (equal (car form) :ok)
                  (equal (nth 2 form) principal)
                  (fn-hsig-enrolled-keys-of-principalp principal (nth 3 form)
                                                       snapshots))
             (equal (fn-pa-current-plan received (cons tomb snapshots)
                                        carried transitp)
                    (if transitp
                        (list :revoked (nth 1 form) principal (nth 3 form)
                              (nth 4 form) tomb g)
                      (list :refused :local-enrollment)))))
  :hints (("Goal" :in-theory (e/d (fn-pa-current-plan fn-pa-revoked-tombstonep
                                   fn-hsig-enrolled-keys-of-principalp
                                   fn-stxk-find)
                                  (fn-hl-revoke-event fn-pa-carrier-form
                                   fn-pa-carriesp fn-hl-current-enrollment
                                   fn-hsig-keyring-snapshot-value
                                   fn-hl-current-for-principal))
           :use ((:instance fn-hl-revoke-event-is-the-principals-tombstone
                            (keyring-generation g))
                 (:instance fn-pa-no-ok-plan-for-a-revoked-principal
                            (snapshots
                             (cons (fn-hl-revoke-event sequence txid
                                                       store-generation g
                                                       principal snapshots)
                                   snapshots)))))))

; KEYSTONE (the revoked event).  A revoked composite the owner can commit
; exists only on the revoked arm with both primitive observations verified
; over the carrier's keys, is the record replay's revoked branch admits at
; these snapshots, and its verdict is :revoked at the tombstone's generation,
; never :verified.
(defthm fn-pa-revoked-event-binds-the-arm-and-both-observations
  (let ((e (fn-pa-revoked-event
            sequence txid generation msgid received groups obligation-id
            content-subject release-evidence charge snapshots
            observed-ml-key ed-observation ml-observation clock-observation))
        (plan (fn-pa-current-plan received snapshots nil t)))
    (implies e
             (and (equal (car plan) :revoked)
                  (fn-hsig-authorize-at (fn-hsig-source-version (nth 1 plan))
                                        (nth 2 plan) (nth 3 plan) (nth 1 plan)
                                        (nth 4 plan) observed-ml-key
                                        ed-observation ml-observation)
                  (equal ed-observation :verified)
                  (equal ml-observation :verified)
                  (fn-hsig-article-event-revoked-bindsp e)
                  (fn-hsig-revoked-tombstone-bindsp
                   (fn-stmt-value (fn-stxe-decode-exact (fn-stxa-verdict-event e)))
                   (fn-hsig-article-event-carrier-keys e)
                   snapshots)
                  (equal (fn-stxe-token
                          (fn-stmt-value
                           (fn-stxe-decode-exact (fn-stxa-verdict-event e))))
                         :revoked))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-pa-revoked-event fn-hsig-authorize-at)
                (fn-pa-current-plan fn-pa-carrier-form
                 fn-pa-revoked-arm-needs-transit-a-tombstone-and-once-enrolled-keys
                 fn-hsig-article-event-revoked-bindsp
                 fn-hsig-article-event-revoked-bindsp-facts
                 fn-hsig-revoked-tombstone-bindsp fn-hsig-article-event-carrier
                 fn-hsig-article-event-carrier-keys
                 fn-stxa-make-carried fn-stxe-encode fn-stxe-decode-exact
                 fn-stxe-make fn-record-make
                 fn-hsig-carried-record-metadatap
                 fn-hsig-subject-at-p fn-hsig-signatures-p fn-hsig-source-version
                 fn-hc-received-plan fn-hsig-authored-source-id
                 fn-hsig-authored-source-fields fn-hsig-evidence-tag
                 fn-record-stamp-of-observation fn-charge-for-payload))
           :use ((:instance fn-hsig-article-event-revoked-bindsp-facts
                            (event (fn-pa-revoked-event
                                    sequence txid generation msgid received
                                    groups obligation-id content-subject
                                    release-evidence charge snapshots
                                    observed-ml-key ed-observation
                                    ml-observation clock-observation)))))))

;; The served POST's outcome word after the carried attempt (served NNTP
;; POST and the bound local submissions call the same attempt transit does,
;; host/native/owner.lisp fnn-owner-attempt-served).  A present carrier
;; refused by fn-pa-carrier-form or fn-pa-current-plan relays that plan's
;; reason; :signature is the primitive observation's refusal and :conflict the
;; Store's existing-action answer.  Each is its own 441 line
;; (books/nntp-post.lisp fn-post-store-refusal-line).  Every other word,
;; including every word of the carrier-absent arm (whose detail is nil), is
;; the attempt's own word unchanged.
(defconst *fn-pa-served-reasons*
  '(:article :carrier :carrier-shape :local-enrollment :signature :conflict
    :control-not-filed :control-malformed :control-signed
    :event :signed-record))

(defun fn-pa-served-word (word detail)
  (declare (xargs :guard t))
  (if (and (equal word :refused)
           (member-equal detail *fn-pa-served-reasons*))
      detail
    word))

(defthm fn-pa-served-word-without-detail-by-definition
  (equal (fn-pa-served-word word nil) word))

;; ---------------------------------------------------------------------------
;; Control messages, packet C1 (planning/design-2026-09-25-control-messages.md
;; section 2.1 rules 1 and 2; specs/peering.md section 8, "Filing").  The
;; filing step every ingress takes before its Store attempt: host/native/
;; owner.lisp fnn-owner-attempt-transit calls it (through host/owner-host.lisp
;; fn-owner-control-filing) first, and served POST (fnn-owner-attempt-served),
;; NNTP transit and BP transit (fnn-owner-complete-bp-transit-submission) all
;; reach the Store only through that function.  GROUPS are the octet names
;; the ingress decision chose (the injection decision's, fn-peer-scope-groups',
;; the bound submission's); DOMAIN the names of the owner's allocation domain,
;; the table fn-owner-group-codes resolves against.
;;
;;   (:file GROUPS')          GROUPS for an ordinary article; for a control
;;                            article exactly its filing group, control.<verb>
;;                            or control, never a group Newsgroups names;
;;   (:refused :control-not-filed)   the operator has not created that group;
;;   (:refused :control-malformed)   two Control fields, Control beside
;;                            Supersedes, or a command outside the grammar;
;;   (:refused :control-signed)      a control article with an FN-Authorship
;;                            carrier.  OPEN (C1): a signed article's Store
;;                            record must list exactly the source's Newsgroups
;;                            (books/hybrid-store.lisp, the three
;;                            `(equal groups (cadr fields))' tests and the
;;                            replay binding), so it cannot be filed under
;;                            control.<verb> until that binding names the
;;                            filing group; refused rather than filed where
;;                            RFC 5537 section 3.7 says not to.
;;
;; The stored bytes are the received bytes; only the membership changes.
(defun fn-pa-filing-plan (received groups domain)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory
                                 (disable fn-ctl-classify-octets
                                          fn-pa-carrier-kind)))))
  (let ((classified (fn-ctl-classify-octets received)))
    (cond ((and (consp classified) (eq (car classified) :malformed))
           (list :refused :control-malformed))
          ((and (consp classified) (eq (car classified) :control))
           (if (not (eq (fn-pa-carrier-kind received) :absent))
               (list :refused :control-signed)
             (let ((group (fn-ctl-filing-group (cadr classified))))
               (if (fn-ctl-memberp group domain)
                   (list :file (list (fn-record-string-octets group)))
                 (list :refused :control-not-filed)))))
          (t (list :file groups)))))

; KEYSTONE (C1).  Over the plan the host calls: a control article is filed
; in exactly one group, its filing group, which is `control' or
; `control.<verb>' and is in the operator's domain, or it is refused with a
; control reason.  No other group, in particular none its Newsgroups field
; names, is ever the answer.
(defthm fn-ctl-control-article-is-filed-only-in-control
  (implies (equal (car (fn-ctl-classify-octets received)) :control)
           (let ((plan (fn-pa-filing-plan received groups domain))
                 (group (fn-ctl-filing-group
                         (cadr (fn-ctl-classify-octets received)))))
             (and (fn-ctl-control-group-namep group)
                  (if (equal (car plan) :file)
                      (and (equal (cadr plan)
                                  (list (fn-record-string-octets group)))
                           (fn-ctl-memberp group domain))
                    (or (equal plan (list :refused :control-not-filed))
                        (equal plan (list :refused :control-signed)))))))
  :hints (("Goal" :in-theory (disable fn-ctl-classify-octets
                                      fn-pa-carrier-kind
                                      fn-record-string-octets))))

; For an unsigned control article the one refusal is the absent group:
; filed exactly when the operator created control.<verb> (or control).
(defthm fn-ctl-unsigned-control-filing-by-definition
  (implies (and (equal (car (fn-ctl-classify-octets received)) :control)
                (equal (fn-pa-carrier-kind received) :absent))
           (equal (fn-pa-filing-plan received groups domain)
                  (if (fn-ctl-memberp (fn-ctl-filing-group
                                     (cadr (fn-ctl-classify-octets received)))
                                    domain)
                      (list :file
                            (list (fn-record-string-octets
                                   (fn-ctl-filing-group
                                    (cadr (fn-ctl-classify-octets received))))))
                    (list :refused :control-not-filed))))
  :hints (("Goal" :in-theory (disable fn-ctl-classify-octets
                                      fn-pa-carrier-kind
                                      fn-record-string-octets))))

; KEYSTONE (C1, RFC 5537 section 5).  An article with no Control field is
; ordinary at the plan: its groups pass through unchanged, whatever its
; Subject ("cmsg cancel ..."), its Newsgroups (".ctl") or Also-Control say.
; fn does not take the RFC's MAY to reject the cmsg form as ambiguous.
(defthm fn-ctl-cmsg-subject-is-ordinary
  (implies (atom (fn-ctl-fields-named
                  *fn-ctl-control-name*
                  (fn-article-fields
                   (fn-article-result-article (fn-article-parse received)))))
           (equal (fn-pa-filing-plan received groups domain)
                  (list :file groups)))
  :hints (("Goal" :in-theory (e/d (fn-ctl-classify-octets fn-ctl-classify)
                                  (fn-pa-carrier-kind fn-article-parse
                                   fn-record-string-octets)))))

(in-theory (disable (:d fn-pa-current-plan) (:d fn-pa-authorized-event)
                    (:d fn-pa-revoked-event) (:d fn-pa-revoked-tombstonep)
                    (:d fn-pa-carried-event) (:d fn-pa-carriesp)
                    (:d fn-pa-filing-plan)))
