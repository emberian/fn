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
; submission, NNTP transit).  Four outcomes:
;   (:ok source principal keys signatures exact-current-snapshot generation)
;     this node's current enrollment of the principal names the carried keys;
;   (:carried source principal keys signatures)
;     D23: this node has no snapshot of the principal at all (never enrolled,
;     never revoked) and CARRIED, the delivering boundary's list, names it;
;   (:refused REASON), carrier-form's refusals and :local-enrollment;
;   :absent, the unsigned arm.
; CARRIED is nil on every path without a delivering peer (served POST, bound
; submission, BP transit), where the decision is the D02 one unchanged
; (fn-pa-current-plan-without-carried-list-never-carries).  A revoked
; principal, or one enrolled under other keys, is refused whatever the list.
(defun fn-pa-current-plan (received snapshots carried)
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
  (let ((plan (fn-pa-current-plan received snapshots nil)))
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
  (let ((plan (fn-pa-current-plan received snapshots carried)))
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
;; SPIKE (spike/peering): the revoked arm.  Defers to dev: folding it into
;; fn-pa-current-plan as a fifth outcome with its keystones (the host asks
;; this plan only after fn-pa-current-plan refused a transit article with
;; :local-enrollment; host/native/owner.lisp fnn-owner-attempt-transit), and
;; binding the two primitive observations into the event (the host requires
;; both verified before it asks for the event, as on the :ok arm).
;;
;; (:revoked source principal keys signatures tombstone-generation) when this
;; node's newest snapshot of the carrier's principal is a revocation
;; tombstone and the carrier's ordered key set is one this node enrolled for
;; that principal before; nil otherwise.

(defun fn-pa-enrolled-keys-of-principalp (principal keys snapshots)
  (declare (xargs :guard t))
  (if (consp snapshots)
      (let ((value (fn-hsig-keyring-snapshot-value (car snapshots))))
        (or (and (true-listp value) (equal (len value) 2)
                 (equal (car value) principal)
                 (equal (cadr value) keys))
            (fn-pa-enrolled-keys-of-principalp principal keys (cdr snapshots))))
    nil))

(defun fn-pa-revoked-plan (received snapshots)
  (declare (xargs :guard t))
  (let ((form (fn-pa-carrier-form received)))
    (if (not (and (consp form) (eq (car form) :ok))) nil
      (let* ((principal (nth 2 form))
             (keys (nth 3 form))
             (current (fn-hl-current-for-principal principal snapshots)))
        (if (and (fn-stxk-p current)
                 (equal (fn-stxk-profile current) *fn-hl-revoked-profile*)
                 (posp (fn-stxk-keyring-generation current))
                 (fn-pa-enrolled-keys-of-principalp principal keys snapshots))
            (list :revoked (nth 1 form) principal keys (nth 4 form)
                  (fn-stxk-keyring-generation current))
          nil)))))

(defun fn-pa-revoked-event
    (sequence txid generation msgid received groups obligation-id
              content-subject release-evidence charge snapshots
              clock-observation)
  (declare (xargs :guard t))
  (let ((plan (fn-pa-revoked-plan received snapshots)))
    (if (not (and (consp plan) (eq (car plan) :revoked))) nil
      (let* ((source (nth 1 plan))
             (principal (nth 2 plan))
             (tombstone (nth 5 plan))
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
                                          :revoked principal tombstone
                                          (fn-hsig-evidence-tag source)))
                   (event (fn-stxa-make-carried
                           sequence txid generation tombstone
                           (fn-hsig-evidence-tag source)
                           (fn-record-string-octets content-subject)
                           (fn-record-encode record)
                           (fn-stxe-encode verdict)
                           source source-id)))
              (if (fn-hsig-article-event-revoked-bindsp event) event nil))
          nil)))))

; The revoked arm is never taken for a principal this node has not revoked.
(defthm fn-pa-revoked-plan-requires-a-tombstone
  (implies (fn-pa-revoked-plan received snapshots)
           (let ((current (fn-hl-current-for-principal
                           (nth 2 (fn-pa-revoked-plan received snapshots))
                           snapshots)))
             (and (fn-stxk-p current)
                  (equal (fn-stxk-profile current) *fn-hl-revoked-profile*))))
  :hints (("Goal" :in-theory (e/d (fn-pa-revoked-plan)
                                  (fn-pa-carrier-form
                                   fn-hl-current-for-principal)))))

;; ---------------------------------------------------------------------------
;; SPIKE (spike/peering): the opaque-carriage resource policy (review
;; 2026-09-24, gpt-6 direction).  A boundary that carries principals this node
;; has not enrolled holds their articles against a byte budget and an
;; obligation count of its own; exhausted, the carried arm is refused by name.
;; A boundary with a carried-source list and no budget carries nothing.
;; USAGE is (octets count) of the carried records already stored for this
;; boundary.  Defers to dev: USAGE as an owner-state counter derived from the
;; carried composites' release evidence at replay, with its preservation
;; theorem; the spike host keeps it (host/native/owner.lisp).

(defun fn-pa-decimal-value (chars acc)
  (declare (xargs :guard t))
  (if (consp chars)
      (if (and (characterp (car chars))
               (char<= #\0 (car chars)) (char<= (car chars) #\9))
          (fn-pa-decimal-value (cdr chars)
                               (+ (* 10 (nfix acc))
                                  (- (char-code (car chars)) 48)))
        nil)
    acc))

(defun fn-pa-budget-slot (slot rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (if (and (equal (fn-cfg-row-b (car rows)) slot)
               (stringp (fn-cfg-row-c (car rows)))
               (consp (coerce (fn-cfg-row-c (car rows)) 'list)))
          (fn-pa-decimal-value (coerce (fn-cfg-row-c (car rows)) 'list) 0)
        (fn-pa-budget-slot slot (cdr rows)))
    nil))

(defun fn-pa-peer-carried-budget (peer peers)
  (declare (xargs :guard t))
  (let ((rows (fn-cfg-rows-with-key peers peer)))
    (list (fn-pa-budget-slot "carried-budget-octets" rows)
          (fn-pa-budget-slot "carried-budget-count" rows))))

(defun fn-pa-carried-budget-decision (budget usage charge)
  (declare (xargs :guard t))
  (let ((octets (and (consp budget) (car budget)))
        (count (and (consp budget) (consp (cdr budget)) (cadr budget)))
        (used-octets (if (and (consp usage) (natp (car usage))) (car usage) 0))
        (used-count (if (and (consp usage) (consp (cdr usage)) (natp (cadr usage)))
                        (cadr usage) 0)))
    (cond ((not (and (natp octets) (natp count)))
           (list :refused :carried-budget-unset))
          ((not (natp charge)) (list :refused :carried-octets-exhausted))
          ((< count (+ 1 used-count)) (list :refused :carried-count-exhausted))
          ((< octets (+ charge used-octets))
           (list :refused :carried-octets-exhausted))
          (t :within))))

; The budget never admits past either bound.
(defthm fn-pa-carried-budget-decision-bounds
  (implies (and (equal (fn-pa-carried-budget-decision budget usage charge) :within)
                (natp (car usage)) (natp (cadr usage)))
           (and (<= (+ charge (car usage)) (car budget))
                (<= (+ 1 (cadr usage)) (cadr budget)))))

;; SPIKE (spike/peering): three outcomes for a signed article that is not
;; verified here, kept apart inside the decision rather than only on a
;; reader badge (review 2026-09-24): no local binding for the author, an
;; unsupported signature profile, and a signature that was checked and
;; failed.  The host names the transit refusal with this class; none of them
;; is `verified' and none is relabelled unsigned (fn-pa-carrier-form never
;; returns :absent for a present field).  OBSERVED is :failed when the host
;; checked the primitives and they refused.  Defers to dev: recording the
;; class in a durable :unverified verdict for held articles, and the keystone
;; that the class is a function of the carrier and the snapshots alone.
(defun fn-pa-signed-refusal-class (received snapshots carried observed)
  (declare (xargs :guard t))
  (let ((parsed (fn-hc-received-plan received))
        (plan (fn-pa-current-plan received snapshots carried)))
    (cond ((equal plan :absent) nil)
          ((equal observed :failed) :signature-failed)
          ((and (consp parsed) (equal (car parsed) :unverified)
                (consp (cdr parsed)) (equal (cadr parsed) :profile))
           :unsupported-profile)
          ((and (consp plan) (equal (car plan) :refused)
                (consp (cdr plan)) (equal (cadr plan) :local-enrollment))
           :no-local-binding)
          ((and (consp plan) (equal (car plan) :refused)) :malformed)
          (t nil))))

(defthm fn-pa-signed-refusal-class-of-absent-is-nil
  (implies (equal (fn-pa-current-plan received snapshots carried) :absent)
           (equal (fn-pa-signed-refusal-class received snapshots carried observed)
                  nil)))

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

; Four outcomes and no fifth: accepted under this node's enrollment, carried
; for the delivering boundary, refused with a reason, or the unsigned arm.
(defthm fn-pa-current-plan-outcomes
  (let ((plan (fn-pa-current-plan received snapshots carried)))
    (or (equal plan :absent)
        (equal (car plan) :ok)
        (equal (car plan) :carried)
        (equal (car plan) :refused)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-pa-current-plan fn-pa-carrier-form)
                                  (fn-pa-carrier-kind fn-hc-received-plan
                                   fn-hl-current-for-principal
                                   fn-hl-current-enrollment fn-pa-carriesp)))))

; The carried arm needs both: the delivering boundary lists the principal,
; and this node has no snapshot of it (never enrolled, never revoked).
(defthm fn-pa-carried-arm-needs-the-list-and-no-local-snapshot
  (let ((plan (fn-pa-current-plan received snapshots carried)))
    (implies (equal (car plan) :carried)
             (and (fn-pa-carriesp (nth 2 plan) carried)
                  (null (fn-hl-current-for-principal (nth 2 plan) snapshots))
                  (equal (nth 1 plan) (nth 1 (fn-pa-carrier-form received)))
                  (equal (nth 2 plan) (nth 2 (fn-pa-carrier-form received))))))
  :hints (("Goal" :in-theory (e/d (fn-pa-current-plan fn-pa-carrier-form)
                                  (fn-pa-carrier-kind fn-hc-received-plan
                                   fn-hl-current-for-principal
                                   fn-hl-current-enrollment fn-pa-carriesp)))))

; Off the carried arm the decision is the D02 one: an enrolled receiver
; accepts exactly as before and an unlisted, unenrolled principal is refused
; with :local-enrollment, whatever list the boundary carries.
(defthm fn-pa-current-plan-off-the-carried-arm-is-the-d02-plan
  (implies (not (equal (car (fn-pa-current-plan received snapshots carried))
                       :carried))
           (equal (fn-pa-current-plan received snapshots carried)
                  (fn-pa-current-plan received snapshots nil)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-pa-current-plan fn-pa-carriesp)
                                  (fn-pa-carrier-form
                                   fn-hl-current-for-principal
                                   fn-hl-current-enrollment)))))

; Every path without a delivering peer passes nil: it never carries.
(defthm fn-pa-current-plan-without-carried-list-never-carries
  (not (equal (car (fn-pa-current-plan received snapshots nil)) :carried))
  :hints (("Goal" :in-theory (e/d (fn-pa-current-plan fn-pa-carriesp)
                                  (fn-pa-carrier-form
                                   fn-hl-current-for-principal
                                   fn-hl-current-enrollment)))))

(defthm fn-pa-carried-event-requires-the-carried-arm
  (implies (fn-pa-carried-event
            sequence txid generation msgid received groups obligation-id
            content-subject release-evidence charge snapshots carried
            clock-observation)
           (equal (car (fn-pa-current-plan received snapshots carried))
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
  (implies (equal (fn-pa-current-plan received snapshots carried) :absent)
           (equal (fn-pa-carrier-kind received) :absent))
  :hints (("Goal" :in-theory (enable fn-pa-current-plan
                                     fn-pa-carrier-form))))

(defthm fn-pa-authorized-event-requires-current-plan-by-definition
  (implies (fn-pa-authorized-event
            sequence txid generation msgid received groups obligation-id
            content-subject release-evidence charge snapshots
            observed-ml-key ed-observation ml-observation clock-observation)
           (equal (car (fn-pa-current-plan received snapshots nil)) :ok))
  :hints (("Goal" :in-theory
           (e/d (fn-pa-authorized-event)
                (fn-pa-current-plan fn-hc-received-plan
                 fn-hsig-authorized-carried-submission-event-base)))))

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
    :control-not-filed :control-malformed :control-signed))

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
           ;; SPIKE: defers the dev proof that the signed record binding
           ;; names the filing group (books/hybrid-store.lisp
           ;; fn-hsig-filed-group-strings); signed control is filed like
           ;; unsigned control, and :control-signed is no longer answered.
           (let ((group (fn-ctl-filing-group (cadr classified))))
             (if (fn-ctl-memberp group domain)
                 (list :file (list (fn-record-string-octets group)))
               (list :refused :control-not-filed))))
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
                    (:d fn-pa-carried-event) (:d fn-pa-carriesp)
                    (:d fn-pa-filing-plan)))
