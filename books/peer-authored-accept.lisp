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
                 (equal groups (fn-hsig-source-filed-groups source fields))
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
;;
;; A signed control article is filed the same way (C3, 2026-09-25): the
;; signed record binding names the filing group, not the source's
;; Newsgroups (books/hybrid-store.lisp `fn-hsig-source-filed-groups', used
;; by every signed constructor and by replay's `fn-hsig-carried-record-
;; metadatap'), so the Store record of a signed cancel lists control.cancel.
;; The binding classifies the signed SOURCE; this plan classifies the
;; received carrier article.  Where the two disagree the constructors return
;; no event and the attempt is refused, never filed elsewhere.
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
                    (equal plan (list :refused :control-not-filed))))))
  :hints (("Goal" :in-theory (disable fn-ctl-classify-octets
                                      fn-pa-carrier-kind
                                      fn-record-string-octets))))

; For a control article, signed or not, the one refusal is the absent
; group: filed exactly when the operator created control.<verb> (or control).
(defthm fn-ctl-control-filing-by-definition
  (implies (equal (car (fn-ctl-classify-octets received)) :control)
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
