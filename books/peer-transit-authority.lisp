; fn: the transit AUTHORITY verdict, on a host path (W5b, lane stx-model-2,
; 2026-09-29).
;
; specs/substrate-transport.md: the statement layer never refuses bytes; it
; refuses authority (section 1, the spine; section 2.3, the typed reasons
; :equivocation and :authority-equivocation, "accepted, authority refused" a
; distinct outcome from refused and from uncertain; section 3, the gate
; fn-pol-admitp over THIS node's lace and THIS node's keyring).  Until this
; book the gate fn-stx-transit-authority-ok (books/stx-policy.lisp) was on
; no host path and walked the lace: linear in the store, once per article.
;
; Here the verdict is decided from the CARRIED state the served path already
; holds -- the store's index (books/stx-index.lisp: bindings, slots, the
; equivocation records and, since W5b, the policy column) and its keyring --
; with no walk of the store and no re-parse of a retained article.  The
; host's transit decision (host/owner-host.lisp fn-owner-transit-decide, the
; native host's decision for IHAVE/TAKETHIS and for BP transit) computes it
; BEFORE the durable intent, beside the byte decision
; fn-peer-decide-transfer-under, which it leaves unchanged; a :want carrying
; an authority refusal is logged "accepted ... authority=NAME", distinct from
; a :refuse and from the persistence outcome.
;
; The group's authority is the explicit local configuration field
; fn-cfg-group-authority, a canonical principal hexadecimal string or empty.
; Posting policy-id is distinct and cannot install an authority. Code29
; set-group-authority is durably journalled; the host uses the connection's
; pinned configuration. Portable multi-node authority remains separate M4.
;
; Keystones: fn-pta-admitted-is-the-gate-over-the-rows (PRF-1023) equates
; :admitted with fn-pol-admitp over the retained rows' lace (the served lace
; of books/stx-lace-rows.lisp) minus the poster's fork, under the carried
; index invariant fn-sn-indexedp and the rows' context invariant;
; fn-pta-decide-admits-iff-every-governed-group-admits (PRF-1024) composes it
; over the host's decision.  The node-lace form of the gate is reached
; through books/stx-lace-rows.lisp fn-stx-lace-of-node-is-the-rows-lace
; (PRF-995) and its correspondence hypothesis.
(in-package "ACL2")
(include-book "stx-lace-rows")
(include-book "stx-policy")
(include-book "peer-inbound")

(local (in-theory (enable fn-pol-invariants-vocabulary)))

; -----------------------------------------------------------------------------
; The closed enumeration

(defconst *fn-pta-verdicts*
  '(:admitted :ungoverned :no-statement :unverified :not-a-post
    :equivocation :authority-equivocation :no-policy :unauthorized))

; -----------------------------------------------------------------------------
; The group's authority, from the configuration in force at GEN

(local (defthm fn-pta-config-hex-is-id-hex
  (implies (fn-cfg-hex-digit-octetsp xs) (fn-id-hex-listp xs))
  :hints (("Goal" :induct (fn-cfg-hex-digit-octetsp xs)
                  :in-theory (enable fn-cfg-hex-digit-octetsp fn-cfg-hex-digit-octetp
                                     fn-id-hex-listp fn-id-hex-digitp)))))
(defun fn-pta-group-authority (v gen name)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable fn-cfg-principal-hexp)))))
  (let* ((e (fn-cfg-group-find (fn-cfg-groups v) name))
         (authority (fn-cfg-group-authority e)))
    (if (and e (fn-cfg-entry-livep e gen) (fn-cfg-principal-hexp authority))
        (fn-id-unhex (fn-record-string-octets authority))
      nil)))

; -----------------------------------------------------------------------------
; The two forks the index already records

; The authority forked at its greatest policy slot: the column's entry
; exists and is flagged, which is the one reason fn-pol-current is nil while
; a candidate exists.
(defun fn-pta-authority-forkedp (index group authority)
  (declare (xargs :guard t))
  (let ((e (cdr (fn-stx-alist-get (cons group authority)
                                  (fn-stx-index-policies index)))))
    (and (consp e) (cdr e) t)))

; The poster forked: a recorded equivocator at this incarnation, or the slot
; of THIS statement already holds a different statement (the merge would
; record the fork, S3-2; the statement carries no authority, section 2.3).
(defun fn-pta-poster-forkedp (index s)
  (declare (xargs :guard (fn-stmt-p s)))
  (or (fn-stx-index-equivocatorp index (fn-stmt-creator s) (fn-stmt-incarnation s))
      (let ((held (fn-stx-index-slot-first index (fn-stx-slot-key s))))
        (and held (not (equal held s)) t))))

; -----------------------------------------------------------------------------
; The verdict for one group

(defun fn-pta-group-verdict (index keyring group authority s)
  (declare (xargs :guard (fn-prin-keyringp keyring)))
  (cond ((not authority) :ungoverned)
        ((not (fn-stmt-p s)) :no-statement)
        ((not (fn-prin-verifiedp s keyring)) :unverified)
        ((not (equal (fn-stmt-kind s) :article)) :not-a-post)
        ((fn-pta-poster-forkedp index s) :equivocation)
        (t (let ((cur (fn-stx-index-policy-current index group authority)))
             (cond ((and (consp cur) (fn-stmt-p cur)
                         ; A frozen index is evidence, not current trust.
                         ; Rotation/revocation must invalidate its authority
                         ; before any later admission can use it.
                         (fn-prin-verifiedp cur keyring))
                    (if (member-equal (fn-stmt-creator s) (fn-pol-authorized-set cur))
                        :admitted
                      :unauthorized))
                   ((fn-pta-authority-forkedp index group authority)
                    :authority-equivocation)
                   (t :no-policy))))))

(defthm fn-pta-group-verdict-is-one-of-the-verdicts
  (member-equal (fn-pta-group-verdict index keyring group authority s)
                *fn-pta-verdicts*))

; -----------------------------------------------------------------------------
; The verdict for an article over its scoped groups (strings, as
; fn-peer-scope-groups answers): :admitted when every governed group admits,
; the first governed group's refusal otherwise, :ungoverned when no scoped
; group has an authority.  The column is keyed by the policy's group name in
; octets (fn-pol-namep), the configuration by the string.

(defun fn-pta-groups-verdict (index keyring v gen names s)
  (declare (xargs :guard (fn-prin-keyringp keyring)))
  (if (atom names)
      :ungoverned
    (let ((authority (fn-pta-group-authority v gen (car names))))
      (if (not (and (stringp (car names)) authority))
          (fn-pta-groups-verdict index keyring v gen (cdr names) s)
        (let ((verdict (fn-pta-group-verdict index keyring
                                             (fn-record-string-octets (car names))
                                             authority s)))
          (if (equal verdict :admitted)
              (let ((rest (fn-pta-groups-verdict index keyring v gen (cdr names) s)))
                (if (equal rest :ungoverned) :admitted rest))
            verdict))))))

; Its specification, member by member.
(defun fn-pta-some-governed (v gen names)
  (declare (xargs :guard t))
  (if (atom names)
      nil
    (or (and (stringp (car names)) (fn-pta-group-authority v gen (car names)) t)
        (fn-pta-some-governed v gen (cdr names)))))

(defun fn-pta-all-governed-admit (index keyring v gen names s)
  (declare (xargs :guard (fn-prin-keyringp keyring)))
  (if (atom names)
      t
    (let ((authority (fn-pta-group-authority v gen (car names))))
      (and (or (not (and (stringp (car names)) authority))
               (equal (fn-pta-group-verdict index keyring
                                            (fn-record-string-octets (car names))
                                            authority s)
                      :admitted))
           (fn-pta-all-governed-admit index keyring v gen (cdr names) s)))))

; A governed group's verdict is never :ungoverned, so the article-level
; verdict is :ungoverned exactly when no scoped group is governed, and then
; every governed group admits vacuously.
(local (defthm fn-pta-governed-verdict-is-not-ungoverned
  (implies authority
           (not (equal (fn-pta-group-verdict index keyring group authority s) :ungoverned)))
  :hints (("Goal" :in-theory (e/d (fn-pta-group-verdict)
                                  (fn-stmt-p fn-prin-verifiedp fn-pta-poster-forkedp
                                   fn-stx-index-policy-current fn-pol-authorized-set
                                   fn-pta-authority-forkedp))))))
(local (defthm fn-pta-groups-verdict-is-ungoverned-iff
  (iff (equal (fn-pta-groups-verdict index keyring v gen names s) :ungoverned)
       (not (fn-pta-some-governed v gen names)))
  :hints (("Goal" :in-theory (disable fn-pta-group-verdict fn-pta-group-authority
                                      fn-record-string-octets)))))
(local (defthm fn-pta-no-governed-admits-vacuously
  (implies (not (fn-pta-some-governed v gen names))
           (fn-pta-all-governed-admit index keyring v gen names s))
  :hints (("Goal" :in-theory (disable fn-pta-group-verdict fn-pta-group-authority
                                      fn-record-string-octets)))))
(defthm fn-pta-groups-verdict-is-admitted-iff
  (iff (equal (fn-pta-groups-verdict index keyring v gen names s) :admitted)
       (and (fn-pta-some-governed v gen names)
            (fn-pta-all-governed-admit index keyring v gen names s)))
  :hints (("Goal" :induct (fn-pta-groups-verdict index keyring v gen names s)
           :in-theory (disable fn-pta-group-verdict fn-pta-group-authority
                               fn-record-string-octets))))

; -----------------------------------------------------------------------------
; The host's decision with its authority verdict

; The byte decision is fn-peer-decide-transfer-under's, unchanged.  On a
; :want the verdict is computed from the carried index and keyring over the
; statement the RELAYED octets carry (the octets the row will hold) and the
; scoped groups fn-peer-injection-arguments derives; on any other decision
; there is no verdict (:none).  Nothing here touches the node or the files:
; the durable intent comes after.
(defun fn-pta-decide (index keyring v gen node cfg peer msgid octets clock id
                            subject limits)
  (declare (xargs :guard (and (fn-node-statep node) (fn-prin-keyringp keyring))
                  :verify-guards nil))
  (let ((d (fn-peer-decide-transfer-under node cfg peer msgid octets clock id
                                          subject limits)))
    (if (not (equal (fn-peer-decision-kind d) :want))
        (mv d :none)
      (let* ((a (fn-stx-parse (fn-peer-relayed-octets cfg peer octets)))
             (s (if a (fn-stx-statement-of a) nil))
             (groups (nth 3 (fn-peer-injection-arguments node cfg peer msgid octets
                                                         0 id subject clock))))
        (mv d (fn-pta-groups-verdict index keyring v gen groups s))))))

(defthm fn-pta-decide-keeps-the-byte-decision-by-definition
  (equal (mv-nth 0 (fn-pta-decide index keyring v gen node cfg peer msgid octets
                                  clock id subject limits))
         (fn-peer-decide-transfer-under node cfg peer msgid octets clock id
                                        subject limits)))

(defthm fn-pta-verdict-only-on-want-by-definition
  (implies (not (equal (fn-peer-decision-kind
                        (fn-peer-decide-transfer-under node cfg peer msgid octets
                                                       clock id subject limits))
                       :want))
           (equal (mv-nth 1 (fn-pta-decide index keyring v gen node cfg peer msgid
                                           octets clock id subject limits))
                  :none)))

(in-theory (disable (:d fn-pta-decide)))

; -----------------------------------------------------------------------------
; KEYSTONE (PRF-1023): the served verdict is the policy gate over the rows'
; lace.  Under the carried index invariant (fn-sn-indexedp: the index is the
; fold of the indexed rows' contexts) and the rows' context invariant, the
; store's index is the wire index of the rows' articles read through the
; arena (store-intern.lisp fn-rows-index-is-the-wire-index) and the rows'
; lace is their wire lace (stx-lace-rows.lisp); over one article list the
; three column agreements of books/stx-index.lisp (policy, equivocators,
; slots) put the verdict and the gate on the same lace.

(local (defthm fn-pta-sn-index-is-the-wire-index
  (implies (and (fn-sn-indexedp st)
                (fn-rows-contexts-okp (fn-sn-indexed-rows st) keyring generation fn-arena))
           (equal (fn-sn-index st)
                  (fn-stx-index-of-store
                   (fn-rows-articles-newest-first (fn-sn-indexed-rows st) fn-arena)
                   keyring)))
  :rule-classes ((:rewrite :match-free :all))
  :hints (("Goal" :use ((:instance fn-rows-index-is-the-wire-index
                                   (rows (fn-sn-indexed-rows st))))
           :in-theory (e/d (fn-sn-indexedp)
                           (fn-sn-statep fn-sn-index-of-rows fn-sn-indexed-rows
                            fn-rows-contexts-okp fn-rows-articles-newest-first
                            fn-stx-index-of-store fn-rows-index-is-the-wire-index))))))

(defthm fn-pta-admitted-is-the-gate-over-the-rows
  (implies (and (fn-sn-indexedp st)
                (fn-rows-contexts-okp (fn-sn-indexed-rows st) keyring generation fn-arena))
           (let ((lace (fn-sn-lace-of-rows (fn-sn-indexed-rows st))))
             (iff (equal (fn-pta-group-verdict (fn-sn-index st) keyring group authority s)
                         :admitted)
                  (and authority
                       (fn-pol-admitp lace keyring group authority s)
                       (not (fn-lace-equivocatorp lace (fn-stmt-creator s)
                                                  (fn-stmt-incarnation s)))
                       (not (let ((held (fn-stx-lace-slot-first lace (fn-stx-slot-key s))))
                              (and held (not (equal held s)))))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-pol-current-is-stmt-or-nil
                            (lace (fn-stx-lace-of-store
                                   (fn-rows-articles-newest-first (fn-sn-indexed-rows st) fn-arena)
                                   keyring)))
                 (:instance fn-pol-current-is-candidate-in-lace
                            (lace (fn-stx-lace-of-store
                                   (fn-rows-articles-newest-first (fn-sn-indexed-rows st) fn-arena)
                                   keyring))))
           :in-theory (e/d (fn-pta-group-verdict fn-pta-poster-forkedp
                            fn-pol-admitp fn-pol-authorizedp fn-pol-candidatep)
                           (fn-sn-statep fn-sn-index-of-rows fn-sn-indexed-rows
                            fn-rows-contexts-okp fn-rows-articles-newest-first
                            fn-stx-index-of-store fn-stx-lace-of-store fn-sn-lace-of-rows
                            fn-pol-current fn-pol-authorized-set fn-stmt-p
                            fn-prin-verifiedp fn-stx-slot-key fn-stx-lace-slot-first
                            (:d fn-lace-equivocatorp) fn-stx-index-policy-current
                            fn-stx-index-equivocatorp fn-stx-index-slot-first
                            fn-pta-authority-forkedp)))))

; -----------------------------------------------------------------------------
; KEYSTONE (PRF-1024): the host's decision admits an article's authority iff
; some scoped group is governed and every governed scoped group's gate opens
; over the rows' lace (each by fn-pta-admitted-is-the-gate-over-the-rows).
; The byte decision is unchanged (fn-pta-decide-keeps-the-byte-decision-by-
; definition); the verdict exists only on :want.

(defthm fn-pta-decide-admits-iff-every-governed-group-admits
  (implies (equal (fn-peer-decision-kind
                   (fn-peer-decide-transfer-under node cfg peer msgid octets clock id
                                                  subject limits))
                  :want)
           (let* ((a (fn-stx-parse (fn-peer-relayed-octets cfg peer octets)))
                  (s (if a (fn-stx-statement-of a) nil))
                  (groups (nth 3 (fn-peer-injection-arguments node cfg peer msgid octets
                                                              0 id subject clock))))
             (iff (equal (mv-nth 1 (fn-pta-decide index keyring v gen node cfg peer msgid
                                                  octets clock id subject limits))
                         :admitted)
                  (and (fn-pta-some-governed v gen groups)
                       (fn-pta-all-governed-admit index keyring v gen groups s)))))
  :hints (("Goal" :in-theory (e/d ((:d fn-pta-decide))
                                  (fn-peer-decide-transfer-under fn-peer-injection-arguments
                                   fn-peer-relayed-octets fn-stx-parse fn-stx-statement-of
                                   fn-pta-groups-verdict fn-pta-some-governed
                                   fn-pta-all-governed-admit fn-pta-group-verdict)))))

(in-theory (disable (:d fn-pta-group-authority) (:d fn-pta-authority-forkedp)
                    (:d fn-pta-poster-forkedp) (:d fn-pta-group-verdict)
                    (:d fn-pta-groups-verdict)))
