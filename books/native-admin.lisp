; fn: bounded native administrative configuration plan.
;
; This is deliberately a narrow command boundary.  It selects group, capacity
; and peer deltas that the store already owns, and it never owns a second
; group/peer table, capacity rule, record encoder, or replay algorithm.
; Raw Lisp supplies bounded argv octets and physical observations; the record
; remains `fn-store-cfg-reconfigure' and a proposed history is checked here by
; the same logical replay/open entry used at ordinary recovery.

(in-package "ACL2")
(include-book "node-config")
(include-book "store-observed")
(include-book "config-observed")
(include-book "byte-store-txn-name")
(include-book "journal-publish")
(include-book "native-config")
(include-book "peer-config")
(include-book "identity")
(include-book "bp-eid-shape")
; The argv, decimal, result and config-name vocabulary, and the peer and
; bp-boundary parsers with the `peer list' codec, are in
; books/native-admin-shape.lisp and books/native-admin-peer.lisp
; (planning/audit-2026-09-25-twins-fanin.md packet 4).  This book keeps the
; group-name rules, the plan, its deltas and the publication decision.
(include-book "native-admin-shape")
(include-book "native-admin-peer")
; `bp-route add|remove', the BP route table (books/bp-route.lisp).
(include-book "bp-route")

;; RFC 5536 s3.1.4 reserved names, a rule about CREATING a group (the
;; RFC requirement): "Groups whose first (or only) <component> is
;; \"example\"" and "The group \"poster\"" MUST NOT be used as the name of a
;; newsgroup.  Syntax is `fn-record-group-namep' (books/records-shape.lisp)
;; and is not repeated here; a store that already carries such a name is
;; still replayed, served and retired, since the rule governs creation only.
;; The comparison folds ASCII case (a stronger fn guarantee): s3.1.4 notes
;; that some systems match names case-insensitively, and s3.2.6 lets agents
;; recognise "Poster" as the keyword, so "Example.a" and "POSTER" are
;; refused too.
(defconst *fn-native-admin-reserved-example* '(101 120 97 109 112 108 101))
(defconst *fn-native-admin-reserved-poster* '(112 111 115 116 101 114))

(defun fn-native-admin-fold-octets (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (cons (if (and (integerp (car xs)) (<= 65 (car xs)) (<= (car xs) 90))
                (+ 32 (car xs))
              (car xs))
            (fn-native-admin-fold-octets (cdr xs)))
    nil))

(defun fn-native-admin-group-name-reservedp (text)
  (declare (xargs :guard t))
  (let ((xs (fn-native-admin-fold-octets (fn-record-string-octets text))))
    (or (equal (fn-record-group-first-component xs)
               *fn-native-admin-reserved-example*)
        (equal xs *fn-native-admin-reserved-poster*))))

(defun fn-native-admin-some-group-name-reservedp (names)
  (declare (xargs :guard t))
  (if (consp names)
      (or (fn-native-admin-group-name-reservedp (car names))
          (fn-native-admin-some-group-name-reservedp (cdr names)))
    nil))

;; RFC 5536 s3.1.4 specific-purpose names: these "MUST NOT be used for the
;; names of normal newsgroups" and "MAY be used for their specific purpose
;; or by local agreement".  The cases are patterns, not five strings: a
;; first (or only) component "to" or "control"; any component "all" or
;; "ctl"; exactly "junk".  Case is folded as for the reserved names above.
;;
;; fn's profile is an explicit local agreement: `group create' admits such
;; a name, so an operator can stand up e.g. "to.peer" or "control.cancel"
;; for a site convention.  It is not an ordinary, globally compatible group
;; name, and it confers nothing: fn has no code path that reads a group's
;; name as control, point-to-point, wildcard or junk authority, and the
;; plan for creating one is exactly the plan any other creatable name gets
;; (`fn-native-admin-plan-create-ignores-special-purpose', below).  This
;; recognizer classifies; nothing grants or refuses on it.
(defconst *fn-native-admin-special-to* '(116 111))
(defconst *fn-native-admin-special-control* '(99 111 110 116 114 111 108))
(defconst *fn-native-admin-special-all* '(97 108 108))
(defconst *fn-native-admin-special-ctl* '(99 116 108))
(defconst *fn-native-admin-special-junk* '(106 117 110 107))

;; The dot-separated components of XS, in order ("a.b" is ("a" "b")).
(defun fn-native-admin-name-components (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (let ((rest (fn-native-admin-name-components (cdr xs))))
        (if (equal (car xs) 46)
            (cons nil rest)
          (cons (cons (car xs) (car rest)) (cdr rest))))
    (list nil)))

(defun fn-native-admin-group-name-special-purposep (text)
  (declare (xargs :guard t))
  (let* ((xs (fn-native-admin-fold-octets (fn-record-string-octets text)))
         (components (fn-native-admin-name-components xs)))
    (or (equal (car components) *fn-native-admin-special-to*)
        (equal (car components) *fn-native-admin-special-control*)
        (if (member-equal *fn-native-admin-special-all* components) t nil)
        (if (member-equal *fn-native-admin-special-ctl* components) t nil)
        (equal xs *fn-native-admin-special-junk*))))

;; The predicate group creation applies: `group create' below, the operator's
;; `init' (`fn-nop-parse-init', books/native-operator.lisp) and the initial
;; configuration record (`fn-cfg-host-initial-octets', host/config-host.lisp).
(defun fn-native-admin-group-name-creatablep (text)
  (declare (xargs :guard t))
  (and (fn-record-group-namep text)
       (not (fn-native-admin-group-name-reservedp text))))

(defun fn-native-admin-plan (argv)
  "Normalize an administrative request; configuration admission stays in the store core."
  (declare (xargs :guard t))
  (if (or (not (fn-native-admin-argvp argv))
          (< *fn-native-admin-max-arguments* (len argv)))
      (fn-native-admin-result :refused :argv nil nil nil nil nil)
    (let ((words (fn-native-admin-words argv)))
      (cond
       ((and (equal (len words) 3)
             (equal (car words) "group")
             (equal (cadr words) "create")
             (fn-native-admin-group-name-reservedp (caddr words)))
        (fn-native-admin-result :refused :reserved-group-name nil nil 0 nil nil))
       ((and (equal (len words) 3)
             (equal (car words) "group")
             (equal (cadr words) "create")
             (fn-record-group-namep (caddr words)))
        (fn-native-admin-result :accepted nil :create-group (caddr argv) 0 nil nil))
       ((and (equal (len words) 3)
             (equal (car words) "group")
             (equal (cadr words) "retire")
             (fn-record-group-namep (caddr words)))
        (fn-native-admin-result :accepted nil :remove-group (caddr argv) 0 nil nil))
       ((and (equal (len words) 2)
             (equal (car words) "capacity")
             (fn-native-admin-decimalp (cadr words)))
        (fn-native-admin-result :accepted nil :set-capacity nil
                                (fn-native-admin-decimal-value
                                 (coerce (cadr words) 'list)) nil nil))
       ; The node's own RFC 5537 section 3.2 <path-identity>.  It is the one
       ; policy slot peering needs: `fn-peer-local-identity' (books/peer-inbound)
       ; reads it, and while it is unset a node cannot recognise its own name
       ; in a Path, so section 3.5 loop suppression cannot fire (measured on
       ; the native v0 matrix, 2026-09-22: V0-TRANSIT-LOOP accepted 235).  The
       ; value must itself be a <path-identity>; the same recognizer admits a
       ; peer's identity in `fn-native-admin-peer-plan'.  The slot is a durable
       ; `:set-policy' configuration record, not a configuration-file key, for
       ; the reason packaging/fn.toml.example gives for served groups.
       ((and (equal (len words) 4)
             (equal (car words) "policy")
             (equal (cadr words) "set")
             (equal (caddr words) "path-identity")
             (fn-path-identityp (cadddr argv)))
        (fn-native-admin-result :accepted nil :set-policy (caddr argv) 0 nil
                                (cadddr argv)))
       ; The served POST posting policy (books/login-binding.lisp):
       ; `bound-logins' refuses a bound login's article unless it is signed
       ; by the login's bound principal; `open' is the default behaviour.
       ; A durable `:set-policy' record like path-identity, applied live.
       ((and (equal (len words) 4)
             (equal (car words) "policy")
             (equal (cadr words) "set")
             (equal (caddr words) "posting-policy")
             (member-equal (cadddr words) '("bound-logins" "open")))
        (fn-native-admin-result :accepted nil :set-policy (caddr argv) 0 nil
                                (cadddr argv)))
       ((and (consp words) (equal (car words) "policy"))
        (fn-native-admin-result :refused :policy nil nil 0 nil nil))
       ((and (consp words) (equal (car words) "peer"))
        (cond
         ; `peer list' is the table's read side.  It carries no name, no
         ; capacity and no record: it is a query over the durable
         ; configuration, and `fn-native-admin-result-queryp' below is what
         ; keeps its executor off the writer lock and off the owner mutex.
         ((and (equal (len words) 2) (equal (cadr words) "list"))
          (fn-native-admin-result :accepted nil :list-peers nil 0 nil nil))
         ((and (equal (len words) 3)
               (equal (cadr words) "remove")
               (stringp (caddr words))
               (not (equal (caddr words) "")))
          (fn-native-admin-result :accepted nil :remove-peer (caddr argv) 0 nil nil))
         (t (fn-native-admin-peer-plan words))))
       ((and (consp words) (equal (car words) "bp-boundary"))
        (fn-native-admin-bp-boundary-plan words))
       ((and (consp words) (equal (car words) "bp-route"))
        (fn-bprt-admin-plan words))
       (t (fn-native-admin-result :refused :syntax nil nil nil nil nil))))))

; The delta list the LIVE owner stages for an accepted plan.
;
; The live arm (host/native-admin-host.lisp
; `fn-native-admin-host-owner-reconfigure') hands this list to
; `fn-owner-reconfigure-deltas'.  A plan carries its labels as the argv
; OCTETS the operator typed (the offline executor, `fn-store-cfg-reconfigure'
; and its siblings in host/store-node-host.lisp, takes octets and converts
; them itself); a configuration delta's labels are STRINGS (`fn-cfg-labelp',
; books/config.lisp).  The live arm used to pass the octets straight into
; `fn-cfg-create-group', `fn-cfg-remove-group' and `fn-cfg-remove-peer-delta',
; which built deltas `fn-cfg-deltap' refuses, so every live `group create',
; `group retire' and `peer remove' was refused `:malformed-delta' by
; `fn-ocfg-reconfig-refusal' (measured 2026-09-22, the ground witness in
; tests/acl2/native-admin-tests.lisp).  The conversion is the same
; `fn-record-octets-string' the plan's own recognizers were applied to, so
; the label a delta carries is exactly the word the plan admitted.
(defun fn-native-admin-plan-deltas (plan)
  (declare (xargs :guard t))
  (if (not (equal (fn-native-admin-result-status plan) :accepted))
      nil
    (let ((kind (fn-native-admin-result-kind plan))
          (name (fn-record-octets-string (fn-native-admin-result-name plan))))
      (cond ((equal kind :set-peer)
             (list (fn-native-admin-set-peer-delta plan)))
            ((member-equal kind '(:set-bp-boundary :set-bp-route))
             (list (fn-cfg-set-peer name
                                    (fn-native-admin-result-value plan))))
            ((member-equal kind '(:remove-peer :remove-bp-route))
             (list (fn-cfg-remove-peer-delta name)))
            ((equal kind :create-group)
             (list (fn-cfg-create-group name *fn-cfg-default-policy-id*)))
            ((equal kind :remove-group)
             (list (fn-cfg-remove-group name)))
            ((equal kind :set-capacity)
             (list (fn-cfg-set-capacity (fn-native-admin-result-capacity plan))))
            ((equal kind :set-policy)
             (list (fn-cfg-set-policy
                    name
                    (fn-record-octets-string (fn-native-admin-result-value plan)))))
            (t nil)))))

(encapsulate ()
(local (defthm kind-of-result
  (equal (fn-native-admin-result-kind (fn-native-admin-result s r k n c p v)) k)))
(local (defthm status-of-result
  (equal (fn-native-admin-result-status (fn-native-admin-result s r k n c p v)) s)))
(local (defthm name-of-result
  (equal (fn-native-admin-result-name (fn-native-admin-result s r k n c p v)) n)))
(local (in-theory (disable fn-native-admin-result fn-native-admin-result-kind
                           fn-native-admin-result-status fn-native-admin-result-name)))
; The bp-boundary arm, closed: an accepted boundary plan is a boundary.
; Opening fn-native-admin-bp-boundary-plan inside the theorem below cost
; 5.1 s of its 5.1 s (hbox, 2 jobs).
(local (defthm accepted-bp-boundary-plan-is-a-boundary
  (implies (equal (fn-native-admin-result-status
                   (fn-native-admin-bp-boundary-plan words))
                  :accepted)
           (equal (fn-native-admin-result-kind
                   (fn-native-admin-bp-boundary-plan words))
                  :set-bp-boundary))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-native-admin-bp-boundary-plan
                               fn-native-admin-bp-with-contact
                               fn-native-admin-bp-with-receipt-options
                               fn-native-admin-bp-boundary-base-plan
                               kind-of-result status-of-result
                               (:executable-counterpart equal))))))
(defthm fn-native-admin-plan-group-name-is-a-group-name
  (implies (and (equal (fn-native-admin-result-status (fn-native-admin-plan argv)) :accepted)
                (member-equal (fn-native-admin-result-kind (fn-native-admin-plan argv))
                              '(:create-group :remove-group)))
           (fn-record-group-namep
            (fn-record-octets-string (fn-native-admin-result-name (fn-native-admin-plan argv)))))
  :hints (("Goal" :in-theory (e/d (fn-native-admin-plan fn-native-admin-words)
                                  (fn-native-admin-peer-plan fn-record-group-namep
                                   fn-path-identityp fn-native-admin-decimalp
                                   fn-native-admin-decimal-value fn-native-admin-argvp
                                   fn-native-admin-bp-boundary-split
                                   fn-native-admin-bp-boundary-rows
                                   fn-native-admin-bp-boundary-plan))
           :use ((:instance fn-native-admin-peer-plan-kind
                            (words (fn-native-admin-words argv)))
                 (:instance accepted-bp-boundary-plan-is-a-boundary
                            (words (fn-native-admin-words argv)))))))
)

; KEYSTONE.  Every delta the live arm stages for an accepted `group create'
; or `group retire' is a typed delta: its name label is the admitted group
; name as a STRING, so `fn-ocfg-reconfig-refusal' cannot refuse it
; `:malformed-delta' for the octet/string confusion described above.  The
; teeth, including the old octet delta that `fn-cfg-deltap' refuses, are in
; tests/acl2/native-admin-tests.lisp.  (`peer remove' and `policy set' carry
; labels the plan bounds at 512 octets and the configuration at 256, so a
; long one is a well-typed refusal of the configuration book, not a type
; confusion; they are witnessed on ground values, not in this theorem.)
(encapsulate ()
(local (defthm group-name-is-label
  (implies (fn-record-group-namep s) (fn-cfg-labelp s))
  :hints (("Goal" :use fn-cfg-labelp-of-record-group-name
                  :in-theory (disable fn-record-group-namep fn-cfg-labelp)))))
(local (defthm group-deltas-typed
  (implies (fn-record-group-namep s)
           (and (fn-cfg-delta-listp (list (fn-cfg-create-group s *fn-cfg-default-policy-id*)))
                (fn-cfg-delta-listp (list (fn-cfg-remove-group s)))))
  :hints (("Goal" :in-theory (e/d (fn-cfg-deltap fn-cfg-delta-listp
                                   fn-cfg-create-group fn-cfg-remove-group)
                                  (fn-record-group-namep fn-cfg-labelp))))))
(defthm fn-native-admin-live-group-delta-is-a-typed-delta
  (implies (and (equal (fn-native-admin-result-status (fn-native-admin-plan argv)) :accepted)
                (member-equal (fn-native-admin-result-kind (fn-native-admin-plan argv))
                              '(:create-group :remove-group)))
           (and (consp (fn-native-admin-plan-deltas (fn-native-admin-plan argv)))
                (fn-cfg-delta-listp (fn-native-admin-plan-deltas (fn-native-admin-plan argv)))))
  :hints (("Goal" :in-theory (e/d (fn-native-admin-plan-deltas)
                                  (fn-native-admin-plan fn-record-group-namep
                                   fn-cfg-delta-listp fn-cfg-create-group fn-cfg-remove-group
                                   fn-record-octets-string))
           :use (fn-native-admin-plan-group-name-is-a-group-name
                 (:instance group-deltas-typed
                            (s (fn-record-octets-string
                                (fn-native-admin-result-name (fn-native-admin-plan argv)))))))))
)

(defun fn-native-admin-result-queryp (result)
  "Does this accepted plan only read the durable configuration?

A query publishes no configuration record, so its executor opens the store
without the exclusive writer lock and never reaches the live owner's
serialized reconfiguration.  The host asks this question rather than deciding
for itself which kinds are safe to read: the plan kinds are ACL2's."
  (declare (xargs :guard t))
  (and (equal (fn-native-admin-result-status result) :accepted)
       (equal (fn-native-admin-result-kind result) :list-peers)))

(encapsulate ()
(local (in-theory (disable fn-bp-eid-shapep)))
(local (defthm plan-of-set-bp-boundary
  (implies (and (equal (fn-native-admin-result-status (fn-native-admin-plan argv))
                       :accepted)
                (equal (fn-native-admin-result-kind (fn-native-admin-plan argv))
                       :set-bp-boundary))
           (equal (fn-native-admin-plan argv)
                  (fn-native-admin-bp-boundary-plan (fn-native-admin-words argv))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-native-admin-plan)
                                  (fn-native-admin-peer-plan fn-native-admin-bp-boundary-plan
                                   fn-record-group-namep fn-native-admin-decimalp
                                   fn-native-admin-decimal-value fn-native-admin-argvp
                                   fn-native-admin-words))
           :use ((:instance fn-native-admin-peer-plan-kind
                            (words (fn-native-admin-words argv))))))))
(local (defthm delta-rows-of-set-bp-boundary
  (implies (and (equal (fn-native-admin-result-status plan) :accepted)
                (equal (fn-native-admin-result-kind plan) :set-bp-boundary))
           (equal (fn-cfg-delta-rows (car (fn-native-admin-plan-deltas plan)))
                  (fn-native-admin-result-value plan)))
  :hints (("Goal" :in-theory (e/d (fn-cfg-set-peer)
                                  (fn-native-admin-result-value
                                   fn-native-admin-result-status
                                   fn-native-admin-result-kind))))))

; KEYSTONE.  `peer list' reads back exactly the rows `bp-boundary add'
; stages: the D23 words of the line rendered from the boundary's group decode
; to its carried sources and release issuers, row for row, with no
; hypothesis on the rows (formerly the hypothesis `fn-native-admin-peer-
; extra-cleanp', now discharged by `fn-native-admin-bp-boundary-plan-rows-
; render-clean').  The subject is the delta of `fn-native-admin-plan', which
; host/native-admin-host.lisp `fn-native-admin-host-plan' calls; the delta is
; `fn-cfg-set-peer' of exactly these rows, the boundary's whole group.
; Covered scope: a group written by an accepted `bp-boundary add'.  A group
; written before `fn-bp-eid-shapep' was enforced, or by another writer, is
; covered only by `fn-native-admin-peer-extra-decode-of-clean-rows' and its
; hypothesis.
(defthm fn-native-admin-peer-extra-decode-lists-exactly-the-rows
  (let* ((plan (fn-native-admin-plan argv))
         (rows (fn-cfg-delta-rows (car (fn-native-admin-plan-deltas plan)))))
    (implies (and (equal (fn-native-admin-result-status plan) :accepted)
                  (equal (fn-native-admin-result-kind plan) :set-bp-boundary))
             (equal (fn-native-admin-peer-extra-decode
                     (append (fn-native-admin-peer-extra-octets rows) (list 10)))
                    (list (fn-native-admin-peer-label-octets-list
                           (fn-native-admin-peer-slot-values rows "carries-principal"))
                          (fn-native-admin-peer-label-octets-list
                           (fn-native-admin-peer-slot-values rows "bp-boundary-carries"))
                          (fn-native-admin-peer-label-octets-list
                           (fn-native-admin-peer-slot-values rows "bp-boundary-releases-for"))
                          (list 10)))))
  :hints (("Goal" :in-theory (disable fn-native-admin-plan fn-native-admin-plan-deltas
                                      fn-native-admin-bp-boundary-plan
                                      fn-native-admin-peer-extra-decode
                                      fn-native-admin-peer-extra-octets
                                      fn-native-admin-peer-extra-cleanp
                                      fn-native-admin-peer-label-octets-list
                                      fn-native-admin-peer-slot-values
                                      fn-native-admin-result-value
                                      fn-native-admin-result-status
                                      fn-native-admin-result-kind)
                  :use ((:instance plan-of-set-bp-boundary)
                        (:instance fn-native-admin-bp-boundary-plan-rows-render-clean
                                   (words (fn-native-admin-words argv)))
                        (:instance fn-native-admin-peer-extra-decode-of-clean-rows
                                   (rows (fn-native-admin-result-value
                                          (fn-native-admin-plan argv))))))))
)

; The physical adapter decodes exact framed records at its byte boundary, then
; calls this total logical function over those typed values.  A candidate that
; cannot replay into the same recovering state ordinary startup requires is a
; refusal before a namespace name is published.
(defun fn-native-admin-candidate-open-result (records frontier config-records)
  (declare (xargs :guard t))
  (let ((configuration (fn-cnode-config-replay config-records)))
    (if (not (equal (fn-replay-result-kind configuration) :ok))
        (list :refused :configuration)
      (let* ((replayed (fn-cpr-replay config-records records))
             (opened (fn-cpo-open-observed config-records frontier records)))
        (if (and (equal (fn-replay-result-kind replayed) :ok)
                 (fn-sn-open-okp opened)
                 (equal (fn-sf-phase (fn-sn-files (fn-sn-open-state opened)))
                        :recovering))
            (list :accepted (fn-replay-result-node replayed))
          (list :refused :history))))))

(defun fn-native-admin-candidate-openp (records frontier config-records)
  (declare (xargs :guard t))
  (equal (car (fn-native-admin-candidate-open-result records frontier config-records))
         :accepted))

(defun fn-native-admin-clock-result (status reason stamp)
  (declare (xargs :guard t))
  (list status reason stamp))
(defun fn-native-admin-clock-status (result)
  (declare (xargs :guard t)) (fn-ag-car result))
(defun fn-native-admin-clock-stamp (result)
  (declare (xargs :guard t)) (fn-ag-car (fn-ag-cdr (fn-ag-cdr result))))

(defun fn-native-admin-clock-observation (monotonic wall)
  "The configuration-record codec, not raw Lisp, decides whether the two host
clock observations fit its schema-0 representation."
  (declare (xargs :guard t))
  (let ((stamp (fn-clock-observation monotonic wall 0 t)))
    (if (fn-cfg-stampp stamp)
        (fn-native-admin-clock-result :accepted nil stamp)
      (fn-native-admin-clock-result :refused :clock-unrepresentable nil))))

(defun fn-native-admin-publication-result (status reason generation name publication)
  (declare (xargs :guard t))
  (list status reason generation name publication))
(defun fn-native-admin-publication-status (result)
  (declare (xargs :guard t)) (fn-ag-car result))
(defun fn-native-admin-publication-reason (result)
  (declare (xargs :guard t)) (fn-ag-car (fn-ag-cdr result)))
(defun fn-native-admin-publication-generation (result)
  (declare (xargs :guard t)) (fn-ag-car (fn-ag-cdr (fn-ag-cdr result))))
(defun fn-native-admin-publication-name (result)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr result)))))
(defun fn-native-admin-publication-jpub (result)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr result))))))

(defun fn-native-admin-name-memberp (name names)
  (declare (xargs :guard t))
  (if (consp names)
      (or (equal name (car names)) (fn-native-admin-name-memberp name (cdr names)))
    nil))

(defun fn-native-admin-append-record (records record)
  "Total, one-record extension for the candidate replay.  The byte decoder
supplies proper record lists, but this boundary remains executable for a
malformed logical value and therefore does not make an unproved LISTP claim
to Common Lisp's guarded APPEND."
  (declare (xargs :guard t))
  (if (consp records)
      (cons (car records) (fn-native-admin-append-record (cdr records) record))
    (list record)))

(defun fn-native-admin-publication-authorize
    (records frontier config-records record lock-owned observed-names)
  "Authorize this exact final configuration name once.  LOCK-OWNED and
OBSERVED-NAMES are raw physical observations.  ACL2 binds them to the record's
generation, the candidate replay/open check, the fixed filename, and the
shared immutable publication state before raw Lisp may execute an I/O action."
  (declare (xargs :guard t))
  (if (not lock-owned)
      (fn-native-admin-publication-result :refused :lock nil nil nil)
    (let ((replayed (fn-cnode-config-replay config-records)))
      (if (not (equal (fn-replay-result-kind replayed) :ok))
          (fn-native-admin-publication-result :refused :configuration nil nil nil)
        (let* ((current (fn-cnode-config (fn-replay-result-node replayed)))
               ; Replay success supplies a configuration generation.  NFIX
               ; keeps this public executable boundary total for malformed
               ; logical inputs without changing a valid replay's generation.
               (generation (+ 1 (nfix (fn-cfg-generation current))))
               (name (fn-native-admin-config-name generation))
               (candidate (fn-native-admin-candidate-openp
                           records frontier
                           (fn-native-admin-append-record config-records record))))
          (cond ((not (fn-cfg-recordp record))
                 (fn-native-admin-publication-result :refused :record nil nil nil))
                ((or (not (equal (fn-cfg-record-sequence record)
                                 (fn-cfg-generation current)))
                     (not (equal (fn-cfg-record-generation record) generation)))
                 (fn-native-admin-publication-result :refused :generation nil nil nil))
                ((null name)
                 (fn-native-admin-publication-result :refused :generation-name nil nil nil))
                ((fn-native-admin-name-memberp name observed-names)
                 (fn-native-admin-publication-result :refused :occupied nil nil nil))
                ((not candidate)
                 (fn-native-admin-publication-result :refused :candidate nil nil nil))
                (t (fn-native-admin-publication-result
                    :accepted nil generation name (fn-jpub-initial t)))))))))

;; KEYSTONE.  An administrative configuration record is published only by a
;; process that observed its own exclusive writer lock, on every arm of the
;; authorization, not only its first branch.  The host subject is
;; `fn-store-cfg-native-admin-authorize' (host/store-node-host.lisp), a
;; program-mode byte wrapper that either refuses `:decode' with no
;; publication state or returns this function's result with LOCK-OWNED
;; unchanged; host/native/admin.lisp `fnn-admin-authorize' calls it with
;; `fnn-admin-lock-observation' (the store is writable and its lock
;; descriptor is live), for both the offline executor (`fnn-admin-execute')
;; and the live owner's arm (`fnn-owner-live-admin-serialized').  Raw Lisp
;; mutates only through `fnn-admin-publish', which hands this result's jpub to
;; `fnn-immutable-publish-effect'; that executor's first action is gated on
;; `fn-jpub-host-authorized-initialp' (host/native/immutable-publish.lisp),
;; which holds only of a non-NIL jpub.  So the stage, link and barrier writes
;; are reachable only under LOCK-OWNED.  A second process over a live owner's
;; store is refused earlier still, `store is already locked' at the
;; nonblocking flock in `fnn-open-lock' (host/native/io.lisp), the word the
;; query executor reports too; this theorem is what keeps publication
;; unreachable if that open ever admitted an unlocked store.
;; Teeth: tests/acl2/native-admin-tests.lisp.
(defthm fn-native-admin-publication-is-authorized-only-under-the-lock
  (let ((result (fn-native-admin-publication-authorize
                 records frontier config-records record lock-owned observed-names)))
    (and (implies (equal (fn-native-admin-publication-status result) :accepted)
                  lock-owned)
         (implies (fn-native-admin-publication-jpub result)
                  lock-owned)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-native-admin-publication-authorize)
                                  (fn-cnode-config-replay fn-native-admin-candidate-openp
                                   fn-native-admin-config-name fn-cfg-recordp)))))

; RFC 5536 s3.1.4 reserved names, stated over the octets the operator typed:
; a creatable name is a valid group name whose case-folded octets are not
; "example", do not begin "example.", and are not "poster".  The
; recognizer reads "first (or only) component" through
; `fn-record-group-first-component'; this equates it with the prefix
; reading of "example.*".
(local (defthm fn-native-admin-true-listp-of-fold-octets
  (true-listp (fn-native-admin-fold-octets xs))))

(local (defthm fn-native-admin-first-component-is-example
  (implies (true-listp xs)
           (equal (equal (fn-record-group-first-component xs)
                         *fn-native-admin-reserved-example*)
                  (or (equal xs *fn-native-admin-reserved-example*)
                      (and (<= 8 (len xs))
                           (equal (take 8 xs)
                                  (append *fn-native-admin-reserved-example*
                                          '(46)))))))
  :hints (("Goal" :expand ((fn-record-group-first-component xs)
                           (fn-record-group-first-component (cdr xs))
                           (fn-record-group-first-component (cddr xs))
                           (fn-record-group-first-component (cdddr xs))
                           (fn-record-group-first-component (cddddr xs))
                           (fn-record-group-first-component (cdr (cddddr xs)))
                           (fn-record-group-first-component (cddr (cddddr xs)))
                           (fn-record-group-first-component (cdddr (cddddr xs))))))))

(defthm fn-native-admin-group-name-creatablep-is-the-rfc-5536-rule
  (equal (fn-native-admin-group-name-creatablep text)
         (and (fn-record-group-namep text)
              (let ((xs (fn-native-admin-fold-octets
                         (fn-record-string-octets text))))
                (not (or (equal xs *fn-native-admin-reserved-example*)
                         (and (<= 8 (len xs))
                              (equal (take 8 xs)
                                     (append *fn-native-admin-reserved-example*
                                             '(46))))
                         (equal xs *fn-native-admin-reserved-poster*))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-record-group-namep
                                      fn-native-admin-fold-octets
                                      fn-record-string-octets))))

; The first component the special-purpose recognizer reads is the one the
; reserved-name rule reads (`fn-record-group-first-component').
(defthm fn-native-admin-name-components-first-is-the-first-component
  (equal (car (fn-native-admin-name-components xs))
         (fn-record-group-first-component xs))
  :hints (("Goal" :in-theory (enable fn-record-group-first-component))))

; KEYSTONE (RFC 5536 s3.1.4 reserved names at `group create').  The subject
; is `fn-native-admin-plan', which host/native-admin-host.lisp:7 calls
; (`fn-native-admin-host-plan', reached from `fnn-admin-plan' and
; `fnn-owner-live-admin-serialized', host/native/admin.lisp).  A request to
; create a reserved name is refused with its named reason and carries no
; delta, so the live arm (`fn-native-admin-host-owner-reconfigure') stages
; nothing; both host arms return :refused on a non-accepted plan before any
; store operation.  `group retire' of such a name stays admitted: a store
; that already carries one can still remove it.
(local (defthm fn-native-admin-len-of-words
  (equal (len (fn-native-admin-words argv)) (len argv))
  :rule-classes nil))

(defthm fn-native-admin-plan-refuses-a-reserved-group-create
  (implies (and (fn-native-admin-argvp argv)
                (equal (fn-native-admin-words argv) (list "group" "create" name))
                (fn-native-admin-group-name-reservedp name))
           (let ((plan (fn-native-admin-plan argv)))
             (and (equal (fn-native-admin-result-status plan) :refused)
                  (equal (fn-native-admin-result-reason plan)
                         :reserved-group-name)
                  (equal (fn-native-admin-plan-deltas plan) nil))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-native-admin-plan)
                                  (fn-native-admin-group-name-reservedp
                                   fn-native-admin-words fn-native-admin-argvp
                                   fn-native-admin-peer-plan
                                   fn-native-admin-bp-boundary-plan
                                   fn-record-group-namep fn-path-identityp
                                   fn-native-admin-decimalp
                                   fn-native-admin-decimal-value))
           :use ((:instance fn-native-admin-len-of-words)))))

; KEYSTONE (RFC 5536 s3.1.4 specific-purpose names, local agreement).  The
; subject is `fn-native-admin-plan' (called as below).  For every creatable
; name, special-purpose or not, `group create' plans exactly one accepted
; :create-group of the name the operator typed, with no capacity, rows or
; policy: no plan field depends on the name's special-purpose class, so
; creating "to.x", "control.x", "a.all", "ctl" or "junk" derives no control,
; moderation, deletion, forwarding or wildcard authority from its name.
(defthm fn-native-admin-plan-create-ignores-special-purpose
  (implies (and (fn-native-admin-argvp argv)
                (equal (fn-native-admin-words argv) (list "group" "create" name))
                (fn-native-admin-group-name-creatablep name))
           (equal (fn-native-admin-plan argv)
                  (fn-native-admin-result :accepted nil :create-group
                                          (caddr argv) 0 nil nil)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-native-admin-plan
                                   fn-native-admin-group-name-creatablep)
                                  (fn-native-admin-group-name-reservedp
                                   fn-native-admin-words fn-native-admin-argvp
                                   fn-native-admin-peer-plan
                                   fn-native-admin-bp-boundary-plan
                                   fn-record-group-namep fn-path-identityp
                                   fn-native-admin-decimalp
                                   fn-native-admin-decimal-value
                                   fn-native-admin-result))
           :use ((:instance fn-native-admin-len-of-words)))))

