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
; PRF-161: the exposure slots and the anonymous words `policy set' admits.
(include-book "public-exposure-rows")
; PRF-235, PRF-236: the transit hygiene limit slots.
(include-book "relay-checks")
(include-book "identity")
(include-book "bp-eid-shape")
; The argv, decimal, result and config-name vocabulary, and the peer and
; bp-boundary parsers with the `peer list' codec, are in
; books/native-admin-shape.lisp and books/native-admin-peer.lisp
; (planning/audit-2026-09-25-twins-fanin.md packet 4).  This book keeps the
; group-name rules, the plan, its deltas and the publication decision.
(include-book "native-admin-shape")
(include-book "native-admin-peer")
; PKT-211: `peer list' renders the carriage budget (its own book, D26).
(include-book "native-admin-peer-budget")
; `bp-route add|remove', the BP route table (books/bp-route.lisp).
(include-book "bp-route")
; D13: `retention set RULE [DAYS]' (books/reclaim-rule).
(include-book "reclaim-rule")
; Q14: `retention expire TARGET ...', the per-group expiry policy
; (books/expiry-policy).
(include-book "expiry-policy")
(include-book "injection-info-policy")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-ipp-addr-specp)
                          (:definition fn-native-admin-words))))

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

; PKT-867: argv words have no length bound; the walks over them are loop
; twins (tools/depth_check.py).
(defun fn-native-admin-fold-octets-loop (xs acc)
  (declare (xargs :guard (true-listp acc)))
  (if (consp xs)
      (fn-native-admin-fold-octets-loop (cdr xs) (cons (if (and (integerp (car xs)) (<= 65 (car xs)) (<= (car xs) 90))
                (+ 32 (car xs))
              (car xs)) acc))
    (revappend acc nil)))

(defun fn-native-admin-fold-octets (xs)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (if (consp xs)
                  (cons (if (and (integerp (car xs)) (<= 65 (car xs)) (<= (car xs) 90))
                (+ 32 (car xs))
              (car xs))
                        (fn-native-admin-fold-octets (cdr xs)))
                nil)
       :exec (fn-native-admin-fold-octets-loop xs nil)))

(local
 (defthm fn-native-admin-fold-octets-loop-is-revappend
   (equal (fn-native-admin-fold-octets-loop xs acc)
          (revappend acc (fn-native-admin-fold-octets xs)))))

(verify-guards fn-native-admin-fold-octets)

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

;; Control authority (D29, packet C2): `control grant PRINCIPAL VERB
;; NAMESPACE-PATTERN' and `control revoke PRINCIPAL VERB NAMESPACE-PATTERN'.
;; The plan carries the namespace as NAME, the principal as PEER and the
;; verb as VALUE, each the octets the operator typed; the delta's structural
;; admissibility is `fn-cfg-delta-reason' (books/config.lisp).  A reserved
;; namespace (RFC 5536 section 3.1.4, the first component of the pattern) is
;; refused here by name.
(defun fn-native-admin-arg (n xs)
  (declare (xargs :guard t :measure (nfix n)))
  (if (consp xs)
      (if (zp (nfix n)) (car xs) (fn-native-admin-arg (1- (nfix n)) (cdr xs)))
    nil))

(defun fn-native-admin-control-plan (words argv)
  (declare (xargs :guard t))
  (let ((op (fn-native-admin-arg 1 words))
        (principal (fn-native-admin-arg 2 words))
        (verb (fn-native-admin-arg 3 words))
        (ns (fn-native-admin-arg 4 words)))
    (cond ((and (equal (len words) 2) (equal op "list"))
           (fn-native-admin-result :accepted nil :list-control nil 0 nil nil))
          ((not (and (equal (len words) 5)
                     (member-equal op '("grant" "revoke"))))
           (fn-native-admin-result :refused :syntax nil nil nil nil nil))
          ((fn-native-admin-group-name-reservedp ns)
           (fn-native-admin-result :refused :reserved-group-name nil nil 0 nil nil))
          ((not (fn-cfg-namespace-patternp ns))
           (fn-native-admin-result :refused :namespace-pattern nil nil 0 nil nil))
          ((not (fn-cfg-principal-hexp principal))
           (fn-native-admin-result :refused :principal nil nil 0 nil nil))
          ((not (member-equal verb *fn-cfg-control-verbs*))
           (fn-native-admin-result :refused :verb-not-grantable nil nil 0 nil nil))
          (t (fn-native-admin-result
              :accepted nil
              (if (equal op "grant") :grant-control :revoke-control)
              (fn-native-admin-arg 4 argv) 0 (fn-native-admin-arg 2 argv)
              (fn-native-admin-arg 3 argv))))))

; A decimal word is a string, which is all the guards below need of it; with
; this the guard proofs keep the decimal recognizer and its value closed.
(local (defthm fn-native-admin-decimalp-is-a-string
  (implies (fn-native-admin-decimalp text) (stringp text))
  :rule-classes :forward-chaining))

; The DAYS of `retention set release-after DAYS', or nil.
(defun fn-native-admin-retention-days (words)
  (declare (xargs :guard t))
  (and (true-listp words)
       (equal (len words) 4)
       (fn-native-admin-decimalp (cadddr words))
       (fn-native-admin-decimal-value (coerce (cadddr words) 'list))))

;; Moderated groups (P3, PRF-228, NNT-047; RFC 5537 sections 3.5 and 3.5.1,
;; RFC 6048 section 2.1.1):
;;
;;   group moderate NAME --moderators LOGIN[,LOGIN...] [--queue QUEUE]
;;                       [--submission ADDRESS]
;;   group moderate NAME --off
;;
;; One :set-group-moderation delta (code 23, books/config.lisp): NAME is
;; moderated by the LOGINs (accounts), and an unapproved article posted to it
;; is forwarded into QUEUE (default NAME.moderation, a live group the
;; operator created); ADDRESS is the optional submission address.  `--off'
;; ends the moderation.  The delta's admission (the group and the queue
;; live, the queue not moderated, the logins' spelling) is the store core's
;; (`fn-cfg-set-group-moderation-reason').
(defun fn-native-admin-split-commas-loop (octets piece-rev acc)
  (declare (xargs :guard (true-listp acc)))
  (if (consp octets)
      (if (equal (car octets) 44)
          (fn-native-admin-split-commas-loop
           (cdr octets) nil (cons (reverse (true-list-fix piece-rev)) acc))
        (fn-native-admin-split-commas-loop (cdr octets)
                                           (cons (car octets) piece-rev) acc))
    (revappend acc (list (reverse (true-list-fix piece-rev))))))

(defun fn-native-admin-split-commas-aux (octets piece-rev)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp octets)
           (if (equal (car octets) 44)
               (cons (reverse (true-list-fix piece-rev))
                     (fn-native-admin-split-commas-aux (cdr octets) nil))
             (fn-native-admin-split-commas-aux (cdr octets)
                                               (cons (car octets) piece-rev)))
         (list (reverse (true-list-fix piece-rev))))
       :exec (fn-native-admin-split-commas-loop octets piece-rev nil)))

(local
 (defthm fn-native-admin-split-commas-loop-is-revappend
   (equal (fn-native-admin-split-commas-loop octets piece-rev acc)
          (revappend acc (fn-native-admin-split-commas-aux octets piece-rev)))))

(verify-guards fn-native-admin-split-commas-aux)

; The comma-separated pieces of OCTETS, in order (an empty piece included).
(defun fn-native-admin-split-commas (octets)
  (declare (xargs :guard t))
  (fn-native-admin-split-commas-aux octets nil))

(defun fn-native-admin-loginsp (pieces)
  (declare (xargs :guard t))
  (if (consp pieces)
      (and (fn-cfg-account-loginp (fn-record-octets-string (car pieces)))
           (fn-native-admin-loginsp (cdr pieces)))
    (null pieces)))

; The options after `group moderate NAME', as (MODS QUEUE ADDRESS) octets,
; or :bad.  Each option at most once.
(defun fn-native-admin-moderate-options (words argv mods queue address)
  (declare (xargs :guard t :measure (len words)))
  (if (consp words)
      (if (and (consp (cdr words)) (consp argv) (consp (cdr argv)))
          (let ((w (car words)) (v (cadr argv)))
            (cond ((and (equal w "--moderators") (null mods))
                   (fn-native-admin-moderate-options (cddr words) (cddr argv)
                                                     (list v) queue address))
                  ((and (equal w "--queue") (null queue))
                   (fn-native-admin-moderate-options (cddr words) (cddr argv)
                                                     mods (list v) address))
                  ((and (equal w "--submission") (null address))
                   (fn-native-admin-moderate-options (cddr words) (cddr argv)
                                                     mods queue (list v)))
                  (t :bad)))
        :bad)
    (list mods queue address)))

(defun fn-native-admin-octets-strings-loop (xs acc)
  (declare (xargs :guard (true-listp acc)))
  (if (consp xs)
      (fn-native-admin-octets-strings-loop (cdr xs) (cons (fn-record-octets-string (car xs)) acc))
    (revappend acc nil)))

(defun fn-native-admin-octets-strings (xs)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (if (consp xs)
                  (cons (fn-record-octets-string (car xs))
                        (fn-native-admin-octets-strings (cdr xs)))
                nil)
       :exec (fn-native-admin-octets-strings-loop xs nil)))

(local
 (defthm fn-native-admin-octets-strings-loop-is-revappend
   (equal (fn-native-admin-octets-strings-loop xs acc)
          (revappend acc (fn-native-admin-octets-strings xs)))))

(verify-guards fn-native-admin-octets-strings)

(defun fn-native-admin-moderate-plan (words argv)
  (declare (xargs :guard t))
  (let ((name (fn-native-admin-arg 2 words))
        (name-octets (fn-native-admin-arg 2 argv)))
    (cond ((not (fn-record-group-namep name))
           (fn-native-admin-result :refused :group-name nil nil 0 nil nil))
          ((and (equal (len words) 4) (equal (fn-native-admin-arg 3 words) "--off"))
           (fn-native-admin-result :accepted nil :set-group-moderation
                                   name-octets 0 nil nil))
          (t
           (let ((opts (fn-native-admin-moderate-options
                        (nthcdr 3 (true-list-fix words))
                        (nthcdr 3 (true-list-fix argv)) nil nil nil)))
             (if (or (not (consp opts))
                     (not (consp (fn-native-admin-arg 0 opts))))
                 (fn-native-admin-result :refused :syntax nil nil nil nil nil)
               (let* ((m (fn-native-admin-arg 0 opts))
                      (q (fn-native-admin-arg 1 opts))
                      (a (fn-native-admin-arg 2 opts))
                      (mods (fn-native-admin-split-commas
                             (true-list-fix (fn-native-admin-arg 0 m))))
                      (queue (if (consp q)
                                 (true-list-fix (fn-native-admin-arg 0 q))
                               (append (true-list-fix name-octets)
                                       '(46 109 111 100 101 114 97 116 105 111 110))))
                      (address (if (consp a)
                                   (true-list-fix (fn-native-admin-arg 0 a))
                                 nil)))
                 (cond ((not (fn-native-admin-loginsp mods))
                        (fn-native-admin-result :refused :moderator-login
                                                nil nil 0 nil nil))
                       ((not (fn-record-group-namep
                              (fn-record-octets-string queue)))
                        (fn-native-admin-result :refused :group-name
                                                nil nil 0 nil nil))
                       (t (fn-native-admin-result
                           :accepted nil :set-group-moderation name-octets 0 nil
                           (cons queue (cons address mods))))))))))))

;; Group descriptions and the node's message (PRF-195, NNT-039; RFC 3977
;; section 7.6.6, RFC 6048 section 2.5):
;;
;;   group describe NAME [WORD ...]   NAME's description, the WORDs joined by
;;                                    one space; no WORD clears it
;;   motd set LINE [LINE ...]         the node's message, one LINE per argv word
;;   motd clear                       no message
;;
;; Each is one :set-group-description delta (code 20, books/config.lisp),
;; published live like every configuration record.  The text is printable
;; ASCII (the argv is ASCII; a control octet is refused here by name);
;; a description is cut into row pieces of at most *fn-cfg-max-label* octets
;; (`fn-native-admin-text-pieces'), so its length is bounded by the argv
;; (PKT-867: by the control frame that carries it, read under the profile's
;; bound, books/native-control.lisp fn-nctrl-read-bound-for) and not by a row.  A message line is
;; one row, so a line is at most *fn-cfg-max-label* octets.
(defun fn-native-admin-text-wordsp (words)
  (declare (xargs :guard t))
  (if (consp words)
      (and (fn-cfg-description-octetsp (car words))
           (fn-native-admin-text-wordsp (cdr words)))
    (null words)))

(defun fn-native-admin-join-words-loop (words acc)
  (declare (xargs :guard (true-listp acc)))
  (if (consp words)
      (if (consp (cdr words))
          (fn-native-admin-join-words-loop
           (cdr words) (cons 32 (revappend (true-list-fix (car words)) acc)))
        (revappend (revappend (true-list-fix (car words)) acc) nil))
    (revappend acc nil)))

(defun fn-native-admin-join-words (words)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp words)
           (if (consp (cdr words))
               (append (true-list-fix (car words))
                       (cons 32 (fn-native-admin-join-words (cdr words))))
             (true-list-fix (car words)))
         nil)
       :exec (fn-native-admin-join-words-loop words nil)))

(local
 (defthm fn-native-admin-revappend-revappend
   (equal (revappend (revappend x acc) y)
          (revappend acc (append x y)))))

(local
 (defthm fn-native-admin-join-words-loop-is-revappend
   (equal (fn-native-admin-join-words-loop words acc)
          (revappend acc (fn-native-admin-join-words words)))))

(verify-guards fn-native-admin-join-words)

(defun fn-native-admin-lines-fitp (lines)
  (declare (xargs :guard t))
  (if (consp lines)
      (and (<= (len (car lines)) *fn-cfg-max-label*)
           (fn-native-admin-lines-fitp (cdr lines)))
    t))

(defun fn-native-admin-group-namesp (words)
  (declare (xargs :guard t))
  (if (consp words)
      (and (fn-record-group-namep (car words))
           (fn-native-admin-group-namesp (cdr words)))
    t))

(defun fn-native-admin-describe-plan (words argv)
  (declare (xargs :guard t))
  (let ((name (fn-native-admin-arg 2 words))
        (text (fn-native-admin-join-words (nthcdr 3 (true-list-fix argv)))))
    (cond ((not (fn-record-group-namep name))
           (fn-native-admin-result :refused :group-name nil nil 0 nil nil))
          ((not (fn-native-admin-text-wordsp (nthcdr 3 (true-list-fix argv))))
           (fn-native-admin-result :refused :description-text nil nil 0 nil nil))
          ((and (consp text) (not (fn-cfg-some-graphic-octetp text)))
           (fn-native-admin-result :refused :description-blank nil nil 0 nil nil))
          (t (fn-native-admin-result :accepted nil :set-group-description
                                     (fn-native-admin-arg 2 argv) 0 nil text)))))

(defun fn-native-admin-motd-plan (words argv)
  (declare (xargs :guard t))
  (let ((lines (nthcdr 2 (true-list-fix argv))))
    (cond ((and (equal (len words) 2) (equal (fn-native-admin-arg 1 words) "clear"))
           (fn-native-admin-result :accepted nil :set-motd nil 0 nil nil))
          ((not (and (<= 3 (len words)) (equal (fn-native-admin-arg 1 words) "set")))
           (fn-native-admin-result :refused :syntax nil nil nil nil nil))
          ((not (fn-native-admin-text-wordsp lines))
           (fn-native-admin-result :refused :description-text nil nil 0 nil nil))
          ((not (fn-native-admin-lines-fitp lines))
           (fn-native-admin-result :refused :motd-line nil nil 0 nil nil))
          (t (fn-native-admin-result :accepted nil :set-motd nil 0 nil lines)))))

; OCTETS as row pieces of at most *fn-cfg-max-label* octets, in order.
(local
 (defthm fn-native-admin-len-of-nthcdr
   (implies (natp n)
            (equal (len (nthcdr n x)) (nfix (- (len x) n))))
   :hints (("Goal" :induct (nthcdr n x) :in-theory (enable nthcdr len)))))

; The loop carries N, the remaining length, so each piece costs its own
; octets rather than a walk of the rest.
(defun fn-native-admin-text-pieces-loop (octets n acc)
  (declare (xargs :guard (and (true-listp octets) (equal n (len octets))
                              (true-listp acc))
                  :measure (len octets)))
  (if (consp octets)
      (if (< *fn-cfg-max-label* (mbe :logic (len octets) :exec n))
          (fn-native-admin-text-pieces-loop
           (nthcdr *fn-cfg-max-label* octets)
           (- (mbe :logic (len octets) :exec n) *fn-cfg-max-label*)
           (cons (fn-record-octets-string (take *fn-cfg-max-label* octets)) acc))
        (revappend acc (list (fn-record-octets-string octets))))
    (revappend acc nil)))

(defun fn-native-admin-text-pieces (octets)
  (declare (xargs :guard (true-listp octets) :measure (len octets)
                  :verify-guards nil))
  (mbe :logic
       (if (consp octets)
           (if (< *fn-cfg-max-label* (len octets))
               (cons (fn-record-octets-string (take *fn-cfg-max-label* octets))
                     (fn-native-admin-text-pieces (nthcdr *fn-cfg-max-label* octets)))
             (list (fn-record-octets-string octets)))
         nil)
       :exec (fn-native-admin-text-pieces-loop octets (len octets) nil)))

(local
 (defthm fn-native-admin-text-pieces-loop-is-revappend
   (equal (fn-native-admin-text-pieces-loop octets n acc)
          (revappend acc (fn-native-admin-text-pieces octets)))))

(verify-guards fn-native-admin-text-pieces)

(defun fn-native-admin-line-pieces-loop (lines acc)
  (declare (xargs :guard (true-listp acc)))
  (if (consp lines)
      (fn-native-admin-line-pieces-loop (cdr lines) (cons (fn-record-octets-string (car lines)) acc))
    (revappend acc nil)))

(defun fn-native-admin-line-pieces (lines)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (if (consp lines)
                  (cons (fn-record-octets-string (car lines))
                        (fn-native-admin-line-pieces (cdr lines)))
                nil)
       :exec (fn-native-admin-line-pieces-loop lines nil)))

(local
 (defthm fn-native-admin-line-pieces-loop-is-revappend
   (equal (fn-native-admin-line-pieces-loop lines acc)
          (revappend acc (fn-native-admin-line-pieces lines)))))

(verify-guards fn-native-admin-line-pieces)

;; PRF-222: `account access LOGIN|--anonymous --read R --post P'.  A
;; pattern is admitted only when it is an RFC 3977 section 4.2 wildmat over
;; newsgroup names (`fn-wildmat-parse', the grammar LIST ACTIVE's argument
;; is read with) and a configuration label; the login is the account
;; grammar of books/config.lisp.
(defun fn-native-admin-access-patternp (word)
  (declare (xargs :guard t))
  (and (fn-cfg-access-patternp word)
       (fn-wildmat-result-okp
        (fn-wildmat-parse (fn-record-string-octets word)))
       t))

(defun fn-native-admin-access-plan (words argv)
  (declare (xargs :guard t))
  (if (and (equal (len words) 5)
           (equal (fn-native-admin-arg 1 words) "--read")
           (equal (fn-native-admin-arg 3 words) "--post"))
      (let ((login (fn-native-admin-arg 0 words))
            (read (fn-native-admin-arg 2 words))
            (post (fn-native-admin-arg 4 words)))
        (cond ((not (or (equal login "--anonymous")
                        (fn-cfg-account-loginp login)))
               (fn-native-admin-result :refused :access-login nil nil 0 nil nil))
              ((not (and (fn-native-admin-access-patternp read)
                         (fn-native-admin-access-patternp post)))
               (fn-native-admin-result :refused :access-pattern nil nil 0 nil nil))
              (t (fn-native-admin-result
                  :accepted nil :account-access
                  (if (equal login "--anonymous") nil (fn-native-admin-arg 0 argv))
                  0 (fn-native-admin-arg 2 argv) (fn-native-admin-arg 4 argv)))))
    (fn-native-admin-result :refused :syntax nil nil nil nil nil)))

;; PRF-234 (CNS-006): `consumer bind NAME --account LOGIN' and `consumer
;; unbind NAME'.  NAME is a local consumer id as `fn consumer register'
;; spells it; LOGIN is the account grammar of books/config.lisp.  One
;; :consumer-bind record (code 24), offline or live; the unbind is the
;; record with LOGIN "" and no row.
(defun fn-native-admin-consumer-plan (words argv)
  (declare (xargs :guard t))
  ;; WORDS and ARGV start at the verb: (bind NAME --account LOGIN),
  ;; (unbind NAME), (show).
  (cond ((and (equal (len words) 2)
              (equal (fn-native-admin-arg 0 words) "unbind"))
         (if (fn-cfg-consumer-namep (fn-native-admin-arg 1 words))
             (fn-native-admin-result :accepted nil :consumer-bind
                                     (fn-native-admin-arg 1 argv) 0 nil nil)
           (fn-native-admin-result :refused :consumer-name nil nil 0 nil nil)))
        ((and (equal (len words) 4)
              (equal (fn-native-admin-arg 0 words) "bind")
              (equal (fn-native-admin-arg 2 words) "--account"))
         (cond ((not (fn-cfg-consumer-namep (fn-native-admin-arg 1 words)))
                (fn-native-admin-result :refused :consumer-name nil nil 0 nil nil))
               ((not (fn-cfg-account-loginp (fn-native-admin-arg 3 words)))
                (fn-native-admin-result :refused :consumer-login nil nil 0 nil nil))
               (t (fn-native-admin-result :accepted nil :consumer-bind
                                          (fn-native-admin-arg 1 argv) 0 nil
                                          (fn-native-admin-arg 3 argv)))))
        ((equal words '("show"))
         (fn-native-admin-result :accepted nil :list-accounts nil 0 nil nil))
        (t (fn-native-admin-result :refused :consumer nil nil 0 nil nil))))

;; PKT-597: `policy set complaints-to ADDR' with ADDR an addr-spec
;; (books/injection-info-policy.lisp).  One opaque test in the plan, so the
;; plan's theorems do not case-split on the address grammar.
(defun fn-native-admin-complaints-wordsp (words argv)
  (declare (xargs :guard t))
  (and (true-listp words) (equal (len words) 4)
       (equal (car words) "policy")
       (equal (cadr words) "set")
       (equal (caddr words) *fn-ipp-complaints-slot*)
       (consp argv) (consp (cdr argv)) (consp (cddr argv)) (consp (cdddr argv))
       (fn-ipp-addr-specp (fn-ipp-octets (cadddr argv)))))

(defthm fn-native-admin-complaints-wordsp-names-the-slot
  (implies (fn-native-admin-complaints-wordsp words argv)
           (and (equal (len words) 4)
                (equal (caddr words) *fn-ipp-complaints-slot*)))
  :rule-classes :forward-chaining)

(in-theory (disable fn-native-admin-complaints-wordsp))

; Row S10: the `policy set' keys that take a decimal count: the public
; reader port's exposure limits (books/public-exposure-rows.lisp), the relay
; checks' limits (books/relay-checks.lisp) and the store limits
; (books/limits-live.lisp: max-transactions, max-history-octets,
; max-article-octets).
(defun fn-native-admin-counted-policy-keyp (key)
  (declare (xargs :guard t))
  (and (or (fn-exp-limit-slotp key)
           (and (fn-rck-limit-slotp key)
                (not (equal key *fn-rck-require-path-slot*)))
           (member-equal key '("max-transactions" "max-history-octets"
                               "max-article-octets" "compress-min-octets")))
       t))

; Row S10: every `policy set' key the grammar above has an arm for: the
; counted ones and the worded ones (the path identity, the posting policy,
; the trusted range, the anonymous policy, the complaints address, the
; relay's require-path switch).  A key outside this set is unknown by name;
; a known key with a malformed value keeps its own arm's answer.
(defun fn-native-admin-known-policy-keyp (key)
  (declare (xargs :guard t))
  (and (or (fn-native-admin-counted-policy-keyp key)
           (member-equal key (list "path-identity" "posting-policy"
                                   *fn-exp-trusted-slot* *fn-exp-policy-slot*
                                   *fn-ipp-complaints-slot*
                                   *fn-rck-require-path-slot*)))
       t))

(defun fn-native-admin-plan (argv)
  "Normalize an administrative request; configuration admission stays in the store core."
  (declare (xargs :guard t
                  :guard-hints
                  ;; The arms' tests stay closed: the guard needs their
                  ;; types, not their bodies (5.0 -> 2.6 s, 1.34M -> 460k
                  ;; steps, persvati REPL 2026-09-28).
                  (("Goal" :in-theory (disable fn-native-admin-decimalp
                                               fn-native-admin-decimal-value
                                               fn-native-admin-words
                                               fn-record-octets-string
                                               fn-cbor-octet-listp
                                               fn-exp-limit-slotp fn-rck-limit-slotp
                                               fn-exp-trusted-wordp
                                               fn-exp-anonymous-wordp
                                               fn-xpy-targetp fn-xpy-words-policy
                                               default-car default-cdr
                                               default-+-1 default-+-2
                                               default-<-1 default-<-2 len
                                               (tau-system))))))
  (if (not (fn-native-admin-argvp argv))
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
       ; O2 (books/group-status.lisp): `group policy NAME n|y' sets the
       ; group's LIST ACTIVE status (RFC 3977 section 7.6.3): "n" closes it
       ; to local posting, "y" opens it.  A durable :set-group-status
       ; configuration record (code 21), offline or live.
       ((and (equal (len words) 4)
             (equal (car words) "group")
             (equal (cadr words) "policy")
             (fn-record-group-namep (caddr words))
             (member-equal (cadddr words) '("y" "n")))
        (fn-native-admin-result :accepted nil :set-group-status (caddr argv) 0
                                nil (cadddr argv)))
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
       ; PKT-597 (books/injection-info-policy.lisp): the mailbox the node's
       ; Injection-Info names as mail-complaints-to (RFC 5536 section
       ; 3.2.8), a durable `:set-policy' row like path-identity, applied
       ; live; the value must be an <addr-spec> of two dot-atoms, so it
       ; stands in the header's quoted-string as it is.
       ((fn-native-admin-complaints-wordsp words argv)
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
       ; PRF-161 (books/public-exposure.lisp): what an unauthenticated
       ; session may do, a durable `:set-policy' record applied live.
       ((and (equal (len words) 4)
             (equal (car words) "policy")
             (equal (cadr words) "set")
             (equal (caddr words) *fn-exp-policy-slot*)
             (fn-exp-anonymous-wordp (cadddr words)))
        (fn-native-admin-result :accepted nil :set-policy (caddr argv) 0 nil
                                (cadddr argv)))
       ; PRF-211: the trusted range exempt from exposure-per-address, a
       ; durable `:set-policy' row applied live; the word is admitted only
       ; when every range in it parses (fn-exp-trusted-wordp), and `none'
       ; clears it.
       ((and (equal (len words) 4)
             (equal (car words) "policy")
             (equal (cadr words) "set")
             (equal (caddr words) *fn-exp-trusted-slot*)
             (fn-exp-trusted-wordp (cadddr words)))
        (fn-native-admin-result :accepted nil :set-policy (caddr argv) 0 nil
                                (cadddr argv)))
       ; PRF-161: a limit of the public reader port, a `:set-limit' row
       ; (SLOT, "") staged, published and replayed like the retention rule.
       ((and (equal (len words) 4)
             (equal (car words) "policy")
             (equal (cadr words) "set")
             (fn-exp-limit-slotp (caddr words))
             (fn-native-admin-decimalp (cadddr words)))
        (fn-native-admin-result :accepted nil :set-exposure (caddr argv)
                                (fn-native-admin-decimal-value
                                 (coerce (cadddr words) 'list))
                                nil nil))
       ; PRF-235 / PRF-236 (books/relay-checks.lisp): `policy set
       ; relay-date-skew SECONDS' (RFC 5537 section 3.6 step 2's margin, at
       ; most its 86400) and `policy set refused-offer-capacity N' (the
       ; refused-offer memory's bound), each a `:set-limit' row keyed
       ; (SLOT, ""), staged, published and replayed like the exposure limits.
       ((and (equal (len words) 4)
             (equal (car words) "policy")
             (equal (cadr words) "set")
             (fn-rck-limit-slotp (caddr words))
             (fn-native-admin-decimalp (cadddr words))
             (fn-rck-limit-valuep (caddr words)
                                  (fn-native-admin-decimal-value
                                   (coerce (cadddr words) 'list))))
        (fn-native-admin-result :accepted nil :set-transit-limit (caddr argv)
                                (fn-native-admin-decimal-value
                                 (coerce (cadddr words) 'list))
                                nil nil))
       ; Lane log-2: the record log's batch bounds, `policy set
       ; log-batch-records N' and `policy set log-batch-octets N'
       ; (books/owner-log-route.lisp fn-olr-bmax / fn-olr-omax read these
       ; `:set-limit' rows), each keyed (SLOT, ""), staged, published and
       ; replayed like the transit limits.  A bound is positive and under the
       ; row's ceiling.  Lane time-model-2 (PRF-311): the disk's profile
       ; fields ride the same rows, `policy set barrier-deadline-ms N' (D),
       ; `barrier-stall-ms N' (H; read as at least D,
       ; books/owner-time-model.lisp fn-otm-limits) and `clock-event-ms N'
       ; (the committer's cadence), each positive milliseconds; a batch in
       ; flight keeps the limits it was issued with, the next one reads the
       ; new row.  Lane compression-extents-2: `policy set
       ; compress-min-octets N', the compression threshold, rides the same
       ; row kind; an article record appended after it with a payload span
       ; of at least N octets is offered to the encoder.
       ((and (equal (len words) 4)
             (equal (car words) "policy")
             (equal (cadr words) "set")
             (member-equal (caddr words) '("log-batch-records" "log-batch-octets"
                                           "barrier-deadline-ms" "barrier-stall-ms"
                                           "clock-event-ms" "compress-min-octets"
                                           ;; PRF-359: the operator's free-space
                                           ;; reserve (books/owner-time-model.lisp
                                           ;; fn-otm-space-need).
                                           "disk-reserve-octets"))
             (fn-native-admin-decimalp (cadddr words))
             ; Lane compression-extents-2 (PRF-341): `compress-min-octets'
             ; (books/payload-lz-append.lisp fn-lzr-config-min) also admits
             ; 0, which is off, as no row is.
             (or (posp (fn-native-admin-decimal-value (coerce (cadddr words) 'list)))
                 (equal (caddr words) "compress-min-octets"))
             (<= (fn-native-admin-decimal-value (coerce (cadddr words) 'list))
                 (fn-cfg-limit-ceiling (caddr words))))
        (fn-native-admin-result :accepted nil :set-transit-limit (caddr argv)
                                (fn-native-admin-decimal-value
                                 (coerce (cadddr words) 'list))
                                nil nil))
       ; Row S10 (lane operability-2): `policy set KEY VALUE' that no arm
       ; above took is refused by name, not by the usage line: a counted
       ; key with a value that is no decimal count, else a key the node
       ; does not have.  (A known key with a wrong non-numeric value keeps
       ; the usage line: the line names the values.)
       ((and (equal (len words) 4)
             (equal (car words) "policy")
             (equal (cadr words) "set")
             (fn-native-admin-counted-policy-keyp (caddr words))
             (not (fn-native-admin-decimalp (cadddr words))))
        (fn-native-admin-result :refused :policy-value-not-a-number nil nil 0 nil nil))
       ((and (equal (len words) 4)
             (equal (car words) "policy")
             (equal (cadr words) "set")
             (not (fn-native-admin-known-policy-keyp (caddr words))))
        (fn-native-admin-result :refused :unknown-policy-key nil nil 0 nil nil))
       ((and (consp words) (equal (car words) "policy"))
        (fn-native-admin-result :refused :policy nil nil 0 nil nil))
       ; D13 (STO-014): the operator's content-retention rule.  Two
       ; `:set-limit' rows (books/reclaim-rule), staged, published and
       ; replayed as every other configuration record.  The default, with
       ; no row, is keep-forever.
       ((and (member-equal (len words) '(3 4))
             (equal (car words) "retention")
             (equal (cadr words) "set")
             (fn-rcl-rule-of-words (caddr words)
                                   (fn-native-admin-retention-days words)))
        (fn-native-admin-result :accepted nil :set-retention (caddr argv)
                                (nfix (fn-native-admin-retention-days words))
                                nil nil))
       ; Q14 (books/expiry-policy): the operator's per-group expiry policy,
       ; `retention expire TARGET clear' or `retention expire TARGET [keep
       ; DAYS] [default DAYS] [purge DAYS] [octets N]', TARGET a group name
       ; or "*" (every group without its own).  Five quota rows keyed
       ; (SCOPE, TARGET), staged, published and replayed as every other
       ; configuration record; `clear' writes the unset policy.
       ((and (<= 4 (len words))
             (equal (car words) "retention")
             (equal (cadr words) "expire")
             (fn-xpy-targetp (caddr words))
             (fn-xpy-words-policy (cdddr words)))
        (fn-native-admin-result :accepted nil :set-expiry (caddr argv) 0 nil
                                (fn-xpy-words-policy (cdddr words))))
       ((and (consp words) (equal (car words) "retention"))
        (fn-native-admin-result :refused :retention nil nil 0 nil nil))
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
         ((and (consp (cdr words))
               (member-equal (cadr words) '("budget" "carries" "pull" "distributions"
                                            "catch-up" "feed")))
          (fn-native-admin-peer-extend-plan words))
         (t (fn-native-admin-peer-plan words))))
       ; PRF-164 (PKT-439): invitation-code accounts.  `account list' is a
       ; query (no digest or verifier is rendered, books/account-list.lisp
       ; `fn-acct-kinds-list-report').  `account invite DIGEST SECONDS' is the
       ; form the operator's `account invite [--expires SECONDS]' sends
       ; after ACL2 rendered the code and its digest on the operator's side
       ; (host/native/operator.lisp): the code itself never reaches this
       ; argv, the owner or any record.
       ((and (equal (len words) 2)
             (equal (car words) "account")
             (equal (cadr words) "list"))
        (fn-native-admin-result :accepted nil :list-accounts nil 0 nil nil))
       ((and (equal (len words) 4)
             (equal (car words) "account")
             (equal (cadr words) "invite")
             (fn-cfg-account-digestp (caddr words))
             (fn-native-admin-decimalp (cadddr words))
             (posp (fn-native-admin-decimal-value
                    (coerce (cadddr words) 'list))))
        (fn-native-admin-result :accepted nil :account-invite (caddr argv)
                                (fn-native-admin-decimal-value
                                 (coerce (cadddr words) 'list))
                                nil nil))
       ; PRF-222 (NNT-046): group access.  `account access show' is the
       ; `account list' report, whose access lines are the rules
       ; (books/account-list.lisp).  `account access LOGIN --read R --post P'
       ; and `account access --anonymous --read R --post P' stage one
       ; :account-access record (code 22), offline or live.
       ((and (equal (len words) 3)
             (equal (car words) "account")
             (equal (cadr words) "access")
             (equal (caddr words) "show"))
        (fn-native-admin-result :accepted nil :list-accounts nil 0 nil nil))
       ((and (<= 3 (len words))
             (equal (car words) "account")
             (equal (cadr words) "access"))
        (fn-native-admin-access-plan (cddr words) (cddr argv)))
       ; public-node-2: `account delete LOGIN' stages one :account-delete
       ; record (code 27), offline or live; the configuration admits it
       ; only while LOGIN holds an account and no obligation
       ; (books/accounts.lisp
       ; fn-acct-delete-is-admitted-exactly-when-held-and-unobligated).
       ((and (equal (len words) 3)
             (equal (car words) "account")
             (equal (cadr words) "delete"))
        (if (fn-cfg-account-loginp (caddr words))
            (fn-native-admin-result :accepted nil :account-delete (caddr argv)
                                    0 nil nil)
          (fn-native-admin-result :refused :account-login nil nil 0 nil nil)))
       ; PRF-388 (PKT-560): `account bind LOGIN HEX' and `account unbind
       ; LOGIN', the vector `principal bind|unbind' sends for a login the
       ; credential file does not hold (books/native-operator.lisp
       ; fn-native-operator-result-principal-account-result).  One
       ; :login-binding record (code 17), offline or live, which
       ; books/login-binding-live.lisp fn-lb-account-bind-plan admits only
       ; while LOGIN holds a redeemed account; HEX is the principal's 64
       ; lowercase hexadecimal digits.
       ((and (equal (len words) 4)
             (equal (car words) "account")
             (equal (cadr words) "bind"))
        (cond ((not (fn-cfg-account-loginp (caddr words)))
               (fn-native-admin-result :refused :account-login nil nil 0 nil nil))
              ((not (fn-cfg-hex-textp (cadddr words) 64))
               (fn-native-admin-result :refused :principal nil nil 0 nil nil))
              (t (fn-native-admin-result :accepted nil :account-bind (caddr argv)
                                         0 nil (cadddr argv)))))
       ((and (equal (len words) 3)
             (equal (car words) "account")
             (equal (cadr words) "unbind"))
        (if (fn-cfg-account-loginp (caddr words))
            (fn-native-admin-result :accepted nil :account-bind (caddr argv)
                                    0 nil nil)
          (fn-native-admin-result :refused :account-login nil nil 0 nil nil)))
       ((and (consp words) (equal (car words) "account"))
        (fn-native-admin-result :refused :account nil nil 0 nil nil))
       ; PRF-234: consumer bindings (books/consumer-bound.lisp).  `consumer
       ; show' is the `account list' report, whose consumer lines are the
       ; bindings.
       ((and (consp words) (equal (car words) "consumer"))
        (fn-native-admin-consumer-plan (cdr words) (cdr argv)))
       ; PKT-575 (CT3): the node operator's withdrawal authorization, the
       ; :withdraw-article record (code 26): `article withdraw-record CAUSE
       ; TARGET REASON'.  The owner's `article withdraw' and `moderation
       ; reject' name this vector (books/moderation-verbs.lisp
       ; `fn-mvb-withdraw-plan') before injecting CAUSE; the row alone
       ; withdraws nothing.
       ((and (equal (len words) 5)
             (equal (car words) "article")
             (equal (cadr words) "withdraw-record"))
        (fn-native-admin-result :accepted nil :withdraw-article (caddr argv) 0
                                (cadddr argv) (car (cddddr argv))))
       ((and (consp words) (equal (car words) "control"))
        (fn-native-admin-control-plan words argv))
       ((and (<= 3 (len words))
             (equal (car words) "group")
             (equal (cadr words) "describe"))
        (fn-native-admin-describe-plan words argv))
       ((and (<= 4 (len words))
             (equal (car words) "group")
             (equal (cadr words) "moderate"))
        (fn-native-admin-moderate-plan words argv))
       ; PRF-243 (RFC 6048 section 2.6): `group subscribe-default [NAME ...]'
       ; sets the list LIST SUBSCRIPTIONS recommends, in order; no NAME
       ; clears it.  One :set-default-subscriptions record (code 25); that
       ; each NAME is a live group named once is the delta's admission.
       ((and (<= 2 (len words))
             (equal (car words) "group")
             (equal (cadr words) "subscribe-default"))
        (if (fn-native-admin-group-namesp (nthcdr 2 words))
            (fn-native-admin-result :accepted nil :set-default-subscriptions
                                    nil 0 nil (nthcdr 2 (true-list-fix argv)))
          (fn-native-admin-result :refused :group-name nil nil 0 nil nil)))
       ((and (consp words) (equal (car words) "motd"))
        (fn-native-admin-motd-plan words argv))
       ((and (consp words) (equal (car words) "bp-boundary"))
        (fn-native-admin-bp-boundary-plan words))
       ((and (consp words) (equal (car words) "bp-route"))
        (fn-bprt-admin-plan words))
       ; PKT-868: what `store compact' and `store checkpoint' send a running
       ; owner (host/native/operator.lisp fnn-operator-execute-compaction): a
       ; request for its publication, no configuration record
       ; (fn-native-admin-result-owner-requestp; books/owner-compact-request).
       ((equal words '("compaction" "request"))
        (fn-native-admin-result :accepted nil :request-compaction nil 0 nil nil))
       ; Row S3 (lane operability-2): what `store inspect ID' sends a running
       ; owner (host/native/operator.lisp fnn-operator-execute-inspect): a
       ; request for its own lookup of ID, no configuration record
       ; (books/owner-maintenance-request.lisp fn-omr-inspect-word).
       ((and (equal (fn-ncfg-first words) "inspect")
             (equal (fn-ncfg-second words) "request")
             (stringp (fn-ncfg-nth 2 words))
             (null (fn-ncfg-rest (fn-ncfg-rest (fn-ncfg-rest words)))))
        (fn-native-admin-result :accepted nil :request-inspect nil 0 nil
                                (fn-ncfg-nth 2 words)))
       ; Q16: what `store reclaim' sends a running owner
       ; (host/native/operator.lisp fnn-operator-execute-store-action): a
       ; request for its reclaim pass (books/owner-reclaim.lisp), no
       ; configuration record of the plan's own.
       ((equal words '("reclaim" "request"))
        (fn-native-admin-result :accepted nil :request-reclaim nil 0 nil nil))
       ((equal words '("reclaim" "recorded"))
        (fn-native-admin-result :accepted nil :request-reclaim-recorded nil 0 nil nil))
       ((equal words '("reclaim" "dry-run"))
        (fn-native-admin-result :accepted nil :request-reclaim-dry-run nil 0 nil nil))
       (t (fn-native-admin-result :refused :syntax nil nil nil nil nil))))))

; PKT-868: an accepted plan the live owner answers from its own state, not by
; publishing a configuration record (the compaction request).
(defun fn-native-admin-result-owner-requestp (result)
  (declare (xargs :guard t))
  (and (equal (fn-native-admin-result-status result) :accepted)
       (member-equal (fn-native-admin-result-kind result)
                     '(:request-compaction :request-inspect :request-reclaim
                       :request-reclaim-recorded :request-reclaim-dry-run))
       t))

; Row S3: the Message-ID an inspect request carries (its value field), or nil.
(defun fn-native-admin-result-inspect-msgid (result)
  (declare (xargs :guard t))
  (and (fn-native-admin-result-owner-requestp result)
       (equal (fn-native-admin-result-kind result) :request-inspect)
       (stringp (fn-native-admin-result-value result))
       (fn-native-admin-result-value result)))

; Q16: the reclaim pass's mode an accepted reclaim request names, or nil
; (the compaction request).
(defun fn-native-admin-result-reclaim-mode (result)
  (declare (xargs :guard t))
  (and (fn-native-admin-result-owner-requestp result)
       (let ((kind (fn-native-admin-result-kind result)))
         (cond ((equal kind :request-reclaim) :reclaim)
               ((equal kind :request-reclaim-recorded) :recorded)
               ((equal kind :request-reclaim-dry-run) :dry-run)
               (t nil)))))

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
            ((equal kind :set-retention)
             (fn-rcl-rule-deltas
              (fn-rcl-rule-of-words
               name
               (if (equal name "release-after")
                   (fn-native-admin-result-capacity plan)
                 nil))))
            ((equal kind :set-expiry)
             (fn-xpy-deltas name (fn-native-admin-result-value plan)))
            ((member-equal kind '(:set-exposure :set-transit-limit))
             (list (fn-cfg-set-limit name (fn-native-admin-result-capacity plan))))
            ((equal kind :consumer-bind)
             (list (fn-cfg-consumer-bind
                    name
                    (fn-record-octets-string (fn-native-admin-result-value plan)))))
            ((equal kind :account-delete)
             (list (fn-cfg-account-delete name)))
            ((equal kind :account-access)
             (list (fn-cfg-account-access
                    name
                    (fn-record-octets-string (fn-native-admin-result-peer plan))
                    (fn-record-octets-string (fn-native-admin-result-value plan)))))
            ((equal kind :set-group-moderation)
             (let ((v (true-list-fix (fn-native-admin-result-value plan))))
               (list (fn-cfg-set-group-moderation
                      name
                      (fn-record-octets-string (car v))
                      (fn-record-octets-string (cadr v))
                      (fn-native-admin-octets-strings (cddr v))))))
            ((equal kind :withdraw-article)
             (list (fn-cfg-withdraw-article
                    name
                    (fn-record-octets-string (fn-native-admin-result-peer plan))
                    (fn-record-octets-string (fn-native-admin-result-value plan)))))
            ((equal kind :set-group-status)
             (list (fn-cfg-set-group-status
                    name
                    (fn-record-octets-string (fn-native-admin-result-value plan)))))
            ((equal kind :set-policy)
             (list (fn-cfg-set-policy
                    name
                    (fn-record-octets-string (fn-native-admin-result-value plan)))))
            ((equal kind :grant-control)
             (list (fn-cfg-grant-control
                    name
                    (fn-record-octets-string (fn-native-admin-result-peer plan))
                    (fn-record-octets-string (fn-native-admin-result-value plan)))))
            ((equal kind :set-group-description)
             (list (fn-cfg-set-group-description
                    name
                    (fn-native-admin-text-pieces
                     (true-list-fix (fn-native-admin-result-value plan))))))
            ((equal kind :set-default-subscriptions)
             (list (fn-cfg-set-default-subscriptions
                    (fn-native-admin-line-pieces
                     (fn-native-admin-result-value plan)))))
            ((equal kind :set-motd)
             (list (fn-cfg-set-group-description
                    "" (fn-native-admin-line-pieces
                        (fn-native-admin-result-value plan)))))
            ((equal kind :revoke-control)
             (list (fn-cfg-revoke-control
                    name
                    (fn-record-octets-string (fn-native-admin-result-peer plan)))))
            (t nil)))))

; PRF-099: the deltas over the live peer table.  An :extend-peer plan
; (`peer carries', `peer budget') extends the named boundary's rows as the
; table holds them now (fn-pcb-extend-deltas); every other plan is
; fn-native-admin-plan-deltas unchanged.  Host: host/native-admin-host.lisp
; fn-native-admin-host-owner-reconfigure (the live owner's table) and
; fn-native-admin-host-apply (the replayed store's table).
(defun fn-native-admin-plan-deltas-over (plan peers)
  (declare (xargs :guard t))
  (if (and (equal (fn-native-admin-result-status plan) :accepted)
           (equal (fn-native-admin-result-kind plan) :extend-peer))
      ; PRF-171: the incremental deltas (:add-peer-rows, then
      ; :remove-peer-rows of a superseded single-valued slot), which apply
      ; as the whole-group `fn-pcb-extend-delta'
      ; (`fn-pcb-extend-deltas-apply-as-the-extend-delta').
      ; `peer feed NAME pause|resume' (books/feed-pause.lisp): the deltas
      ; that set the one pause row, removing the other.
      (if (fn-fps-plan-rowsp (fn-native-admin-result-value plan))
          (fn-fps-deltas
           (fn-record-octets-string (fn-native-admin-result-name plan))
           (fn-fps-plan-pausep (fn-native-admin-result-value plan))
           peers)
        (fn-pcb-extend-deltas
         (fn-record-octets-string (fn-native-admin-result-name plan))
         (fn-native-admin-result-value plan)
         peers))
    (fn-native-admin-plan-deltas plan)))

(defthm fn-native-admin-plan-deltas-over-other-plans-by-definition
  (implies (not (equal (fn-native-admin-result-kind plan) :extend-peer))
           (equal (fn-native-admin-plan-deltas-over plan peers)
                  (fn-native-admin-plan-deltas plan))))

; public-node-2: the record an accepted `account delete LOGIN' stages, live
; (through fn-native-admin-plan-deltas-over) or offline, is exactly the
; configuration's deletion of the login the plan admitted.  An unfold.
(defthm fn-native-admin-plan-deltas-of-account-delete-unfolds
  (implies (and (equal (fn-native-admin-result-status plan) :accepted)
                (equal (fn-native-admin-result-kind plan) :account-delete))
           (equal (fn-native-admin-plan-deltas-over plan peers)
                  (list (fn-cfg-account-delete
                         (fn-record-octets-string
                          (fn-native-admin-result-name plan))))))
  :hints (("Goal" :in-theory (enable fn-native-admin-plan-deltas))))

; The sub-plans, closed (D26): none plans a group creation or retirement,
; so the plan theorems below need not open them (merged with group-access's
; access plan, opening all five cost 15 s of native-admin's 23 s at 2 jobs).
(local (defthm fn-native-admin-sub-plans-neither-create-nor-retire
  (and
       (not (equal (fn-native-admin-result-kind
                    (fn-native-admin-control-plan words argv))
                   :create-group))
       (not (equal (fn-native-admin-result-kind
                    (fn-native-admin-control-plan words argv))
                   :remove-group))
       (not (equal (fn-native-admin-result-kind
                    (fn-native-admin-control-plan words argv))
                   :set-bp-boundary))
       (not (equal (fn-native-admin-result-kind
                    (fn-native-admin-moderate-plan words argv))
                   :create-group))
       (not (equal (fn-native-admin-result-kind
                    (fn-native-admin-moderate-plan words argv))
                   :remove-group))
       (not (equal (fn-native-admin-result-kind
                    (fn-native-admin-moderate-plan words argv))
                   :set-bp-boundary))
       (not (equal (fn-native-admin-result-kind
                    (fn-native-admin-describe-plan words argv))
                   :create-group))
       (not (equal (fn-native-admin-result-kind
                    (fn-native-admin-describe-plan words argv))
                   :remove-group))
       (not (equal (fn-native-admin-result-kind
                    (fn-native-admin-describe-plan words argv))
                   :set-bp-boundary))
       (not (equal (fn-native-admin-result-kind
                    (fn-native-admin-motd-plan words argv))
                   :create-group))
       (not (equal (fn-native-admin-result-kind
                    (fn-native-admin-motd-plan words argv))
                   :remove-group))
       (not (equal (fn-native-admin-result-kind
                    (fn-native-admin-motd-plan words argv))
                   :set-bp-boundary))
       (not (equal (fn-native-admin-result-kind
                    (fn-native-admin-access-plan words argv))
                   :create-group))
       (not (equal (fn-native-admin-result-kind
                    (fn-native-admin-access-plan words argv))
                   :remove-group))
       (not (equal (fn-native-admin-result-kind
                    (fn-native-admin-access-plan words argv))
                   :set-bp-boundary))
       (not (equal (caddr (fn-native-admin-control-plan words argv))
                   :set-bp-boundary))
       (not (equal (caddr (fn-native-admin-moderate-plan words argv))
                   :set-bp-boundary))
       (not (equal (caddr (fn-native-admin-describe-plan words argv))
                   :set-bp-boundary))
       (not (equal (caddr (fn-native-admin-motd-plan words argv))
                   :set-bp-boundary))
       (not (equal (caddr (fn-native-admin-access-plan words argv))
                   :set-bp-boundary)))
  :hints (("Goal" :in-theory (enable fn-native-admin-result-kind
                                     fn-native-admin-result)))))

;; The peer-extend arm, closed: the theorems below that open the plan
;; would otherwise open it at every one of its occurrences (404 openings,
;; 1.0 s of fn-native-admin-plan-group-name-is-a-group-name's 2.3 s; 0.65 s
;; of plan-of-set-bp-boundary's 1.06 s, which reads the kind as its caddr).
(local (defthm fn-native-admin-peer-extend-plan-neither-create-nor-retire
  (and (not (equal (fn-native-admin-result-kind
                    (fn-native-admin-peer-extend-plan words))
                   :create-group))
       (not (equal (fn-native-admin-result-kind
                    (fn-native-admin-peer-extend-plan words))
                   :remove-group))
       (not (equal (fn-native-admin-result-kind
                    (fn-native-admin-peer-extend-plan words))
                   :set-bp-boundary))
       (not (equal (caddr (fn-native-admin-peer-extend-plan words))
                   :set-bp-boundary)))
  :hints (("Goal" :in-theory (enable fn-native-admin-result-kind
                                     fn-native-admin-result)))))

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
; The argv words, closed: the plan's tests read the words and its results
; the argv, and these four rules relate them without re-expanding the map
; at every occurrence (16,000 expansions, 6.4 s REPL hbox, with the
; retention and peer-extend arms).
(local (defthm car-of-words
  (equal (car (fn-native-admin-words argv))
         (if (consp argv) (fn-record-octets-string (car argv)) nil))))
(local (defthm cdr-of-words
  (equal (cdr (fn-native-admin-words argv))
         (fn-native-admin-words (cdr argv)))))
(local (defthm consp-of-words
  (equal (consp (fn-native-admin-words argv)) (consp argv))))
(local (defthm len-of-words
  (equal (len (fn-native-admin-words argv)) (len argv))))
(defthm fn-native-admin-plan-group-name-is-a-group-name
  (implies (and (equal (fn-native-admin-result-status (fn-native-admin-plan argv)) :accepted)
                (member-equal (fn-native-admin-result-kind (fn-native-admin-plan argv))
                              '(:create-group :remove-group)))
           (fn-record-group-namep
            (fn-record-octets-string (fn-native-admin-result-name (fn-native-admin-plan argv)))))
  :hints (("Goal" :in-theory (e/d (fn-native-admin-plan)
                                  ((tau-system) fn-native-admin-words
                                   fn-record-octets-string fn-cbor-octet-listp
                                   fn-digest-octetsp-implies-octet-listp
                                   fn-native-admin-carries-rows
                                   fn-native-admin-carries-hexp subsetp-equal
                                   fn-native-admin-retention-days
                                   fn-native-admin-peer-plan fn-record-group-namep
                                   fn-path-identityp fn-native-admin-decimalp
                                   fn-native-admin-decimal-value fn-native-admin-argvp
                                   fn-native-admin-bp-boundary-split
                                   fn-native-admin-bp-boundary-rows
                                   fn-native-admin-bp-boundary-plan
                                   fn-native-admin-control-plan
                                   fn-native-admin-moderate-plan
                                   fn-native-admin-describe-plan
                                   fn-native-admin-motd-plan
                                   fn-native-admin-access-plan
                                   fn-native-admin-peer-extend-plan))
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
       (member-equal (fn-native-admin-result-kind result)
                     '(:list-peers :list-control :list-accounts))
       t))

;; `control list': one line per grant row of the replayed configuration,
;; "grant PRINCIPAL VERB NAMESPACE", in row order.
;; Executes by a loop (lane peer-list-depth): the grant table is operator
;; data with no row cap (D27), so the recursion took one control-stack frame
;; per grant.  The :logic is the recursion, unchanged; the :exec folds the
;; reversed rows (fn-ag-rev-onto) from the left with the same step.
(defun fn-native-admin-control-report-loop (rev acc)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp rev)
      (fn-native-admin-control-report-loop
       (cdr rev)
       (append (fn-record-string-octets "grant ")
               (fn-record-string-octets (fn-cfg-row-b (car rev)))
               (list 32)
               (fn-record-string-octets (fn-cfg-row-c (car rev)))
               (list 32)
               (fn-record-string-octets (fn-cfg-row-a (car rev)))
               (list 10)
               acc))
    acc))

(defun fn-native-admin-control-report (rows)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp rows)
           (append (fn-record-string-octets "grant ")
                   (fn-record-string-octets (fn-cfg-row-b (car rows)))
                   (list 32)
                   (fn-record-string-octets (fn-cfg-row-c (car rows)))
                   (list 32)
                   (fn-record-string-octets (fn-cfg-row-a (car rows)))
                   (list 10)
                   (fn-native-admin-control-report (cdr rows)))
         nil)
       :exec (fn-native-admin-control-report-loop (fn-ag-rev-onto rows nil) nil)))

(local
 (defthm fn-native-admin-control-report-loop-of-rev-onto
   (equal (fn-native-admin-control-report-loop (fn-ag-rev-onto rows zs) nil)
          (fn-native-admin-control-report-loop
           zs (fn-native-admin-control-report rows)))
   :hints (("Goal" :induct (fn-ag-rev-onto rows zs)
                   :in-theory (union-theories
                               '(fn-native-admin-control-report-loop
                                 fn-native-admin-control-report fn-ag-rev-onto
                                 car-cons cdr-cons)
                               (theory 'minimal-theory))))))

(verify-guards fn-native-admin-control-report-loop)

(verify-guards fn-native-admin-control-report
  :hints (("Goal" :in-theory (union-theories
                              '(fn-native-admin-control-report
                                fn-native-admin-control-report-loop)
                              (union-theories (theory 'minimal-theory)
                                              (executable-counterpart-theory :here)))
                  :use ((:instance fn-native-admin-control-report-loop-of-rev-onto
                                   (zs nil))))))

;; `control list' lists exactly when the configuration holds a grant row:
;; the report is empty only over no authority row (qual-e747dbcc A3 printed
;; nothing over a durable grant).
(defthm fn-native-admin-control-report-empty-iff-no-rows
  (iff (consp (fn-native-admin-control-report rows))
       (consp rows))
  :hints (("Goal" :expand ((fn-native-admin-control-report rows)))))

;; The status-path report kind an accepted query plan names: the live owner's
;; FNLS request and the offline report (books/native-live-status.lisp
;; fn-nls-report) take it, so the host names no kind of its own.
(defun fn-native-admin-result-report-kind (plan)
  (declare (xargs :guard t))
  (cond ((equal (fn-native-admin-result-kind plan) :list-control) :control)
        ((equal (fn-native-admin-result-kind plan) :list-accounts) :accounts)
        (t :peers)))

;; The report a query plan asks for, over a replayed configuration value.
(defun fn-native-admin-query-report (plan value)
  (declare (xargs :guard t))
  (cond ((equal (fn-native-admin-result-kind plan) :list-control)
         (fn-native-admin-control-report (fn-cfg-authorities value)))
        (t (fn-native-admin-peer-budget-report (fn-cfg-peers value)))))


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
                                  ((tau-system) fn-native-admin-peer-plan fn-native-admin-bp-boundary-plan
                                   fn-record-octets-string fn-cbor-octet-listp
                                   fn-digest-octetsp-implies-octet-listp
                                   fn-record-group-namep fn-native-admin-decimalp
                                   fn-native-admin-decimal-value fn-native-admin-argvp
                                   fn-native-admin-words
                                   fn-native-admin-control-plan
                                   fn-native-admin-moderate-plan
                                   fn-native-admin-describe-plan
                                   fn-native-admin-motd-plan
                                   fn-native-admin-access-plan
                                   fn-native-admin-peer-extend-plan))
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

; The stopped node's record stamp (PRF-378, PRF-379): the host's two
; readings, both MILLISECONDS (the owner clock's unit, the record stamp's
; unit), and whether the wall reading was usable (host/native/io.lisp
; fnn-owner-wall-milliseconds's second value, which fnn-admin-clock-plan
; used to drop, stamping every record with a wall claim).  Without a wall
; the stamp claims none and carries the zero wall, so no decision reads an
; instant from it (books/accounts.lisp fn-acct-offline-invite-refusal).
; The configuration-record codec, not raw Lisp, decides whether the
; observation fits its representation.
(defun fn-native-admin-clock-observation (monotonic wall has-wall)
  (declare (xargs :guard t))
  (let ((stamp (fn-clock-observation monotonic (if has-wall wall 0) 0
                                     has-wall)))
    (if (fn-cfg-stampp stamp)
        (fn-native-admin-clock-result :accepted nil stamp)
      (fn-native-admin-clock-result :refused :clock-unrepresentable nil))))

; KEYSTONE (PRF-379).  An accepted stamp claims a wall exactly when the
; host read one, and then its record-stamp reading's upper end is the
; reading itself, in milliseconds; without one it has no upper end.
(defthm fn-native-admin-clock-observation-keeps-the-wall-claim
  (let ((result (fn-native-admin-clock-observation monotonic wall has-wall)))
    (implies (equal (fn-native-admin-clock-status result) :accepted)
             (and (fn-cfg-stampp (fn-native-admin-clock-stamp result))
                  (iff (fn-clock-has-wall (fn-native-admin-clock-stamp result))
                       has-wall)
                  (equal (fn-clock-reading-latest-milliseconds
                          (fn-clock-reading *fn-clock-record-stamp-unit*
                                            (fn-native-admin-clock-stamp result)))
                         (if has-wall wall nil)))))
  :hints (("Goal" :in-theory (enable fn-cfg-stampp fn-clock-observationp
                                     fn-clock-timep
                                     fn-clock-reading-latest-milliseconds
                                     fn-clock-reading fn-clock-readingp
                                     fn-clock-reading-unit
                                     fn-clock-reading-observation))))

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

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-native-admin-append-record-loop (records record acc)
  (declare (xargs :guard (true-listp acc) :verify-guards nil))
  (if (consp records)
      (fn-native-admin-append-record-loop (cdr records) record (cons (car records) acc))
    (revappend acc (list record))))

(defun fn-native-admin-append-record (records record)
  "Total, one-record extension for the candidate replay.  The byte decoder
supplies proper record lists, but this boundary remains executable for a
malformed logical value and therefore does not make an unproved LISTP claim
to Common Lisp's guarded APPEND."
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp records)
           (cons (car records) (fn-native-admin-append-record (cdr records) record))
         (list record))
       :exec (fn-native-admin-append-record-loop records record nil)))

(local
 (defthm fn-native-admin-append-record-loop-is-revappend
   (equal (fn-native-admin-append-record-loop records record acc)
          (revappend acc (fn-native-admin-append-record records record)))
   :hints (("Goal" :induct (fn-native-admin-append-record-loop records record acc)
                   :in-theory (union-theories '(fn-native-admin-append-record-loop fn-native-admin-append-record revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-native-admin-append-record-loop)

(verify-guards fn-native-admin-append-record
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-native-admin-append-record)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-native-admin-append-record-loop-is-revappend (acc nil))))))


(defun fn-native-admin-publication-authorize
    (records frontier config-records record lock-owned observed-names
             max-generations)
  "Authorize this exact final configuration name once.  LOCK-OWNED and
OBSERVED-NAMES are raw physical observations.  ACL2 binds them to the record's
generation, the candidate replay/open check, the fixed filename, and the
shared immutable publication state before raw Lisp may execute an I/O action.
MAX-GENERATIONS is the operator's bound, the store profile's
`max-config-generations' (D27, PRF-102): a generation above it is refused
`:max-config-generations', so the namespace never outgrows the listing bound
recovery observes it under (`fn-nco-observe')."
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
                ((< (nfix max-generations) generation)
                 (fn-native-admin-publication-result
                  :refused :max-config-generations nil nil nil))
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
                 records frontier config-records record lock-owned observed-names
                 max-generations)))
    (and (implies (equal (fn-native-admin-publication-status result) :accepted)
                  lock-owned)
         (implies (fn-native-admin-publication-jpub result)
                  lock-owned)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-native-admin-publication-authorize)
                                  (fn-cnode-config-replay fn-native-admin-candidate-openp
                                   fn-native-admin-config-name fn-cfg-recordp)))))

;; KEYSTONE (D27, PRF-102: the writer refuses exactly past the operator's
;; bound).  An accepted publication names a natural generation within
;; MAX-GENERATIONS, the profile's `max-config-generations' the host reads
;; from the store it opened (host/native/admin.lisp `fnn-admin-authorize' ->
;; host/store-node-host.lisp `fn-store-cfg-native-admin-authorize', which
;; computes it with `fn-bs-profile-max-config-generations'); and a record
;; that every other gate admits is refused `:max-config-generations' exactly
;; when its generation is above that bound.  Generations are contiguous from
;; 1 (`fn-nco-canonical-contiguousp'), so the namespace after an accepted
;; publication holds GENERATION entries, which `fn-nco-observe' admits under
;; the same field (`fn-nco-observe-refuses-exactly-past-the-operator-bound').
(defthm fn-native-admin-publication-within-the-operator-bound
  (let ((result (fn-native-admin-publication-authorize
                 records frontier config-records record lock-owned observed-names
                 max-generations)))
    (implies (equal (fn-native-admin-publication-status result) :accepted)
             (and (natp (fn-native-admin-publication-generation result))
                  (<= (fn-native-admin-publication-generation result)
                      (nfix max-generations)))))
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
                                  ((tau-system) fn-native-admin-group-name-reservedp
                                   fn-record-octets-string fn-cbor-octet-listp
                                   fn-digest-octetsp-implies-octet-listp
                                   fn-native-admin-words fn-native-admin-argvp
                                   fn-native-admin-peer-plan fn-native-admin-peer-extend-plan
                                   fn-native-admin-bp-boundary-plan
                                   fn-native-admin-control-plan
                                   fn-native-admin-moderate-plan
                                   fn-native-admin-describe-plan
                                   fn-native-admin-motd-plan
                                   fn-native-admin-access-plan
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
                                  ((tau-system) fn-native-admin-group-name-reservedp
                                   fn-record-octets-string fn-cbor-octet-listp
                                   fn-digest-octetsp-implies-octet-listp
                                   fn-native-admin-words fn-native-admin-argvp
                                   fn-native-admin-peer-plan fn-native-admin-peer-extend-plan
                                   fn-native-admin-bp-boundary-plan
                                   fn-native-admin-control-plan
                                   fn-native-admin-moderate-plan
                                   fn-native-admin-describe-plan
                                   fn-native-admin-motd-plan
                                   fn-native-admin-access-plan
                                   fn-record-group-namep fn-path-identityp
                                   fn-native-admin-decimalp
                                   fn-native-admin-decimal-value
                                   fn-native-admin-result))
           :use ((:instance fn-native-admin-len-of-words)))))

