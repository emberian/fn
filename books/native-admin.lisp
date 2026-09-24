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

(defconst *fn-native-admin-max-arguments* 16)
(defconst *fn-native-admin-max-argument-octets* 512)
(defconst *fn-native-admin-config-name-width* 8)
(defconst *fn-native-admin-config-name-limit* 100000000)
(defconst *fn-native-admin-config-name-suffix* '(#\. #\c #\f #\g))

(local (defthm fn-native-admin-natural-digits-characters
  (character-listp (fn-bs-txn-natural-digits n))
  :hints (("Goal" :in-theory (enable fn-bs-txn-natural-digits
                                        fn-bs-txn-natural-digits-rev
                                        fn-bs-txn-reverse)))))

(local (defthm fn-native-admin-zeroes-characters
  (character-listp (fn-bs-txn-zeroes n))
  :hints (("Goal" :induct (fn-bs-txn-zeroes n)))) )

(local (defthm fn-native-admin-config-name-chars
  (character-listp
   (append (fn-bs-txn-zeroes n) (fn-bs-txn-natural-digits generation)
           *fn-native-admin-config-name-suffix*))
  :hints (("Goal" :use ((:instance fn-native-admin-zeroes-characters (n n))
                         (:instance fn-native-admin-natural-digits-characters
                                    (n generation)))))))

(defun fn-native-admin-argvp (argv)
  (declare (xargs :guard t))
  (if (consp argv)
      (and (consp (car argv))
           (<= (len (car argv)) *fn-native-admin-max-argument-octets*)
           (fn-record-ascii-octet-listp (car argv))
           (fn-native-admin-argvp (cdr argv)))
    (null argv)))

(defun fn-native-admin-words (argv)
  (declare (xargs :guard t))
  (if (consp argv)
      (cons (fn-record-octets-string (car argv))
            (fn-native-admin-words (cdr argv)))
    nil))

(defun fn-native-admin-digit-value (char)
  (declare (xargs :guard t))
  (if (characterp char)
      (let ((digit (char-code char)))
        (if (and (<= (char-code #\0) digit) (<= digit (char-code #\9)))
            (- digit (char-code #\0))
          -1))
    -1))

(defun fn-native-admin-decimal-value-aux (chars value)
  (declare (xargs :guard t))
  (if (consp chars)
      (let ((digit (fn-native-admin-digit-value (car chars))))
        (if (<= 0 digit)
            (fn-native-admin-decimal-value-aux
             (cdr chars) (+ (* 10 (nfix value)) digit))
          -1))
    (nfix value)))

(defun fn-native-admin-decimal-value (chars)
  (declare (xargs :guard t))
  (fn-native-admin-decimal-value-aux chars 0))

(defun fn-native-admin-decimalp (text)
  (declare (xargs :guard t))
  (if (not (stringp text)) nil
    (let ((chars (coerce text 'list)))
      (and (consp chars)
           (not (and (consp (cdr chars)) (equal (car chars) #\0)))
           (<= 0 (fn-native-admin-decimal-value chars))
           (fn-record-uint32p (fn-native-admin-decimal-value chars))))))

(defun fn-native-admin-result (status reason kind name capacity peer value)
  ; `value' is the second label of a two-label delta: the policy id of
  ; `policy set SLOT VALUE' (`name' carries the slot).  Every other kind
  ; leaves it nil.
  (declare (xargs :guard t))
  (list status reason kind name capacity peer value))

(defun fn-native-admin-result-status (result)
  (declare (xargs :guard t))
  (mbe :logic (car result) :exec (fn-ag-car result)))
(defun fn-native-admin-result-reason (result)
  (declare (xargs :guard t))
  (mbe :logic (cadr result) :exec (fn-ag-car (fn-ag-cdr result))))
(defun fn-native-admin-result-kind (result)
  (declare (xargs :guard t))
  (mbe :logic (caddr result) :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr result)))))
(defun fn-native-admin-result-name (result)
  (declare (xargs :guard t))
  (mbe :logic (cadddr result)
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr result))))))
(defun fn-native-admin-result-capacity (result) (declare (xargs :guard t))
  (mbe :logic (car (cddddr result))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr result)))))))
(defun fn-native-admin-result-peer (result) (declare (xargs :guard t))
  (mbe :logic (cadr (cddddr result))
       :exec (fn-ag-car
              (fn-ag-cdr
               (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr result))))))))
(defun fn-native-admin-result-value (result) (declare (xargs :guard t))
  (mbe :logic (caddr (cddddr result))
       :exec (fn-ag-car
              (fn-ag-cdr
               (fn-ag-cdr
                (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr result)))))))))

(defun fn-native-admin-peer-plan-base (words)
  "Build the complete peer record in ACL2; raw Lisp receives no field defaults.

The explicit grammar carries auth-kind/auth-value.  The older grammar is
decoded as source-address for durable command compatibility."
  (declare (xargs :guard t))
  ; The vector is decided before any `nth' of it.  `fn-native-admin-plan' only
  ; ever hands over `fn-native-admin-words' of a recognized argv, which is a
  ; proper list; the raw boundary stays total, and an improper vector is the
  ; same :syntax refusal it has been since e34523a1.  Leading with the test is
  ; what lets `nth' run under a verified guard: the conjunct this replaces sat
  ; below the `nth' calls in the `let*', so the guard conjecture asked for
  ; (implies (equal (len words) 13) (true-listp words)), which is false.
  (if (not (true-listp words))
      (fn-native-admin-result :refused :syntax nil nil 0 nil nil)
  (let* ((count (len words))
         (v2p (and (member-equal count '(13 16))
                   (member-equal (nth 8 words) '("source-address" "principal"))))
         (explicitp (or v2p (member-equal count '(11 14))))
         (auth-kind (if explicitp (nth 8 words) "source-address"))
         (auth-value (if explicitp (nth 9 words) (nth 8 words)))
         (profile (if v2p (nth 10 words) "-"))
         (allow-clear (if v2p (nth 11 words) "false"))
         (streaming (if v2p (nth 12 words)
                      (if explicitp (nth 10 words) (nth 9 words))))
         (security-index (if v2p 13 (if explicitp 11 10))))
    (if (and (member-equal count '(10 11 13 14 16))
             (equal (car words) "peer")
             (equal (cadr words) "add")
             (fn-native-admin-decimalp (nth 5 words))
             (<= 1 (fn-native-admin-decimal-value
                    (coerce (nth 5 words) 'list)))
             (<= (fn-native-admin-decimal-value
                  (coerce (nth 5 words) 'list)) 65535)
             (member-equal auth-kind '("source-address" "principal"))
             (if (equal auth-kind "source-address")
                 (not (equal (fn-native-config-ipv4-address
                              (fn-record-string-octets auth-value)) :bad))
               (and (equal (len (fn-record-string-octets auth-value)) 64)
                    (fn-id-hex-listp (fn-record-string-octets auth-value))))
             (member-equal streaming '("true" "false"))
             (or (not v2p)
                 (and (not (equal profile "-"))
                      (member-equal allow-clear '("true" "false"))))
             (or (equal count 10) (equal count 11)
                 (and v2p (equal count 13))
                 (and (member-equal (nth security-index words)
                                    '("clear" "implicit" "starttls"))
                      (if (equal (nth security-index words) "clear")
                          (and (equal (nth (+ 1 security-index) words) "-")
                               (equal (nth (+ 2 security-index) words) "-"))
                        (and (not (equal (nth (+ 1 security-index) words) "-"))
                             (not (equal (nth (+ 2 security-index) words) "-")))))))
        (let* ((inbound (if (equal (nth 6 words) "-") nil
                          (list (nth 6 words) *fn-record-max-payload* 16)))
               (outbound (if (equal (nth 7 words) "-") nil
                           (append (list (nth 7 words) (equal streaming "true")
                                         1024 1000)
                                   (if v2p
                                       (list (list :authinfo profile
                                                   (equal allow-clear "true")))
                                     nil))))
               (peer (fn-cfg-peer-make
                      (nth 2 words) (nth 3 words)
                      (list :nntp 1 (nth 4 words)
                            (fn-native-admin-decimal-value
                             (coerce (nth 5 words) 'list))
                            (if (or (equal count 10) (equal count 11)
                                    (and v2p (equal count 13))
                                    (equal (nth security-index words) "clear"))
                                '(:clear)
                              (list :tls
                                    (if (equal (nth security-index words) "implicit")
                                        :implicit :starttls)
                                    (nth (+ 1 security-index) words)
                                    (nth (+ 2 security-index) words))))
                      inbound outbound
                      (list (if (equal auth-kind "principal")
                                :principal :source-address)
                            auth-value))))
          (if (fn-cfg-peerp peer)
              (fn-native-admin-result :accepted nil :set-peer nil 0 peer nil)
            (fn-native-admin-result :refused :peer-record nil nil 0 nil nil)))
      (fn-native-admin-result :refused :syntax nil nil 0 nil nil)))))

;; D23: `peer add ... carries HEX [HEX ...]'.  The words before `carries'
;; are the record grammar above; each HEX after it is a principal, 64
;; lowercase hexadecimal characters, and becomes one row
;; (name "carries-principal" HEX 0) of the peer's group, the carried-source
;; list books/peer-authored-accept.lisp fn-pa-peer-carried-sources reads.
;; The rows ride in the result's value slot; a peer without `carries' is the
;; base plan unchanged.
(defun fn-native-admin-carries-hexp (x)
  (declare (xargs :guard t))
  (and (stringp x)
       (equal (length x) 64)
       (subsetp-equal (coerce x 'list) (coerce "0123456789abcdef" 'list))))

(defun fn-native-admin-carries-rows (name hexes)
  (declare (xargs :guard t))
  (if (consp hexes)
      (let ((rest (fn-native-admin-carries-rows name (cdr hexes))))
        (if (and (fn-native-admin-carries-hexp (car hexes)) (listp rest))
            (cons (list name "carries-principal" (car hexes) 0) rest)
          :bad))
    nil))

(defun fn-native-admin-before-carries (words)
  (declare (xargs :guard t))
  (if (or (atom words) (equal (car words) "carries")) nil
    (cons (car words) (fn-native-admin-before-carries (cdr words)))))

(defun fn-native-admin-peer-plan (words)
  (declare (xargs :guard t))
  (let ((tail (member-equal "carries" (if (true-listp words) words nil))))
    (if (not tail)
        (fn-native-admin-peer-plan-base words)
      (let* ((base (fn-native-admin-peer-plan-base
                    (fn-native-admin-before-carries words)))
             (rows (fn-native-admin-carries-rows (nth 2 words) (cdr tail))))
        (cond ((not (equal (fn-native-admin-result-status base) :accepted)) base)
              ((or (not (consp rows)) (equal rows :bad))
               (fn-native-admin-result :refused :carries nil nil 0 nil nil))
              (t (fn-native-admin-result
                  :accepted nil :set-peer nil 0
                  (fn-native-admin-result-peer base) rows)))))))

(defun fn-native-admin-set-peer-delta (plan)
  (declare (xargs :guard t))
  (let ((peer (fn-native-admin-result-peer plan))
        (rows (fn-native-admin-result-value plan)))
    (if (consp rows)
        (fn-cfg-set-peer (fn-cfg-peer-name peer)
                         (append (fn-cfg-peer-rows peer) rows))
      (fn-cfg-set-peer-delta peer))))

; A BP-only peer boundary is one durable :set-peer row group.  The profile is
; deliberately narrow: loopback IPv4, no translation, and every co-resident
; process in the originator set.  Its auth-principal value cannot be a SHA-256
; principal hex, so this row does not grant an NNTP peer login as a side effect.
; D23: the source EIDs the neighbour may carry, one row each.
(defun fn-native-admin-bp-carries-rows (name eids)
  (declare (xargs :guard t))
  (if (consp eids)
      (cons (fn-cfg-row-make name "bp-boundary-carries" (car eids) 0)
            (fn-native-admin-bp-carries-rows name (cdr eids)))
    nil))

; A carried EID is a configuration label with a BP scheme ("dtn:" or
; "ipn:"), so it cannot be confused with the decimal limits of the long form.
(defun fn-native-admin-bp-eid-wordp (word)
  (declare (xargs :guard t))
  (and (stringp word)
       (fn-cfg-labelp word)
       (<= 5 (length word))
       (let ((chars (coerce word 'list)))
         (or (equal (take 4 chars) '(#\d #\t #\n #\:))
             (equal (take 4 chars) '(#\i #\p #\n #\:))))))

(defun fn-native-admin-bp-carried-wordsp (words)
  (declare (xargs :guard t))
  (if (consp words)
      (and (fn-native-admin-bp-eid-wordp (car words))
           (true-listp (cdr words))
           (not (member-equal (car words) (cdr words)))
           (fn-native-admin-bp-carried-wordsp (cdr words)))
    (null words)))

; D23: the release-issuer EIDs whose receipts the neighbour may relay, one
; (NAME "bp-boundary-releases-for" EID 0) row each.  A separate row kind from
; the carried list: a carried source is not a release issuer.
(defun fn-native-admin-bp-releases-rows (name eids)
  (declare (xargs :guard t))
  (if (consp eids)
      (cons (fn-cfg-row-make name "bp-boundary-releases-for" (car eids) 0)
            (fn-native-admin-bp-releases-rows name (cdr eids)))
    nil))

(defun fn-native-admin-bp-list-keywordp (word)
  (declare (xargs :guard t))
  (or (equal word "carries") (equal word "releases-for")))

; The clauses after the base form: [carries EID ...] [releases-for EID ...],
; each list non-empty, in that order.  (mv ok carried releases).
(defun fn-native-admin-bp-before-releases (words)
  (declare (xargs :guard t))
  (if (or (atom words) (equal (car words) "releases-for"))
      nil
    (cons (car words) (fn-native-admin-bp-before-releases (cdr words)))))

(defun fn-native-admin-bp-list-clauses (tail)
  (declare (xargs :guard t))
  (let* ((tail (if (true-listp tail) tail nil))
         (rel (member-equal "releases-for" tail))
         (head (fn-native-admin-bp-before-releases tail)))
    (cond ((not (or (null head)
                    (and (equal (car head) "carries")
                         (consp (cdr head))
                         (fn-native-admin-bp-carried-wordsp (cdr head)))))
           (mv nil nil nil))
          ((not (or (null rel)
                    (and (consp (cdr rel))
                         (fn-native-admin-bp-carried-wordsp (cdr rel)))))
           (mv nil nil nil))
          (t (mv t (cdr head) (cdr rel))))))

; `bp-boundary add NAME PATH BP-EID PORT [INBOUND MAX-OCTETS MAX-INFLIGHT]
; [carries EID ...] [releases-for EID ...]': the base form's length (6 or 9),
; the carried list and the release list.  A malformed clause gives base 0,
; which the plan refuses.
(defun fn-native-admin-bp-boundary-split (words)
  (declare (xargs :guard t))
  (let ((words (if (true-listp words) words nil)))
    (cond ((and (< 6 (len words))
                (fn-native-admin-bp-list-keywordp (nth 6 words)))
           (mv-let (ok carried releases)
             (fn-native-admin-bp-list-clauses (nthcdr 6 words))
             (if ok (mv 6 carried releases) (mv 0 nil nil))))
          ((and (< 9 (len words))
                (fn-native-admin-bp-list-keywordp (nth 9 words)))
           (mv-let (ok carried releases)
             (fn-native-admin-bp-list-clauses (nthcdr 9 words))
             (if ok (mv 9 carried releases) (mv 0 nil nil))))
          (t (mv (len words) nil nil)))))

(defun fn-native-admin-bp-boundary-rows
  (name path eid port inbound max-octets max-inflight carried releases)
  (declare (xargs :guard t))
  (append
   (list (fn-cfg-row-make name "path-identity" path 0)
        (fn-cfg-row-make name "transport-bp" eid 0)
        (fn-cfg-row-make name "auth-principal" "bp-only-no-nntp-principal" 0))
   (if inbound
       (list (fn-cfg-row-make name "inbound-groups" inbound max-octets)
             (fn-cfg-row-make name "inbound-inflight" "" max-inflight))
     nil)
   (list
        (fn-cfg-row-make name "bp-trust" "network" 0)
        (fn-cfg-row-make name "bp-boundary-listener" "127.0.0.1" port)
        (fn-cfg-row-make name "bp-boundary-source" "127.0.0.1" 0)
        (fn-cfg-row-make name "bp-boundary-translation" "none" 0)
        (fn-cfg-row-make name "bp-boundary-originators"
                         "all-co-resident" 0))
   (fn-native-admin-bp-carries-rows name carried)
   (fn-native-admin-bp-releases-rows name releases)))

(defun fn-native-admin-bp-boundary-plan (words)
  (declare (xargs :guard t))
  (mv-let (base carried releases) (fn-native-admin-bp-boundary-split words)
  (if (and (true-listp words) (member-equal base '(6 9))
           (equal (nth 0 words) "bp-boundary")
           (equal (nth 1 words) "add")
           (fn-cfg-labelp (nth 2 words))
           (not (equal (nth 2 words) ""))
           (fn-path-identityp (fn-record-string-octets (nth 3 words)))
           (fn-cfg-labelp (nth 4 words))
           (fn-native-admin-decimalp (nth 5 words))
           (<= 1 (fn-native-admin-decimal-value
                  (coerce (nth 5 words) 'list)))
           (<= (fn-native-admin-decimal-value
                (coerce (nth 5 words) 'list)) 65535)
           (or (equal base 6)
               (and (fn-cfg-wildmatp (nth 6 words))
                    (fn-native-admin-decimalp (nth 7 words))
                    (<= 1 (fn-native-admin-decimal-value
                           (coerce (nth 7 words) 'list)))
                    (<= (fn-native-admin-decimal-value
                         (coerce (nth 7 words) 'list)) *fn-record-max-payload*)
                    (fn-native-admin-decimalp (nth 8 words))
                    (<= 1 (fn-native-admin-decimal-value
                           (coerce (nth 8 words) 'list)))
                    (<= (fn-native-admin-decimal-value
                         (coerce (nth 8 words) 'list)) *fn-record-max-payload*))))
      (let* ((name (nth 2 words))
             (rows (fn-native-admin-bp-boundary-rows
                    name (nth 3 words) (nth 4 words)
                    (fn-native-admin-decimal-value
                     (coerce (nth 5 words) 'list))
                    (if (equal base 9) (nth 6 words) nil)
                    (if (equal base 9)
                        (fn-native-admin-decimal-value
                         (coerce (nth 7 words) 'list)) 0)
                    (if (equal base 9)
                        (fn-native-admin-decimal-value
                         (coerce (nth 8 words) 'list)) 0)
                    carried releases)))
        (fn-native-admin-result :accepted nil :set-bp-boundary
                                (fn-record-string-octets name) 0 nil rows))
    (fn-native-admin-result :refused :bp-boundary nil nil 0 nil nil))))

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
            ((equal kind :set-bp-boundary)
             (list (fn-cfg-set-peer name
                                    (fn-native-admin-result-value plan))))
            ((equal kind :remove-peer)
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
(defthm fn-native-admin-peer-plan-base-kind
  (member-equal (fn-native-admin-result-kind (fn-native-admin-peer-plan-base words))
                '(:set-peer nil))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-native-admin-peer-plan-base)
                                  (fn-cfg-peerp fn-cfg-peer-make nth len
                                   fn-native-admin-decimalp fn-native-admin-decimal-value
                                   fn-native-config-ipv4-address fn-id-hex-listp)))))
(defthm fn-native-admin-peer-plan-kind
  (member-equal (fn-native-admin-result-kind (fn-native-admin-peer-plan words))
                '(:set-peer nil))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-native-admin-peer-plan
                                   fn-native-admin-result
                                   fn-native-admin-result-kind)
                                  (fn-native-admin-peer-plan-base
                                   fn-native-admin-carries-rows
                                   fn-native-admin-before-carries))
           :use ((:instance fn-native-admin-peer-plan-base-kind)
                 (:instance fn-native-admin-peer-plan-base-kind
                  (words (fn-native-admin-before-carries words)))))))
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
                                   fn-native-admin-bp-boundary-rows))
           :use ((:instance fn-native-admin-peer-plan-kind
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
  :hints (("Goal" :in-theory (enable fn-record-group-namep fn-cfg-labelp
                                     fn-record-nonempty-at-mostp)))))
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

; -----------------------------------------------------------------------------
; `peer list': the public projection of the durable peer table.
;
; The fields are the ones `peer add' takes, in that order, so an operator can
; read a record back and see the command that would write it again.  Raw Lisp
; supplies the configuration value's peer rows and writes these octets to a
; descriptor; it renders no field, formats no number, and supplies no name for
; an absent half.  Wildmats and identities are printed as the configuration
; holds them (books/peer-config.lisp is the codec); nothing here re-derives a
; transport, an auth kind or a security mode.

(defconst *fn-native-admin-peer-absent* (list 45)) ; "-"

(defun fn-native-admin-peer-label-octets (text)
  "One configuration label as octets, or `-' when the slot holds no label."
  (declare (xargs :guard t))
  (if (and (stringp text) (consp (fn-record-string-octets text)))
      (fn-record-string-octets text)
    *fn-native-admin-peer-absent*))

(defun fn-native-admin-peer-security-octets (security)
  (declare (xargs :guard t))
  (cond ((equal security '(:clear)) (fn-record-string-octets "clear"))
        ((equal (fn-ag-car (fn-ag-cdr security)) :implicit)
         (fn-record-string-octets "implicit"))
        ((equal (fn-ag-car (fn-ag-cdr security)) :starttls)
         (fn-record-string-octets "starttls"))
        (t *fn-native-admin-peer-absent*)))

(defun fn-native-admin-peer-transport-octets (transport)
  "address, port and security for one peer's transport half.

The three transport shapes `fn-cfg-peer-transportp' admits are the three
arms here: the explicit NNTP endpoint with its security mode, the legacy
durable NNTP endpoint (explicit cleartext), and a BP endpoint, whose EID is
the address and which has no port or TLS mode of its own."
  (declare (xargs :guard t))
  (let ((kind (fn-ag-car transport)))
    (cond
     ((and (equal kind :nntp) (equal (len transport) 5))
      (append (fn-record-string-octets " address=")
              (fn-native-admin-peer-label-octets
               (fn-ag-car (fn-ag-cdr (fn-ag-cdr transport))))
              (fn-record-string-octets " port=")
              (fn-nntp-decimal-field
               (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr transport)))))
              (fn-record-string-octets " security=")
              (fn-native-admin-peer-security-octets
               (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                                                 (fn-ag-cdr transport))))))))
     ((and (equal kind :nntp) (equal (len transport) 3))
      (append (fn-record-string-octets " address=")
              (fn-native-admin-peer-label-octets (fn-ag-car (fn-ag-cdr transport)))
              (fn-record-string-octets " port=")
              (fn-nntp-decimal-field
               (fn-ag-car (fn-ag-cdr (fn-ag-cdr transport))))
              (fn-record-string-octets " security=clear")))
     ((equal kind :bp)
      (append (fn-record-string-octets " address=")
              (fn-native-admin-peer-label-octets (fn-ag-car (fn-ag-cdr transport)))
              (fn-record-string-octets " port=0 security=-")))
     (t (fn-record-string-octets " address=- port=0 security=-")))))

(defun fn-native-admin-peer-auth-octets (auth)
  (declare (xargs :guard t))
  (append (fn-record-string-octets " auth=")
          (if (equal (fn-ag-car auth) :principal)
              (fn-record-string-octets "principal:")
            (fn-record-string-octets "source-address:"))
          (fn-native-admin-peer-label-octets (fn-ag-car (fn-ag-cdr auth)))))

(defun fn-native-admin-peer-row-octets (p)
  (declare (xargs :guard t))
  (append (fn-native-admin-peer-label-octets (fn-cfg-peer-name p))
          (fn-record-string-octets " path-identity=")
          (fn-native-admin-peer-label-octets (fn-cfg-peer-path-identity p))
          (fn-native-admin-peer-transport-octets (fn-cfg-peer-transport p))
          (fn-record-string-octets " inbound=")
          (if (fn-cfg-peer-inbound p)
              (fn-native-admin-peer-label-octets (fn-cfg-peer-inbound-groups p))
            *fn-native-admin-peer-absent*)
          (fn-record-string-octets " outbound=")
          (if (fn-cfg-peer-outbound p)
              (fn-native-admin-peer-label-octets (fn-cfg-peer-outbound-groups p))
            *fn-native-admin-peer-absent*)
          (fn-native-admin-peer-auth-octets (fn-cfg-peer-auth p))
          (list 10)))

(defun fn-native-admin-peer-report-rows (names peers)
  (declare (xargs :guard t))
  (if (consp names)
      (let ((p (fn-cfg-peer-find (car names) peers)))
        (append (if p (fn-native-admin-peer-row-octets p) nil)
                (fn-native-admin-peer-report-rows (cdr names) peers)))
    nil))

(defun fn-native-admin-peer-report (peers)
  "The `peer list' report for a configuration value's peer rows.

The enumeration is `fn-cfg-peer-names' and each record is `fn-cfg-peer-find';
a row group that denotes no well-formed record contributes no line rather
than a partially rendered one."
  (declare (xargs :guard t))
  (fn-native-admin-peer-report-rows (fn-cfg-peer-names peers) peers))

; Config record names are a fixed-width namespace.  The digit renderer is the
; existing ACL2 byte-store renderer; no host formatter derives a durable name.
(defun fn-native-admin-config-name-bounded (generation)
  (declare (xargs :guard (and (natp generation)
                              (< generation *fn-native-admin-config-name-limit*))
                  :verify-guards nil))
  (coerce
   (append (fn-bs-txn-zeroes
            (nfix (- *fn-native-admin-config-name-width*
                     (len (fn-bs-txn-natural-digits generation)))))
           (fn-bs-txn-natural-digits generation)
           *fn-native-admin-config-name-suffix*)
   'string))

(verify-guards fn-native-admin-config-name-bounded
  :hints (("Goal"
           :use ((:instance fn-native-admin-config-name-chars
                            (n (nfix (- *fn-native-admin-config-name-width*
                                        (len (fn-bs-txn-natural-digits generation)))))
                            (generation generation))))))

(defun fn-native-admin-config-name (generation)
  (declare (xargs :guard t))
  (if (and (natp generation)
           (< generation *fn-native-admin-config-name-limit*))
      (fn-native-admin-config-name-bounded generation)
    nil))

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

(defthm fn-native-admin-config-name-of-one
  (equal (fn-native-admin-config-name 1) "00000001.cfg"))

(defthm fn-native-admin-config-name-refuses-overflow
  (equal (fn-native-admin-config-name *fn-native-admin-config-name-limit*) nil))

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

