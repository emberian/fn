;; fn: the peer and bp-boundary parsers of the native administrative command,
;; and the `peer list' codec.
;
; Split out of books/native-admin.lisp (planning/audit-2026-09-25-twins-fanin.md
; packet 4): `peer add', `bp-boundary add' and the `peer list' rendering and
; decoding certify beside the group-name rules and the plan instead of in front
; of them.  books/native-admin.lisp includes this book; fn-native-admin-plan
; dispatches to the parsers below.  The definitions and theorems are the ones
; books/native-admin.lisp had, unchanged; the theorems that read
; fn-native-admin-plan stayed there.

(in-package "ACL2")
(include-book "native-admin-shape")
(include-book "peer-config")
(include-book "native-config")
(include-book "identity")
(include-book "bp-eid-shape")
; fn-nntp-decimal-field (the peer port and capacity words).
(include-book "nntp-syntax")
; PRF-099: the opaque-carriage budget rows and the row extension.
(include-book "peer-carriage-rows")

; A decimal word is a string, which is all the guards below need of it; with
; this the guard proofs keep the decimal recognizer and its value closed.
(local (defthm fn-native-admin-decimalp-is-a-string
  (implies (fn-native-admin-decimalp text) (stringp text))
  :rule-classes :forward-chaining))

(defun fn-native-admin-peer-plan-base (words)
  "Build the complete peer record in ACL2; raw Lisp receives no field defaults.

The explicit grammar carries auth-kind/auth-value.  The older grammar is
decoded as source-address for durable command compatibility."
  (declare (xargs :guard t
                  :guard-hints
                  (("Goal" :in-theory (disable fn-native-admin-decimalp
                                               fn-native-admin-decimal-value)))))
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

;; PRF-099: a boundary's carried list and opaque-carriage budget change by
;; request, never by a longer argv (the argv bound is a per-request work
;; bound, D27):
;;
;;   peer carries NAME HEX [HEX ...]   ; adds principals to NAME's list
;;   peer budget NAME OCTETS COUNT     ; sets NAME's budget
;;
;; Both are :extend-peer plans: the rows ride in the value slot and the
;; delta is built over the live peer table (books/native-admin.lisp
;; fn-native-admin-plan-deltas-over, books/peer-carriage-rows.lisp
;; fn-pcb-extend-delta), so a request for a peer that does not exist is
;; refused there.  OCTETS is the operator's octet budget, at most twenty
;; decimal digits (a work bound on the word); it is kept in whole Store
;; charge pages, floor(OCTETS / 4096), which must fit the row's uint32, the
;; width of the Store's own charge capacity.  COUNT is a uint32.
(defun fn-native-admin-octets-wordp (text)
  (declare (xargs :guard t))
  (and (stringp text)
       (let ((chars (coerce text 'list)))
         (and (consp chars)
              (<= (len chars) 20)
              (not (and (consp (cdr chars)) (equal (car chars) #\0)))
              (<= 0 (fn-native-admin-decimal-value chars))))))

(defun fn-native-admin-budget-pages (octets)
  (declare (xargs :guard t))
  (floor (nfix octets) *fn-id-charge-page-octets*))

;; PRF-100: `peer pull NAME SECONDS' sets the NEWNEWS pull interval
;; (books/peer-pull.lisp); 0 stops pulling.  SECONDS is a uint32.  PRF-165:
;; `peer pull NAME SECONDS ROUNDS' also sets how many consecutive complete
;; rounds an id the peer lists but answers 430 holds the cursor; ROUNDS is a
;; positive uint32.  The rows, or nil for words of any other shape.  Kept
;; closed so the admin plan's case analysis does not grow with it.
(defun fn-native-admin-pull-rows (words)
  (declare (xargs :guard (true-listp words)
                  :guard-hints
                  (("Goal" :in-theory (disable fn-native-admin-decimalp
                                               fn-native-admin-decimal-value)))))
  (if (and (or (equal (len words) 4)
               (and (equal (len words) 5)
                    (fn-native-admin-decimalp (nth 4 words))
                    (posp (fn-native-admin-decimal-value
                           (coerce (nth 4 words) 'list)))))
           (stringp (nth 2 words))
           (fn-native-admin-decimalp (nth 3 words)))
      (cons (fn-cfg-row-make (nth 2 words) *fn-pcb-pull-interval-slot* ""
                             (fn-native-admin-decimal-value
                              (coerce (nth 3 words) 'list)))
            (if (equal (len words) 5)
                (list (fn-cfg-row-make (nth 2 words)
                                       *fn-pcb-pull-unavailable-slot* ""
                                       (fn-native-admin-decimal-value
                                        (coerce (nth 4 words) 'list))))
              nil))
    nil))

(in-theory (disable fn-native-admin-pull-rows))

(defun fn-native-admin-peer-extend-plan (words)
  (declare (xargs :guard t))
  (let ((words (if (true-listp words) words nil)))
    (cond
     ((not (and (<= 4 (len words))
                (fn-cfg-labelp (nth 2 words))
                (not (equal (nth 2 words) ""))))
      (fn-native-admin-result :refused :syntax nil nil 0 nil nil))
     ((equal (nth 1 words) "budget")
      (if (and (equal (len words) 5)
               (fn-native-admin-octets-wordp (nth 3 words))
               (fn-record-uint32p
                (fn-native-admin-budget-pages
                 (fn-native-admin-decimal-value (coerce (nth 3 words) 'list))))
               (fn-native-admin-decimalp (nth 4 words)))
          (fn-native-admin-result
           :accepted nil :extend-peer
           (fn-record-string-octets (nth 2 words)) 0 nil
           (fn-pcb-budget-rows
            (nth 2 words)
            (fn-native-admin-budget-pages
             (fn-native-admin-decimal-value (coerce (nth 3 words) 'list)))
            (fn-native-admin-decimal-value (coerce (nth 4 words) 'list))))
        (fn-native-admin-result :refused :budget nil nil 0 nil nil)))
     ; PRF-100 / PRF-165: `peer pull NAME SECONDS [ROUNDS]'
     ; (`fn-native-admin-pull-rows').
     ((equal (nth 1 words) "pull")
      (let ((rows (fn-native-admin-pull-rows words)))
        (if (consp rows)
            (fn-native-admin-result
             :accepted nil :extend-peer
             (fn-record-string-octets (nth 2 words)) 0 nil rows)
          (fn-native-admin-result :refused :pull nil nil 0 nil nil))))
     ((equal (nth 1 words) "carries")
      (let ((rows (fn-native-admin-carries-rows (nth 2 words)
                                                (nthcdr 3 words))))
        (if (and (consp rows) (not (equal rows :bad)))
            (fn-native-admin-result
             :accepted nil :extend-peer
             (fn-record-string-octets (nth 2 words)) 0 nil rows)
          (fn-native-admin-result :refused :carries nil nil 0 nil nil))))
     (t (fn-native-admin-result :refused :syntax nil nil 0 nil nil)))))

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

; A carried or release EID has the shape above; its scheme prefix also keeps
; it from being confused with the decimal limits of the long form.
(defun fn-native-admin-bp-eid-wordp (word)
  (declare (xargs :guard t))
  (fn-bp-eid-shapep word))

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

; Signed receipts (lane signed-receipts): `receipt-signer HEX' names the
; 64-lowercase-hex hybrid principal whose signature on a receipt from this
; boundary's own EID releases (`fn-bpah-receipt-signer-enrolledp'); the flag
; `require-signed-receipts' makes receipts this boundary delivers release
; only by their own signature (`fn-bpah-require-signed-receiptsp').  Both
; come last, in that order.
(defun fn-native-admin-lower-hex-charsp (chars)
  (declare (xargs :guard t))
  (if (consp chars)
      (and (member (car chars) '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9
                                 #\a #\b #\c #\d #\e #\f))
           (fn-native-admin-lower-hex-charsp (cdr chars)))
    (null chars)))

(defun fn-native-admin-principal-hexp (word)
  (declare (xargs :guard t))
  (and (stringp word)
       (equal (length word) 64)
       (fn-native-admin-lower-hex-charsp (coerce word 'list))))

; (mv words signer requirep): the words before the two trailing options.
(defun fn-native-admin-bp-receipt-options (words)
  (declare (xargs :guard t))
  (let* ((words (if (true-listp words) words nil))
         (requirep (and (consp words)
                        (equal (car (last words)) "require-signed-receipts")))
         (w1 (if requirep (butlast words 1) words))
         (n (len w1))
         (signerp (and (<= 2 n)
                       (equal (nth (- n 2) w1) "receipt-signer")
                       (fn-native-admin-principal-hexp (nth (- n 1) w1)))))
    (mv (if signerp (butlast w1 2) w1)
        (if signerp (nth (- n 1) w1) nil)
        requirep)))

(defun fn-native-admin-bp-receipt-option-rows (name signer requirep)
  (declare (xargs :guard t))
  (append (if signer
              (list (fn-cfg-row-make name "bp-boundary-receipt-signer"
                                     signer 0))
            nil)
          (if requirep
              (list (fn-cfg-row-make name "bp-boundary-require-signed-receipts"
                                     "yes" 0))
            nil)))

(in-theory (disable fn-native-admin-bp-receipt-options))

(defun fn-native-admin-bp-boundary-base-plan (words)
  (declare (xargs :guard t
                  :guard-hints
                  (("Goal" :in-theory (disable fn-native-admin-decimalp
                                               fn-native-admin-decimal-value
                                               fn-native-admin-bp-boundary-split)))))
  (mv-let (base carried releases) (fn-native-admin-bp-boundary-split words)
  (if (and (true-listp words) (member-equal base '(6 9))
           (equal (nth 0 words) "bp-boundary")
           (equal (nth 1 words) "add")
           (fn-cfg-labelp (nth 2 words))
           (not (equal (nth 2 words) ""))
           (fn-path-identityp (fn-record-string-octets (nth 3 words)))
           (fn-bp-eid-shapep (nth 4 words))
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

; The base plan with the signed-receipt option rows appended to an accepted
; boundary's rows (the boundary name is the base plan's).
(defun fn-native-admin-bp-with-receipt-options (plan name signer requirep)
  (declare (xargs :guard t))
  (if (and (equal (fn-native-admin-result-status plan) :accepted)
           (or signer requirep))
      (fn-native-admin-result :accepted nil :set-bp-boundary
                              (fn-native-admin-result-name plan) 0 nil
                              (append (let ((rows (fn-native-admin-result-value
                                                   plan)))
                                        (if (true-listp rows) rows nil))
                                      (fn-native-admin-bp-receipt-option-rows
                                       name signer requirep)))
    plan))

; Routing (spec bp-node-machine 4.6): `contact PORT', before the two receipt
; options, is where an outbound session to this boundary connects, on the
; loopback profile's 127.0.0.1.  It is the boundary's own row
; (NAME "bp-boundary-contact" "127.0.0.1" PORT); a boundary without one is
; routable but never contacted (`fn-bprt-boundary-port').
; (mv words port): the words before the option, and PORT or nil.
(defun fn-native-admin-bp-contact-option (words)
  (declare (xargs :guard t))
  (let* ((words (if (true-listp words) words nil))
         (n (len words)))
    (if (and (<= 2 n)
             (equal (nth (- n 2) words) "contact")
             (fn-native-admin-decimalp (nth (- n 1) words))
             (<= 1 (fn-native-admin-decimal-value
                    (coerce (nth (- n 1) words) 'list)))
             (<= (fn-native-admin-decimal-value
                  (coerce (nth (- n 1) words) 'list)) 65535))
        (mv (butlast words 2)
            (fn-native-admin-decimal-value (coerce (nth (- n 1) words) 'list)))
      (mv words nil))))

(in-theory (disable fn-native-admin-bp-contact-option))

(defun fn-native-admin-bp-with-contact (plan name port)
  (declare (xargs :guard t))
  (if (and (equal (fn-native-admin-result-status plan) :accepted) port)
      (fn-native-admin-result :accepted nil :set-bp-boundary
                              (fn-native-admin-result-name plan) 0 nil
                              (append (let ((rows (fn-native-admin-result-value
                                                   plan)))
                                        (if (true-listp rows) rows nil))
                                      (list (fn-cfg-row-make
                                             name "bp-boundary-contact"
                                             "127.0.0.1" port))))
    plan))

(defun fn-native-admin-bp-boundary-plan (all-words)
  (declare (xargs :guard t))
  (mv-let (words0 signer requirep)
    (fn-native-admin-bp-receipt-options all-words)
    (mv-let (words port)
      (fn-native-admin-bp-contact-option words0)
      (fn-native-admin-bp-with-contact
       (fn-native-admin-bp-with-receipt-options
        (fn-native-admin-bp-boundary-base-plan words)
        (if (true-listp words) (nth 2 words) nil) signer requirep)
       (if (true-listp words) (nth 2 words) nil) port))))

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
  ;; Every branch builds its result with a literal kind, so the branch tests
  ;; need no simplification: in the minimal theory the proof only splits.
  :hints (("Goal" :in-theory (union-theories
                              '(fn-native-admin-peer-plan-base kind-of-result
                                (:executable-counterpart member-equal))
                              (theory 'minimal-theory)))))
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
)

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

; D23 row kinds a peer record holds beyond the typed record: the carried
; principals of an NNTP peer, and the carried sources and release issuers of
; a BP boundary.  `fn-cfg-peer-of-rows' ignores them, so the line renders
; them from the peer's own row group, one ` TAG=VALUE' word per row, in row
; order, after the auth field.  The decoder below reads them back, and
; `fn-native-admin-peer-extra-decode-lists-exactly-the-rows' is the keystone:
; the words of the three tags are exactly the rows of the three kinds.
(defun fn-native-admin-peer-slot-values (rows slot)
  "The value of every row of ROWS whose slot label is SLOT, in row order."
  (declare (xargs :guard t))
  (if (consp rows)
      (if (equal (fn-cfg-row-b (car rows)) slot)
          (cons (fn-cfg-row-c (car rows))
                (fn-native-admin-peer-slot-values (cdr rows) slot))
        (fn-native-admin-peer-slot-values (cdr rows) slot))
    nil))

(defun fn-native-admin-peer-list-octets (head values)
  (declare (xargs :guard (true-listp head)))
  (if (consp values)
      (append head
              (true-list-fix (fn-native-admin-peer-label-octets (car values)))
              (fn-native-admin-peer-list-octets head (cdr values)))
    nil))

(defun fn-native-admin-peer-word-octetp (x)
  (declare (xargs :guard t))
  (and (not (equal x 32)) (not (equal x 10))))

(defun fn-native-admin-peer-token (octets)
  (declare (xargs :guard t))
  (if (and (consp octets) (fn-native-admin-peer-word-octetp (car octets)))
      (cons (car octets) (fn-native-admin-peer-token (cdr octets)))
    nil))

(defun fn-native-admin-peer-after-token (octets)
  (declare (xargs :guard t))
  (if (and (consp octets) (fn-native-admin-peer-word-octetp (car octets)))
      (fn-native-admin-peer-after-token (cdr octets))
    octets))

(defun fn-native-admin-peer-head-p (head octets)
  (declare (xargs :guard t))
  (if (consp head)
      (and (consp octets)
           (equal (car head) (car octets))
           (fn-native-admin-peer-head-p (cdr head) (cdr octets)))
    t))

(defun fn-native-admin-peer-drop (head octets)
  (declare (xargs :guard t))
  (if (and (consp head) (consp octets))
      (fn-native-admin-peer-drop (cdr head) (cdr octets))
    octets))

(defthm fn-native-admin-peer-after-token-len
  (<= (len (fn-native-admin-peer-after-token x)) (len x))
  :rule-classes :linear)

(defthm fn-native-admin-peer-drop-len
  (implies (and (consp head) (fn-native-admin-peer-head-p head x))
           (< (len (fn-native-admin-peer-drop head x)) (len x)))
  :rule-classes :linear)

; The reader of a rendered list: the values of consecutive ` TAG=VALUE'
; words at the head of OCTETS, and what follows them.  A value ends at a
; space or a newline.
(defun fn-native-admin-peer-list-decode (head octets)
  (declare (xargs :guard t :measure (len octets)))
  (if (and (consp head) (fn-native-admin-peer-head-p head octets))
      (let ((rest (fn-native-admin-peer-drop head octets)))
        (let ((more (fn-native-admin-peer-list-decode
                     head (fn-native-admin-peer-after-token rest))))
          (list (cons (fn-native-admin-peer-token rest) (car more))
                (cadr more))))
    (list nil octets)))

(defun fn-native-admin-peer-label-octets-list (values)
  (declare (xargs :guard t))
  (if (consp values)
      (cons (true-list-fix (fn-native-admin-peer-label-octets (car values)))
            (fn-native-admin-peer-label-octets-list (cdr values)))
    nil))

(defun fn-native-admin-peer-wordp (octets)
  (declare (xargs :guard t))
  (if (consp octets)
      (and (fn-native-admin-peer-word-octetp (car octets))
           (fn-native-admin-peer-wordp (cdr octets)))
    t))

(defun fn-native-admin-peer-clean-valuesp (values)
  (declare (xargs :guard t))
  (if (consp values)
      (and (fn-native-admin-peer-wordp
            (true-list-fix (fn-native-admin-peer-label-octets (car values))))
           (fn-native-admin-peer-clean-valuesp (cdr values)))
    t))

(defun fn-native-admin-peer-boundaryp (octets)
  (declare (xargs :guard t))
  (or (atom octets) (not (fn-native-admin-peer-word-octetp (car octets)))))

(local (defthm fn-native-admin-peer-append-assoc
  (equal (append (append a b) c) (append a (append b c)))))
(local (defthm head-p-of-append-head
  (fn-native-admin-peer-head-p head (append head x))))
(local (defthm drop-of-append-head
  (implies (true-listp head)
           (equal (fn-native-admin-peer-drop head (append head x)) x))))
(local (defthm token-of-append-word
  (implies (and (fn-native-admin-peer-wordp w) (true-listp w)
                (fn-native-admin-peer-boundaryp x))
           (equal (fn-native-admin-peer-token (append w x)) w))))
(local (defthm after-token-of-append-word
  (implies (and (fn-native-admin-peer-wordp w)
                (fn-native-admin-peer-boundaryp x))
           (equal (fn-native-admin-peer-after-token (append w x)) x))))
(local (defthm boundaryp-of-list-octets
  (implies (and (fn-native-admin-peer-boundaryp x)
                (consp head)
                (not (fn-native-admin-peer-word-octetp (car head))))
           (fn-native-admin-peer-boundaryp
            (append (fn-native-admin-peer-list-octets head values) x)))))

(defthm fn-native-admin-peer-list-decode-of-list-octets
  (implies (and (fn-native-admin-peer-clean-valuesp values)
                (true-listp head)
                (consp head)
                (not (fn-native-admin-peer-word-octetp (car head)))
                (fn-native-admin-peer-boundaryp tail)
                (not (fn-native-admin-peer-head-p head tail)))
           (equal (fn-native-admin-peer-list-decode
                   head (append (fn-native-admin-peer-list-octets head values) tail))
                  (list (fn-native-admin-peer-label-octets-list values) tail)))
  :hints (("Goal" :in-theory (disable fn-native-admin-peer-label-octets))))

(defconst *fn-native-admin-peer-carries-principal-head*
  (list 32 99 97 114 114 105 101 115 45 112 114 105 110 99 105 112 97 108 61)) ; " carries-principal="
(defconst *fn-native-admin-peer-carries-head*
  (list 32 99 97 114 114 105 101 115 61)) ; " carries="
(defconst *fn-native-admin-peer-releases-for-head*
  (list 32 114 101 108 101 97 115 101 115 45 102 111 114 61)) ; " releases-for="

(defun fn-native-admin-peer-extra-octets (rows)
  (declare (xargs :guard t))
  (append (fn-native-admin-peer-list-octets
           *fn-native-admin-peer-carries-principal-head*
           (fn-native-admin-peer-slot-values rows "carries-principal"))
          (fn-native-admin-peer-list-octets
           *fn-native-admin-peer-carries-head*
           (fn-native-admin-peer-slot-values rows "bp-boundary-carries"))
          (fn-native-admin-peer-list-octets
           *fn-native-admin-peer-releases-for-head*
           (fn-native-admin-peer-slot-values rows "bp-boundary-releases-for"))))

(defun fn-native-admin-peer-extra-decode (octets)
  (declare (xargs :guard t))
  (let* ((a (fn-native-admin-peer-list-decode
             *fn-native-admin-peer-carries-principal-head* octets))
         (b (fn-native-admin-peer-list-decode
             *fn-native-admin-peer-carries-head* (cadr a)))
         (c (fn-native-admin-peer-list-decode
             *fn-native-admin-peer-releases-for-head* (cadr b))))
    (list (car a) (car b) (car c) (cadr c))))

(defun fn-native-admin-peer-extra-cleanp (rows)
  (declare (xargs :guard t))
  (and (fn-native-admin-peer-clean-valuesp
        (fn-native-admin-peer-slot-values rows "carries-principal"))
       (fn-native-admin-peer-clean-valuesp
        (fn-native-admin-peer-slot-values rows "bp-boundary-carries"))
       (fn-native-admin-peer-clean-valuesp
        (fn-native-admin-peer-slot-values rows "bp-boundary-releases-for"))))

(local (defthm head-p-of-append-when-diverged
  (implies (and (not (fn-native-admin-peer-head-p h1 h2))
                (not (fn-native-admin-peer-head-p h2 h1)))
           (not (fn-native-admin-peer-head-p h1 (append h2 x))))))

(local (defthm head-p-of-list-octets-when-diverged
  (implies (and (consp vs)
                (not (fn-native-admin-peer-head-p h1 h2))
                (not (fn-native-admin-peer-head-p h2 h1)))
           (not (fn-native-admin-peer-head-p
                 h1 (append (fn-native-admin-peer-list-octets h2 vs) x))))
  :hints (("Goal" :expand ((fn-native-admin-peer-list-octets h2 vs))))))

(local (defthm list-decode-when-not-head
  (implies (not (fn-native-admin-peer-head-p head octets))
           (equal (fn-native-admin-peer-list-decode head octets)
                  (list nil octets)))))

(local (defthm list-octets-of-atom
  (implies (not (consp vs))
           (equal (fn-native-admin-peer-list-octets h vs) nil))))

; The general reader lemma: over rows whose D23 values each render as one
; word, the three lists decode to exactly those values.  The hypothesis is
; discharged for every group `bp-boundary add' writes by the keystone below.
(defthm fn-native-admin-peer-extra-decode-of-clean-rows
  (implies (fn-native-admin-peer-extra-cleanp rows)
           (equal (fn-native-admin-peer-extra-decode
                   (append (fn-native-admin-peer-extra-octets rows) (list 10)))
                  (list (fn-native-admin-peer-label-octets-list
                         (fn-native-admin-peer-slot-values rows "carries-principal"))
                        (fn-native-admin-peer-label-octets-list
                         (fn-native-admin-peer-slot-values rows "bp-boundary-carries"))
                        (fn-native-admin-peer-label-octets-list
                         (fn-native-admin-peer-slot-values rows "bp-boundary-releases-for"))
                        (list 10))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable fn-native-admin-peer-list-octets
                                      fn-native-admin-peer-list-decode
                                      fn-native-admin-peer-slot-values
                                      fn-native-admin-peer-clean-valuesp
                                      fn-native-admin-peer-label-octets-list
                                      fn-native-admin-peer-label-octets)
                  :cases ((and (consp (fn-native-admin-peer-slot-values rows "bp-boundary-carries"))
                               (consp (fn-native-admin-peer-slot-values rows "bp-boundary-releases-for")))
                          (and (consp (fn-native-admin-peer-slot-values rows "bp-boundary-carries"))
                               (not (consp (fn-native-admin-peer-slot-values rows "bp-boundary-releases-for"))))
                          (and (not (consp (fn-native-admin-peer-slot-values rows "bp-boundary-carries")))
                               (consp (fn-native-admin-peer-slot-values rows "bp-boundary-releases-for")))))))

(encapsulate ()
(local (in-theory (disable fn-bp-eid-shapep)))
(local (defthm slot-values-of-append
  (equal (fn-native-admin-peer-slot-values (append a b) slot)
         (append (fn-native-admin-peer-slot-values a slot)
                 (fn-native-admin-peer-slot-values b slot)))))
(local (defthm slot-values-of-carries-rows
  (equal (fn-native-admin-peer-slot-values
          (fn-native-admin-bp-carries-rows name eids) slot)
         (if (equal slot "bp-boundary-carries") (true-list-fix eids) nil))))
(local (defthm slot-values-of-releases-rows
  (equal (fn-native-admin-peer-slot-values
          (fn-native-admin-bp-releases-rows name eids) slot)
         (if (equal slot "bp-boundary-releases-for") (true-list-fix eids) nil))))
(local (defthm shape-list-of-carried-words
  (implies (fn-native-admin-bp-carried-wordsp eids)
           (fn-bp-eid-shape-listp eids))))
(local (defthm shape-list-of-append
  (equal (fn-bp-eid-shape-listp (append a b))
         (and (fn-bp-eid-shape-listp a) (fn-bp-eid-shape-listp b)))))
(local (defthm shape-list-of-true-list-fix
  (equal (fn-bp-eid-shape-listp (true-list-fix xs)) (fn-bp-eid-shape-listp xs))))
(local (defthm list-clauses-shaped
  (implies (mv-nth 0 (fn-native-admin-bp-list-clauses tail))
           (and (fn-native-admin-bp-carried-wordsp
                 (mv-nth 1 (fn-native-admin-bp-list-clauses tail)))
                (fn-native-admin-bp-carried-wordsp
                 (mv-nth 2 (fn-native-admin-bp-list-clauses tail)))))))
(local (defthm split-shaped
  (and (fn-native-admin-bp-carried-wordsp
        (mv-nth 1 (fn-native-admin-bp-boundary-split words)))
       (fn-native-admin-bp-carried-wordsp
        (mv-nth 2 (fn-native-admin-bp-boundary-split words))))
  :hints (("Goal" :in-theory (disable fn-native-admin-bp-list-clauses
                                      fn-native-admin-bp-carried-wordsp
                                      fn-native-admin-bp-list-keywordp)))))

; KEYSTONE (admission).  Every EID an accepted `bp-boundary add' writes, the
; boundary's own (`transport-bp') and each `carries' and `releases-for' row,
; has `fn-bp-eid-shapep'.  A word that does not is refused `:bp-boundary'
; before any row exists.
(defthm fn-native-admin-bp-boundary-plan-eids-are-shaped
  (let ((rows (fn-native-admin-result-value
               (fn-native-admin-bp-boundary-plan words))))
    (implies (equal (fn-native-admin-result-status
                     (fn-native-admin-bp-boundary-plan words))
                    :accepted)
             (and (fn-bp-eid-shape-listp
                   (fn-native-admin-peer-slot-values rows "transport-bp"))
                  (fn-bp-eid-shape-listp
                   (fn-native-admin-peer-slot-values rows "bp-boundary-carries"))
                  (fn-bp-eid-shape-listp
                   (fn-native-admin-peer-slot-values rows "bp-boundary-releases-for")))))
  :hints (("Goal" :in-theory (disable fn-native-admin-bp-boundary-split
                                      fn-path-identityp fn-native-admin-decimalp
                                      fn-native-admin-decimal-value fn-cfg-wildmatp
                                      fn-cfg-labelp fn-record-string-octets))))

(local (defthm peer-wordp-of-vchar-octets
  (implies (fn-bp-eid-vchar-octetsp xs) (fn-native-admin-peer-wordp xs))))
; An accepted EID renders as one `peer list' word: no octet of it is the
; space or newline the reader splits on.
(defthm fn-native-admin-bp-eid-renders-as-one-word
  (implies (fn-bp-eid-shapep x)
           (fn-native-admin-peer-wordp (fn-native-admin-peer-label-octets x)))
  :hints (("Goal" :use fn-bp-eid-shapep-octets-are-vchar
                  :in-theory (disable fn-bp-eid-shapep-octets-are-vchar))))
(local (defthm clean-values-of-shape-list
  (implies (fn-bp-eid-shape-listp vs)
           (fn-native-admin-peer-clean-valuesp vs))
  :hints (("Goal" :in-theory (disable fn-native-admin-peer-label-octets)))))
(local (defthm no-principal-rows-in-a-boundary
  (equal (fn-native-admin-peer-slot-values
          (fn-native-admin-result-value
           (fn-native-admin-bp-boundary-plan words))
          "carries-principal")
         nil)
  :hints (("Goal" :in-theory (disable fn-native-admin-bp-boundary-split
                                      fn-path-identityp fn-native-admin-decimalp
                                      fn-native-admin-decimal-value fn-cfg-wildmatp
                                      fn-cfg-labelp fn-record-string-octets)))))
(defthm fn-native-admin-bp-boundary-plan-rows-render-clean
  (implies (equal (fn-native-admin-result-status
                   (fn-native-admin-bp-boundary-plan words))
                  :accepted)
           (fn-native-admin-peer-extra-cleanp
            (fn-native-admin-result-value
             (fn-native-admin-bp-boundary-plan words))))
  :hints (("Goal" :use (fn-native-admin-bp-boundary-plan-eids-are-shaped
                        no-principal-rows-in-a-boundary)
                  :in-theory (disable fn-native-admin-bp-boundary-plan
                                      fn-native-admin-result-value
                                      fn-native-admin-result-status
                                      no-principal-rows-in-a-boundary
                                      fn-native-admin-bp-boundary-plan-eids-are-shaped))))

)

(defun fn-native-admin-peer-row-octets (p rows)
  "One `peer list' line: the typed record P, then the D23 rows of ROWS (the
peer's row group), then a newline."
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
          (fn-native-admin-peer-extra-octets rows)
          (list 10)))

(defun fn-native-admin-peer-report-rows (names peers)
  (declare (xargs :guard t))
  (if (consp names)
      (let ((p (fn-cfg-peer-find (car names) peers)))
        (append (if p
                    (fn-native-admin-peer-row-octets
                     p (fn-cfg-rows-with-key peers (car names)))
                  nil)
                (fn-native-admin-peer-report-rows (cdr names) peers)))
    nil))

(defun fn-native-admin-peer-report (peers)
  "The `peer list' report for a configuration value's peer rows.

The enumeration is `fn-cfg-peer-names' and each record is `fn-cfg-peer-find';
a row group that denotes no well-formed record contributes no line rather
than a partially rendered one."
  (declare (xargs :guard t))
  (fn-native-admin-peer-report-rows (fn-cfg-peer-names peers) peers))
