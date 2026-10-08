; Teeth for books/served-access-revoke.lisp (ACCESS-REVOKE-PINNED).
;
; Fixture (tests/acl2/group-access-tests.lisp's): fn.public and fn.private.x,
; <p@> in fn.public, <s@> in fn.private.x, <c@> cross-posted to both; alice
; and bob hold credentials.  A PIN is the configuration a connection opened
; under, LIVE the one the operator published since; the served configuration
; is (fn-gac-config-with-live PIN LIVE), what books/owner.lisp
; fn-own-served-conn serves (fn-sar-served-config).
;
; (1) The old socket: pinned unrestricted, live revoked to fn.public.  The
;     pre-fix serving (the pin alone) answers STAT <s@> 223 and lists
;     fn.private.x; the served configuration answers 430 exactly as for an
;     absent article, refuses GROUP fn.private.x with 411, omits it from LIST
;     ACTIVE, and cuts <c@>'s Xref.
; (2) Pipelined AUTHINFO: the anonymous rule is unchanged and only bob's is
;     revoked.  One socket read carries AUTHINFO USER bob, AUTHINFO PASS and
;     STAT <s@>.  A decision taken once per read, for the login at its start
;     (anonymous, unchanged), serves the pin and answers 223; the served
;     configuration decides the STAT by bob's live rule: 430.
; (3) Widening: pinned to fn.public, live unrestricted.  The open connection
;     stays at its pin (STAT <s@> 430), and is not a refusal (STAT <p@> 223).
; (4) The keystone's premises inhabited at the witness of (1).

(in-package "ACL2")
(include-book "../../books/served-access-revoke")
(include-book "../../books/defkeystone")
(include-book "arena-lift")

(defun sar-payload (id)
  (append (fn-nntp-string-octets "Message-ID: ") (fn-nntp-string-octets id)
          '(13 10) (fn-nntp-string-octets "Subject: sar") '(13 10 13 10 88 13 10)))
(defconst *sar-groups* '("fn.public" "fn.private.x"))
(defconst *sar-p*
  (fn-make-article "<p@example.invalid>" 0
                   '("fn.public") (list (cons "fn.public" 1)) t 841000000))
(defconst *sar-s*
  (fn-make-article "<s@example.invalid>" 1
                   '("fn.private.x") (list (cons "fn.private.x" 1)) t 841000000))
(defconst *sar-c*
  (fn-make-article "<c@example.invalid>" 2
                   '("fn.public" "fn.private.x")
                   (list (cons "fn.public" 2) (cons "fn.private.x" 2)) t 841000000))
(defconst *sar-articles* (list *sar-c* *sar-s* *sar-p*))
(defconst *sar-state*
  (fn-make-state *sar-groups* (list (cons "fn.public" 3) (cons "fn.private.x" 3))
                 *sar-articles* 3 nil nil))
(assert-event (fn-nntp-projectionp *sar-state*))
(defconst *sar-pin-index*
  (fn-gidx-pin (fn-gidx-build *sar-articles*)))
(defconst *sar-arena*
  (list (sar-payload "<p@example.invalid>") (sar-payload "<s@example.invalid>")
        (sar-payload "<c@example.invalid>")))

(defconst *sar-salt* (make-list 16 :initial-element 3))
(defconst *sar-verifier*
  (fn-authsec-verifier
   *sar-salt*
   '(42 82 187 10 181 221 230 125 199 188 135 91 193 55 205 245
     177 50 208 139 71 236 67 86 54 24 223 76 55 144 61 51)
   (car (fn-scram-keys (fn-nntp-string-octets "correct-horse") *sar-salt* 4096))
   (cadr (fn-scram-keys (fn-nntp-string-octets "correct-horse") *sar-salt* 4096))))
(defconst *sar-bob*
  (fn-auth-make-cred (fn-nntp-string-octets "bob") (make-list 32 :initial-element 8)
                     *sar-verifier* t))
(defconst *sar-acfg* (fn-auth-make-config nil nil t (list *sar-bob*)))
(assert-event (fn-auth-configp *sar-acfg*))

(defconst *sar-agent* (fn-nntp-string-octets "fn.example.invalid"))
(defun sar-config (rows)
  (fn-inj-make-config-full t *sar-agent*
                           (list (fn-nntp-string-octets "fn.public")
                                 (fn-nntp-string-octets "fn.private.x"))
                           32768
                           (list nil nil *sar-agent*
                                 (fn-cfg-access-table rows))
                           nil))
(defun sar-row (login read) (fn-cfg-row-make login read "*" 3))
(defconst *sar-obs* (fn-clock-observation 1000000 843004800000 500 t))
(defconst *sar-as-anon* (fn-auth-open-session *sar-state* nil nil nil *sar-acfg* nil))

;; One command, the per-event step books/served.lisp dispatches.
(defun sar-step (as config text fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (fn-auth-step-pinned as *sar-state* *sar-pin-index* nil config *sar-obs* *sar-obs*
                       (list :command (fn-nntp-string-octets text)) fn-arena))
(defun sar-lines (effects)
  (if (consp effects) (append (cadr (car effects)) (sar-lines (cdr effects))) nil))
(defun sar-text (as config text fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let ((x (sar-lines (fn-post-result-effects (sar-step as config text fn-arena)))))
    (if (fn-octet-listp x) (fn-record-octets-string x) nil)))
(defun sar-after (as config text fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (fn-post-result-session (sar-step as config text fn-arena)))
(bpr-lift sar-text 3)
(bpr-lift sar-after 3)
(defun sar-prefixp (p s) (and (stringp s) (<= (length p) (length s))
                              (equal (subseq s 0 (length p)) p)))
(defun sar-searchp (needle s) (and (stringp s) (search needle s) t))
(defmacro sar (as config text) `(in-arena-sar-text *sar-arena* ,as ,config ,text))

; -----------------------------------------------------------------------------
; (1) The old socket.
(defconst *sar-pin1* (sar-config nil))
(defconst *sar-live1* (sar-config (list (sar-row "" "fn.public"))))
(defconst *sar-served1* (fn-gac-config-with-live *sar-pin1* *sar-live1*))

; Before: the pin alone serves the revoked article and group.
(assert-event (sar-prefixp "223 " (sar *sar-as-anon* *sar-pin1* "STAT <s@example.invalid>")))
(assert-event (sar-searchp "fn.private.x" (sar *sar-as-anon* *sar-pin1* "LIST ACTIVE")))
(assert-event (sar-prefixp "211 " (sar *sar-as-anon* *sar-pin1* "GROUP fn.private.x")))
; After: decided by the live rule.
(assert-event (sar-prefixp "430 " (sar *sar-as-anon* *sar-served1* "STAT <s@example.invalid>")))
(assert-event (equal (sar *sar-as-anon* *sar-served1* "STAT <s@example.invalid>")
                     (sar *sar-as-anon* *sar-served1* "STAT <nothere@example.invalid>")))
(assert-event (sar-prefixp "430 " (sar *sar-as-anon* *sar-served1* "ARTICLE <s@example.invalid>")))
(assert-event (sar-prefixp "430 " (sar *sar-as-anon* *sar-served1* "HDR Subject <s@example.invalid>")))
(assert-event (not (sar-searchp "fn.private.x" (sar *sar-as-anon* *sar-served1* "LIST ACTIVE"))))
(assert-event (sar-prefixp "411 " (sar *sar-as-anon* *sar-served1* "GROUP fn.private.x")))
(assert-event (sar-prefixp "223 " (sar *sar-as-anon* *sar-served1* "STAT <p@example.invalid>")))
; After GROUP fn.public (the old socket's advance), still refused; <c@>'s
; Xref names only the readable group.
(defconst *sar-in-public*
  (in-arena-sar-after *sar-arena* *sar-as-anon* *sar-served1* "GROUP fn.public"))
(assert-event (sar-prefixp "430 " (sar *sar-in-public* *sar-served1* "STAT <s@example.invalid>")))
(assert-event (sar-prefixp "224 " (sar *sar-in-public* *sar-served1* "OVER 2")))
(assert-event (not (sar-searchp "fn.private.x" (sar *sar-in-public* *sar-served1* "OVER 2"))))
; The same served rule is what the live configuration alone gives.
(assert-event (equal (fn-auth-access-read *sar-as-anon* *sar-served1*)
                     (fn-auth-access-read *sar-as-anon* *sar-live1*)))

; -----------------------------------------------------------------------------
; (2) Pipelined AUTHINFO in one socket read.
(defconst *sar-pin2* (sar-config (list (sar-row "" "fn.public") (sar-row "bob" "fn.*"))))
(defconst *sar-live2* (sar-config (list (sar-row "" "fn.public") (sar-row "bob" "fn.public"))))
(defconst *sar-served2* (fn-gac-config-with-live *sar-pin2* *sar-live2*))
; The anonymous rule did not change: a once-per-read decision at the read's
; start sees nothing to revoke.
(assert-event (equal (fn-auth-access-text *sar-as-anon* *sar-pin2* 1)
                     (fn-auth-access-text *sar-as-anon* *sar-live2* 1)))
(defun sar-line (s) (append (fn-nntp-string-octets s) '(13 10)))
(defconst *sar-pipelined*
  (append (sar-line "AUTHINFO USER bob") (sar-line "AUTHINFO PASS correct-horse")
          (sar-line "STAT <s@example.invalid>")))
(defun sar-read (config octets fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let ((x (sar-lines
            (fn-served-result-effects
             (fn-served-step
              (fn-served-result-conn
               (fn-served-open *sar-state* 510 8192 config *sar-obs* *sar-obs* *sar-acfg*))
              octets fn-arena)))))
    (if (fn-octet-listp x) (fn-record-octets-string x) nil)))
(bpr-lift sar-read 2)
; (The SCRAM digest is an attachment, which a defconst may not call: each
; read is evaluated inside its assertion.)
; The pin: bob authenticates (281) and is served <s@> (223).
(assert-event
 (let ((r (in-arena-sar-read *sar-arena* *sar-pin2* *sar-pipelined*)))
   (and (sar-searchp "281 " r) (sar-searchp "223 " r))))
; The served configuration: bob authenticates in the same read, and his
; STAT is decided by his live rule: 430, never 223.
(assert-event
 (let ((r (in-arena-sar-read *sar-arena* *sar-served2* *sar-pipelined*)))
   (and (sar-searchp "281 " r) (sar-searchp "430 " r) (not (sar-searchp "223 " r)))))

; -----------------------------------------------------------------------------
; (3) Widening stays at the pin.
(defconst *sar-pin3* (sar-config (list (sar-row "" "fn.public"))))
(defconst *sar-live3* (sar-config nil))
(defconst *sar-served3* (fn-gac-config-with-live *sar-pin3* *sar-live3*))
(assert-event (sar-prefixp "223 " (sar *sar-as-anon* *sar-live3* "STAT <s@example.invalid>")))
(assert-event (sar-prefixp "430 " (sar *sar-as-anon* *sar-served3* "STAT <s@example.invalid>")))
(assert-event (sar-prefixp "223 " (sar *sar-as-anon* *sar-served3* "STAT <p@example.invalid>")))
(assert-event (not (sar-searchp "fn.private.x" (sar *sar-as-anon* *sar-served3* "LIST ACTIVE"))))

; -----------------------------------------------------------------------------
; (4) The keystone's premises at (1): the session is projected, the live
; rule restricts and refuses fn.private.x; its conclusion is observed above.
(assert-event (fn-nntp-session-projected (fn-auth-reader-session *sar-as-anon*)))
(assert-event (equal (fn-sar-live-rule *sar-live1* (fn-auth-access-login *sar-as-anon*))
                     "fn.public"))
(assert-event (not (fn-gac-readablep "fn.public" "fn.private.x")))
(assert-event (not (member-equal "fn.private.x"
                                 (fn-state-groups
                                  (fn-auth-view-archive *sar-as-anon* *sar-served1* *sar-state*)))))

; TEETH-21 BEGIN
; Teeth (TEETH CONTRACT v1) for the three served-access-revoke "T" keystones.
; The owner and the connection are the lists their accessors read (fn-own-config
; the tenth element of the owner, fn-own-conn-config the seventh of the
; connection); the let-wrapped claims drop one antecedent per mutation.
(defun sar-o (cfg) (declare (xargs :guard t)) (list nil nil nil nil nil nil nil nil nil cfg))
(defun sar-cn (cfg) (declare (xargs :guard t)) (list nil nil nil nil nil nil cfg))

(defteeth fn-own-served-conn-refuses-what-the-live-rule-refuses
  :claim (() (let ((c (fn-served-conn-config (fn-own-served-conn o conn session)))
                    (live (fn-sar-live-rule (fn-own-config o) (fn-auth-access-login as))))
                (implies (and (fn-nntp-session-projected (fn-auth-reader-session as)) live (not (fn-gac-readablep live g)))
                         (and (not (member-equal g (fn-state-groups
                                                    (fn-auth-view-archive as c archive))))
                              (not (fn-auth-arts-name-groupp
                                    g (fn-state-articles (fn-auth-view-archive as c archive))))))))
  :subject fn-own-served-conn
  :witness ((o (sar-o *sar-live1*)) (conn (sar-cn *sar-pin1*)) (session nil) (as *sar-as-anon*) (archive *sar-state*) (g "fn.private.x"))
  :mutations ((session-not-projected
               (:conclusion (let ((c (fn-served-conn-config (fn-own-served-conn o conn session)))
                    (live (fn-sar-live-rule (fn-own-config o) (fn-auth-access-login as))))
                (implies (and live (not (fn-gac-readablep live g)))
                         (and (not (member-equal g (fn-state-groups
                                                    (fn-auth-view-archive as c archive))))
                              (not (fn-auth-arts-name-groupp
                                    g (fn-state-articles (fn-auth-view-archive as c archive))))))))
               ((o (sar-o *sar-live1*)) (conn (sar-cn *sar-pin1*)) (session nil) (as nil) (archive *sar-state*) (g "fn.private.x"))
               :fault "a connection whose reader session is not a projected session: the served view is not refused")
              (no-live-rule
               (:conclusion (let ((c (fn-served-conn-config (fn-own-served-conn o conn session)))
                    (live (fn-sar-live-rule (fn-own-config o) (fn-auth-access-login as))))
                (implies (and (fn-nntp-session-projected (fn-auth-reader-session as)) (not (fn-gac-readablep live g)))
                         (and (not (member-equal g (fn-state-groups
                                                    (fn-auth-view-archive as c archive))))
                              (not (fn-auth-arts-name-groupp
                                    g (fn-state-articles (fn-auth-view-archive as c archive))))))))
               ((o (sar-o *sar-pin1*)) (conn (sar-cn *sar-pin1*)) (session nil) (as *sar-as-anon*) (archive *sar-state*) (g "fn.private.x"))
               :fault "an owner configuration with no rule for the login: the old pin serves the revoked group")
              (live-rule-reads-the-group
               (:conclusion (let ((c (fn-served-conn-config (fn-own-served-conn o conn session)))
                    (live (fn-sar-live-rule (fn-own-config o) (fn-auth-access-login as))))
                (implies (and (fn-nntp-session-projected (fn-auth-reader-session as)) live)
                         (and (not (member-equal g (fn-state-groups
                                                    (fn-auth-view-archive as c archive))))
                              (not (fn-auth-arts-name-groupp
                                    g (fn-state-articles (fn-auth-view-archive as c archive))))))))
               ((o (sar-o *sar-live1*)) (conn (sar-cn *sar-pin1*)) (session nil) (as *sar-as-anon*) (archive *sar-state*) (g "fn.public"))
               :fault "a group the live rule still lets the login read, which the view names")))

(defteeth fn-own-served-conn-refuses-what-the-pin-refuses
  :claim (() (let ((c (fn-served-conn-config (fn-own-served-conn o conn session)))
                    (pin (fn-auth-rule-text
                          (fn-gac-listing-table (fn-inj-config-listing (fn-own-conn-config conn)))
                          (fn-inj-config-closed (fn-own-conn-config conn))
                          (fn-auth-access-login as) 1)))
                (implies (and (fn-nntp-session-projected (fn-auth-reader-session as)) pin (not (fn-gac-readablep pin g)))
                         (and (not (member-equal g (fn-state-groups
                                                    (fn-auth-view-archive as c archive))))
                              (not (fn-auth-arts-name-groupp
                                    g (fn-state-articles (fn-auth-view-archive as c archive))))))))
  :subject fn-own-served-conn
  :witness ((o (sar-o *sar-live1*)) (conn (sar-cn *sar-live1*)) (session nil) (as *sar-as-anon*) (archive *sar-state*) (g "fn.private.x"))
  :mutations ((session-not-projected
               (:conclusion (let ((c (fn-served-conn-config (fn-own-served-conn o conn session)))
                    (pin (fn-auth-rule-text
                          (fn-gac-listing-table (fn-inj-config-listing (fn-own-conn-config conn)))
                          (fn-inj-config-closed (fn-own-conn-config conn))
                          (fn-auth-access-login as) 1)))
                (implies (and pin (not (fn-gac-readablep pin g)))
                         (and (not (member-equal g (fn-state-groups
                                                    (fn-auth-view-archive as c archive))))
                              (not (fn-auth-arts-name-groupp
                                    g (fn-state-articles (fn-auth-view-archive as c archive))))))))
               ((o (sar-o *sar-live1*)) (conn (sar-cn *sar-live1*)) (session nil) (as nil) (archive *sar-state*) (g "fn.private.x"))
               :fault "a connection whose reader session is not a projected session")
              (no-pin-rule
               (:conclusion (let ((c (fn-served-conn-config (fn-own-served-conn o conn session)))
                    (pin (fn-auth-rule-text
                          (fn-gac-listing-table (fn-inj-config-listing (fn-own-conn-config conn)))
                          (fn-inj-config-closed (fn-own-conn-config conn))
                          (fn-auth-access-login as) 1)))
                (implies (and (fn-nntp-session-projected (fn-auth-reader-session as)) (not (fn-gac-readablep pin g)))
                         (and (not (member-equal g (fn-state-groups
                                                    (fn-auth-view-archive as c archive))))
                              (not (fn-auth-arts-name-groupp
                                    g (fn-state-articles (fn-auth-view-archive as c archive))))))))
               ((o (sar-o *sar-pin1*)) (conn (sar-cn *sar-pin1*)) (session nil) (as *sar-as-anon*) (archive *sar-state*) (g "fn.private.x"))
               :fault "a connection configuration with no rule for the login: nothing refuses the group")
              (pin-reads-the-group
               (:conclusion (let ((c (fn-served-conn-config (fn-own-served-conn o conn session)))
                    (pin (fn-auth-rule-text
                          (fn-gac-listing-table (fn-inj-config-listing (fn-own-conn-config conn)))
                          (fn-inj-config-closed (fn-own-conn-config conn))
                          (fn-auth-access-login as) 1)))
                (implies (and (fn-nntp-session-projected (fn-auth-reader-session as)) pin)
                         (and (not (member-equal g (fn-state-groups
                                                    (fn-auth-view-archive as c archive))))
                              (not (fn-auth-arts-name-groupp
                                    g (fn-state-articles (fn-auth-view-archive as c archive))))))))
               ((o (sar-o *sar-live1*)) (conn (sar-cn *sar-live1*)) (session nil) (as *sar-as-anon*) (archive *sar-state*) (g "fn.public"))
               :fault "a group the connection's own rule lets the login read, which the view names")))

(defteeth fn-own-served-conn-rule-is-the-pin-when-access-is-unchanged
  :claim (((no-live (not (consp (fn-gac-listing-live
                                 (fn-inj-config-listing (fn-own-conn-config conn))))))
           (rules-agree (equal (fn-sar-live-rule (fn-own-config o) (fn-auth-access-login as))
                               (fn-auth-rule-text
                                (fn-gac-listing-table (fn-inj-config-listing (fn-own-conn-config conn)))
                                (fn-inj-config-closed (fn-own-conn-config conn))
                                (fn-auth-access-login as) 1))))
          (equal (fn-auth-access-text
                  as (fn-served-conn-config (fn-own-served-conn o conn session)) 1)
                 (fn-auth-access-text as (fn-own-conn-config conn) 1)))
  :subject fn-own-served-conn
  :witness ((o (sar-o *sar-pin1*)) (conn (sar-cn *sar-pin1*)) (session nil) (as *sar-as-anon*))
  :breaks ((no-live ((conn (sar-cn *sar-served1*))))
           (rules-agree ((o (sar-o *sar-live1*)))))
  :mutations (:not-applicable "both hypotheses are labelled; their removal witnesses are the teeth"))
; TEETH-21 END
