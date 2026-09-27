; Teeth for per-login group access (PRF-222, NNT-046; books/group-access.lisp,
; books/nntp-auth.lisp fn-auth-delegate-pinned).  Every reply below is the
; host-called fn-auth-step-pinned's (books/served.lisp fn-served-dispatch
; calls it for each framed line) over a two-group store: fn.public and
; fn.private.x, with one article in each and one cross-posted to both.
; bob's rule reads fn.* except fn.private.* and posts only to fn.private.*;
; alice has no rule.
(in-package "ACL2")
(include-book "../../books/nntp-auth")
(include-book "../../books/native-admin")
(include-book "std/testing/must-fail" :dir :system)

(defun gat-payload (id)
  (append (fn-nntp-string-octets "Message-ID: ") (fn-nntp-string-octets id)
          '(13 10) (fn-nntp-string-octets "Subject: gat") '(13 10 13 10 88 13 10)))

(defconst *gat-groups* '("fn.public" "fn.private.x"))
(defconst *gat-p*
  (fn-make-article "<p@example.invalid>" (gat-payload "<p@example.invalid>")
                   '("fn.public") (list (cons "fn.public" 1)) t 841000000))
(defconst *gat-s*
  (fn-make-article "<s@example.invalid>" (gat-payload "<s@example.invalid>")
                   '("fn.private.x") (list (cons "fn.private.x" 1)) t 841000000))
(defconst *gat-c*
  (fn-make-article "<c@example.invalid>" (gat-payload "<c@example.invalid>")
                   '("fn.public" "fn.private.x")
                   (list (cons "fn.public" 2) (cons "fn.private.x" 2)) t 841000000))
(defconst *gat-articles* (list *gat-c* *gat-s* *gat-p*))
(defconst *gat-state*
  (fn-make-state *gat-groups* (list (cons "fn.public" 3) (cons "fn.private.x" 3))
                 *gat-articles* 3 nil nil))
(assert-event (fn-nntp-projectionp *gat-state*))
(defconst *gat-pin*
  (fn-gidx-pin (fn-midx-build *gat-articles*) (fn-gidx-build *gat-articles*)))

; Credentials: one verifier (books/nntp-auth-teeth-tests' literal, re-derived).
(defconst *gat-secret* (fn-nntp-string-octets "correct-horse"))
(defconst *gat-salt* (make-list 16 :initial-element 3))
(defconst *gat-verifier*
  (fn-authsec-verifier
   *gat-salt*
   '(60 237 250 71 154 204 168 180 72 224 241 93 232 185 72 59
     73 5 240 237 54 116 175 93 127 219 39 238 113 83 63 194)))
(assert-event (equal *gat-verifier* (fn-authsec-enrol *gat-salt* *gat-secret*)))
(defconst *gat-alice*
  (fn-auth-make-cred (fn-nntp-string-octets "alice") (make-list 32 :initial-element 7)
                     *gat-verifier* t))
(defconst *gat-bob*
  (fn-auth-make-cred (fn-nntp-string-octets "bob") (make-list 32 :initial-element 8)
                     *gat-verifier* t))
(defconst *gat-acfg* (fn-auth-make-config t nil t (list *gat-alice* *gat-bob*)))
(assert-event (fn-auth-configp *gat-acfg*))

; The rule row, as books/config.lisp `fn-cfg-account-access' writes it and
; books/owner-agent.lisp `fn-oag-listing' projects it (the listing's fourth
; element).
(defconst *gat-delta*
  (fn-cfg-account-access "bob" "fn.*,!fn.private.*" "fn.private.*"))
(assert-event (fn-cfg-deltap *gat-delta*))
(assert-event (null (fn-cfg-account-access-reason *gat-delta*)))
(assert-event (equal (fn-cfg-kind-code :account-access) 22))
(assert-event (equal (fn-cfg-code-kind 22) :account-access))
(defconst *gat-table* (fn-cfg-access-table (fn-cfg-delta-rows *gat-delta*)))
(defconst *gat-agent* (fn-nntp-string-octets "fn.example.invalid"))
(defun gat-config (table)
  (fn-inj-make-config-full t *gat-agent*
                           (list (fn-nntp-string-octets "fn.public")
                                 (fn-nntp-string-octets "fn.private.x"))
                           32768 (list nil nil *gat-agent* table) nil))
(defconst *gat-config* (gat-config *gat-table*))
(defconst *gat-config-none* (gat-config nil))
(defconst *gat-obs* (fn-clock-observation 1000000 843004800000 500 t))

(defun gat-step (as text fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (fn-auth-step-pinned as *gat-state* *gat-pin* nil *gat-config* *gat-obs* *gat-obs*
                       (list :command (fn-nntp-string-octets text)) fn-arena))
(defun gat-after (as text fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil)) (fn-post-result-session (gat-step as text fn-arena)))
(defun gat-reply (as text fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil)) (fn-post-result-effects (gat-step as text fn-arena)))
(defun gat-login (name fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (gat-after (gat-after (fn-auth-open-session *gat-state* nil nil nil *gat-acfg* nil)
                        (concatenate 'string "AUTHINFO USER " name) fn-arena)
             "AUTHINFO PASS correct-horse" fn-arena))
;; The sessions AUTHINFO USER/PASS leaves (the digest is an attachment, which
;; a defconst may not call, so the session is written out and the served
;; login is checked to produce exactly it).
(defconst *gat-as-anon* (fn-auth-open-session *gat-state* nil nil nil *gat-acfg* nil))
(defun gat-logged-in (name principal)
  (fn-auth-make-session (fn-auth-session-base *gat-as-anon*) *gat-acfg*
                        (fn-nntp-string-octets name) principal nil nil))
(defconst *gat-as-bob* (gat-logged-in "bob" (make-list 32 :initial-element 8)))
(defconst *gat-as-alice* (gat-logged-in "alice" (make-list 32 :initial-element 7)))
(include-book "arena-lift")
;; The payloads the arena holds at handles 0, 1, ...: none (no byte is read here).
(defconst *sr-arena* nil)
(bpr-lift fn-auth-step-pinned 8)
(bpr-lift gat-after 2)
(bpr-lift gat-login 1)
(bpr-lift gat-reply 2)
(bpr-lift gat-text 2)
(assert-event (equal (in-arena-gat-login *sr-arena* "bob") *gat-as-bob*))
(assert-event (equal (in-arena-gat-login *sr-arena* "alice") *gat-as-alice*))
(assert-event (fn-auth-session-subject *gat-as-bob*))
(assert-event (fn-auth-session-subject *gat-as-alice*))

; The rule each session is served.
(assert-event (equal (fn-auth-access-read *gat-as-bob* *gat-config*) "fn.*,!fn.private.*"))
(assert-event (equal (fn-auth-access-post *gat-as-bob* *gat-config*) "fn.private.*"))
(assert-event (not (fn-auth-access-restrictedp *gat-as-alice* *gat-config*)))
(assert-event (not (fn-auth-access-restrictedp *gat-as-anon* *gat-config*)))
(assert-event (not (fn-auth-access-restrictedp *gat-as-bob* *gat-config-none*)))

(defun gat-lines (effects)
  (if (consp effects)
      (append (cadr (car effects)) (gat-lines (cdr effects)))
    nil))
(defun gat-string (x)
  (if (fn-octet-listp x) (fn-record-octets-string x) nil))
(defun gat-text (as text fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil)) (gat-string (gat-lines (gat-reply as text fn-arena))))

(defun gat-prefixp (p s)
  (and (stringp s) (<= (length p) (length s)) (equal (subseq s 0 (length p)) p)))
(defun gat-searchp (needle s)
  (and (stringp s) (search needle s) t))

; ---------------------------------------------------------------------------
; Reachable witnesses on the host-called step

; GROUP: bob selects the public group, and the private group answers exactly
; as an absent group does; alice selects both.
(assert-event (gat-prefixp "211 " (in-arena-gat-text *sr-arena* *gat-as-bob* "GROUP fn.public")))
(assert-event (equal (in-arena-gat-reply *sr-arena* *gat-as-bob* "GROUP fn.private.x")
                     (in-arena-gat-reply *sr-arena* *gat-as-bob* "GROUP fn.absent")))
(assert-event (gat-prefixp "411 " (in-arena-gat-text *sr-arena* *gat-as-bob* "GROUP fn.private.x")))
(assert-event (gat-prefixp "211 " (in-arena-gat-text *sr-arena* *gat-as-alice* "GROUP fn.private.x")))
(assert-event (gat-prefixp "411 " (in-arena-gat-text *sr-arena* *gat-as-bob* "LISTGROUP fn.private.x")))

; LIST ACTIVE and LIST NEWSGROUPS: the private group is not listed for bob.
(assert-event (not (gat-searchp "fn.private.x" (in-arena-gat-text *sr-arena* *gat-as-bob* "LIST ACTIVE"))))
(assert-event (gat-searchp "fn.public" (in-arena-gat-text *sr-arena* *gat-as-bob* "LIST ACTIVE")))
(assert-event (gat-searchp "fn.private.x" (in-arena-gat-text *sr-arena* *gat-as-alice* "LIST ACTIVE")))
(assert-event (not (gat-searchp "fn.private.x" (in-arena-gat-text *sr-arena* *gat-as-bob* "LIST NEWSGROUPS"))))
(assert-event (not (gat-searchp "fn.private.x" (in-arena-gat-text *sr-arena* *gat-as-bob* "LIST COUNTS"))))
; bob may not post to fn.public: its status is n to him (RFC 6048 2.1).
(assert-event (gat-searchp "fn.public 2 1 n" (in-arena-gat-text *sr-arena* *gat-as-bob* "LIST ACTIVE")))
(assert-event (gat-searchp "fn.public 2 1 y" (in-arena-gat-text *sr-arena* *gat-as-alice* "LIST ACTIVE")))

; By Message-ID: the private-only article answers 430 to bob; the
; cross-posted one is held; alice reads both.
(assert-event (gat-prefixp "430 " (in-arena-gat-text *sr-arena* *gat-as-bob* "STAT <s@example.invalid>")))
(assert-event (gat-prefixp "430 " (in-arena-gat-text *sr-arena* *gat-as-bob* "ARTICLE <s@example.invalid>")))
(assert-event (gat-prefixp "430 " (in-arena-gat-text *sr-arena* *gat-as-bob* "OVER <s@example.invalid>")))
(assert-event (gat-prefixp "430 " (in-arena-gat-text *sr-arena* *gat-as-bob* "HDR Subject <s@example.invalid>")))
(assert-event (gat-prefixp "223 " (in-arena-gat-text *sr-arena* *gat-as-bob* "STAT <c@example.invalid>")))
(assert-event (gat-prefixp "223 " (in-arena-gat-text *sr-arena* *gat-as-alice* "STAT <s@example.invalid>")))
; the absent-article reply, exactly
(assert-event (equal (in-arena-gat-reply *sr-arena* *gat-as-bob* "STAT <s@example.invalid>")
                     (in-arena-gat-reply *sr-arena* *gat-as-bob* "STAT <nothere@example.invalid>")))

; The cross-posted article's Xref names only the readable group to bob.
(defconst *gat-bob-in-public* (in-arena-gat-after *sr-arena* *gat-as-bob* "GROUP fn.public"))
(assert-event (gat-prefixp "224 " (in-arena-gat-text *sr-arena* *gat-bob-in-public* "OVER 2")))
(assert-event (not (gat-searchp "fn.private.x"
                                (in-arena-gat-text *sr-arena* *gat-bob-in-public* "OVER 2"))))
(assert-event (gat-searchp "fn.private.x"
                           (in-arena-gat-text *sr-arena* (in-arena-gat-after *sr-arena* *gat-as-alice* "GROUP fn.public") "OVER 2")))

; A selection bob's view lacks is dropped: a reader session that selected
; fn.private.x under alice's (unrestricted) login, carried under bob's rule,
; is served as if nothing were selected (the delegate deselects first).
(defconst *gat-alice-in-private* (in-arena-gat-after *sr-arena* *gat-as-alice* "GROUP fn.private.x"))
(defconst *gat-bob-in-private*
  (fn-auth-make-session (fn-auth-session-base *gat-alice-in-private*) *gat-acfg*
                        (fn-nntp-string-octets "bob")
                        (make-list 32 :initial-element 8) nil nil))
(assert-event (gat-prefixp "220 " (in-arena-gat-text *sr-arena* *gat-alice-in-private* "ARTICLE")))
(assert-event (gat-prefixp "412 " (in-arena-gat-text *sr-arena* *gat-bob-in-private* "ARTICLE")))
(assert-event (gat-prefixp "412 " (in-arena-gat-text *sr-arena* *gat-bob-in-private* "NEXT")))

; The step's reply for bob IS the unrestricted reply over the view (the
; delegate's construction): alice, over the store with fn.private.x absent,
; answers LIST ACTIVE ... except for the status field bob's post rule sets,
; so compare with bob's rule minus the post pattern.
(defconst *gat-read-only-table*
  (list (fn-cfg-row-make "bob" "fn.*,!fn.private.*" "*" 3)))
(defconst *gat-view* (fn-gac-restrict-state "fn.*,!fn.private.*" *gat-state*))
(assert-event (equal (fn-state-groups *gat-view*) '("fn.public")))
(assert-event (equal (len (fn-state-articles *gat-view*)) 2))
(assert-event
 (equal (fn-post-result-effects
         (in-arena-fn-auth-step-pinned *sr-arena* *gat-as-bob* *gat-state* *gat-pin* nil (gat-config *gat-read-only-table*) *gat-obs* *gat-obs* (list :command (fn-nntp-string-octets "LIST ACTIVE"))))
        (fn-post-result-effects
         (in-arena-fn-auth-step-pinned *sr-arena* *gat-as-alice* *gat-view* (fn-gac-restrict-index "fn.*,!fn.private.*" *gat-pin*
                                                     (fn-state-articles *gat-view*)) nil *gat-config-none* *gat-obs* *gat-obs* (list :command (fn-nntp-string-octets "LIST ACTIVE"))))))

; POST: the view's served groups drop what bob may neither read nor post
; to, and close what he may read but not post to.
(defconst *gat-bob-config*
  (fn-auth-view-config *gat-as-bob* *gat-config* *gat-state*))
(assert-event (equal (fn-inj-config-groups *gat-bob-config*)
                     (list (fn-nntp-string-octets "fn.public")
                           (fn-nntp-string-octets "fn.private.x"))))
(assert-event (member-equal (fn-nntp-string-octets "fn.public")
                            (fn-inj-config-closed *gat-bob-config*)))
(defconst *gat-carol-table*
  (list (fn-cfg-row-make "bob" "fn.public" "fn.public" 3)))
(defconst *gat-carol-config*
  (fn-auth-view-config *gat-as-bob* (gat-config *gat-carol-table*) *gat-state*))
(assert-event (equal (fn-inj-config-groups *gat-carol-config*)
                     (list (fn-nntp-string-octets "fn.public"))))

; ---------------------------------------------------------------------------
; Keystones: a witness asserting every hypothesis and the conclusion, and a
; failure of the conclusion without each hypothesis.

; fn-gac-restrict-state-is-a-projection
(assert-event (and (fn-nntp-projectionp *gat-state*)
                   (fn-nntp-projectionp (fn-gac-restrict-state "fn.*" *gat-state*))))
(must-fail
 (defthm gat-projection-without-projection
   (fn-nntp-projectionp (fn-gac-restrict-state text s))))

; fn-gac-consistent-into-view: the selection must be readable and the
; session projected.
(defconst *gat-ns-private*
  (fn-nntp-set-cursor (fn-nntp-open-session *gat-state*) "fn.private.x" 1))
(assert-event (fn-nntp-session-consistentp *gat-ns-private* *gat-state*))
(assert-event (not (fn-nntp-session-consistentp *gat-ns-private* *gat-view*)))
(must-fail
 (defthm gat-into-view-without-readable
   (implies (and (fn-nntp-session-consistentp ns s)
                 (fn-nntp-session-projected ns))
            (fn-nntp-session-consistentp ns (fn-gac-restrict-state text s)))))
(defconst *gat-ns-public*
  (fn-nntp-set-cursor (fn-nntp-open-session *gat-state*) "fn.public" 1))
(assert-event (and (fn-nntp-session-consistentp *gat-ns-public* *gat-state*)
                   (fn-nntp-session-projected *gat-ns-public*)
                   (fn-gac-readablep "fn.*,!fn.private.*" "fn.public")
                   (fn-nntp-session-consistentp *gat-ns-public* *gat-view*)))
(must-fail
 (defthm gat-into-view-without-projected
   (implies (and (fn-nntp-session-consistentp ns s)
                 (or (null (fn-nntp-session-group ns))
                     (fn-gac-readablep text (fn-nntp-session-group ns))))
            (fn-nntp-session-consistentp ns (fn-gac-restrict-state text s)))))

; fn-gac-restrict-absent-groups (no oracle): a store with the private group
; removed ("fn.*,!fn.private.x" admits everything bob's rule admits) gives
; bob the same view; without the covering hypothesis it does not.
(assert-event (fn-gac-coversp "fn.*,!fn.private.*" "fn.*,!fn.private.x" *gat-groups*))
(assert-event
 (equal (fn-gac-restrict-state "fn.*,!fn.private.*"
                               (fn-gac-restrict-state "fn.*,!fn.private.x" *gat-state*))
        *gat-view*))
(assert-event (not (fn-gac-coversp "fn.*" "fn.*,!fn.private.x" *gat-groups*)))
(assert-event
 (not (equal (fn-gac-restrict-state "fn.*"
                                    (fn-gac-restrict-state "fn.*,!fn.private.x" *gat-state*))
             (fn-gac-restrict-state "fn.*" *gat-state*))))
(must-fail
 (defthm gat-absent-without-covers
   (implies (fn-statep s)
            (equal (fn-gac-restrict-state text (fn-gac-restrict-state text2 s))
                   (fn-gac-restrict-state text s)))))

; fn-gac-restricted-article-is-held: exactly the articles with a readable
; group.
(assert-event (not (fn-acceptedp "<s@example.invalid>" (fn-state-articles *gat-view*))))
(assert-event (fn-acceptedp "<c@example.invalid>" (fn-state-articles *gat-view*)))

; The verb.
(defun gat-argv (words)
  (if (consp words)
      (cons (fn-record-string-octets (car words)) (gat-argv (cdr words)))
    nil))
(defconst *gat-plan*
  (fn-native-admin-plan
   (gat-argv '("account" "access" "bob" "--read" "fn.*,!fn.private.*"
               "--post" "fn.private.*"))))
(assert-event (equal (fn-native-admin-plan-deltas *gat-plan*) (list *gat-delta*)))
(assert-event
 (equal (fn-native-admin-result-reason
         (fn-native-admin-plan
          (gat-argv '("account" "access" "bob" "--read" "fn.[" "--post" "*"))))
        :access-pattern))
(assert-event
 (equal (fn-native-admin-plan-deltas
         (fn-native-admin-plan
          (gat-argv '("account" "access" "--anonymous" "--read" "fn.public"
                      "--post" "fn.public"))))
        (list (fn-cfg-account-access "" "fn.public" "fn.public"))))
(assert-event
 (fn-native-admin-result-queryp
  (fn-native-admin-plan (gat-argv '("account" "access" "show")))))

;; -----------------------------------------------------------------------------
;; PKT-643: the restricted view carried with the pin (books/group-access.lisp
;; fn-gac-views-find-is-restriction, fn-gac-access-views-covers-pattern).

(defconst *gat-ctl* (fn-ctl-pin nil nil))
(defconst *gat-views*
  (fn-gac-access-views (fn-gac-read-texts *gat-table*) *gat-state* *gat-ctl*))
(defconst *gat-bob-read* (fn-gac-pattern *gat-table* (fn-nntp-string-octets "bob") 1))
(assert-event (stringp *gat-bob-read*))

; fn-gac-views-find-is-restriction, reachable: bob's entry in the table the
; pin builds is his view, and the view drops the private article.
(assert-event (fn-gac-views-okp *gat-views* *gat-state* *gat-ctl*))
(assert-event (fn-gac-views-find *gat-bob-read* *gat-views*))
(assert-event (equal (cdr (fn-gac-views-find *gat-bob-read* *gat-views*))
                     (fn-gac-view-entry *gat-bob-read* *gat-state* *gat-ctl*)))
(assert-event (equal (len (fn-state-articles
                           (car (cdr (fn-gac-views-find *gat-bob-read* *gat-views*)))))
                     2))
; Without okp: a forged entry (the unrestricted store) is found and is not
; the view.
(defconst *gat-forged* (list (cons *gat-bob-read* (cons *gat-state* *gat-pin*))))
(assert-event (and (fn-gac-views-find *gat-bob-read* *gat-forged*)
                   (not (fn-gac-views-okp *gat-forged* *gat-state* *gat-ctl*))
                   (not (equal (cdr (fn-gac-views-find *gat-bob-read* *gat-forged*))
                               (fn-gac-view-entry *gat-bob-read* *gat-state* *gat-ctl*)))))
; Without the find: a text the table lacks.
(assert-event (and (fn-gac-views-okp *gat-views* *gat-state* *gat-ctl*)
                   (not (fn-gac-views-find "fn.none" *gat-views*))
                   (not (equal (cdr (fn-gac-views-find "fn.none" *gat-views*))
                               (fn-gac-view-entry "fn.none" *gat-state* *gat-ctl*)))))
(must-fail
 (defthm gat-views-find-without-okp
   (implies (fn-gac-views-find text views)
            (equal (cdr (fn-gac-views-find text views))
                   (fn-gac-view-entry text archive control)))))
(must-fail
 (defthm gat-views-find-without-find
   (implies (fn-gac-views-okp views archive control)
            (equal (cdr (fn-gac-views-find text views))
                   (fn-gac-view-entry text archive control)))))

; fn-gac-access-views-covers-pattern, reachable (bob) and without its
; hypothesis (carol has no rule: the pattern is nil and nothing is found).
(assert-event (fn-gac-views-find (fn-gac-pattern *gat-table* (fn-nntp-string-octets "bob") 1)
                                 *gat-views*))
(assert-event (and (null (fn-gac-pattern *gat-table* (fn-nntp-string-octets "carol") 1))
                   (not (fn-gac-views-find
                         (fn-gac-pattern *gat-table* (fn-nntp-string-octets "carol") 1)
                         *gat-views*))))
(must-fail
 (defthm gat-covers-without-pattern
   (fn-gac-views-find (fn-gac-pattern table login 1)
                      (fn-gac-access-views (fn-gac-read-texts table) archive control))))
