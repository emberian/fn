; Teeth for books/group-access-cache.lisp and the served delegate's use of
; it (books/served-catalog-chain.lisp fn-scr-auth-delegate,
; fn-scr-prepare-access; PKT-643).  The fixture is
; tests/acl2/group-access-tests.lisp's: fn.public and fn.private.x, one
; article in each and one cross-posted; bob reads fn.* except fn.private.*.
(in-package "ACL2")
(include-book "../../books/served-catalog-chain")
(include-book "must-fail-checked")

(defun gacct-payload (id)
  (append (fn-nntp-string-octets "Message-ID: ") (fn-nntp-string-octets id)
          '(13 10) (fn-nntp-string-octets "Subject: gat") '(13 10 13 10 88 13 10)))

(defconst *gacct-groups* '("fn.public" "fn.private.x"))
(defconst *gacct-p*
  (fn-make-article "<p@example.invalid>" 0
                   '("fn.public") (list (cons "fn.public" 1)) t 841000000))
(defconst *gacct-s*
  (fn-make-article "<s@example.invalid>" 1
                   '("fn.private.x") (list (cons "fn.private.x" 1)) t 841000000))
(defconst *gacct-c*
  (fn-make-article "<c@example.invalid>" 2
                   '("fn.public" "fn.private.x")
                   (list (cons "fn.public" 2) (cons "fn.private.x" 2)) t 841000000))
(defconst *gacct-articles* (list *gacct-c* *gacct-s* *gacct-p*))
(defconst *gacct-state*
  (fn-make-state *gacct-groups* (list (cons "fn.public" 3) (cons "fn.private.x" 3))
                 *gacct-articles* 3 nil nil))
(assert-event (fn-nntp-projectionp *gacct-state*))
(defconst *gacct-pin*
  (fn-gidx-pin (fn-midx-build *gacct-articles*) (fn-gidx-build *gacct-articles*)))
(defconst *gacct-text* "fn.*,!fn.private.*")
(defconst *gacct-ctl* (fn-gidx-pin-control *gacct-pin*))

;; -----------------------------------------------------------------------------
;; The cache: prepared, answered, kept.

(defconst *gacct-c1* (fn-gacc-prepare *gacct-text* *gacct-state* *gacct-ctl* nil))
(assert-event (fn-gacc-okp nil))
(assert-event (fn-gacc-okp *gacct-c1*))
; fn-gacc-view-of-prepare, reachable: the prepared key is answered, and the
; answer is the per-command view (fn-gac-view-entry).
(assert-event (equal (fn-gacc-view *gacct-text* *gacct-state* *gacct-ctl* *gacct-c1*)
                     (fn-gac-view-entry *gacct-text* *gacct-state* *gacct-ctl*)))
; The view holds the public article and the cross-posted one cut to fn.public.
(assert-event (equal (len (fn-state-articles
                           (car (fn-gacc-view *gacct-text* *gacct-state* *gacct-ctl* *gacct-c1*))))
                     2))
; Another archive (another pin) is not answered: the key is the pin.
(assert-event (null (fn-gacc-view *gacct-text* (fn-make-state *gacct-groups* nil nil 0 nil nil)
                                  *gacct-ctl* *gacct-c1*)))
; Another rule is not answered.
(assert-event (null (fn-gacc-view "fn.*" *gacct-state* *gacct-ctl* *gacct-c1*)))

;; The prefix walk's two values, as a list (for ground evaluation).
(defun gacct-prefix (new old)
  (mv-let (found prefix) (fn-gacc-prefix new old nil) (list found prefix)))

;; Acceptances since the key: the entry grows by them (the prefix is found),
;; and is the view of the new key.
(defconst *gacct-q*
  (fn-make-article "<q@example.invalid>" 3
                   '("fn.public") (list (cons "fn.public" 3)) t 841000001))
(defconst *gacct-t*
  (fn-make-article "<t@example.invalid>" 4
                   '("fn.private.x") (list (cons "fn.private.x" 3)) t 841000002))
(defconst *gacct-state2*
  (fn-make-state *gacct-groups* (list (cons "fn.public" 4) (cons "fn.private.x" 4))
                 (list* *gacct-t* *gacct-q* *gacct-articles*) 5 nil nil))
(assert-event (equal (gacct-prefix (fn-state-articles *gacct-state2*)
                                   (fn-state-articles *gacct-state*))
                     (list t (list *gacct-q* *gacct-t*))))
(defconst *gacct-c2* (fn-gacc-prepare *gacct-text* *gacct-state2* *gacct-ctl* *gacct-c1*))
(assert-event (fn-gacc-okp *gacct-c2*))
(assert-event (equal (fn-gacc-view *gacct-text* *gacct-state2* *gacct-ctl* *gacct-c2*)
                     (fn-gac-view-entry *gacct-text* *gacct-state2* *gacct-ctl*)))
; One entry per rule: the grown entry replaced the old one.
(assert-event (equal (len *gacct-c2*) 1))
; The grown view took q (fn.public) and not t (fn.private.x only).
(assert-event (equal (len (fn-state-articles
                           (car (fn-gacc-view *gacct-text* *gacct-state2* *gacct-ctl* *gacct-c2*))))
                     3))
; The same key again keeps the entry itself.
(assert-event (equal (fn-gacc-prepare *gacct-text* *gacct-state2* *gacct-ctl* *gacct-c2*)
                     *gacct-c2*))

;; -----------------------------------------------------------------------------
;; Hypotheses.

; fn-gacc-view-is-the-view-entry without fn-gacc-okp: a forged entry keyed to
; the pin with another view is answered as it is.
(defconst *gacct-forged*
  (list (fn-gacc-entry *gacct-text* *gacct-state* *gacct-ctl* (cons *gacct-state* *gacct-pin*))))
(assert-event (not (fn-gacc-okp *gacct-forged*)))
(assert-event (fn-gacc-view *gacct-text* *gacct-state* *gacct-ctl* *gacct-forged*))
(assert-event (not (equal (fn-gacc-view *gacct-text* *gacct-state* *gacct-ctl* *gacct-forged*)
                          (fn-gac-view-entry *gacct-text* *gacct-state* *gacct-ctl*))))
(must-fail-checked
 (defthm gacct-view-without-okp
   (implies (fn-gacc-view text archive control cache)
            (equal (fn-gacc-view text archive control cache)
                   (fn-gac-view-entry text archive control)))))

; fn-gacc-extend-view-is-the-view-entry without the same control cut: the
; control's withdrawn list moved (c withdrawn), and growing the old view is
; not the new view (its withdrawn list is stale).
(defconst *gacct-ctl-w* (fn-ctl-pin (list *gacct-c*) nil))
(assert-event (not (fn-gacc-same-cut-p *gacct-ctl-w* *gacct-ctl*)))
(assert-event
 (not (equal (fn-gacc-extend-view *gacct-text* *gacct-state2*
                                  (list *gacct-q* *gacct-t*)
                                  (fn-gac-view-entry *gacct-text* *gacct-state* *gacct-ctl*))
             (fn-gac-view-entry *gacct-text* *gacct-state2* *gacct-ctl-w*))))
(must-fail-checked
 (defthm gacct-extend-without-same-cut
   (implies (mv-nth 0 (fn-gacc-prefix (fn-state-articles archive) (fn-state-articles old) nil))
            (equal (fn-gacc-extend-view
                    text archive
                    (mv-nth 1 (fn-gacc-prefix (fn-state-articles archive) (fn-state-articles old) nil))
                    (fn-gac-view-entry text old octl))
                   (fn-gac-view-entry text archive control)))))
; ... and the refresh builds instead (its result is still the new view).
(assert-event (equal (fn-gacc-view *gacct-text* *gacct-state2* *gacct-ctl-w*
                                   (fn-gacc-prepare *gacct-text* *gacct-state2* *gacct-ctl-w*
                                                    *gacct-c1*))
                     (fn-gac-view-entry *gacct-text* *gacct-state2* *gacct-ctl-w*)))

; Without the prefix: an archive whose articles do not extend the entry's
; (p, a public article, withdrawn from the visible list) is not a grown view.
(defconst *gacct-state3*
  (fn-make-state *gacct-groups* (list (cons "fn.public" 3) (cons "fn.private.x" 3))
                 (list *gacct-q* *gacct-c* *gacct-s*) 5 nil nil))
(assert-event (not (car (gacct-prefix (fn-state-articles *gacct-state3*)
                                      (fn-state-articles *gacct-state*)))))
(assert-event
 (not (equal (fn-gacc-extend-view *gacct-text* *gacct-state3* (list *gacct-q*)
                                  (fn-gac-view-entry *gacct-text* *gacct-state* *gacct-ctl*))
             (fn-gac-view-entry *gacct-text* *gacct-state3* *gacct-ctl*))))
(must-fail-checked
 (defthm gacct-extend-without-prefix
   (implies (fn-gacc-same-cut-p control octl)
            (equal (fn-gacc-extend-view
                    text archive
                    (mv-nth 1 (fn-gacc-prefix (fn-state-articles archive) (fn-state-articles old) nil))
                    (fn-gac-view-entry text old octl))
                   (fn-gac-view-entry text archive control)))))
(assert-event (equal (fn-gacc-view *gacct-text* *gacct-state3* *gacct-ctl*
                                   (fn-gacc-prepare *gacct-text* *gacct-state3* *gacct-ctl*
                                                    *gacct-c1*))
                     (fn-gac-view-entry *gacct-text* *gacct-state3* *gacct-ctl*)))

;; -----------------------------------------------------------------------------
;; The served delegate (the host's path: fn-scr-auth-delegate, reached from
;; host/owner-host.lisp fn-owner-chunk-span-at through fn-oas-read-span): bob's
;; commands answered from the prepared cache are the per-command view's.

; One verifier v2 (group-access-tests' literal): the SCRAM keys computed once.
(defconst *gacct-verifier*
  (let ((keys (fn-scram-keys (fn-nntp-string-octets "correct-horse")
                             (make-list 16 :initial-element 3) 4096)))
    (fn-authsec-verifier
     (make-list 16 :initial-element 3)
     '(42 82 187 10 181 221 230 125 199 188 135 91 193 55 205 245
       177 50 208 139 71 236 67 86 54 24 223 76 55 144 61 51)
     (car keys) (cadr keys))))
(defun gacct-cred (name octet)
  (fn-auth-make-cred (fn-nntp-string-octets name) (make-list 32 :initial-element octet)
                     *gacct-verifier* t))
(defconst *gacct-acfg*
  (fn-auth-make-config t nil t (list (gacct-cred "alice" 7) (gacct-cred "bob" 8))))
(defconst *gacct-table*
  (fn-cfg-access-table (fn-cfg-delta-rows
                        (fn-cfg-account-access "bob" *gacct-text* "fn.private.*"))))
(defconst *gacct-agent* (fn-nntp-string-octets "fn.example.invalid"))
(defconst *gacct-config*
  (fn-inj-make-config-full t *gacct-agent*
                           (list (fn-nntp-string-octets "fn.public")
                                 (fn-nntp-string-octets "fn.private.x"))
                           32768 (list nil nil *gacct-agent* *gacct-table*) nil))
(defconst *gacct-obs* (fn-clock-observation 1000000 843004800000 500 t))
(defconst *gacct-anon* (fn-auth-open-session *gacct-state* nil nil nil *gacct-acfg* nil))
(defconst *gacct-bob*
  (fn-auth-make-session (fn-auth-session-base *gacct-anon*) *gacct-acfg*
                        (fn-nntp-string-octets "bob") (make-list 32 :initial-element 8)
                        nil nil nil nil))
(assert-event (equal (fn-auth-access-read *gacct-bob* *gacct-config*) *gacct-text*))
(assert-event (fn-scr-cached-view *gacct-bob* *gacct-config* *gacct-state* *gacct-pin* *gacct-c1*))
(assert-event (null (fn-scr-cached-view *gacct-bob* *gacct-config* *gacct-state* *gacct-pin* nil)))

(include-book "arena-lift")
(defconst *sr-arena*
  (list (gacct-payload "<p@example.invalid>") (gacct-payload "<s@example.invalid>")
        (gacct-payload "<c@example.invalid>")))
(defun gacct-served (cache text fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (with-local-stobj fn-cat
    (mv-let (r fn-cat)
      (mv (fn-scr-auth-delegate *gacct-bob* nil nil nil cache *gacct-state* *gacct-pin* nil
                                *gacct-config* *gacct-obs* *gacct-obs*
                                (list :command (fn-nntp-string-octets text)) 0 fn-arena fn-cat)
          fn-cat)
      r)))
(defun gacct-reference (text fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (fn-scar-auth-delegate-pinned *gacct-bob* nil nil nil *gacct-state* *gacct-pin* nil
                                *gacct-config* *gacct-obs* *gacct-obs*
                                (list :command (fn-nntp-string-octets text)) fn-arena))
(bpr-lift gacct-served 2)
(bpr-lift gacct-reference 1)
; With the prepared cache and without it, every command's result is the
; reference's (fn-scr-auth-delegate-is-scar-auth-delegate-pinned).
(assert-event
 (and (equal (in-arena-gacct-served *sr-arena* *gacct-c1* "LIST ACTIVE")
             (in-arena-gacct-reference *sr-arena* "LIST ACTIVE"))
      (equal (in-arena-gacct-served *sr-arena* nil "LIST ACTIVE")
             (in-arena-gacct-reference *sr-arena* "LIST ACTIVE"))
      (equal (in-arena-gacct-served *sr-arena* *gacct-c1* "GROUP fn.private.x")
             (in-arena-gacct-reference *sr-arena* "GROUP fn.private.x"))
      (equal (in-arena-gacct-served *sr-arena* *gacct-c1* "STAT <s@example.invalid>")
             (in-arena-gacct-reference *sr-arena* "STAT <s@example.invalid>"))
      (equal (in-arena-gacct-served *sr-arena* *gacct-c1* "OVER <c@example.invalid>")
             (in-arena-gacct-reference *sr-arena* "OVER <c@example.invalid>"))))
; With the forged cache the served LIST ACTIVE lists fn.private.x -- the
; unrestricted archive the forged entry claims -- which the reference hides:
; the equation needs fn-gacc-okp (tests/acl2/served-catalog-chain-tests.lisp
; scct-read-span-needs-the-access-cache).
(assert-event
 (not (equal (in-arena-gacct-served *sr-arena* *gacct-forged* "LIST ACTIVE")
             (in-arena-gacct-reference *sr-arena* "LIST ACTIVE"))))
