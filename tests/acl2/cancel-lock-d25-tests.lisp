; Witnesses and teeth for books/cancel-lock-d25.lisp (SEC-006, PRF-210; D25
; restored under gpt-6's wave-5 review section 3): a same-source retry is
; "already stored here" across accounts and key epochs, the held article and
; its lock are unchanged, the retrying account's cancel opens nothing, and a
; changed user-supplied Cancel-Lock is a conflict.
;
; The subject is fn-rcl-existing-action over fn-own-sub-stored-octets (the
; host's verdict over the octets fn-owner-take stages).  The sources are
; injected by the real fn-inj-decide at two clock readings 37 s apart and
; held by the real Store (the tests/acl2/source-routes-tests.lisp fixture).
(in-package "ACL2")
(include-book "../../books/cancel-lock-d25")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defun cdt-text (s) (fn-record-string-octets s))
(defconst *cdt-agent* (cdt-text "hbox.ember.software"))
(defconst *cdt-config*
  (fn-inj-make-config t *cdt-agent* (list (cdt-text "fn.test")) 32768))
(defconst *cdt-a* (fn-clock-observation 5000000 843004800000 0 t))
(defconst *cdt-b* (fn-clock-observation 5037000 843004837000 0 t))
(defconst *cdt-no-wall* (fn-clock-observation 5037000 nil 0 t))

(defconst *cdt-msgid* "<cd@example.invalid>")
(defconst *cdt-crlf* '(13 10))
(defun cdt-source (extra)
  (append (cdt-text "From: poster@example.invalid") *cdt-crlf*
          (cdt-text "Newsgroups: fn.test") *cdt-crlf*
          (cdt-text "Subject: retry") *cdt-crlf*
          (cdt-text "Message-ID: ") (cdt-text *cdt-msgid*) *cdt-crlf*
          extra
          *cdt-crlf* (cdt-text "hello") *cdt-crlf*))
(defconst *cdt-plain* (cdt-source nil))
; A poster's own Cancel-Lock (user input), and the same source with that
; field's value changed.
(defconst *cdt-locked*
  (cdt-source (append (cdt-text "Cancel-Lock: sha256:AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA=")
                      *cdt-crlf*)))
(defconst *cdt-relocked*
  (cdt-source (append (cdt-text "Cancel-Lock: sha256:BBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB=")
                      *cdt-crlf*)))

(defun cdt-d (source obs) (fn-inj-decide source *cdt-config* obs))

; Two accounts and two key epochs.
(defconst *cdt-e1* (fn-ns-create-entry (cdt-text "fn.test") (make-list 32 :initial-element 7)))
(defconst *cdt-e2* (fn-ns-rotate-entry *cdt-e1* nil (make-list 32 :initial-element 9)))
(defconst *cdt-ring1* (list *cdt-e1*))
(defconst *cdt-ring2* (list *cdt-e2* *cdt-e1*))
(defconst *cdt-alice* (make-list 32 :initial-element 1))
(defconst *cdt-bob* (make-list 32 :initial-element 2))
(defun cdt-sub (source obs login account)
  (fn-own-sub-make-author 4 2 0 (cdt-d source obs) (cdt-text login) account))
(defun cdt-stored (source obs login account ring)
  (fn-own-sub-stored-octets nil (cdt-sub source obs login account) ring))

; A Store holding one payload under *cdt-msgid*, through the real Store.
(defconst *cdt-groups* '("fn.test"))
(defun cdt-store (payload)
  (fn-sn-finish
   (fn-sn-io (fn-sn-io (fn-sn-io
     (fn-sn-prepare
      (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io
        (fn-sn-initial *cdt-groups* 10) :start-frontier nil)
        :frontier-file :ok) :frontier-replace :ok) :frontier-directory :ok)
      (fn-record-make 0 0 0 *cdt-msgid* payload *cdt-groups*
                      "cdt-pin" "cdt-subject" "cdt-release" 2 841000000))
     :record-file :ok) :record-link :ok) :record-directory :ok)))
(defun cdt-held (s)
  (fn-find-article *cdt-msgid* (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))

; Alice posted at A under epoch 1.
(defconst *cdt-held-octets* (cdt-stored *cdt-plain* *cdt-a* "alice" *cdt-alice* *cdt-ring1*))
(defconst *cdt-s* (cdt-store *cdt-held-octets*))
(assert-event (and (fn-sn-statep *cdt-s*)
                   (equal (fn-article-payload (cdt-held *cdt-s*)) *cdt-held-octets*)))
(assert-event (equal (fn-ctl-locks-octets *cdt-held-octets*)
                     (list (fn-cl-lock *cdt-e1* *cdt-alice* (cdt-text *cdt-msgid*)))))

; The complete antecedent of fn-cld-a-retry-by-any-account-or-epoch-is-
; already-stored.
(defun cdt-retry-antecedent (s sub-a sub-b ring-a source a b groups)
  (let ((held (cdt-held s))
        (da (cdt-d source a)) (db (cdt-d source b)))
    (and (equal (fn-own-sub-decision sub-a) da)
         (equal (fn-own-sub-decision sub-b) db)
         (equal (fn-article-payload held) (fn-own-sub-stored-octets nil sub-a ring-a))
         (fn-inj-injectedp da) (fn-inj-injectedp db)
         (equal (fn-inj-decision-msgid da) (cdt-text *cdt-msgid*))
         (equal (fn-inj-decision-msgid db) (cdt-text *cdt-msgid*))
         (equal groups (fn-article-groups held)))))

; Witness 1: bob resends alice's source at B under the same epoch.  His
; stored octets differ from alice's (his lock), yet the verdict is
; :duplicate.
(defconst *cdt-bob-octets* (cdt-stored *cdt-plain* *cdt-b* "bob" *cdt-bob* *cdt-ring1*))
(assert-event
 (and (cdt-retry-antecedent *cdt-s* (cdt-sub *cdt-plain* *cdt-a* "alice" *cdt-alice*)
                            (cdt-sub *cdt-plain* *cdt-b* "bob" *cdt-bob*)
                            *cdt-ring1* *cdt-plain* *cdt-a* *cdt-b* *cdt-groups*)
      (not (equal *cdt-bob-octets* *cdt-held-octets*))
      (equal (fn-rcl-existing-action *cdt-msgid* *cdt-bob-octets* *cdt-groups* *cdt-s*)
             :duplicate)))
; Witness 2: alice resends after a key rotation (epoch 2).
(defconst *cdt-alice-e2-octets*
  (cdt-stored *cdt-plain* *cdt-b* "alice" *cdt-alice* *cdt-ring2*))
(assert-event
 (and (cdt-retry-antecedent *cdt-s* (cdt-sub *cdt-plain* *cdt-a* "alice" *cdt-alice*)
                            (cdt-sub *cdt-plain* *cdt-b* "alice" *cdt-alice*)
                            *cdt-ring1* *cdt-plain* *cdt-a* *cdt-b* *cdt-groups*)
      (not (equal *cdt-alice-e2-octets* *cdt-held-octets*))
      (equal (fn-rcl-existing-action *cdt-msgid* *cdt-alice-e2-octets* *cdt-groups* *cdt-s*)
             :duplicate)))
; A duplicate writes nothing: the held article keeps alice's lock, and the
; retrying account's cancel key opens nothing in it.
(assert-event
 (and (equal (fn-ctl-locks-octets (fn-article-payload (cdt-held *cdt-s*)))
             (list (fn-cl-lock *cdt-e1* *cdt-alice* (cdt-text *cdt-msgid*))))
      (not (fn-ctl-some-key-opens-p
            (fn-cl-ring-keys *cdt-ring2* *cdt-bob* (cdt-text *cdt-msgid*))
            (fn-ctl-locks-octets (fn-article-payload (cdt-held *cdt-s*)))))
      (fn-ctl-some-key-opens-p
       (fn-cl-ring-keys *cdt-ring2* *cdt-alice* (cdt-text *cdt-msgid*))
       (fn-ctl-locks-octets (fn-article-payload (cdt-held *cdt-s*))))))

; Removal of "the same groups": the same source filed elsewhere is a conflict.
(assert-event
 (and (not (equal '("fn.other") (fn-article-groups (cdt-held *cdt-s*))))
      (equal (fn-rcl-existing-action *cdt-msgid* *cdt-bob-octets* '("fn.other") *cdt-s*)
             :conflict)))
; Removal of "injected at B": no wall clock, the decision is a refusal and
; its stored octets (none) are not the held article.
(assert-event
 (and (not (fn-inj-injectedp (cdt-d *cdt-plain* *cdt-no-wall*)))
      (not (equal (fn-rcl-existing-action
                   *cdt-msgid* (cdt-stored *cdt-plain* *cdt-no-wall* "bob" *cdt-bob* *cdt-ring1*)
                   *cdt-groups* *cdt-s*)
                  :duplicate))))
; Removal of "the held article is this source's": a store holding nothing
; under the Message-ID answers nil.
(assert-event
 (equal (fn-rcl-existing-action "<other@example.invalid>" *cdt-bob-octets* *cdt-groups* *cdt-s*)
        nil))
(must-fail
 (defthm cdt-retry-needs-the-same-source
   (let ((held (fn-find-article
                msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
         (da (fn-inj-decide source1 config a))
         (db (fn-inj-decide source2 config b)))
     (implies (and (equal (fn-own-sub-decision sub-a) da)
                   (equal (fn-own-sub-decision sub-b) db)
                   (equal (fn-article-payload held)
                          (fn-own-sub-stored-octets cfg-a sub-a ring-a))
                   (fn-inj-injectedp da) (fn-inj-injectedp db)
                   (equal (fn-inj-decision-msgid da) (fn-record-string-octets msgid))
                   (equal (fn-inj-decision-msgid db) (fn-record-string-octets msgid))
                   (equal groups (fn-article-groups held)))
              (equal (fn-rcl-existing-action
                      msgid (fn-own-sub-stored-octets cfg-b sub-b ring-b) groups s)
                     :duplicate)))))

; ---------------------------------------------------------------------------
; fn-cld-a-changed-source-is-a-conflict-whatever-the-account: a poster's own
; Cancel-Lock is user input.  Held: alice's source carrying her own lock
; (the node adds none); a resend with the lock's value changed is a
; conflict; the unchanged resend by bob is a duplicate.
(defconst *cdt-locked-octets* (cdt-stored *cdt-locked* *cdt-a* "alice" *cdt-alice* *cdt-ring1*))
(defconst *cdt-s2* (cdt-store *cdt-locked-octets*))
(assert-event
 (and (equal *cdt-locked-octets* (fn-inj-decision-octets (cdt-d *cdt-locked* *cdt-a*)))
      (not (equal *cdt-locked* *cdt-relocked*))
      (fn-inj-injectedp (cdt-d *cdt-relocked* *cdt-b*))
      (equal (fn-rcl-existing-action
              *cdt-msgid* (cdt-stored *cdt-relocked* *cdt-b* "alice" *cdt-alice* *cdt-ring1*)
              *cdt-groups* *cdt-s2*)
             :conflict)
      (equal (fn-rcl-existing-action
              *cdt-msgid* (cdt-stored *cdt-locked* *cdt-b* "bob" *cdt-bob* *cdt-ring2*)
              *cdt-groups* *cdt-s2*)
             :duplicate)))
; Removal of "different sources": the node's own lock line differs between
; alice's and bob's copies of *cdt-plain*, and that is no conflict (the
; generated lines are not the source).
(assert-event
 (and (equal *cdt-plain* *cdt-plain*)
      (not (equal (fn-ctl-locks-octets *cdt-bob-octets*)
                  (fn-ctl-locks-octets *cdt-held-octets*)))
      (not (equal (fn-rcl-existing-action *cdt-msgid* *cdt-bob-octets* *cdt-groups* *cdt-s*)
                  :conflict))))
