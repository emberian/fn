; Witnesses and teeth for books/consumer-artifact-retry.lisp (PRF-137).
;
; The subject is fn-rcl-existing-action, which host/native/hybrid-control.lisp
; fnn-hybrid-control-author asks (through host/owner-host.lisp
; fn-owner-existing-action) on the octets fn-hsig-injected-carrier-octets
; computes, before it commits.  The article is a dated source injected by
; the real fn-inj-decide through a real rendered dual-signature carrier
; (the signatures are opaque octets here: rendering does not verify, the
; route verifies before it), held by the real Store.  The two signature
; sets differ as randomized ML-DSA-65 signing makes them differ: the same
; Ed25519 signature, another ML-DSA-65 signature.
(in-package "ACL2")
(include-book "../../books/consumer-artifact-retry")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defun crt-text (s) (fn-record-string-octets s))
(defconst *crt-crlf* '(13 10))
(defconst *crt-config*
  (fn-inj-make-config t (crt-text "hbox.ember.software") (list (crt-text "fn.test")) 32768))
(defconst *crt-off*
  (fn-inj-make-config nil (crt-text "hbox.ember.software") (list (crt-text "fn.test")) 32768))
(defconst *crt-a* (fn-clock-observation 5000000 843004800000 0 t))
(defconst *crt-b* (fn-clock-observation 5037000 843004837000 0 t))
(defconst *crt-msgid* "<fn-e1.r1@agent-a.invalid>")
(defconst *crt-other-msgid* "<fn-e1.r2@agent-a.invalid>")
(defconst *crt-groups* '("fn.test"))
(defconst *crt-source*
  (append (crt-text "From: agent-a@example.invalid") *crt-crlf*
          (crt-text "Date: Sat, 26 Sep 2026 05:45:22 +0000") *crt-crlf*
          (crt-text "Newsgroups: fn.test") *crt-crlf*
          (crt-text "Subject: report r1") *crt-crlf*
          (crt-text "Message-ID: ") (crt-text *crt-msgid*) *crt-crlf*
          *crt-crlf*
          (crt-text "fn-app: e1/1") *crt-crlf*
          (crt-text "operation-id: r1") *crt-crlf*))
(defconst *crt-principal* (make-list 32 :initial-element 161))
(defconst *crt-keys* (list (cons :ed25519 (make-list 32 :initial-element 11))
                           (cons :ml-dsa-65 (make-list 1952 :initial-element 13))))
(defconst *crt-s1* (list (cons :ed25519 (make-list 64 :initial-element 17))
                         (cons :ml-dsa-65 (make-list 3309 :initial-element 19))))
(defconst *crt-s2* (list (cons :ed25519 (make-list 64 :initial-element 17))
                         (cons :ml-dsa-65 (make-list 3309 :initial-element 23))))

(defun crt-plan (sigs config obs)
  (fn-hsig-injected-carrier-plan *crt-source* *crt-principal* *crt-keys* sigs config obs))
(defun crt-octets (sigs config obs)
  (fn-hsig-injected-carrier-octets *crt-source* *crt-principal* *crt-keys* sigs config obs))

; A Store holding PAYLOAD under MSGID, through the real Store.
(defun crt-store (msgid payload)
  (fn-sn-finish
   (fn-sn-io (fn-sn-io (fn-sn-io
     (fn-sn-prepare
      (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io
        (fn-sn-initial *crt-groups* 10) :start-frontier nil)
        :frontier-file :ok) :frontier-replace :ok) :frontier-directory :ok)
      (fn-record-make 0 0 0 msgid payload *crt-groups*
                      "crt-pin" "crt-subject" "crt-release" 2 841000000))
     :record-file :ok) :record-link :ok) :record-directory :ok)))
(defun crt-held (msgid s)
  (fn-find-article msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))

; Rendering calls the statement codec's attachment, which a defconst's
; evaluation may not; make-event evaluates each value once.
(make-event `(defconst *crt-oa* ',(crt-octets *crt-s1* *crt-config* *crt-a*)))
(make-event `(defconst *crt-ob* ',(crt-octets *crt-s2* *crt-config* *crt-b*)))
(make-event `(defconst *crt-ob-same* ',(crt-octets *crt-s1* *crt-config* *crt-b*)))
(make-event `(defconst *crt-ob-off* ',(crt-octets *crt-s2* *crt-off* *crt-b*)))
(make-event `(defconst *crt-msgids*
               ',(list (fn-inj-decision-msgid (crt-plan *crt-s1* *crt-config* *crt-a*))
                       (fn-inj-decision-msgid (crt-plan *crt-s2* *crt-config* *crt-b*))
                       (fn-inj-decision-msgid (crt-plan *crt-s1* *crt-config* *crt-b*)))))
(defconst *crt-mo* (crt-text *crt-msgid*))
(defconst *crt-s* (crt-store *crt-msgid* *crt-oa*))
(defconst *crt-misfiled* (crt-store *crt-other-msgid* *crt-oa*))
(defconst *crt-empty* *crt-misfiled*)   ; nothing under *crt-msgid*

; fn-sr-a-re-signed-carrier-is-a-conflict, reachable positive witness: every
; hypothesis holds (both octets exist, the first is held, both plans name
; the held Message-ID, the signatures differ) and the answer is :conflict.
(assert-event
 (let ((held (crt-held *crt-msgid* *crt-s*)))
   (and (fn-sn-statep *crt-s*)
        *crt-oa* *crt-ob*
        (equal (fn-article-payload held) *crt-oa*)
        (equal (first *crt-msgids*) *crt-mo*)
        (equal (second *crt-msgids*) *crt-mo*)
        (not (equal *crt-s1* *crt-s2*))
        (not (equal *crt-oa* *crt-ob*))
        (equal (fn-rcl-existing-action *crt-msgid* *crt-ob* *crt-groups* *crt-s*)
               :conflict))))

; fn-cra-a-re-signed-carrier-is-other-octets, witness: both render, the
; signatures differ, and the rendered carriers differ.
(make-event
 `(assert-event
   (let ((r1 ',(fn-hc-render-at-most *fn-article-max-octets* *crt-source*
                                     *crt-principal* *crt-keys* *crt-s1*))
         (r2 ',(fn-hc-render-at-most *fn-article-max-octets* *crt-source*
                                     *crt-principal* *crt-keys* *crt-s2*)))
     (and r1 r2 (not (equal *crt-s1* *crt-s2*)) (not (equal r1 r2))))))

; Hypothesis removed: the signatures are the same.  Every other hypothesis
; holds, and the answer is :duplicate (fn-sr-a-signed-retry-is-already-
; stored), not :conflict.
(assert-event
 (let ((held (crt-held *crt-msgid* *crt-s*)))
   (and *crt-oa* *crt-ob-same*
        (equal (fn-article-payload held) *crt-oa*)
        (equal (first *crt-msgids*) *crt-mo*)
        (equal (third *crt-msgids*) *crt-mo*)
        (equal (fn-rcl-existing-action *crt-msgid* *crt-ob-same* *crt-groups* *crt-s*)
               :duplicate))))
(must-fail
 (defthm crt-re-signed-without-different-signatures
   (let ((held (fn-find-article msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
         (pa (fn-hsig-injected-carrier-plan source principal keys s1 config a))
         (pb (fn-hsig-injected-carrier-plan source principal keys s2 config b))
         (oa (fn-hsig-injected-carrier-octets source principal keys s1 config a))
         (ob (fn-hsig-injected-carrier-octets source principal keys s2 config b)))
     (implies (and oa ob (equal (fn-article-payload held) oa)
                   (equal (fn-inj-decision-msgid pa) (fn-record-string-octets msgid))
                   (equal (fn-inj-decision-msgid pb) (fn-record-string-octets msgid)))
              (equal (fn-rcl-existing-action msgid ob groups s) :conflict)))
   :hints (("Goal" :in-theory (disable fn-hsig-injected-carrier-octets
                                       fn-hsig-injected-carrier-plan fn-rcl-existing-action)))))

; Hypothesis removed: the first carrier is held.  A Store holding it under
; another Message-ID holds nothing under this one; every other hypothesis
; holds, and the answer is :absent (a first acceptance), not :conflict.
(assert-event
 (let ((held (crt-held *crt-msgid* *crt-empty*)))
   (and *crt-oa* *crt-ob*
        (not (equal (fn-article-payload held) *crt-oa*))
        (equal (first *crt-msgids*) *crt-mo*)
        (equal (second *crt-msgids*) *crt-mo*)
        (not (equal *crt-s1* *crt-s2*))
        (not (equal (fn-rcl-existing-action *crt-msgid* *crt-ob* *crt-groups* *crt-empty*)
                    :conflict)))))
(must-fail
 (defthm crt-re-signed-without-the-held-carrier
   (let ((pa (fn-hsig-injected-carrier-plan source principal keys s1 config a))
         (pb (fn-hsig-injected-carrier-plan source principal keys s2 config b))
         (oa (fn-hsig-injected-carrier-octets source principal keys s1 config a))
         (ob (fn-hsig-injected-carrier-octets source principal keys s2 config b)))
     (implies (and oa ob
                   (equal (fn-inj-decision-msgid pa) (fn-record-string-octets msgid))
                   (equal (fn-inj-decision-msgid pb) (fn-record-string-octets msgid))
                   (not (equal s1 s2)))
              (equal (fn-rcl-existing-action msgid ob groups s) :conflict)))
   :hints (("Goal" :in-theory (disable fn-hsig-injected-carrier-octets
                                       fn-hsig-injected-carrier-plan fn-rcl-existing-action)))))

; The remaining hypotheses -- both octets exist and both plans name the
; asked Message-ID -- are the ones fn-sr-a-changed-source-is-a-conflict,
; which this keystone instantiates, carries.  Neither has a conclusion-
; failing witness here: with injection disabled there are no retry octets
; (below) and the verdict on them is still :conflict, and asking under
; another Message-ID that holds the first carrier is still :conflict.  They
; are not claimed necessary, and the weakened theorem is not proved.
(assert-event
 (and *crt-oa* (null *crt-ob-off*)
      (equal (fn-rcl-existing-action *crt-msgid* *crt-ob-off* *crt-groups* *crt-s*)
             :conflict)
      (equal (fn-article-payload (crt-held *crt-other-msgid* *crt-misfiled*)) *crt-oa*)
      (equal (fn-rcl-existing-action *crt-other-msgid* *crt-ob* *crt-groups*
                                     *crt-misfiled*)
             :conflict)))
