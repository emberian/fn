; Teeth for books/post-fields.lisp (lane host-decisions): the Store prepares'
; field checks, which host/owner-host.lisp, host/store-node-host.lisp and
; host/bp-ingress-host.lisp call instead of the host predicates they defined.
;
; REACHABLE witnesses use the values the node builds for a POST: the content
; subject and obligation identities (books/identity.lisp, the digests
; host/native/io.lisp fnn-metadata-buffer asks ACL2 for) rendered by fn-id-text,
; and the post evidence fn-pfld-post-evidence (host/store-node-host.lisp
; fn-store-prov-post).  BOUNDARY witnesses are constructed field values at and
; past the record's metadata ceiling; they are not claimed reachable.
(in-package "ACL2")
(include-book "../../books/post-fields")
; The digest seam's realiser, so the identities the POST carries evaluate.
(include-book "../../books/crypto-attach")
(include-book "std/testing/must-fail" :dir :system)

(defconst *pft-msgid* '(60 97 64 98 62))                    ; "<a@b>"
(defconst *pft-payload* '(83 117 98 106 101 99 116 58 32 120 13 10 13 10 121))
; fn-frame-digest runs through its attachment, which a defconst may not call.
(make-event `(defconst *pft-subject-id* ',(fn-id-subject-of-payload *pft-payload*)))
(make-event `(defconst *pft-obligation-id*
               ',(fn-id-obligation-of *pft-msgid* *pft-subject-id*)))
(defconst *pft-subject* (fn-id-text *pft-subject-id*))
(defconst *pft-obligation* (fn-id-text *pft-obligation-id*))
(defconst *pft-evidence* (fn-pfld-post-evidence "fn.example" 3))
(defconst *pft-evidence-unset* (fn-pfld-post-evidence "" 3))

; ---------------------------------------------------------------------------
; REACHABLE: fn-pfld-identity-text-is-admitted, complete antecedent and
; conclusion, for both identities the POST carries.
(assert-event (and (fn-cbor-octet-listp *pft-subject-id*) (consp *pft-subject-id*)
                   (<= (len *pft-subject-id*) 128)
                   (fn-pfld-textp *pft-subject*)))
(assert-event (and (fn-cbor-octet-listp *pft-obligation-id*)
                   (consp *pft-obligation-id*)
                   (<= (len *pft-obligation-id*) 128)
                   (fn-pfld-textp *pft-obligation*)))
; REACHABLE: fn-pfld-post-evidence-is-admitted, with a configured identity
; (the canonical wire form) and without one (principal "local").
(assert-event (and (natp 3) (fn-pfld-textp *pft-evidence*)
                   (fn-pfld-textp *pft-evidence-unset*)
                   (fn-prov-durablep (fn-prov-make-post "fn.example" 3))
                   (equal (take 8 *pft-evidence*) *fn-prov-wire-prefix*)))
; fn-pfld-textp-is-a-record-metadata-field on the three reachable fields.
(assert-event (and (fn-record-metadata-bytes-p (fn-record-octets-string *pft-subject*))
                   (fn-record-metadata-bytes-p (fn-record-octets-string *pft-obligation*))
                   (fn-record-metadata-bytes-p (fn-record-octets-string *pft-evidence*))
                   (equal (fn-record-string-octets (fn-record-octets-string *pft-evidence*))
                          *pft-evidence*)))
; REACHABLE: the composed article verdict the host calls, and each conjunct's
; removal refuses (the host answers :invalid).
(assert-event (fn-pfld-article-inputsp *pft-msgid* (len *pft-payload*) '("fn.test")
                                       *pft-obligation* *pft-subject* *pft-evidence* 1))
(assert-event (not (fn-pfld-article-inputsp '(97 64 98) (len *pft-payload*) '("fn.test")
                                            *pft-obligation* *pft-subject* *pft-evidence* 1)))
(assert-event (not (fn-pfld-article-inputsp *pft-msgid* (1+ *fn-record-max-payload*) '("fn.test")
                                            *pft-obligation* *pft-subject* *pft-evidence* 1)))
(assert-event (not (fn-pfld-article-inputsp *pft-msgid* (len *pft-payload*) :bad
                                            *pft-obligation* *pft-subject* *pft-evidence* 1)))
(assert-event (not (fn-pfld-article-inputsp *pft-msgid* (len *pft-payload*) nil
                                            *pft-obligation* *pft-subject* *pft-evidence* 1)))
(assert-event (not (fn-pfld-article-inputsp *pft-msgid* (len *pft-payload*) '("fn.test")
                                            nil *pft-subject* *pft-evidence* 1)))
(assert-event (not (fn-pfld-article-inputsp *pft-msgid* (len *pft-payload*) '("fn.test")
                                            *pft-obligation* '(32) *pft-evidence* 1)))
(assert-event (not (fn-pfld-article-inputsp *pft-msgid* (len *pft-payload*) '("fn.test")
                                            *pft-obligation* *pft-subject* '(127) 1)))
(assert-event (not (fn-pfld-article-inputsp *pft-msgid* (len *pft-payload*) '("fn.test")
                                            *pft-obligation* *pft-subject* *pft-evidence* 0)))
(assert-event (equal (fn-pfld-article-inputsp *pft-msgid* (len *pft-payload*) '("fn.test")
                                              *pft-obligation* *pft-subject* *pft-evidence* 1)
                     t))
; The retention verdict and the lookup verdict.
(assert-event (fn-pfld-retention-inputsp :undertake *pft-obligation* *pft-subject* *pft-evidence* 0))
(assert-event (not (fn-pfld-retention-inputsp :other *pft-obligation* *pft-subject* *pft-evidence* 0)))
(assert-event (not (fn-pfld-retention-inputsp :release *pft-obligation* *pft-subject* *pft-evidence* -1)))
(assert-event (fn-pfld-lookup-inputsp *pft-msgid* '("fn.test")))
(assert-event (not (fn-pfld-lookup-inputsp *pft-msgid* :bad)))
(assert-event (equal (fn-pfld-msgid-validp *pft-msgid*) t))
(assert-event (equal (fn-pfld-msgid-validp '(60 62)) nil))

; ---------------------------------------------------------------------------
; BOUNDARY: the ceiling is the record's, exactly
; (fn-pfld-textp-is-exactly-the-record-metadata-domain).
(defconst *pft-256* (make-list 256 :initial-element 97))
(defconst *pft-257* (make-list 257 :initial-element 97))
(defconst *pft-512* (make-list 512 :initial-element 97))
(assert-event (and (fn-pfld-printable-octetsp *pft-256*) (fn-pfld-textp *pft-256*)
                   (fn-record-metadata-bytes-p (fn-record-octets-string *pft-256*))))
(assert-event (and (fn-pfld-printable-octetsp *pft-257*) (not (fn-pfld-textp *pft-257*))
                   (not (fn-record-metadata-bytes-p (fn-record-octets-string *pft-257*)))))
; The deleted host check admitted 512 printable octets; the record refuses
; them.  The book's check refuses them before a record is built.
(assert-event (and (not (fn-pfld-textp *pft-512*))
                   (not (fn-record-metadata-bytes-p (fn-record-octets-string *pft-512*)))))
; The printable hypothesis of the exactness theorem is needed: a space or DEL
; is a record metadata octet the check refuses.
(assert-event (and (not (fn-pfld-printable-octetsp '(32)))
                   (fn-record-metadata-bytes-p (fn-record-octets-string '(32)))
                   (not (fn-pfld-textp '(32)))))
(assert-event (not (fn-pfld-textp nil)))
; The identity hypothesis of fn-pfld-identity-text-is-admitted is needed: an
; identity of 129 octets renders 258 hexadecimal octets.
(assert-event (not (fn-pfld-textp (fn-id-text (make-list 129 :initial-element 0)))))
(assert-event (fn-pfld-textp (fn-id-text (make-list 128 :initial-element 0))))
; Group-name requests: the codec's 256.
(assert-event (and (fn-pfld-group-name-requestp (make-list 256 :initial-element 97))
                   (not (fn-pfld-group-name-requestp (make-list 257 :initial-element 97)))
                   (fn-pfld-group-name-requestp '(102 110 46 116 101 115 116))
                   (not (fn-pfld-group-name-requestp '(102 110 32 116)))))
; BP ingress inputs.
(assert-event (fn-pfld-bp-ingress-inputsp '(100 116 110) '(100 116 110) '(49) 60
                                          *pft-obligation* *pft-subject* *pft-evidence* 1))
(assert-event (not (fn-pfld-bp-ingress-inputsp '(100 116 110) *pft-257* '(49) 60
                                               *pft-obligation* *pft-subject* *pft-evidence* 1)))
(assert-event (not (fn-pfld-bp-ingress-inputsp '(100 116 110) '(100 116 110) '(49) 60
                                               *pft-obligation* *pft-subject* *pft-evidence* 0)))

; The keystones hold of every input: none of the three is provable without
; its hypothesis.
(must-fail (defthm pft-textp-without-printable
             (equal (fn-pfld-textp xs)
                    (fn-record-metadata-bytes-p (fn-record-octets-string xs)))))
(must-fail (defthm pft-identity-text-without-bound
             (implies (and (fn-cbor-octet-listp identity) (consp identity))
                      (fn-pfld-textp (fn-id-text identity)))))
