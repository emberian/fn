; Witnesses for books/store-format-9-records.lisp: the format-9 -> 10 record
; translation, per kind (lane format10-import).
;
; A "format-9" record here is a format-10 fixture with every content
; identity it carries replaced by an algorithm-1 identity (label, 0, version
; 1, algorithm 1, another digest): what a format-9 node wrote for the same
; article.  The translation must give back exactly the format-10 fixture.
(in-package "ACL2")
(include-book "../../books/store-format-9-records")
(include-book "peer-authored-accept-tests")
(include-book "topic-history-admission-tests")
(include-book "stx-accept-records-tests")
(include-book "must-fail-checked")

; -----------------------------------------------------------------------------
; Format-9 twins of format-10 fixtures

; ID (octets) as algorithm 1: its label kept, the version octet 1, the
; algorithm octet 1, the digest reversed.
(defun f9rt-v1-id (id)
  (declare (xargs :guard t :verify-guards nil))
  (let ((n (- (len id) 35)))
    (append (take n id) (list 0 1 1) (rev (nthcdr (+ n 3) id)))))

(defun f9rt-v1-text (text)
  (declare (xargs :guard t :verify-guards nil))
  (fn-record-octets-string
   (fn-id-text (f9rt-v1-id (fn-id-from-text (fn-record-string-octets text))))))

(defun f9rt-v1-record (r)
  (declare (xargs :guard t :verify-guards nil))
  (fn-record-make (fn-record-sequence r) (fn-record-txid r) (fn-record-generation r)
                  (fn-record-msgid r) (fn-record-payload r) (fn-record-groups r)
                  (f9rt-v1-text (fn-record-obligation-id r))
                  (f9rt-v1-text (fn-record-content-subject r))
                  (fn-record-release-evidence r) (fn-record-charge r)
                  (fn-record-stamp r)))

(defun f9rt-v1-composite (e)
  (declare (xargs :guard t :verify-guards nil))
  (let ((r9 (f9rt-v1-record (fn-f9r-composite-article e))))
    (fn-stxa-make-full (fn-stxa-sequence e) (fn-stxa-txid e) (fn-stxa-generation e)
                       (fn-stxa-keyring-generation e) (fn-stxa-profile e)
                       (fn-record-string-octets (fn-record-content-subject r9))
                       (fn-record-encode r9)
                       (fn-stxa-verdict-event e)
                       (fn-stxa-authored-source e)
                       (if (equal (fn-stxa-authored-source e) :legacy)
                           (fn-stxa-authored-id e)
                         (f9rt-v1-id (fn-stxa-authored-id e))))))

; -----------------------------------------------------------------------------
; Signed composites: schema 1 verified (*pat-event*), schema 1 carried
; (*pat-carried-event*), and the report of a topic (*thad-event*)

(make-event `(defconst *f9rt-pat-9* ',(f9rt-v1-composite *pat-event*)))
(make-event `(defconst *f9rt-pat-9-octets* ',(fn-stxa-encode *f9rt-pat-9*)))
; The twin is a format-9 composite: a composite that binds, whose identities
; are algorithm 1 and not the fixture's.
(assert-event (fn-stxa-p *f9rt-pat-9*))
(assert-event (fn-stxa-bindsp *f9rt-pat-9*))
(assert-event (not (equal *f9rt-pat-9* *pat-event*)))
(assert-event (fn-f9r-v1-identity-textp
               (fn-record-content-subject (fn-f9r-composite-article *f9rt-pat-9*))))
(assert-event (fn-f9r-v1-identity-textp
               (fn-record-obligation-id (fn-f9r-composite-article *f9rt-pat-9*))))
(assert-event (not (equal (fn-stxa-authored-id *f9rt-pat-9*)
                          (fn-stxa-authored-id *pat-event*))))
; Format 10 decodes it as a composite (the codec checks no identity).
(assert-event (equal (fn-store-event-decode-exact *f9rt-pat-9-octets*)
                     (list :ok *f9rt-pat-9*)))

; fn-f9r-composite-keeps-what-it-binds and
; fn-f9r-composite-identities-are-format-10s, reachable: the translation is
; the format-10 fixture itself, field by field.
(make-event `(defconst *f9rt-pat-10* ',(fn-f9r-composite *f9rt-pat-9*)))
(assert-event (equal *f9rt-pat-10* *pat-event*))
(assert-event (equal (fn-stxa-verdict-event *f9rt-pat-10*) (fn-stxa-verdict-event *f9rt-pat-9*)))
(assert-event (equal (fn-stxa-authored-source *f9rt-pat-10*) (fn-stxa-authored-source *f9rt-pat-9*)))
(assert-event (equal (fn-stxa-keyring-generation *f9rt-pat-10*) 4))
(assert-event (equal (fn-stxa-authored-id *f9rt-pat-10*)
                     (fn-hsig-authored-source-id (fn-stxa-authored-source *f9rt-pat-9*))))
(assert-event (equal (fn-stxa-content-subject *f9rt-pat-10*)
                     (fn-record-string-octets *pat-subject*)))
; What it asserts: the translated composite binds its article, its verdict and
; the enrolled keys, exactly as replay checks it, with the SAME signatures (no
; key was needed).
(assert-event (fn-hsig-article-event-snapshot-bindsp-v1 *f9rt-pat-10* *tha-snapshot*))
(assert-event (not (fn-hsig-article-event-snapshot-bindsp-v1 *f9rt-pat-9* *tha-snapshot*)))
(assert-event (equal (fn-record-payload (fn-f9r-composite-article *f9rt-pat-10*))
                     (fn-record-payload (fn-f9r-composite-article *f9rt-pat-9*))))

; fn-f9r-step-of-a-composite, reachable: the complete antecedent, then the
; admitted disjunct.
(make-event `(defconst *f9rt-pat-9-decoded* ',(fn-store-event-decode-exact *f9rt-pat-9-octets*)))
(assert-event (equal (car *f9rt-pat-9-decoded*) :ok))
(assert-event (not (fn-record-p (cadr *f9rt-pat-9-decoded*))))
(assert-event (not (fn-store-retention-event-p (cadr *f9rt-pat-9-decoded*))))
(assert-event (fn-stxa-p (cadr *f9rt-pat-9-decoded*)))
(make-event `(defconst *f9rt-pat-step* ',(fn-f9r-step *f9rt-pat-9-octets* nil)))
(assert-event (equal (car *f9rt-pat-step*) :ok))
(assert-event (equal (cadr *f9rt-pat-step*) (fn-stxa-encode *pat-event*)))
(assert-event (fn-stxa-bindsp (fn-f9r-composite (cadr *f9rt-pat-9-decoded*))))

; Carried (D23, keyring generation 0).
(make-event `(defconst *f9rt-carried-9* ',(f9rt-v1-composite *pat-carried-event*)))
(assert-event (fn-stxa-bindsp *f9rt-carried-9*))
(assert-event (not (equal *f9rt-carried-9* *pat-carried-event*)))
(assert-event (equal (fn-f9r-composite *f9rt-carried-9*) *pat-carried-event*))
(assert-event (fn-hsig-article-event-carried-bindsp (fn-f9r-composite *f9rt-carried-9*)))
(assert-event (equal (cadr (fn-f9r-step (fn-stxa-encode *f9rt-carried-9*) nil))
                     (fn-stxa-encode *pat-carried-event*)))

; Schema 0 (:legacy, no authored source): the article's identities and the
; content subject re-derived, the legacy authored identity (none) kept.
(make-event `(defconst *f9rt-legacy-10* ',(fn-f9r-composite *stxa-event*)))
(assert-event (equal (fn-stxa-schema *f9rt-legacy-10*) 0))
(assert-event (null (fn-stxa-authored-id *f9rt-legacy-10*)))
(assert-event (fn-stxa-bindsp *f9rt-legacy-10*))
(assert-event (equal (fn-stxa-content-subject *f9rt-legacy-10*)
                     (fn-id-text (fn-id-subject-of-payload *stxa-payload*))))
(assert-event (equal (car (fn-f9r-step (fn-stxa-encode *stxa-event*) nil)) :ok))

; Hypothesis-removal witness (fn-f9r-step-of-a-composite, the refusal
; disjunct): a composite whose verdict names another Message-ID than its
; article.  Every retained hypothesis holds (it decodes as a composite), the
; translation does not bind, and the step refuses by name.
(make-event
 `(defconst *f9rt-unbound*
    ',(fn-stxa-make 4 9 12 3 *stxa-profile*
                    (fn-record-string-octets *stxa-subject*)
                    (fn-record-encode-impl *stxa-record*)
                    (fn-stxe-encode (fn-stxe-make 4 9 12 "<other@example.invalid>"
                                                  :unverified *fn-stx-token-signature*
                                                  3 *stxa-profile*)))))
(assert-event (equal (car (fn-store-event-decode-exact (fn-stxa-encode *f9rt-unbound*))) :ok))
(assert-event (fn-stxa-p (cadr (fn-store-event-decode-exact (fn-stxa-encode *f9rt-unbound*)))))
(assert-event (not (fn-stxa-bindsp (fn-f9r-composite *f9rt-unbound*))))
(assert-event (equal (fn-f9r-step (fn-stxa-encode *f9rt-unbound*) nil)
                     '(:refused :composite-binding)))
(must-fail-checked
 (assert-event (equal (car (fn-f9r-step (fn-stxa-encode *f9rt-unbound*) nil)) :ok)))

; -----------------------------------------------------------------------------
; Kinds carried verbatim (fn-f9r-step-carries-identity-free-kinds-verbatim)

(defun f9rt-verbatimp (octets)
  (declare (xargs :guard t :verify-guards nil))
  (let ((decoded (fn-store-event-decode-exact octets)))
    (and (equal (car decoded) :ok) (consp (cdr decoded))
         (not (fn-record-p (cadr decoded)))
         (not (fn-store-retention-event-p (cadr decoded)))
         (not (fn-stxa-p (cadr decoded)))
         (fn-f9r-verbatim-kindp (cadr decoded))
         (equal (fn-f9r-step octets '((a . b))) (list :ok octets '((a . b)))))))

; A statement verdict (the verified verdict *pat-event* carries).
(defconst *f9rt-verdict-octets* (fn-stxa-verdict-event *pat-event*))
(assert-event (fn-stxe-p (cadr (fn-store-event-decode-exact *f9rt-verdict-octets*))))
(assert-event (f9rt-verbatimp *f9rt-verdict-octets*))
; A keyring snapshot (an enrollment: principal and keys).
(make-event `(defconst *f9rt-snapshot-octets* ',(fn-store-event-encode *tha-snapshot*)))
(assert-event (fn-stxk-p (cadr (fn-store-event-decode-exact *f9rt-snapshot-octets*))))
(assert-event (f9rt-verbatimp *f9rt-snapshot-octets*))
; The revocation a key statement makes (kind 3).
(make-event `(defconst *f9rt-revoked-octets* ',(fn-store-event-encode *pat-revoked*)))
(assert-event (f9rt-verbatimp *f9rt-revoked-octets*))
; A consumer bootstrap.
(make-event
 `(defconst *f9rt-consumer-octets*
    ',(fn-store-event-encode
       (fn-cpe-make 3 4 4 (list :bootstrap (make-list 32 :initial-element 1)
                                (make-list 32 :initial-element 2))))))
(assert-event (fn-cpe-eventp (cadr (fn-store-event-decode-exact *f9rt-consumer-octets*))))
(assert-event (f9rt-verbatimp *f9rt-consumer-octets*))
; The topic administrator's install.
(make-event
 `(defconst *f9rt-install-octets*
    ',(fn-store-event-encode
       (fn-stmt-value (fn-th-local-admin-install 0 1 1 501 (make-list 32 :initial-element 3) nil)))))
(assert-event (fn-th-local-admin-eventp (cadr (fn-store-event-decode-exact *f9rt-install-octets*))))
(assert-event (f9rt-verbatimp *f9rt-install-octets*))
; Tooth (the kind): an article is not verbatim -- its format-9 twin
; translates to other octets.
(make-event
 `(defconst *f9rt-article-9-octets*
    ',(fn-record-encode (f9rt-v1-record (fn-f9r-composite-article *pat-event*)))))
(assert-event (fn-record-p (cadr (fn-store-event-decode-exact *f9rt-article-9-octets*))))
(assert-event (not (equal (cadr (fn-f9r-step *f9rt-article-9-octets* nil))
                          *f9rt-article-9-octets*)))
(assert-event (equal (cadr (fn-f9r-step *f9rt-article-9-octets* nil))
                     (fn-stxa-article-record *pat-event*)))
(must-fail-checked
 (assert-event (f9rt-verbatimp *f9rt-article-9-octets*)))

; -----------------------------------------------------------------------------
; Topic anchors and admissions: refused by name

; Decoded under format 10 (a format-10 anchor; no format-9 archive holds one).
(make-event `(defconst *f9rt-anchor-octets* ',(fn-store-event-encode *thad-anchor-event*)))
(assert-event (fn-th-topic-eventp (cadr (fn-store-event-decode-exact *f9rt-anchor-octets*))))
(assert-event (equal (fn-f9r-step *f9rt-anchor-octets* nil)
                     '(:refused :signed-format-9-identity)))
; A format-9 anchor: its source identities are algorithm 1, which format 10
; does not decode; the envelope names it.
(defun f9rt-v1-anchor (ev)
  (declare (xargs :guard t :verify-guards nil))
  (let ((ref (fn-th-at 5 ev)))
    (list :topic-anchor (fn-th-at 1 ev) (fn-th-at 2 ev) (fn-th-at 3 ev)
          (f9rt-v1-id (fn-th-at 4 ev))
          (list (fn-th-at 0 ref) (fn-th-at 1 ref) (f9rt-v1-id (fn-th-at 2 ref))
                (fn-th-at 3 ref) (fn-th-at 4 ref) (fn-th-at 5 ref))
          (fn-th-at 6 ev) (fn-th-at 7 ev))))
(make-event
 `(defconst *f9rt-anchor-9-octets*
    ',(fn-stxe-encode-items (fn-th-topic-event-items (f9rt-v1-anchor *thad-anchor-event*)))))
(assert-event (not (equal (car (fn-store-event-decode-exact *f9rt-anchor-9-octets*)) :ok)))
(assert-event (fn-f9r-signed-topic-octetsp *f9rt-anchor-9-octets*))
(assert-event (equal (fn-f9r-step *f9rt-anchor-9-octets* nil)
                     '(:refused :signed-format-9-identity)))
; The import names it by the sequence its envelope carries (the anchor's
; coordinates, 8), so the MANIFEST check reads the right entry.
(assert-event (equal (fn-f9r-signed-topic-sequence *f9rt-anchor-9-octets*) 8))
(assert-event (null (fn-f9r-signed-topic-sequence *f9rt-install-octets*)))
; Tooth: octets that are no record at all are a codec refusal, not a topic.
(assert-event (not (fn-f9r-signed-topic-octetsp '(1 2 3))))
(assert-event (equal (fn-f9r-step '(1 2 3) nil) '(:refused :record-codec)))
; Why no translation exists: the root the anchor re-prepares from is signed,
; and it names its controller by the identity of its key set -- the digest
; this format derives.  A format-9 controller identity (algorithm 1) is not a
; source identity format 10 accepts.
(assert-event (fn-th-source-id-p (fn-th-at 4 *thad-anchor-event*)))
(assert-event (not (fn-th-source-id-p (f9rt-v1-id (fn-th-at 4 *thad-anchor-event*)))))

; -----------------------------------------------------------------------------
; A whole format-9 history (fn-f9r-records): an article, a signed composite,
; a retention event naming the composite's article, the keyring snapshot, the
; verdict, a consumer event and the install -- in order, each translated.

(make-event `(defconst *f9rt-article-10* ',(fn-f9r-composite-article *thad-event*)))
(make-event
 `(defconst *f9rt-undertake-9*
    ',(fn-store-event-encode
       (fn-store-retention-event-make
        :undertake 9 10 1
        (fn-record-obligation-id (fn-f9r-composite-article *f9rt-pat-9*))
        (fn-record-content-subject (fn-f9r-composite-article *f9rt-pat-9*))
        "local" 1))))
(make-event
 `(defconst *f9rt-archive*
    ',(list (cons 1 (fn-record-encode (f9rt-v1-record *f9rt-article-10*)))
            (cons 2 *f9rt-snapshot-octets*)
            (cons 3 *f9rt-pat-9-octets*)
            (cons 4 *f9rt-verdict-octets*)
            (cons 5 *f9rt-consumer-octets*)
            (cons 6 *f9rt-install-octets*)
            (cons 9 *f9rt-undertake-9*))))
(make-event `(defconst *f9rt-imported* ',(fn-f9r-records *f9rt-archive*)))
(assert-event (equal (strip-cars *f9rt-imported*) '(1 2 3 4 5 6 9)))
(assert-event (equal (cdr (nth 0 *f9rt-imported*)) (fn-record-encode *f9rt-article-10*)))
(assert-event (equal (cdr (nth 1 *f9rt-imported*)) *f9rt-snapshot-octets*))
(assert-event (equal (cdr (nth 2 *f9rt-imported*)) (fn-stxa-encode *pat-event*)))
(assert-event (equal (cdr (nth 3 *f9rt-imported*)) *f9rt-verdict-octets*))
(assert-event (equal (cdr (nth 4 *f9rt-imported*)) *f9rt-consumer-octets*))
(assert-event (equal (cdr (nth 5 *f9rt-imported*)) *f9rt-install-octets*))
; The retention event now names the composite's format-10 identities.
(assert-event
 (equal (cadr (fn-store-event-decode-exact (cdr (nth 6 *f9rt-imported*))))
        (fn-store-retention-event-make
         :undertake 9 10 1
         (fn-record-obligation-id (fn-f9r-composite-article *pat-event*))
         (fn-record-content-subject (fn-f9r-composite-article *pat-event*))
         "local" 1)))
; fn-f9r-loop-keeps-sequences, reachable.
(assert-event (equal (car (fn-f9r-loop *f9rt-archive* nil nil)) :ok))
(assert-event (equal (strip-cars (cdr (fn-f9r-loop *f9rt-archive* nil nil)))
                     (rev (strip-cars *f9rt-archive*))))
; A format-9 anchor in the history refuses the whole import, naming its
; sequence; nothing after it is translated.
(assert-event
 (equal (fn-f9r-records (append (take 3 *f9rt-archive*)
                                (list (cons 7 *f9rt-anchor-9-octets*))
                                (nthcdr 3 *f9rt-archive*)))
        '(:refused :signed-format-9-identity 7)))
; The retention event before the composite that defines its identities is
; refused by name (the map is built in order).
(assert-event
 (equal (fn-f9r-records (list (cons 9 *f9rt-undertake-9*) (cons 10 *f9rt-pat-9-octets*)))
        '(:refused :unknown-identity 9)))
