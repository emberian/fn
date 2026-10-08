; Teeth for books/served-available-access.lisp (PRF-1328).
;
; The fixture is the catalog of tests/acl2/served-catalog-chain-tests.lisp:
; <a@x> and <c@x> in fn.test, <b@x> cross-posted to fn.test and fn.other,
; their payloads as the arena's logical value.  A connection that has not
; authenticated is served the anonymous rule "fn.other" (account access
; --anonymous --read fn.other): <a@x> and <c@x> are outside its view, <b@x>
; is in it cut to fn.other.  Theorems name the arena's and the catalog's
; logical values where the stobjs are required.
;
; (1) The pre-fix template (tools/available_read_emit.py's AUTH before
; access-check, verbatim below) answers excluded articles: the leak.
; (2) Positive witnesses for the per-event keystones, with an empty and a
; prepared cache: every Message-ID retrieval form of an excluded article is
; the reference's 430; a readable one is the reference's 223.
; (3) Number forms: the template names the excluded group in <b@x>'s Xref.
; (4) Hypothesis removal for fn-av-scr-auth-delegate-restricted-is-reference.
; (5) The read-level predicate inhabited by a served connection's span.

(in-package "ACL2")
(include-book "../../books/served-available-access")

(defconst *avac-p0* (append (fn-record-string-octets "Subject: a") '(13 10 13 10 65 13 10)))
(defconst *avac-p1* (append (fn-record-string-octets "Subject: b") '(13 10 13 10 66 13 10)))
(defconst *avac-p2* (append (fn-record-string-octets "Subject: c") '(13 10 13 10 67 13 10)))

;; A held row from a wire record and its arena handle (numbers by
;; fn-cat-assign, as fn-cat-load assigns them).
(defun avac-held (w handle numbers)
  (fn-held-make (fn-record-sequence w) (fn-record-txid w) (fn-record-generation w)
                (fn-record-msgid w) handle (fn-record-groups w) (fn-record-obligation-id w)
                (fn-record-content-subject w) (fn-record-release-evidence w)
                (fn-record-charge w) (fn-record-stamp w)
                (fn-held-facts-of (fn-record-payload w))
                (fn-held-context-of (fn-record-payload w) nil 0) numbers nil))

(defun avac-catalog (ws handle c)
  (if (consp ws)
      (avac-catalog (cdr ws) (+ 1 handle)
                    (append c (list (fn-cat-assign (avac-held (car ws) handle nil) c))))
    c))

;; Consecutive record sequences 0, 1, 2: the history holds articles only.
(defconst *avac-w0* (fn-record-make 0 1 1 "<a@x>" *avac-p0* '("fn.test") "o" "s" "e" 1 5))
(defconst *avac-w1* (fn-record-make 1 2 2 "<b@x>" *avac-p1* '("fn.test" "fn.other") "o" "s" "e" 1 5))
(defconst *avac-w2* (fn-record-make 2 3 3 "<c@x>" *avac-p2* '("fn.test") "o" "s" "e" 1 5))
(defconst *avac-a* (list *avac-p0* *avac-p1* *avac-p2*))
(defconst *avac-c* (avac-catalog (list *avac-w0* *avac-w1* *avac-w2*) 0 nil))

(defmacro avac-arch (v)
  `(fn-make-state '("fn.test" "fn.other") '(("fn.test" . 4) ("fn.other" . 2))
                  (fn-cat-view-articles ,v *avac-a* *avac-c*) 0 nil nil))
(defmacro avac-index (v)
  `(fn-gidx-pin (fn-midx-build (fn-cat-view-articles ,v *avac-a* *avac-c*))
                (fn-gidx-build (fn-cat-view-articles ,v *avac-a* *avac-c*))))
(defconst *avac-agent* (fn-nntp-string-octets "fn.example.invalid"))
(defconst *avac-table*
  (fn-cfg-access-table (fn-cfg-delta-rows (fn-cfg-account-access "" "fn.other" "*"))))
(defconst *avac-config*
  (fn-inj-make-config-full t *avac-agent*
                           (list (fn-nntp-string-octets "fn.test") (fn-nntp-string-octets "fn.other"))
                           32768 (list nil nil *avac-agent* *avac-table*) nil))
(defconst *avac-obs* (fn-clock-observation 1000000 843004800000 500 t))

(defmacro avac-as () '(fn-auth-open-session (avac-arch 3) nil nil nil nil nil))
(defmacro avac-event (line) `(list :command (fn-nntp-string-octets ,line)))
(defmacro avac-code (r) `(take 3 (cadr (car (fn-post-result-effects ,r)))))
(defconst *avac-430* '(52 51 48))
(defconst *avac-223* '(50 50 51))

;; The restricted view prepared for the rule (books/group-access-cache.lisp),
;; and a corrupted entry that claims the unrestricted archive is the view.
(defmacro avac-prepared ()
  '(list (fn-gacc-entry "fn.other" (avac-arch 3) (fn-gidx-pin-control (avac-index 3))
                        (fn-gac-view-entry "fn.other" (avac-arch 3)
                                           (fn-gidx-pin-control (avac-index 3))))))
(defmacro avac-corrupt ()
  '(list (fn-gacc-entry "fn.other" (avac-arch 3) (fn-gidx-pin-control (avac-index 3))
                        (cons (avac-arch 3) (avac-index 3)))))

;; The host-called step (fn-av-scr-auth-step), the reference
;; (fn-scar-auth-step-pinned), the generated delegate and the reference
;; delegate, over the fixture at catalog version 3.
(defmacro avac-step (as cache config line)
  `(fn-av-scr-auth-step ,as nil nil 3 nil ,cache (avac-arch 3) (avac-index 3) nil ,config
                        *avac-obs* *avac-obs* (avac-event ,line) 3 *avac-a* *avac-c*))
(defmacro avac-reference (as config line)
  `(fn-scar-auth-step-pinned ,as nil nil nil (avac-arch 3) (avac-index 3) nil ,config
                             *avac-obs* *avac-obs* (avac-event ,line) *avac-a*))
(defmacro avac-delegate (as cache config line)
  `(fn-av-scr-auth-delegate ,as nil nil 3 nil ,cache (avac-arch 3) (avac-index 3) nil ,config
                            *avac-obs* *avac-obs* (avac-event ,line) 3 *avac-a* *avac-c*))
(defmacro avac-reference-delegate (as config line)
  `(fn-scar-auth-delegate-pinned ,as nil nil nil (avac-arch 3) (avac-index 3) nil ,config
                                 *avac-obs* *avac-obs* (avac-event ,line) *avac-a*))

; The template access-check removed from the generator, verbatim.
(defun avac-prefix-auth-delegate
    (as live lver arts cache archive index verdicts config observation injection wire-event
        v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (let* ((restricted (fn-auth-access-read as config))
         (view (and restricted (fn-scr-cached-view as config archive index cache)))
         (a (if restricted (if view (fn-ag-car view)
                             (fn-auth-view-archive as config archive)) archive))
         (ix (if restricted (if view (fn-ag-cdr view)
                              (fn-auth-view-index as config archive index)) index))
         (r (fn-av-scr-peer-step
             (fn-auth-view-session as config) live lver arts a ix verdicts
             (fn-auth-view-config as (fn-auth-moderation-config as config) archive)
             observation injection wire-event v fn-arena fn-cat)))
    (fn-post-make-result (fn-auth-with-base as (fn-post-result-session r))
                         (fn-post-result-effects r) (fn-post-result-submission r))))

(defmacro avac-prefix (as line)
  `(avac-prefix-auth-delegate ,as nil nil 3 nil nil (avac-arch 3) (avac-index 3) nil *avac-config*
                              *avac-obs* *avac-obs* (avac-event ,line) 3 *avac-a* *avac-c*))

(defun avac-flat (x)
  (cond ((fn-octet-listp x) x)
        ((consp x) (append (avac-flat (car x)) (avac-flat (cdr x))))
        (t nil)))
(defmacro avac-text (r)
  `(fn-record-octets-string
    (avac-flat (fn-ovw-expand (fn-post-result-effects ,r) *avac-a* *avac-c*))))

; The premises: the anonymous session is a served session, read-restricted
; to "fn.other"; both caches but the corrupt one are fn-gacc-okp.
(defthm avac-premises
  (and (fn-scar-auth-sessionp (avac-as) nil)
       (equal (fn-auth-access-read (avac-as) *avac-config*) "fn.other")
       (fn-gacc-okp nil)
       (fn-gacc-okp (avac-prepared))
       (not (fn-gacc-okp (avac-corrupt)))
       (fn-scr-cached-view (avac-as) *avac-config* (avac-arch 3) (avac-index 3) (avac-prepared)))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; (1) and (2): Message-ID forms of the excluded <a@x>.  The template answers
; STAT 223 and differs from the reference on every form; the host-called
; step is the reference and answers 430, with either cache.

(defmacro avac-msgid-teeth (line)
  `(and (not (equal (avac-prefix (avac-as) ,line)
                    (avac-reference-delegate (avac-as) *avac-config* ,line)))
        (equal (avac-step (avac-as) nil *avac-config* ,line)
               (avac-reference (avac-as) *avac-config* ,line))
        (equal (avac-step (avac-as) (avac-prepared) *avac-config* ,line)
               (avac-reference (avac-as) *avac-config* ,line))
        (equal (avac-code (avac-step (avac-as) nil *avac-config* ,line)) *avac-430*)))

(defthm avac-template-answers-an-excluded-article
  (equal (avac-code (avac-prefix (avac-as) "STAT <a@x>")) *avac-223*)
  :rule-classes nil)

(defthm avac-msgid-forms
  (and (avac-msgid-teeth "STAT <a@x>")
       (avac-msgid-teeth "OVER <a@x>")
       (avac-msgid-teeth "HDR Subject <a@x>")
       (avac-msgid-teeth "XHDR Subject <a@x>")
       (avac-msgid-teeth "XPAT Subject <a@x> *")
       (avac-msgid-teeth "ARTICLE <a@x>")
       (avac-msgid-teeth "HEAD <a@x>")
       (avac-msgid-teeth "BODY <a@x>"))
  :rule-classes nil)

; The excluded article answers exactly as an absent one.
(defthm avac-excluded-is-absent
  (equal (avac-step (avac-as) nil *avac-config* "STAT <a@x>")
         (avac-step (avac-as) nil *avac-config* "STAT <nothere@x>"))
  :rule-classes nil)

; The readable <b@x> is served (the restricted route is not a refusal).
(defthm avac-readable-article
  (and (equal (avac-step (avac-as) (avac-prepared) *avac-config* "STAT <b@x>")
              (avac-reference (avac-as) *avac-config* "STAT <b@x>"))
       (equal (avac-code (avac-step (avac-as) (avac-prepared) *avac-config* "STAT <b@x>"))
              *avac-223*))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; (3) Number forms in the readable group: the template's OVER, HDR and
; ARTICLE of <b@x> name fn.test in its Xref; the host-called step's do not
; and are the reference's.

(defmacro avac-in-other ()
  '(fn-post-result-session (avac-step (avac-as) nil *avac-config* "GROUP fn.other")))

(defmacro avac-number-teeth (line)
  `(and (search "fn.test" (avac-text (avac-prefix (avac-in-other) ,line)))
        (not (search "fn.test" (avac-text (avac-step (avac-in-other) nil *avac-config* ,line))))
        (equal (avac-step (avac-in-other) nil *avac-config* ,line)
               (avac-reference (avac-in-other) *avac-config* ,line))))

(defthm avac-number-forms
  (and (equal (take 3 (cadr (car (fn-post-result-effects
                                  (avac-step (avac-as) nil *avac-config* "GROUP fn.other")))))
              '(50 49 49))
       (equal (take 3 (cadr (car (fn-post-result-effects
                                  (avac-step (avac-as) nil *avac-config* "GROUP fn.test")))))
              '(52 49 49))
       (avac-number-teeth "OVER 1")
       (avac-number-teeth "HDR Xref 1")
       (avac-number-teeth "ARTICLE 1"))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; (4) Hypothesis removal for fn-av-scr-auth-delegate-restricted-is-reference.
; (a) Without the rule: the cache is okp, the session is not restricted, and
; the delegate is not the reference (the catalog's OVER answers a cursor).
(defconst *avac-config-none*
  (fn-inj-make-config-full t *avac-agent*
                           (list (fn-nntp-string-octets "fn.test") (fn-nntp-string-octets "fn.other"))
                           32768 (list nil nil *avac-agent* nil) nil))
(defmacro avac-in-test-unrestricted ()
  '(fn-post-result-session (avac-step (avac-as) nil *avac-config-none* "GROUP fn.test")))
(defthm avac-without-the-rule
  (and (fn-gacc-okp nil)
       (not (fn-auth-access-read (avac-in-test-unrestricted) *avac-config-none*))
       (not (equal (avac-delegate (avac-in-test-unrestricted) nil *avac-config-none* "OVER 1-3")
                   (avac-reference-delegate (avac-in-test-unrestricted) *avac-config-none*
                                            "OVER 1-3"))))
  :rule-classes nil)
; (b) Without fn-gacc-okp: the session is restricted, the corrupt cache is
; not okp, and the delegate serves the excluded article.
(defthm avac-without-an-okp-cache
  (and (fn-auth-access-read (avac-as) *avac-config*)
       (not (fn-gacc-okp (avac-corrupt)))
       (equal (avac-code (avac-delegate (avac-as) (avac-corrupt) *avac-config* "STAT <a@x>"))
              *avac-223*)
       (not (equal (avac-delegate (avac-as) (avac-corrupt) *avac-config* "STAT <a@x>")
                   (avac-reference-delegate (avac-as) *avac-config* "STAT <a@x>"))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; (5) The read-level hypothesis inhabited: a served connection under the
; anonymous rule reads "STAT <a@x>" and "LIST ACTIVE" in one span.  Every
; event goes to the restricted session (fn-av-span-restrictedp), the host's
; span is the legacy span, STAT is 430 and LIST ACTIVE omits fn.test.  Under
; no rule the same span is not restricted and the host's span is not the
; legacy one (the available route answers its LIST ACTIVE): not idle.
(defun avac-line (s) (append (fn-nntp-string-octets s) '(13 10)))
(defconst *avac-span* (append (avac-line "STAT <a@x>") (avac-line "LIST ACTIVE")))
(defun avac-open (config)
  (declare (xargs :verify-guards nil))
  (fn-served-result-conn
   (fn-served-open (fn-initial-state '("fn.test" "fn.other")) 510 8192
                   config *avac-obs* *avac-obs* (fn-auth-open-config))))

(defun avac-span-run (conn octets fn-octets fn-arena fn-cat)
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat) :verify-guards nil))
  (let* ((fn-octets (fn-octets-from-list octets fn-octets))
         (n (fn-octets-len fn-octets)))
    (mv (list (fn-av-span-restrictedp conn 0 n nil nil nil nil nil fn-octets fn-arena fn-cat)
              (equal (fn-av-scr-feed-span conn 0 n nil nil nil nil nil fn-octets fn-arena fn-cat)
                     (fn-scr-feed-span conn 0 n nil nil nil nil nil fn-octets fn-arena fn-cat))
              (fn-record-octets-string
               (avac-flat (fn-served-result-effects
                           (fn-served-counted-result
                            (fn-av-scr-step-span-fast conn 0 n nil nil nil nil nil
                                                      fn-octets fn-arena fn-cat))))))
        fn-octets)))

(defun avac-span (conn octets)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (v fn-octets)
      (with-local-stobj fn-arena
        (mv-let (v fn-octets fn-arena)
          (with-local-stobj fn-cat
            (mv-let (v fn-octets fn-cat)
              (mv-let (v fn-octets) (avac-span-run conn octets fn-octets fn-arena fn-cat)
                (mv v fn-octets fn-cat))
              (mv v fn-octets fn-arena)))
          (mv v fn-octets)))
      v)))

(assert-event
 (let ((r (avac-span (avac-open *avac-config*) *avac-span*)))
   (and (fn-auth-access-read (fn-served-conn-session (avac-open *avac-config*)) *avac-config*)
        (equal (car r) t)
        (equal (cadr r) t)
        (search "430" (caddr r))
        (search "fn.other" (caddr r))
        (not (search "fn.test" (caddr r))))))

(assert-event
 (let ((r (avac-span (avac-open *avac-config-none*) *avac-span*)))
   (and (not (car r))
        (not (cadr r)))))
