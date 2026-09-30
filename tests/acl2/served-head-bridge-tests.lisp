; PKT-772 literal HEAD bridge teeth; no qualification claim before all removals.
(in-package "ACL2")
(include-book "../../books/served-head-bridge")
(include-book "must-fail-checked")
(include-book "arena-lift")

(defconst *hdt-payload*
 (append (fn-nntp-string-octets "Message-ID: <head@fn.test>") '(13 10)
         (fn-nntp-string-octets "Subject: retained header") '(13 10 13 10)
         (fn-nntp-string-octets "body excluded from HEAD") '(13 10)))
(defconst *hdt-article*
 (fn-make-article "<head@fn.test>" 0 '("fn.test") '(("fn.test" . 1)) t 1))
(defconst *hdt-archive*
 (fn-make-state '("fn.test") '(("fn.test" . 2)) (list *hdt-article*) 1 nil nil))
(defconst *hdt-config*
 (fn-inj-make-config-listed t "news.fn.test" '("fn.test") 65536
  (list nil nil (fn-nntp-string-octets "news.fn.test") nil nil nil)))
(defconst *hdt-open*
 (fn-served-result-conn
  (fn-served-open-group-indexed *hdt-archive*
   (fn-midx-build (list *hdt-article*)) (fn-gidx-build (list *hdt-article*))
   nil 510 65536 *hdt-config* nil nil (fn-auth-open-config))))
(defconst *sr-arena* (list *hdt-payload*))
(bpr-lift fn-served-step 2)
(defconst *hdt-selected*
 (fn-served-result-conn
  (in-arena-fn-served-step *sr-arena* *hdt-open*
   (append (fn-nntp-string-octets "GROUP fn.test") '(13 10)))))
(defconst *hdt-token* (fn-nntp-string-octets "<head@fn.test>"))
(defconst *hdt-line* (append *fn-hdc-head-keyword* '(32) *hdt-token*))
(assert-event (and (fn-statep *hdt-archive*) (fn-served-conn-shapep *hdt-selected*)))


(defconst *hdt-as* (fn-served-conn-session *hdt-selected*))
(defconst *hdt-peer* (fn-auth-session-base *hdt-as*))
(defconst *hdt-post* (fn-peer-session-base *hdt-peer*))
(defconst *hdt-reader* (fn-post-session-base *hdt-post*))

; Complete reachable antecedent and full conclusion of the literal public keystone.
(defthm
  hdt-complete-head-positive
  (let*
    ((conn
       (fn-served-make-conn-live
         (fn-wire-make-state :command nil 0 nil nil 0 510 65536)
         (fn-served-conn-session *hdt-selected*)
         (fn-served-conn-archive *hdt-selected*)
         (fn-served-conn-config *hdt-selected*)
         (fn-served-conn-observation *hdt-selected*)
         (fn-served-conn-injection *hdt-selected*)
         (fn-served-conn-verdicts *hdt-selected*)
         (fn-served-conn-index *hdt-selected*)
         (fn-served-conn-group-index *hdt-selected*)
         (fn-served-conn-control *hdt-selected*)
         (fn-served-conn-pinned *hdt-selected*)
         (fn-served-conn-live *hdt-selected*)))
     (as (fn-served-conn-session conn))
     (config (fn-served-conn-config conn))
     (archive (fn-served-conn-archive conn))
     (index (fn-served-conn-pinned-index conn))
     (observation (fn-served-conn-observation conn))
     (peer (fn-auth-view-session as config))
     (viewarchive (fn-auth-view-archive as config archive))
     (viewindex (fn-auth-view-index as config archive index))
     (viewconfig (fn-auth-view-config as (fn-auth-moderation-config as config) archive))
     (ps (fn-peer-session-base peer))
     (session (fn-post-session-base ps))
     (env (fn-post-reader-env viewconfig observation))
     (server (fn-nntp-xref-server env))
     (r
       (fn-rcompat-retrieval
         session
         viewarchive
         (fn-gidx-pin-trie viewindex)
         :head
         (list *hdt-token*)
         server
         (list *hdt-payload*)))
     (p (fn-served-step conn (append *hdt-line* (quote (13 10))) (list *hdt-payload*))))
    (and
      (and
        (fn-wire-statep (fn-served-conn-wire conn))
        (<= (len *hdt-line*) 510)
        (fn-auth-sessionp as)
        (not (fn-auth-session-handshakingp as))
        (not (fn-auth-sasl-waitingp as))
        (or
          (not (fn-auth-config-requiredp (fn-auth-session-config as)))
          (fn-auth-session-subject as))
        (null (fn-peer-session-peer peer))
        (not (fn-post-session-awaiting ps))
        (equal (fn-nntp-session-openp session) t)
        (fn-nntp-session-projected session)
        (fn-nntp-command-inputp *hdt-line*)
        (equal (fn-nntp-tokenize *hdt-line*) (list *fn-hdc-head-keyword* *hdt-token*))
        server
        (fn-gidx-pinp viewindex)
        (not (fn-nntp-number-withdrawn-p session viewarchive viewindex *hdt-token*))
        (not
          (and
            (fn-nntp-message-id-tokenp *hdt-token*)
            (fn-nntp-msgid-withdrawn-p viewindex *hdt-token*))))
      (and
        (equal (fn-served-result-effects p) (fn-nntp-result-effects r))
        (equal
          (fn-post-session-base
            (fn-peer-session-base
              (fn-auth-session-base (fn-served-conn-session (fn-served-result-conn p)))))
          (fn-nntp-result-session r))
        (equal (fn-served-conn-pinned (fn-served-result-conn p)) (fn-served-conn-pinned conn))
        (equal (fn-served-conn-archive (fn-served-result-conn p)) (fn-served-conn-archive conn))
        (equal (fn-served-conn-index (fn-served-result-conn p)) (fn-served-conn-index conn)))))
  :rule-classes
  nil)

; Corrupted-state hypothesis removal: wire-state.
; Every other retained hypothesis holds; the omitted one and full conclusion fail.
(defthm
  hdt-without-wire-state
  (let*
    ((conn
       (fn-served-make-conn-live
         (fn-wire-make-state :command nil 0 nil nil 0 510 -1)
         (fn-served-conn-session *hdt-selected*)
         (fn-served-conn-archive *hdt-selected*)
         (fn-served-conn-config *hdt-selected*)
         (fn-served-conn-observation *hdt-selected*)
         (fn-served-conn-injection *hdt-selected*)
         (fn-served-conn-verdicts *hdt-selected*)
         (fn-served-conn-index *hdt-selected*)
         (fn-served-conn-group-index *hdt-selected*)
         (fn-served-conn-control *hdt-selected*)
         (fn-served-conn-pinned *hdt-selected*)
         (fn-served-conn-live *hdt-selected*)))
     (as (fn-served-conn-session conn))
     (config (fn-served-conn-config conn))
     (archive (fn-served-conn-archive conn))
     (index (fn-served-conn-pinned-index conn))
     (observation (fn-served-conn-observation conn))
     (peer (fn-auth-view-session as config))
     (viewarchive (fn-auth-view-archive as config archive))
     (viewindex (fn-auth-view-index as config archive index))
     (viewconfig (fn-auth-view-config as (fn-auth-moderation-config as config) archive))
     (ps (fn-peer-session-base peer))
     (session (fn-post-session-base ps))
     (env (fn-post-reader-env viewconfig observation))
     (server (fn-nntp-xref-server env))
     (r
       (fn-rcompat-retrieval
         session
         viewarchive
         (fn-gidx-pin-trie viewindex)
         :head
         (list *hdt-token*)
         server
         (list *hdt-payload*)))
     (p (fn-served-step conn (append *hdt-line* (quote (13 10))) (list *hdt-payload*))))
    (and
      (<= (len *hdt-line*) 510)
      (fn-auth-sessionp as)
      (not (fn-auth-session-handshakingp as))
      (not (fn-auth-sasl-waitingp as))
      (or
        (not (fn-auth-config-requiredp (fn-auth-session-config as)))
        (fn-auth-session-subject as))
      (null (fn-peer-session-peer peer))
      (not (fn-post-session-awaiting ps))
      (equal (fn-nntp-session-openp session) t)
      (fn-nntp-session-projected session)
      (fn-nntp-command-inputp *hdt-line*)
      (equal (fn-nntp-tokenize *hdt-line*) (list *fn-hdc-head-keyword* *hdt-token*))
      server
      (fn-gidx-pinp viewindex)
      (not (fn-nntp-number-withdrawn-p session viewarchive viewindex *hdt-token*))
      (not
        (and
          (fn-nntp-message-id-tokenp *hdt-token*)
          (fn-nntp-msgid-withdrawn-p viewindex *hdt-token*)))
      (not (fn-wire-statep (fn-served-conn-wire conn)))
      (not
        (and
          (equal (fn-served-result-effects p) (fn-nntp-result-effects r))
          (equal
            (fn-post-session-base
              (fn-peer-session-base
                (fn-auth-session-base (fn-served-conn-session (fn-served-result-conn p)))))
            (fn-nntp-result-session r))
          (equal (fn-served-conn-pinned (fn-served-result-conn p)) (fn-served-conn-pinned conn))
          (equal
            (fn-served-conn-archive (fn-served-result-conn p))
            (fn-served-conn-archive conn))
          (equal (fn-served-conn-index (fn-served-result-conn p)) (fn-served-conn-index conn))))))
  :rule-classes
  nil)

; Session/input hypothesis removal: wire-line-limit.
; Every other retained hypothesis holds; the omitted one and full conclusion fail.
(defthm
  hdt-without-wire-line-limit
  (let*
    ((conn
       (fn-served-make-conn-live
         (fn-wire-make-state :command nil 0 nil nil 0 1 65536)
         (fn-served-conn-session *hdt-selected*)
         (fn-served-conn-archive *hdt-selected*)
         (fn-served-conn-config *hdt-selected*)
         (fn-served-conn-observation *hdt-selected*)
         (fn-served-conn-injection *hdt-selected*)
         (fn-served-conn-verdicts *hdt-selected*)
         (fn-served-conn-index *hdt-selected*)
         (fn-served-conn-group-index *hdt-selected*)
         (fn-served-conn-control *hdt-selected*)
         (fn-served-conn-pinned *hdt-selected*)
         (fn-served-conn-live *hdt-selected*)))
     (as (fn-served-conn-session conn))
     (config (fn-served-conn-config conn))
     (archive (fn-served-conn-archive conn))
     (index (fn-served-conn-pinned-index conn))
     (observation (fn-served-conn-observation conn))
     (peer (fn-auth-view-session as config))
     (viewarchive (fn-auth-view-archive as config archive))
     (viewindex (fn-auth-view-index as config archive index))
     (viewconfig (fn-auth-view-config as (fn-auth-moderation-config as config) archive))
     (ps (fn-peer-session-base peer))
     (session (fn-post-session-base ps))
     (env (fn-post-reader-env viewconfig observation))
     (server (fn-nntp-xref-server env))
     (r
       (fn-rcompat-retrieval
         session
         viewarchive
         (fn-gidx-pin-trie viewindex)
         :head
         (list *hdt-token*)
         server
         (list *hdt-payload*)))
     (p (fn-served-step conn (append *hdt-line* (quote (13 10))) (list *hdt-payload*))))
    (and
      (fn-wire-statep (fn-served-conn-wire conn))
      (fn-auth-sessionp as)
      (not (fn-auth-session-handshakingp as))
      (not (fn-auth-sasl-waitingp as))
      (or
        (not (fn-auth-config-requiredp (fn-auth-session-config as)))
        (fn-auth-session-subject as))
      (null (fn-peer-session-peer peer))
      (not (fn-post-session-awaiting ps))
      (equal (fn-nntp-session-openp session) t)
      (fn-nntp-session-projected session)
      (fn-nntp-command-inputp *hdt-line*)
      (equal (fn-nntp-tokenize *hdt-line*) (list *fn-hdc-head-keyword* *hdt-token*))
      server
      (fn-gidx-pinp viewindex)
      (not (fn-nntp-number-withdrawn-p session viewarchive viewindex *hdt-token*))
      (not
        (and
          (fn-nntp-message-id-tokenp *hdt-token*)
          (fn-nntp-msgid-withdrawn-p viewindex *hdt-token*)))
      (not (<= (len *hdt-line*) 1))
      (not
        (and
          (equal (fn-served-result-effects p) (fn-nntp-result-effects r))
          (equal
            (fn-post-session-base
              (fn-peer-session-base
                (fn-auth-session-base (fn-served-conn-session (fn-served-result-conn p)))))
            (fn-nntp-result-session r))
          (equal (fn-served-conn-pinned (fn-served-result-conn p)) (fn-served-conn-pinned conn))
          (equal
            (fn-served-conn-archive (fn-served-result-conn p))
            (fn-served-conn-archive conn))
          (equal (fn-served-conn-index (fn-served-result-conn p)) (fn-served-conn-index conn))))))
  :rule-classes
  nil)

; Corrupted-state hypothesis removal: auth-shape.
; Every other retained hypothesis holds; the omitted one and full conclusion fail.
(defthm
  hdt-without-auth-shape
  (let*
    ((conn
       (fn-served-make-conn-live
         (fn-wire-make-state :command nil 0 nil nil 0 510 65536)
         (fn-served-conn-session (update-nth 1 (append *hdt-as* (list nil)) *hdt-selected*))
         (fn-served-conn-archive (update-nth 1 (append *hdt-as* (list nil)) *hdt-selected*))
         (fn-served-conn-config (update-nth 1 (append *hdt-as* (list nil)) *hdt-selected*))
         (fn-served-conn-observation (update-nth 1 (append *hdt-as* (list nil)) *hdt-selected*))
         (fn-served-conn-injection (update-nth 1 (append *hdt-as* (list nil)) *hdt-selected*))
         (fn-served-conn-verdicts (update-nth 1 (append *hdt-as* (list nil)) *hdt-selected*))
         (fn-served-conn-index (update-nth 1 (append *hdt-as* (list nil)) *hdt-selected*))
         (fn-served-conn-group-index (update-nth 1 (append *hdt-as* (list nil)) *hdt-selected*))
         (fn-served-conn-control (update-nth 1 (append *hdt-as* (list nil)) *hdt-selected*))
         (fn-served-conn-pinned (update-nth 1 (append *hdt-as* (list nil)) *hdt-selected*))
         (fn-served-conn-live (update-nth 1 (append *hdt-as* (list nil)) *hdt-selected*))))
     (as (fn-served-conn-session conn))
     (config (fn-served-conn-config conn))
     (archive (fn-served-conn-archive conn))
     (index (fn-served-conn-pinned-index conn))
     (observation (fn-served-conn-observation conn))
     (peer (fn-auth-view-session as config))
     (viewarchive (fn-auth-view-archive as config archive))
     (viewindex (fn-auth-view-index as config archive index))
     (viewconfig (fn-auth-view-config as (fn-auth-moderation-config as config) archive))
     (ps (fn-peer-session-base peer))
     (session (fn-post-session-base ps))
     (env (fn-post-reader-env viewconfig observation))
     (server (fn-nntp-xref-server env))
     (r
       (fn-rcompat-retrieval
         session
         viewarchive
         (fn-gidx-pin-trie viewindex)
         :head
         (list *hdt-token*)
         server
         (list *hdt-payload*)))
     (p (fn-served-step conn (append *hdt-line* (quote (13 10))) (list *hdt-payload*))))
    (and
      (fn-wire-statep (fn-served-conn-wire conn))
      (<= (len *hdt-line*) 510)
      (not (fn-auth-session-handshakingp as))
      (not (fn-auth-sasl-waitingp as))
      (or
        (not (fn-auth-config-requiredp (fn-auth-session-config as)))
        (fn-auth-session-subject as))
      (null (fn-peer-session-peer peer))
      (not (fn-post-session-awaiting ps))
      (equal (fn-nntp-session-openp session) t)
      (fn-nntp-session-projected session)
      (fn-nntp-command-inputp *hdt-line*)
      (equal (fn-nntp-tokenize *hdt-line*) (list *fn-hdc-head-keyword* *hdt-token*))
      server
      (fn-gidx-pinp viewindex)
      (not (fn-nntp-number-withdrawn-p session viewarchive viewindex *hdt-token*))
      (not
        (and
          (fn-nntp-message-id-tokenp *hdt-token*)
          (fn-nntp-msgid-withdrawn-p viewindex *hdt-token*)))
      (not (fn-auth-sessionp as))
      (not
        (and
          (equal (fn-served-result-effects p) (fn-nntp-result-effects r))
          (equal
            (fn-post-session-base
              (fn-peer-session-base
                (fn-auth-session-base (fn-served-conn-session (fn-served-result-conn p)))))
            (fn-nntp-result-session r))
          (equal (fn-served-conn-pinned (fn-served-result-conn p)) (fn-served-conn-pinned conn))
          (equal
            (fn-served-conn-archive (fn-served-result-conn p))
            (fn-served-conn-archive conn))
          (equal (fn-served-conn-index (fn-served-result-conn p)) (fn-served-conn-index conn))))))
  :rule-classes
  nil)

; Session/input hypothesis removal: handshake.
; Every other retained hypothesis holds; the omitted one and full conclusion fail.
(defthm
  hdt-without-handshake
  (let*
    ((conn
       (fn-served-make-conn-live
         (fn-wire-make-state :command nil 0 nil nil 0 510 65536)
         (fn-served-conn-session (update-nth 1 (update-nth 5 t *hdt-as*) *hdt-selected*))
         (fn-served-conn-archive (update-nth 1 (update-nth 5 t *hdt-as*) *hdt-selected*))
         (fn-served-conn-config (update-nth 1 (update-nth 5 t *hdt-as*) *hdt-selected*))
         (fn-served-conn-observation (update-nth 1 (update-nth 5 t *hdt-as*) *hdt-selected*))
         (fn-served-conn-injection (update-nth 1 (update-nth 5 t *hdt-as*) *hdt-selected*))
         (fn-served-conn-verdicts (update-nth 1 (update-nth 5 t *hdt-as*) *hdt-selected*))
         (fn-served-conn-index (update-nth 1 (update-nth 5 t *hdt-as*) *hdt-selected*))
         (fn-served-conn-group-index (update-nth 1 (update-nth 5 t *hdt-as*) *hdt-selected*))
         (fn-served-conn-control (update-nth 1 (update-nth 5 t *hdt-as*) *hdt-selected*))
         (fn-served-conn-pinned (update-nth 1 (update-nth 5 t *hdt-as*) *hdt-selected*))
         (fn-served-conn-live (update-nth 1 (update-nth 5 t *hdt-as*) *hdt-selected*))))
     (as (fn-served-conn-session conn))
     (config (fn-served-conn-config conn))
     (archive (fn-served-conn-archive conn))
     (index (fn-served-conn-pinned-index conn))
     (observation (fn-served-conn-observation conn))
     (peer (fn-auth-view-session as config))
     (viewarchive (fn-auth-view-archive as config archive))
     (viewindex (fn-auth-view-index as config archive index))
     (viewconfig (fn-auth-view-config as (fn-auth-moderation-config as config) archive))
     (ps (fn-peer-session-base peer))
     (session (fn-post-session-base ps))
     (env (fn-post-reader-env viewconfig observation))
     (server (fn-nntp-xref-server env))
     (r
       (fn-rcompat-retrieval
         session
         viewarchive
         (fn-gidx-pin-trie viewindex)
         :head
         (list *hdt-token*)
         server
         (list *hdt-payload*)))
     (p (fn-served-step conn (append *hdt-line* (quote (13 10))) (list *hdt-payload*))))
    (and
      (fn-wire-statep (fn-served-conn-wire conn))
      (<= (len *hdt-line*) 510)
      (fn-auth-sessionp as)
      (not (fn-auth-sasl-waitingp as))
      (or
        (not (fn-auth-config-requiredp (fn-auth-session-config as)))
        (fn-auth-session-subject as))
      (null (fn-peer-session-peer peer))
      (not (fn-post-session-awaiting ps))
      (equal (fn-nntp-session-openp session) t)
      (fn-nntp-session-projected session)
      (fn-nntp-command-inputp *hdt-line*)
      (equal (fn-nntp-tokenize *hdt-line*) (list *fn-hdc-head-keyword* *hdt-token*))
      server
      (fn-gidx-pinp viewindex)
      (not (fn-nntp-number-withdrawn-p session viewarchive viewindex *hdt-token*))
      (not
        (and
          (fn-nntp-message-id-tokenp *hdt-token*)
          (fn-nntp-msgid-withdrawn-p viewindex *hdt-token*)))
      (not (not (fn-auth-session-handshakingp as)))
      (not
        (and
          (equal (fn-served-result-effects p) (fn-nntp-result-effects r))
          (equal
            (fn-post-session-base
              (fn-peer-session-base
                (fn-auth-session-base (fn-served-conn-session (fn-served-result-conn p)))))
            (fn-nntp-result-session r))
          (equal (fn-served-conn-pinned (fn-served-result-conn p)) (fn-served-conn-pinned conn))
          (equal
            (fn-served-conn-archive (fn-served-result-conn p))
            (fn-served-conn-archive conn))
          (equal (fn-served-conn-index (fn-served-result-conn p)) (fn-served-conn-index conn))))))
  :rule-classes
  nil)

; Session/input hypothesis removal: sasl-phase.
; Every other retained hypothesis holds; the omitted one and full conclusion fail.
(defthm
  hdt-without-sasl-phase
  (let*
    ((conn
       (fn-served-make-conn-live
         (fn-wire-make-state :command nil 0 nil nil 0 510 65536)
         (fn-served-conn-session
           (update-nth 1 (update-nth 2 (quote (:sasl-plain)) *hdt-as*) *hdt-selected*))
         (fn-served-conn-archive
           (update-nth 1 (update-nth 2 (quote (:sasl-plain)) *hdt-as*) *hdt-selected*))
         (fn-served-conn-config
           (update-nth 1 (update-nth 2 (quote (:sasl-plain)) *hdt-as*) *hdt-selected*))
         (fn-served-conn-observation
           (update-nth 1 (update-nth 2 (quote (:sasl-plain)) *hdt-as*) *hdt-selected*))
         (fn-served-conn-injection
           (update-nth 1 (update-nth 2 (quote (:sasl-plain)) *hdt-as*) *hdt-selected*))
         (fn-served-conn-verdicts
           (update-nth 1 (update-nth 2 (quote (:sasl-plain)) *hdt-as*) *hdt-selected*))
         (fn-served-conn-index
           (update-nth 1 (update-nth 2 (quote (:sasl-plain)) *hdt-as*) *hdt-selected*))
         (fn-served-conn-group-index
           (update-nth 1 (update-nth 2 (quote (:sasl-plain)) *hdt-as*) *hdt-selected*))
         (fn-served-conn-control
           (update-nth 1 (update-nth 2 (quote (:sasl-plain)) *hdt-as*) *hdt-selected*))
         (fn-served-conn-pinned
           (update-nth 1 (update-nth 2 (quote (:sasl-plain)) *hdt-as*) *hdt-selected*))
         (fn-served-conn-live
           (update-nth 1 (update-nth 2 (quote (:sasl-plain)) *hdt-as*) *hdt-selected*))))
     (as (fn-served-conn-session conn))
     (config (fn-served-conn-config conn))
     (archive (fn-served-conn-archive conn))
     (index (fn-served-conn-pinned-index conn))
     (observation (fn-served-conn-observation conn))
     (peer (fn-auth-view-session as config))
     (viewarchive (fn-auth-view-archive as config archive))
     (viewindex (fn-auth-view-index as config archive index))
     (viewconfig (fn-auth-view-config as (fn-auth-moderation-config as config) archive))
     (ps (fn-peer-session-base peer))
     (session (fn-post-session-base ps))
     (env (fn-post-reader-env viewconfig observation))
     (server (fn-nntp-xref-server env))
     (r
       (fn-rcompat-retrieval
         session
         viewarchive
         (fn-gidx-pin-trie viewindex)
         :head
         (list *hdt-token*)
         server
         (list *hdt-payload*)))
     (p (fn-served-step conn (append *hdt-line* (quote (13 10))) (list *hdt-payload*))))
    (and
      (fn-wire-statep (fn-served-conn-wire conn))
      (<= (len *hdt-line*) 510)
      (fn-auth-sessionp as)
      (not (fn-auth-session-handshakingp as))
      (or
        (not (fn-auth-config-requiredp (fn-auth-session-config as)))
        (fn-auth-session-subject as))
      (null (fn-peer-session-peer peer))
      (not (fn-post-session-awaiting ps))
      (equal (fn-nntp-session-openp session) t)
      (fn-nntp-session-projected session)
      (fn-nntp-command-inputp *hdt-line*)
      (equal (fn-nntp-tokenize *hdt-line*) (list *fn-hdc-head-keyword* *hdt-token*))
      server
      (fn-gidx-pinp viewindex)
      (not (fn-nntp-number-withdrawn-p session viewarchive viewindex *hdt-token*))
      (not
        (and
          (fn-nntp-message-id-tokenp *hdt-token*)
          (fn-nntp-msgid-withdrawn-p viewindex *hdt-token*)))
      (not (not (fn-auth-sasl-waitingp as)))
      (not
        (and
          (equal (fn-served-result-effects p) (fn-nntp-result-effects r))
          (equal
            (fn-post-session-base
              (fn-peer-session-base
                (fn-auth-session-base (fn-served-conn-session (fn-served-result-conn p)))))
            (fn-nntp-result-session r))
          (equal (fn-served-conn-pinned (fn-served-result-conn p)) (fn-served-conn-pinned conn))
          (equal
            (fn-served-conn-archive (fn-served-result-conn p))
            (fn-served-conn-archive conn))
          (equal (fn-served-conn-index (fn-served-result-conn p)) (fn-served-conn-index conn))))))
  :rule-classes
  nil)

; Session/input hypothesis removal: authorization.
; Every other retained hypothesis holds; the omitted one and full conclusion fail.
(defthm
  hdt-without-authorization
  (let*
    ((conn
       (fn-served-make-conn-live
         (fn-wire-make-state :command nil 0 nil nil 0 510 65536)
         (fn-served-conn-session
           (update-nth
             1
             (update-nth 1 (fn-auth-make-config t nil nil nil) *hdt-as*)
             *hdt-selected*))
         (fn-served-conn-archive
           (update-nth
             1
             (update-nth 1 (fn-auth-make-config t nil nil nil) *hdt-as*)
             *hdt-selected*))
         (fn-served-conn-config
           (update-nth
             1
             (update-nth 1 (fn-auth-make-config t nil nil nil) *hdt-as*)
             *hdt-selected*))
         (fn-served-conn-observation
           (update-nth
             1
             (update-nth 1 (fn-auth-make-config t nil nil nil) *hdt-as*)
             *hdt-selected*))
         (fn-served-conn-injection
           (update-nth
             1
             (update-nth 1 (fn-auth-make-config t nil nil nil) *hdt-as*)
             *hdt-selected*))
         (fn-served-conn-verdicts
           (update-nth
             1
             (update-nth 1 (fn-auth-make-config t nil nil nil) *hdt-as*)
             *hdt-selected*))
         (fn-served-conn-index
           (update-nth
             1
             (update-nth 1 (fn-auth-make-config t nil nil nil) *hdt-as*)
             *hdt-selected*))
         (fn-served-conn-group-index
           (update-nth
             1
             (update-nth 1 (fn-auth-make-config t nil nil nil) *hdt-as*)
             *hdt-selected*))
         (fn-served-conn-control
           (update-nth
             1
             (update-nth 1 (fn-auth-make-config t nil nil nil) *hdt-as*)
             *hdt-selected*))
         (fn-served-conn-pinned
           (update-nth
             1
             (update-nth 1 (fn-auth-make-config t nil nil nil) *hdt-as*)
             *hdt-selected*))
         (fn-served-conn-live
           (update-nth
             1
             (update-nth 1 (fn-auth-make-config t nil nil nil) *hdt-as*)
             *hdt-selected*))))
     (as (fn-served-conn-session conn))
     (config (fn-served-conn-config conn))
     (archive (fn-served-conn-archive conn))
     (index (fn-served-conn-pinned-index conn))
     (observation (fn-served-conn-observation conn))
     (peer (fn-auth-view-session as config))
     (viewarchive (fn-auth-view-archive as config archive))
     (viewindex (fn-auth-view-index as config archive index))
     (viewconfig (fn-auth-view-config as (fn-auth-moderation-config as config) archive))
     (ps (fn-peer-session-base peer))
     (session (fn-post-session-base ps))
     (env (fn-post-reader-env viewconfig observation))
     (server (fn-nntp-xref-server env))
     (r
       (fn-rcompat-retrieval
         session
         viewarchive
         (fn-gidx-pin-trie viewindex)
         :head
         (list *hdt-token*)
         server
         (list *hdt-payload*)))
     (p (fn-served-step conn (append *hdt-line* (quote (13 10))) (list *hdt-payload*))))
    (and
      (fn-wire-statep (fn-served-conn-wire conn))
      (<= (len *hdt-line*) 510)
      (fn-auth-sessionp as)
      (not (fn-auth-session-handshakingp as))
      (not (fn-auth-sasl-waitingp as))
      (null (fn-peer-session-peer peer))
      (not (fn-post-session-awaiting ps))
      (equal (fn-nntp-session-openp session) t)
      (fn-nntp-session-projected session)
      (fn-nntp-command-inputp *hdt-line*)
      (equal (fn-nntp-tokenize *hdt-line*) (list *fn-hdc-head-keyword* *hdt-token*))
      server
      (fn-gidx-pinp viewindex)
      (not (fn-nntp-number-withdrawn-p session viewarchive viewindex *hdt-token*))
      (not
        (and
          (fn-nntp-message-id-tokenp *hdt-token*)
          (fn-nntp-msgid-withdrawn-p viewindex *hdt-token*)))
      (not
        (or
          (not (fn-auth-config-requiredp (fn-auth-session-config as)))
          (fn-auth-session-subject as)))
      (not
        (and
          (equal (fn-served-result-effects p) (fn-nntp-result-effects r))
          (equal
            (fn-post-session-base
              (fn-peer-session-base
                (fn-auth-session-base (fn-served-conn-session (fn-served-result-conn p)))))
            (fn-nntp-result-session r))
          (equal (fn-served-conn-pinned (fn-served-result-conn p)) (fn-served-conn-pinned conn))
          (equal
            (fn-served-conn-archive (fn-served-result-conn p))
            (fn-served-conn-archive conn))
          (equal (fn-served-conn-index (fn-served-result-conn p)) (fn-served-conn-index conn))))))
  :rule-classes
  nil)

; Session/input hypothesis removal: peer-transfer.
; Every other retained hypothesis holds; the omitted one and full conclusion fail.
(defthm
  hdt-without-peer-transfer
  (let*
    ((conn
       (fn-served-make-conn-live
         (fn-wire-make-state :command nil 0 nil nil 0 510 65536)
         (fn-served-conn-session
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-make-session
                 *hdt-post*
                 "test-peer"
                 (list :ihave (fn-nntp-string-octets "<held@fn.test>"))
                 0
                 (fn-node-initial-state (quote ("fn.test")) 100000)
                 (fn-cfg-initial)
                 nil))
             *hdt-selected*))
         (fn-served-conn-archive
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-make-session
                 *hdt-post*
                 "test-peer"
                 (list :ihave (fn-nntp-string-octets "<held@fn.test>"))
                 0
                 (fn-node-initial-state (quote ("fn.test")) 100000)
                 (fn-cfg-initial)
                 nil))
             *hdt-selected*))
         (fn-served-conn-config
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-make-session
                 *hdt-post*
                 "test-peer"
                 (list :ihave (fn-nntp-string-octets "<held@fn.test>"))
                 0
                 (fn-node-initial-state (quote ("fn.test")) 100000)
                 (fn-cfg-initial)
                 nil))
             *hdt-selected*))
         (fn-served-conn-observation
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-make-session
                 *hdt-post*
                 "test-peer"
                 (list :ihave (fn-nntp-string-octets "<held@fn.test>"))
                 0
                 (fn-node-initial-state (quote ("fn.test")) 100000)
                 (fn-cfg-initial)
                 nil))
             *hdt-selected*))
         (fn-served-conn-injection
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-make-session
                 *hdt-post*
                 "test-peer"
                 (list :ihave (fn-nntp-string-octets "<held@fn.test>"))
                 0
                 (fn-node-initial-state (quote ("fn.test")) 100000)
                 (fn-cfg-initial)
                 nil))
             *hdt-selected*))
         (fn-served-conn-verdicts
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-make-session
                 *hdt-post*
                 "test-peer"
                 (list :ihave (fn-nntp-string-octets "<held@fn.test>"))
                 0
                 (fn-node-initial-state (quote ("fn.test")) 100000)
                 (fn-cfg-initial)
                 nil))
             *hdt-selected*))
         (fn-served-conn-index
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-make-session
                 *hdt-post*
                 "test-peer"
                 (list :ihave (fn-nntp-string-octets "<held@fn.test>"))
                 0
                 (fn-node-initial-state (quote ("fn.test")) 100000)
                 (fn-cfg-initial)
                 nil))
             *hdt-selected*))
         (fn-served-conn-group-index
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-make-session
                 *hdt-post*
                 "test-peer"
                 (list :ihave (fn-nntp-string-octets "<held@fn.test>"))
                 0
                 (fn-node-initial-state (quote ("fn.test")) 100000)
                 (fn-cfg-initial)
                 nil))
             *hdt-selected*))
         (fn-served-conn-control
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-make-session
                 *hdt-post*
                 "test-peer"
                 (list :ihave (fn-nntp-string-octets "<held@fn.test>"))
                 0
                 (fn-node-initial-state (quote ("fn.test")) 100000)
                 (fn-cfg-initial)
                 nil))
             *hdt-selected*))
         (fn-served-conn-pinned
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-make-session
                 *hdt-post*
                 "test-peer"
                 (list :ihave (fn-nntp-string-octets "<held@fn.test>"))
                 0
                 (fn-node-initial-state (quote ("fn.test")) 100000)
                 (fn-cfg-initial)
                 nil))
             *hdt-selected*))
         (fn-served-conn-live
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-make-session
                 *hdt-post*
                 "test-peer"
                 (list :ihave (fn-nntp-string-octets "<held@fn.test>"))
                 0
                 (fn-node-initial-state (quote ("fn.test")) 100000)
                 (fn-cfg-initial)
                 nil))
             *hdt-selected*))))
     (as (fn-served-conn-session conn))
     (config (fn-served-conn-config conn))
     (archive (fn-served-conn-archive conn))
     (index (fn-served-conn-pinned-index conn))
     (observation (fn-served-conn-observation conn))
     (peer (fn-auth-view-session as config))
     (viewarchive (fn-auth-view-archive as config archive))
     (viewindex (fn-auth-view-index as config archive index))
     (viewconfig (fn-auth-view-config as (fn-auth-moderation-config as config) archive))
     (ps (fn-peer-session-base peer))
     (session (fn-post-session-base ps))
     (env (fn-post-reader-env viewconfig observation))
     (server (fn-nntp-xref-server env))
     (r
       (fn-rcompat-retrieval
         session
         viewarchive
         (fn-gidx-pin-trie viewindex)
         :head
         (list *hdt-token*)
         server
         (list *hdt-payload*)))
     (p (fn-served-step conn (append *hdt-line* (quote (13 10))) (list *hdt-payload*))))
    (and
      (fn-wire-statep (fn-served-conn-wire conn))
      (<= (len *hdt-line*) 510)
      (fn-auth-sessionp as)
      (not (fn-auth-session-handshakingp as))
      (not (fn-auth-sasl-waitingp as))
      (or
        (not (fn-auth-config-requiredp (fn-auth-session-config as)))
        (fn-auth-session-subject as))
      (not (fn-post-session-awaiting ps))
      (equal (fn-nntp-session-openp session) t)
      (fn-nntp-session-projected session)
      (fn-nntp-command-inputp *hdt-line*)
      (equal (fn-nntp-tokenize *hdt-line*) (list *fn-hdc-head-keyword* *hdt-token*))
      server
      (fn-gidx-pinp viewindex)
      (not (fn-nntp-number-withdrawn-p session viewarchive viewindex *hdt-token*))
      (not
        (and
          (fn-nntp-message-id-tokenp *hdt-token*)
          (fn-nntp-msgid-withdrawn-p viewindex *hdt-token*)))
      (not (null (fn-peer-session-peer peer)))
      (not
        (and
          (equal (fn-served-result-effects p) (fn-nntp-result-effects r))
          (equal
            (fn-post-session-base
              (fn-peer-session-base
                (fn-auth-session-base (fn-served-conn-session (fn-served-result-conn p)))))
            (fn-nntp-result-session r))
          (equal (fn-served-conn-pinned (fn-served-result-conn p)) (fn-served-conn-pinned conn))
          (equal
            (fn-served-conn-archive (fn-served-result-conn p))
            (fn-served-conn-archive conn))
          (equal (fn-served-conn-index (fn-served-result-conn p)) (fn-served-conn-index conn))))))
  :rule-classes
  nil)

; Corrupted-state hypothesis removal: post-phase.
; Every other retained hypothesis holds; the omitted one and full conclusion fail.
(defthm
  hdt-without-post-phase
  (let*
    ((conn
       (fn-served-make-conn-live
         (fn-wire-make-state :command nil 0 nil nil 0 510 65536)
         (fn-served-conn-session
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-with-base *hdt-peer* (fn-post-make-session *hdt-reader* t)))
             *hdt-selected*))
         (fn-served-conn-archive
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-with-base *hdt-peer* (fn-post-make-session *hdt-reader* t)))
             *hdt-selected*))
         (fn-served-conn-config
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-with-base *hdt-peer* (fn-post-make-session *hdt-reader* t)))
             *hdt-selected*))
         (fn-served-conn-observation
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-with-base *hdt-peer* (fn-post-make-session *hdt-reader* t)))
             *hdt-selected*))
         (fn-served-conn-injection
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-with-base *hdt-peer* (fn-post-make-session *hdt-reader* t)))
             *hdt-selected*))
         (fn-served-conn-verdicts
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-with-base *hdt-peer* (fn-post-make-session *hdt-reader* t)))
             *hdt-selected*))
         (fn-served-conn-index
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-with-base *hdt-peer* (fn-post-make-session *hdt-reader* t)))
             *hdt-selected*))
         (fn-served-conn-group-index
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-with-base *hdt-peer* (fn-post-make-session *hdt-reader* t)))
             *hdt-selected*))
         (fn-served-conn-control
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-with-base *hdt-peer* (fn-post-make-session *hdt-reader* t)))
             *hdt-selected*))
         (fn-served-conn-pinned
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-with-base *hdt-peer* (fn-post-make-session *hdt-reader* t)))
             *hdt-selected*))
         (fn-served-conn-live
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-with-base *hdt-peer* (fn-post-make-session *hdt-reader* t)))
             *hdt-selected*))))
     (as (fn-served-conn-session conn))
     (config (fn-served-conn-config conn))
     (archive (fn-served-conn-archive conn))
     (index (fn-served-conn-pinned-index conn))
     (observation (fn-served-conn-observation conn))
     (peer (fn-auth-view-session as config))
     (viewarchive (fn-auth-view-archive as config archive))
     (viewindex (fn-auth-view-index as config archive index))
     (viewconfig (fn-auth-view-config as (fn-auth-moderation-config as config) archive))
     (ps (fn-peer-session-base peer))
     (session (fn-post-session-base ps))
     (env (fn-post-reader-env viewconfig observation))
     (server (fn-nntp-xref-server env))
     (r
       (fn-rcompat-retrieval
         session
         viewarchive
         (fn-gidx-pin-trie viewindex)
         :head
         (list *hdt-token*)
         server
         (list *hdt-payload*)))
     (p (fn-served-step conn (append *hdt-line* (quote (13 10))) (list *hdt-payload*))))
    (and
      (fn-wire-statep (fn-served-conn-wire conn))
      (<= (len *hdt-line*) 510)
      (fn-auth-sessionp as)
      (not (fn-auth-session-handshakingp as))
      (not (fn-auth-sasl-waitingp as))
      (or
        (not (fn-auth-config-requiredp (fn-auth-session-config as)))
        (fn-auth-session-subject as))
      (null (fn-peer-session-peer peer))
      (equal (fn-nntp-session-openp session) t)
      (fn-nntp-session-projected session)
      (fn-nntp-command-inputp *hdt-line*)
      (equal (fn-nntp-tokenize *hdt-line*) (list *fn-hdc-head-keyword* *hdt-token*))
      server
      (fn-gidx-pinp viewindex)
      (not (fn-nntp-number-withdrawn-p session viewarchive viewindex *hdt-token*))
      (not
        (and
          (fn-nntp-message-id-tokenp *hdt-token*)
          (fn-nntp-msgid-withdrawn-p viewindex *hdt-token*)))
      (not (not (fn-post-session-awaiting ps)))
      (not
        (and
          (equal (fn-served-result-effects p) (fn-nntp-result-effects r))
          (equal
            (fn-post-session-base
              (fn-peer-session-base
                (fn-auth-session-base (fn-served-conn-session (fn-served-result-conn p)))))
            (fn-nntp-result-session r))
          (equal (fn-served-conn-pinned (fn-served-result-conn p)) (fn-served-conn-pinned conn))
          (equal
            (fn-served-conn-archive (fn-served-result-conn p))
            (fn-served-conn-archive conn))
          (equal (fn-served-conn-index (fn-served-result-conn p)) (fn-served-conn-index conn))))))
  :rule-classes
  nil)

; Corrupted-state hypothesis removal: reader-open.
; Every other retained hypothesis holds; the omitted one and full conclusion fail.
(defthm
  hdt-without-reader-open
  (let*
    ((conn
       (fn-served-make-conn-live
         (fn-wire-make-state :command nil 0 nil nil 0 510 65536)
         (fn-served-conn-session
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-with-base
                 *hdt-peer*
                 (fn-post-make-session (update-nth 0 nil *hdt-reader*) nil)))
             *hdt-selected*))
         (fn-served-conn-archive
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-with-base
                 *hdt-peer*
                 (fn-post-make-session (update-nth 0 nil *hdt-reader*) nil)))
             *hdt-selected*))
         (fn-served-conn-config
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-with-base
                 *hdt-peer*
                 (fn-post-make-session (update-nth 0 nil *hdt-reader*) nil)))
             *hdt-selected*))
         (fn-served-conn-observation
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-with-base
                 *hdt-peer*
                 (fn-post-make-session (update-nth 0 nil *hdt-reader*) nil)))
             *hdt-selected*))
         (fn-served-conn-injection
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-with-base
                 *hdt-peer*
                 (fn-post-make-session (update-nth 0 nil *hdt-reader*) nil)))
             *hdt-selected*))
         (fn-served-conn-verdicts
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-with-base
                 *hdt-peer*
                 (fn-post-make-session (update-nth 0 nil *hdt-reader*) nil)))
             *hdt-selected*))
         (fn-served-conn-index
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-with-base
                 *hdt-peer*
                 (fn-post-make-session (update-nth 0 nil *hdt-reader*) nil)))
             *hdt-selected*))
         (fn-served-conn-group-index
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-with-base
                 *hdt-peer*
                 (fn-post-make-session (update-nth 0 nil *hdt-reader*) nil)))
             *hdt-selected*))
         (fn-served-conn-control
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-with-base
                 *hdt-peer*
                 (fn-post-make-session (update-nth 0 nil *hdt-reader*) nil)))
             *hdt-selected*))
         (fn-served-conn-pinned
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-with-base
                 *hdt-peer*
                 (fn-post-make-session (update-nth 0 nil *hdt-reader*) nil)))
             *hdt-selected*))
         (fn-served-conn-live
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-with-base
                 *hdt-peer*
                 (fn-post-make-session (update-nth 0 nil *hdt-reader*) nil)))
             *hdt-selected*))))
     (as (fn-served-conn-session conn))
     (config (fn-served-conn-config conn))
     (archive (fn-served-conn-archive conn))
     (index (fn-served-conn-pinned-index conn))
     (observation (fn-served-conn-observation conn))
     (peer (fn-auth-view-session as config))
     (viewarchive (fn-auth-view-archive as config archive))
     (viewindex (fn-auth-view-index as config archive index))
     (viewconfig (fn-auth-view-config as (fn-auth-moderation-config as config) archive))
     (ps (fn-peer-session-base peer))
     (session (fn-post-session-base ps))
     (env (fn-post-reader-env viewconfig observation))
     (server (fn-nntp-xref-server env))
     (r
       (fn-rcompat-retrieval
         session
         viewarchive
         (fn-gidx-pin-trie viewindex)
         :head
         (list *hdt-token*)
         server
         (list *hdt-payload*)))
     (p (fn-served-step conn (append *hdt-line* (quote (13 10))) (list *hdt-payload*))))
    (and
      (fn-wire-statep (fn-served-conn-wire conn))
      (<= (len *hdt-line*) 510)
      (fn-auth-sessionp as)
      (not (fn-auth-session-handshakingp as))
      (not (fn-auth-sasl-waitingp as))
      (or
        (not (fn-auth-config-requiredp (fn-auth-session-config as)))
        (fn-auth-session-subject as))
      (null (fn-peer-session-peer peer))
      (not (fn-post-session-awaiting ps))
      (fn-nntp-session-projected session)
      (fn-nntp-command-inputp *hdt-line*)
      (equal (fn-nntp-tokenize *hdt-line*) (list *fn-hdc-head-keyword* *hdt-token*))
      server
      (fn-gidx-pinp viewindex)
      (not (fn-nntp-number-withdrawn-p session viewarchive viewindex *hdt-token*))
      (not
        (and
          (fn-nntp-message-id-tokenp *hdt-token*)
          (fn-nntp-msgid-withdrawn-p viewindex *hdt-token*)))
      (not (equal (fn-nntp-session-openp session) t))
      (not
        (and
          (equal (fn-served-result-effects p) (fn-nntp-result-effects r))
          (equal
            (fn-post-session-base
              (fn-peer-session-base
                (fn-auth-session-base (fn-served-conn-session (fn-served-result-conn p)))))
            (fn-nntp-result-session r))
          (equal (fn-served-conn-pinned (fn-served-result-conn p)) (fn-served-conn-pinned conn))
          (equal
            (fn-served-conn-archive (fn-served-result-conn p))
            (fn-served-conn-archive conn))
          (equal (fn-served-conn-index (fn-served-result-conn p)) (fn-served-conn-index conn))))))
  :rule-classes
  nil)

; Corrupted-state hypothesis removal: reader-projection.
; Every other retained hypothesis holds; the omitted one and full conclusion fail.
(defthm
  hdt-without-reader-projection
  (let*
    ((conn
       (fn-served-make-conn-live
         (fn-wire-make-state :command nil 0 nil nil 0 510 65536)
         (fn-served-conn-session
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-with-base
                 *hdt-peer*
                 (fn-post-make-session (update-nth 3 nil *hdt-reader*) nil)))
             *hdt-selected*))
         (fn-served-conn-archive
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-with-base
                 *hdt-peer*
                 (fn-post-make-session (update-nth 3 nil *hdt-reader*) nil)))
             *hdt-selected*))
         (fn-served-conn-config
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-with-base
                 *hdt-peer*
                 (fn-post-make-session (update-nth 3 nil *hdt-reader*) nil)))
             *hdt-selected*))
         (fn-served-conn-observation
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-with-base
                 *hdt-peer*
                 (fn-post-make-session (update-nth 3 nil *hdt-reader*) nil)))
             *hdt-selected*))
         (fn-served-conn-injection
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-with-base
                 *hdt-peer*
                 (fn-post-make-session (update-nth 3 nil *hdt-reader*) nil)))
             *hdt-selected*))
         (fn-served-conn-verdicts
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-with-base
                 *hdt-peer*
                 (fn-post-make-session (update-nth 3 nil *hdt-reader*) nil)))
             *hdt-selected*))
         (fn-served-conn-index
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-with-base
                 *hdt-peer*
                 (fn-post-make-session (update-nth 3 nil *hdt-reader*) nil)))
             *hdt-selected*))
         (fn-served-conn-group-index
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-with-base
                 *hdt-peer*
                 (fn-post-make-session (update-nth 3 nil *hdt-reader*) nil)))
             *hdt-selected*))
         (fn-served-conn-control
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-with-base
                 *hdt-peer*
                 (fn-post-make-session (update-nth 3 nil *hdt-reader*) nil)))
             *hdt-selected*))
         (fn-served-conn-pinned
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-with-base
                 *hdt-peer*
                 (fn-post-make-session (update-nth 3 nil *hdt-reader*) nil)))
             *hdt-selected*))
         (fn-served-conn-live
           (update-nth
             1
             (fn-auth-with-base
               *hdt-as*
               (fn-peer-with-base
                 *hdt-peer*
                 (fn-post-make-session (update-nth 3 nil *hdt-reader*) nil)))
             *hdt-selected*))))
     (as (fn-served-conn-session conn))
     (config (fn-served-conn-config conn))
     (archive (fn-served-conn-archive conn))
     (index (fn-served-conn-pinned-index conn))
     (observation (fn-served-conn-observation conn))
     (peer (fn-auth-view-session as config))
     (viewarchive (fn-auth-view-archive as config archive))
     (viewindex (fn-auth-view-index as config archive index))
     (viewconfig (fn-auth-view-config as (fn-auth-moderation-config as config) archive))
     (ps (fn-peer-session-base peer))
     (session (fn-post-session-base ps))
     (env (fn-post-reader-env viewconfig observation))
     (server (fn-nntp-xref-server env))
     (r
       (fn-rcompat-retrieval
         session
         viewarchive
         (fn-gidx-pin-trie viewindex)
         :head
         (list *hdt-token*)
         server
         (list *hdt-payload*)))
     (p (fn-served-step conn (append *hdt-line* (quote (13 10))) (list *hdt-payload*))))
    (and
      (fn-wire-statep (fn-served-conn-wire conn))
      (<= (len *hdt-line*) 510)
      (fn-auth-sessionp as)
      (not (fn-auth-session-handshakingp as))
      (not (fn-auth-sasl-waitingp as))
      (or
        (not (fn-auth-config-requiredp (fn-auth-session-config as)))
        (fn-auth-session-subject as))
      (null (fn-peer-session-peer peer))
      (not (fn-post-session-awaiting ps))
      (equal (fn-nntp-session-openp session) t)
      (fn-nntp-command-inputp *hdt-line*)
      (equal (fn-nntp-tokenize *hdt-line*) (list *fn-hdc-head-keyword* *hdt-token*))
      server
      (fn-gidx-pinp viewindex)
      (not (fn-nntp-number-withdrawn-p session viewarchive viewindex *hdt-token*))
      (not
        (and
          (fn-nntp-message-id-tokenp *hdt-token*)
          (fn-nntp-msgid-withdrawn-p viewindex *hdt-token*)))
      (not (fn-nntp-session-projected session))
      (not
        (and
          (equal (fn-served-result-effects p) (fn-nntp-result-effects r))
          (equal
            (fn-post-session-base
              (fn-peer-session-base
                (fn-auth-session-base (fn-served-conn-session (fn-served-result-conn p)))))
            (fn-nntp-result-session r))
          (equal (fn-served-conn-pinned (fn-served-result-conn p)) (fn-served-conn-pinned conn))
          (equal
            (fn-served-conn-archive (fn-served-result-conn p))
            (fn-served-conn-archive conn))
          (equal (fn-served-conn-index (fn-served-result-conn p)) (fn-served-conn-index conn))))))
  :rule-classes
  nil)

; Session/input hypothesis removal: command-input.
; Every other retained hypothesis holds; the omitted one and full conclusion fail.
(defthm
  hdt-without-command-input
  (let*
    ((conn
       (fn-served-make-conn-live
         (fn-wire-make-state :command nil 0 nil nil 0 600 65536)
         (fn-served-conn-session *hdt-selected*)
         (fn-served-conn-archive *hdt-selected*)
         (fn-served-conn-config *hdt-selected*)
         (fn-served-conn-observation *hdt-selected*)
         (fn-served-conn-injection *hdt-selected*)
         (fn-served-conn-verdicts *hdt-selected*)
         (fn-served-conn-index *hdt-selected*)
         (fn-served-conn-group-index *hdt-selected*)
         (fn-served-conn-control *hdt-selected*)
         (fn-served-conn-pinned *hdt-selected*)
         (fn-served-conn-live *hdt-selected*)))
     (as (fn-served-conn-session conn))
     (config (fn-served-conn-config conn))
     (archive (fn-served-conn-archive conn))
     (index (fn-served-conn-pinned-index conn))
     (observation (fn-served-conn-observation conn))
     (peer (fn-auth-view-session as config))
     (viewarchive (fn-auth-view-archive as config archive))
     (viewindex (fn-auth-view-index as config archive index))
     (viewconfig (fn-auth-view-config as (fn-auth-moderation-config as config) archive))
     (ps (fn-peer-session-base peer))
     (session (fn-post-session-base ps))
     (env (fn-post-reader-env viewconfig observation))
     (server (fn-nntp-xref-server env))
     (r
       (fn-rcompat-retrieval
         session
         viewarchive
         (fn-gidx-pin-trie viewindex)
         :head
         (list *hdt-token*)
         server
         (list *hdt-payload*)))
     (p
       (fn-served-step
         conn
         (append
           (append *fn-hdc-head-keyword* (make-list 520 :initial-element 32) *hdt-token*)
           (quote (13 10)))
         (list *hdt-payload*))))
    (and
      (fn-wire-statep (fn-served-conn-wire conn))
      (<=
        (len (append *fn-hdc-head-keyword* (make-list 520 :initial-element 32) *hdt-token*))
        600)
      (fn-auth-sessionp as)
      (not (fn-auth-session-handshakingp as))
      (not (fn-auth-sasl-waitingp as))
      (or
        (not (fn-auth-config-requiredp (fn-auth-session-config as)))
        (fn-auth-session-subject as))
      (null (fn-peer-session-peer peer))
      (not (fn-post-session-awaiting ps))
      (equal (fn-nntp-session-openp session) t)
      (fn-nntp-session-projected session)
      (equal
        (fn-nntp-tokenize
          (append *fn-hdc-head-keyword* (make-list 520 :initial-element 32) *hdt-token*))
        (list *fn-hdc-head-keyword* *hdt-token*))
      server
      (fn-gidx-pinp viewindex)
      (not (fn-nntp-number-withdrawn-p session viewarchive viewindex *hdt-token*))
      (not
        (and
          (fn-nntp-message-id-tokenp *hdt-token*)
          (fn-nntp-msgid-withdrawn-p viewindex *hdt-token*)))
      (not
        (fn-nntp-command-inputp
          (append *fn-hdc-head-keyword* (make-list 520 :initial-element 32) *hdt-token*)))
      (not
        (and
          (equal (fn-served-result-effects p) (fn-nntp-result-effects r))
          (equal
            (fn-post-session-base
              (fn-peer-session-base
                (fn-auth-session-base (fn-served-conn-session (fn-served-result-conn p)))))
            (fn-nntp-result-session r))
          (equal (fn-served-conn-pinned (fn-served-result-conn p)) (fn-served-conn-pinned conn))
          (equal
            (fn-served-conn-archive (fn-served-result-conn p))
            (fn-served-conn-archive conn))
          (equal (fn-served-conn-index (fn-served-result-conn p)) (fn-served-conn-index conn))))))
  :rule-classes
  nil)

; Session/input hypothesis removal: matching-token.
; Every other retained hypothesis holds; the omitted one and full conclusion fail.
(defthm
  hdt-without-matching-token
  (let*
    ((conn
       (fn-served-make-conn-live
         (fn-wire-make-state :command nil 0 nil nil 0 510 65536)
         (fn-served-conn-session *hdt-selected*)
         (fn-served-conn-archive *hdt-selected*)
         (fn-served-conn-config *hdt-selected*)
         (fn-served-conn-observation *hdt-selected*)
         (fn-served-conn-injection *hdt-selected*)
         (fn-served-conn-verdicts *hdt-selected*)
         (fn-served-conn-index *hdt-selected*)
         (fn-served-conn-group-index *hdt-selected*)
         (fn-served-conn-control *hdt-selected*)
         (fn-served-conn-pinned *hdt-selected*)
         (fn-served-conn-live *hdt-selected*)))
     (as (fn-served-conn-session conn))
     (config (fn-served-conn-config conn))
     (archive (fn-served-conn-archive conn))
     (index (fn-served-conn-pinned-index conn))
     (observation (fn-served-conn-observation conn))
     (peer (fn-auth-view-session as config))
     (viewarchive (fn-auth-view-archive as config archive))
     (viewindex (fn-auth-view-index as config archive index))
     (viewconfig (fn-auth-view-config as (fn-auth-moderation-config as config) archive))
     (ps (fn-peer-session-base peer))
     (session (fn-post-session-base ps))
     (env (fn-post-reader-env viewconfig observation))
     (server (fn-nntp-xref-server env))
     (r
       (fn-rcompat-retrieval
         session
         viewarchive
         (fn-gidx-pin-trie viewindex)
         :head
         (list (fn-nntp-string-octets "<other@fn.test>"))
         server
         (list *hdt-payload*)))
     (p (fn-served-step conn (append *hdt-line* (quote (13 10))) (list *hdt-payload*))))
    (and
      (fn-wire-statep (fn-served-conn-wire conn))
      (<= (len *hdt-line*) 510)
      (fn-auth-sessionp as)
      (not (fn-auth-session-handshakingp as))
      (not (fn-auth-sasl-waitingp as))
      (or
        (not (fn-auth-config-requiredp (fn-auth-session-config as)))
        (fn-auth-session-subject as))
      (null (fn-peer-session-peer peer))
      (not (fn-post-session-awaiting ps))
      (equal (fn-nntp-session-openp session) t)
      (fn-nntp-session-projected session)
      (fn-nntp-command-inputp *hdt-line*)
      server
      (fn-gidx-pinp viewindex)
      (not
        (fn-nntp-number-withdrawn-p
          session
          viewarchive
          viewindex
          (fn-nntp-string-octets "<other@fn.test>")))
      (not
        (and
          (fn-nntp-message-id-tokenp (fn-nntp-string-octets "<other@fn.test>"))
          (fn-nntp-msgid-withdrawn-p viewindex (fn-nntp-string-octets "<other@fn.test>"))))
      (not
        (equal
          (fn-nntp-tokenize *hdt-line*)
          (list *fn-hdc-head-keyword* (fn-nntp-string-octets "<other@fn.test>"))))
      (not
        (and
          (equal (fn-served-result-effects p) (fn-nntp-result-effects r))
          (equal
            (fn-post-session-base
              (fn-peer-session-base
                (fn-auth-session-base (fn-served-conn-session (fn-served-result-conn p)))))
            (fn-nntp-result-session r))
          (equal (fn-served-conn-pinned (fn-served-result-conn p)) (fn-served-conn-pinned conn))
          (equal
            (fn-served-conn-archive (fn-served-result-conn p))
            (fn-served-conn-archive conn))
          (equal (fn-served-conn-index (fn-served-result-conn p)) (fn-served-conn-index conn))))))
  :rule-classes
  nil)

; Session/input hypothesis removal: xref-server.
; Every other retained hypothesis holds; the omitted one and full conclusion fail.
(defthm
  hdt-without-xref-server
  (let*
    ((conn
       (fn-served-make-conn-live
         (fn-wire-make-state :command nil 0 nil nil 0 510 65536)
         (fn-served-conn-session (update-nth 3 (update-nth 4 nil *hdt-config*) *hdt-selected*))
         (fn-served-conn-archive (update-nth 3 (update-nth 4 nil *hdt-config*) *hdt-selected*))
         (fn-served-conn-config (update-nth 3 (update-nth 4 nil *hdt-config*) *hdt-selected*))
         (fn-served-conn-observation
           (update-nth 3 (update-nth 4 nil *hdt-config*) *hdt-selected*))
         (fn-served-conn-injection (update-nth 3 (update-nth 4 nil *hdt-config*) *hdt-selected*))
         (fn-served-conn-verdicts (update-nth 3 (update-nth 4 nil *hdt-config*) *hdt-selected*))
         (fn-served-conn-index (update-nth 3 (update-nth 4 nil *hdt-config*) *hdt-selected*))
         (fn-served-conn-group-index
           (update-nth 3 (update-nth 4 nil *hdt-config*) *hdt-selected*))
         (fn-served-conn-control (update-nth 3 (update-nth 4 nil *hdt-config*) *hdt-selected*))
         (fn-served-conn-pinned (update-nth 3 (update-nth 4 nil *hdt-config*) *hdt-selected*))
         (fn-served-conn-live (update-nth 3 (update-nth 4 nil *hdt-config*) *hdt-selected*))))
     (as (fn-served-conn-session conn))
     (config (fn-served-conn-config conn))
     (archive (fn-served-conn-archive conn))
     (index (fn-served-conn-pinned-index conn))
     (observation (fn-served-conn-observation conn))
     (peer (fn-auth-view-session as config))
     (viewarchive (fn-auth-view-archive as config archive))
     (viewindex (fn-auth-view-index as config archive index))
     (viewconfig (fn-auth-view-config as (fn-auth-moderation-config as config) archive))
     (ps (fn-peer-session-base peer))
     (session (fn-post-session-base ps))
     (env (fn-post-reader-env viewconfig observation))
     (server (fn-nntp-xref-server env))
     (r
       (fn-rcompat-retrieval
         session
         viewarchive
         (fn-gidx-pin-trie viewindex)
         :head
         (list *hdt-token*)
         server
         (list *hdt-payload*)))
     (p (fn-served-step conn (append *hdt-line* (quote (13 10))) (list *hdt-payload*))))
    (and
      (fn-wire-statep (fn-served-conn-wire conn))
      (<= (len *hdt-line*) 510)
      (fn-auth-sessionp as)
      (not (fn-auth-session-handshakingp as))
      (not (fn-auth-sasl-waitingp as))
      (or
        (not (fn-auth-config-requiredp (fn-auth-session-config as)))
        (fn-auth-session-subject as))
      (null (fn-peer-session-peer peer))
      (not (fn-post-session-awaiting ps))
      (equal (fn-nntp-session-openp session) t)
      (fn-nntp-session-projected session)
      (fn-nntp-command-inputp *hdt-line*)
      (equal (fn-nntp-tokenize *hdt-line*) (list *fn-hdc-head-keyword* *hdt-token*))
      (fn-gidx-pinp viewindex)
      (not (fn-nntp-number-withdrawn-p session viewarchive viewindex *hdt-token*))
      (not
        (and
          (fn-nntp-message-id-tokenp *hdt-token*)
          (fn-nntp-msgid-withdrawn-p viewindex *hdt-token*)))
      (not server)
      (not
        (and
          (equal (fn-served-result-effects p) (fn-nntp-result-effects r))
          (equal
            (fn-post-session-base
              (fn-peer-session-base
                (fn-auth-session-base (fn-served-conn-session (fn-served-result-conn p)))))
            (fn-nntp-result-session r))
          (equal (fn-served-conn-pinned (fn-served-result-conn p)) (fn-served-conn-pinned conn))
          (equal
            (fn-served-conn-archive (fn-served-result-conn p))
            (fn-served-conn-archive conn))
          (equal (fn-served-conn-index (fn-served-result-conn p)) (fn-served-conn-index conn))))))
  :rule-classes
  nil)

; Corrupted-state hypothesis removal: pinned-index.
; Every other retained hypothesis holds; the omitted one and full conclusion fail.
(defthm
  hdt-without-pinned-index
  (let*
    ((conn
       (fn-served-make-conn-live
         (fn-wire-make-state :command nil 0 nil nil 0 510 65536)
         (fn-served-conn-session (update-nth 8 nil *hdt-selected*))
         (fn-served-conn-archive (update-nth 8 nil *hdt-selected*))
         (fn-served-conn-config (update-nth 8 nil *hdt-selected*))
         (fn-served-conn-observation (update-nth 8 nil *hdt-selected*))
         (fn-served-conn-injection (update-nth 8 nil *hdt-selected*))
         (fn-served-conn-verdicts (update-nth 8 nil *hdt-selected*))
         (fn-served-conn-index (update-nth 8 nil *hdt-selected*))
         (fn-served-conn-group-index (update-nth 8 nil *hdt-selected*))
         (fn-served-conn-control (update-nth 8 nil *hdt-selected*))
         (fn-served-conn-pinned (update-nth 8 nil *hdt-selected*))
         (fn-served-conn-live (update-nth 8 nil *hdt-selected*))))
     (as (fn-served-conn-session conn))
     (config (fn-served-conn-config conn))
     (archive (fn-served-conn-archive conn))
     (index (fn-served-conn-pinned-index conn))
     (observation (fn-served-conn-observation conn))
     (peer (fn-auth-view-session as config))
     (viewarchive (fn-auth-view-archive as config archive))
     (viewindex (fn-auth-view-index as config archive index))
     (viewconfig (fn-auth-view-config as (fn-auth-moderation-config as config) archive))
     (ps (fn-peer-session-base peer))
     (session (fn-post-session-base ps))
     (env (fn-post-reader-env viewconfig observation))
     (server (fn-nntp-xref-server env))
     (r
       (fn-rcompat-retrieval
         session
         viewarchive
         (fn-gidx-pin-trie viewindex)
         :head
         (list *hdt-token*)
         server
         (list *hdt-payload*)))
     (p (fn-served-step conn (append *hdt-line* (quote (13 10))) (list *hdt-payload*))))
    (and
      (fn-wire-statep (fn-served-conn-wire conn))
      (<= (len *hdt-line*) 510)
      (fn-auth-sessionp as)
      (not (fn-auth-session-handshakingp as))
      (not (fn-auth-sasl-waitingp as))
      (or
        (not (fn-auth-config-requiredp (fn-auth-session-config as)))
        (fn-auth-session-subject as))
      (null (fn-peer-session-peer peer))
      (not (fn-post-session-awaiting ps))
      (equal (fn-nntp-session-openp session) t)
      (fn-nntp-session-projected session)
      (fn-nntp-command-inputp *hdt-line*)
      (equal (fn-nntp-tokenize *hdt-line*) (list *fn-hdc-head-keyword* *hdt-token*))
      server
      (not (fn-nntp-number-withdrawn-p session viewarchive viewindex *hdt-token*))
      (not
        (and
          (fn-nntp-message-id-tokenp *hdt-token*)
          (fn-nntp-msgid-withdrawn-p viewindex *hdt-token*)))
      (not (fn-gidx-pinp viewindex))
      (not
        (and
          (equal (fn-served-result-effects p) (fn-nntp-result-effects r))
          (equal
            (fn-post-session-base
              (fn-peer-session-base
                (fn-auth-session-base (fn-served-conn-session (fn-served-result-conn p)))))
            (fn-nntp-result-session r))
          (equal (fn-served-conn-pinned (fn-served-result-conn p)) (fn-served-conn-pinned conn))
          (equal
            (fn-served-conn-archive (fn-served-result-conn p))
            (fn-served-conn-archive conn))
          (equal (fn-served-conn-index (fn-served-result-conn p)) (fn-served-conn-index conn))))))
  :rule-classes
  nil)

; Session/input hypothesis removal: number-withdrawal.
; Every other retained hypothesis holds; the omitted one and full conclusion fail.
(defthm
  hdt-without-number-withdrawal
  (let*
    ((conn
       (fn-served-make-conn-live
         (fn-wire-make-state :command nil 0 nil nil 0 510 65536)
         (fn-served-conn-session
           (update-nth
             9
             (fn-ctl-pin (list *hdt-article*) nil)
             (update-nth
               8
               nil
               (update-nth 7 nil (update-nth 2 (update-nth 2 nil *hdt-archive*) *hdt-selected*)))))
         (fn-served-conn-archive
           (update-nth
             9
             (fn-ctl-pin (list *hdt-article*) nil)
             (update-nth
               8
               nil
               (update-nth 7 nil (update-nth 2 (update-nth 2 nil *hdt-archive*) *hdt-selected*)))))
         (fn-served-conn-config
           (update-nth
             9
             (fn-ctl-pin (list *hdt-article*) nil)
             (update-nth
               8
               nil
               (update-nth 7 nil (update-nth 2 (update-nth 2 nil *hdt-archive*) *hdt-selected*)))))
         (fn-served-conn-observation
           (update-nth
             9
             (fn-ctl-pin (list *hdt-article*) nil)
             (update-nth
               8
               nil
               (update-nth 7 nil (update-nth 2 (update-nth 2 nil *hdt-archive*) *hdt-selected*)))))
         (fn-served-conn-injection
           (update-nth
             9
             (fn-ctl-pin (list *hdt-article*) nil)
             (update-nth
               8
               nil
               (update-nth 7 nil (update-nth 2 (update-nth 2 nil *hdt-archive*) *hdt-selected*)))))
         (fn-served-conn-verdicts
           (update-nth
             9
             (fn-ctl-pin (list *hdt-article*) nil)
             (update-nth
               8
               nil
               (update-nth 7 nil (update-nth 2 (update-nth 2 nil *hdt-archive*) *hdt-selected*)))))
         (fn-served-conn-index
           (update-nth
             9
             (fn-ctl-pin (list *hdt-article*) nil)
             (update-nth
               8
               nil
               (update-nth 7 nil (update-nth 2 (update-nth 2 nil *hdt-archive*) *hdt-selected*)))))
         (fn-served-conn-group-index
           (update-nth
             9
             (fn-ctl-pin (list *hdt-article*) nil)
             (update-nth
               8
               nil
               (update-nth 7 nil (update-nth 2 (update-nth 2 nil *hdt-archive*) *hdt-selected*)))))
         (fn-served-conn-control
           (update-nth
             9
             (fn-ctl-pin (list *hdt-article*) nil)
             (update-nth
               8
               nil
               (update-nth 7 nil (update-nth 2 (update-nth 2 nil *hdt-archive*) *hdt-selected*)))))
         (fn-served-conn-pinned
           (update-nth
             9
             (fn-ctl-pin (list *hdt-article*) nil)
             (update-nth
               8
               nil
               (update-nth 7 nil (update-nth 2 (update-nth 2 nil *hdt-archive*) *hdt-selected*)))))
         (fn-served-conn-live
           (update-nth
             9
             (fn-ctl-pin (list *hdt-article*) nil)
             (update-nth
               8
               nil
               (update-nth 7 nil (update-nth 2 (update-nth 2 nil *hdt-archive*) *hdt-selected*)))))))
     (as (fn-served-conn-session conn))
     (config (fn-served-conn-config conn))
     (archive (fn-served-conn-archive conn))
     (index (fn-served-conn-pinned-index conn))
     (observation (fn-served-conn-observation conn))
     (peer (fn-auth-view-session as config))
     (viewarchive (fn-auth-view-archive as config archive))
     (viewindex (fn-auth-view-index as config archive index))
     (viewconfig (fn-auth-view-config as (fn-auth-moderation-config as config) archive))
     (ps (fn-peer-session-base peer))
     (session (fn-post-session-base ps))
     (env (fn-post-reader-env viewconfig observation))
     (server (fn-nntp-xref-server env))
     (r
       (fn-rcompat-retrieval
         session
         viewarchive
         (fn-gidx-pin-trie viewindex)
         :head
         (list (quote (49)))
         server
         (list *hdt-payload*)))
     (p
       (fn-served-step
         conn
         (append (fn-nntp-string-octets "HEAD 1") (quote (13 10)))
         (list *hdt-payload*))))
    (and
      (fn-wire-statep (fn-served-conn-wire conn))
      (<= (len (fn-nntp-string-octets "HEAD 1")) 510)
      (fn-auth-sessionp as)
      (not (fn-auth-session-handshakingp as))
      (not (fn-auth-sasl-waitingp as))
      (or
        (not (fn-auth-config-requiredp (fn-auth-session-config as)))
        (fn-auth-session-subject as))
      (null (fn-peer-session-peer peer))
      (not (fn-post-session-awaiting ps))
      (equal (fn-nntp-session-openp session) t)
      (fn-nntp-session-projected session)
      (fn-nntp-command-inputp (fn-nntp-string-octets "HEAD 1"))
      (equal
        (fn-nntp-tokenize (fn-nntp-string-octets "HEAD 1"))
        (list *fn-hdc-head-keyword* (quote (49))))
      server
      (fn-gidx-pinp viewindex)
      (not
        (and
          (fn-nntp-message-id-tokenp (quote (49)))
          (fn-nntp-msgid-withdrawn-p viewindex (quote (49)))))
      (not (not (fn-nntp-number-withdrawn-p session viewarchive viewindex (quote (49)))))
      (not
        (and
          (equal (fn-served-result-effects p) (fn-nntp-result-effects r))
          (equal
            (fn-post-session-base
              (fn-peer-session-base
                (fn-auth-session-base (fn-served-conn-session (fn-served-result-conn p)))))
            (fn-nntp-result-session r))
          (equal (fn-served-conn-pinned (fn-served-result-conn p)) (fn-served-conn-pinned conn))
          (equal
            (fn-served-conn-archive (fn-served-result-conn p))
            (fn-served-conn-archive conn))
          (equal (fn-served-conn-index (fn-served-result-conn p)) (fn-served-conn-index conn))))))
  :rule-classes
  nil)

; Session/input hypothesis removal: msgid-withdrawal.
; Every other retained hypothesis holds; the omitted one and full conclusion fail.
(defthm
  hdt-without-msgid-withdrawal
  (let*
    ((conn
       (fn-served-make-conn-live
         (fn-wire-make-state :command nil 0 nil nil 0 510 65536)
         (fn-served-conn-session
           (update-nth
             9
             (fn-ctl-pin (list *hdt-article*) nil)
             (update-nth
               8
               nil
               (update-nth 7 nil (update-nth 2 (update-nth 2 nil *hdt-archive*) *hdt-selected*)))))
         (fn-served-conn-archive
           (update-nth
             9
             (fn-ctl-pin (list *hdt-article*) nil)
             (update-nth
               8
               nil
               (update-nth 7 nil (update-nth 2 (update-nth 2 nil *hdt-archive*) *hdt-selected*)))))
         (fn-served-conn-config
           (update-nth
             9
             (fn-ctl-pin (list *hdt-article*) nil)
             (update-nth
               8
               nil
               (update-nth 7 nil (update-nth 2 (update-nth 2 nil *hdt-archive*) *hdt-selected*)))))
         (fn-served-conn-observation
           (update-nth
             9
             (fn-ctl-pin (list *hdt-article*) nil)
             (update-nth
               8
               nil
               (update-nth 7 nil (update-nth 2 (update-nth 2 nil *hdt-archive*) *hdt-selected*)))))
         (fn-served-conn-injection
           (update-nth
             9
             (fn-ctl-pin (list *hdt-article*) nil)
             (update-nth
               8
               nil
               (update-nth 7 nil (update-nth 2 (update-nth 2 nil *hdt-archive*) *hdt-selected*)))))
         (fn-served-conn-verdicts
           (update-nth
             9
             (fn-ctl-pin (list *hdt-article*) nil)
             (update-nth
               8
               nil
               (update-nth 7 nil (update-nth 2 (update-nth 2 nil *hdt-archive*) *hdt-selected*)))))
         (fn-served-conn-index
           (update-nth
             9
             (fn-ctl-pin (list *hdt-article*) nil)
             (update-nth
               8
               nil
               (update-nth 7 nil (update-nth 2 (update-nth 2 nil *hdt-archive*) *hdt-selected*)))))
         (fn-served-conn-group-index
           (update-nth
             9
             (fn-ctl-pin (list *hdt-article*) nil)
             (update-nth
               8
               nil
               (update-nth 7 nil (update-nth 2 (update-nth 2 nil *hdt-archive*) *hdt-selected*)))))
         (fn-served-conn-control
           (update-nth
             9
             (fn-ctl-pin (list *hdt-article*) nil)
             (update-nth
               8
               nil
               (update-nth 7 nil (update-nth 2 (update-nth 2 nil *hdt-archive*) *hdt-selected*)))))
         (fn-served-conn-pinned
           (update-nth
             9
             (fn-ctl-pin (list *hdt-article*) nil)
             (update-nth
               8
               nil
               (update-nth 7 nil (update-nth 2 (update-nth 2 nil *hdt-archive*) *hdt-selected*)))))
         (fn-served-conn-live
           (update-nth
             9
             (fn-ctl-pin (list *hdt-article*) nil)
             (update-nth
               8
               nil
               (update-nth 7 nil (update-nth 2 (update-nth 2 nil *hdt-archive*) *hdt-selected*)))))))
     (as (fn-served-conn-session conn))
     (config (fn-served-conn-config conn))
     (archive (fn-served-conn-archive conn))
     (index (fn-served-conn-pinned-index conn))
     (observation (fn-served-conn-observation conn))
     (peer (fn-auth-view-session as config))
     (viewarchive (fn-auth-view-archive as config archive))
     (viewindex (fn-auth-view-index as config archive index))
     (viewconfig (fn-auth-view-config as (fn-auth-moderation-config as config) archive))
     (ps (fn-peer-session-base peer))
     (session (fn-post-session-base ps))
     (env (fn-post-reader-env viewconfig observation))
     (server (fn-nntp-xref-server env))
     (r
       (fn-rcompat-retrieval
         session
         viewarchive
         (fn-gidx-pin-trie viewindex)
         :head
         (list *hdt-token*)
         server
         (list *hdt-payload*)))
     (p (fn-served-step conn (append *hdt-line* (quote (13 10))) (list *hdt-payload*))))
    (and
      (fn-wire-statep (fn-served-conn-wire conn))
      (<= (len *hdt-line*) 510)
      (fn-auth-sessionp as)
      (not (fn-auth-session-handshakingp as))
      (not (fn-auth-sasl-waitingp as))
      (or
        (not (fn-auth-config-requiredp (fn-auth-session-config as)))
        (fn-auth-session-subject as))
      (null (fn-peer-session-peer peer))
      (not (fn-post-session-awaiting ps))
      (equal (fn-nntp-session-openp session) t)
      (fn-nntp-session-projected session)
      (fn-nntp-command-inputp *hdt-line*)
      (equal (fn-nntp-tokenize *hdt-line*) (list *fn-hdc-head-keyword* *hdt-token*))
      server
      (fn-gidx-pinp viewindex)
      (not (fn-nntp-number-withdrawn-p session viewarchive viewindex *hdt-token*))
      (not
        (not
          (and
            (fn-nntp-message-id-tokenp *hdt-token*)
            (fn-nntp-msgid-withdrawn-p viewindex *hdt-token*))))
      (not
        (and
          (equal (fn-served-result-effects p) (fn-nntp-result-effects r))
          (equal
            (fn-post-session-base
              (fn-peer-session-base
                (fn-auth-session-base (fn-served-conn-session (fn-served-result-conn p)))))
            (fn-nntp-result-session r))
          (equal (fn-served-conn-pinned (fn-served-result-conn p)) (fn-served-conn-pinned conn))
          (equal
            (fn-served-conn-archive (fn-served-result-conn p))
            (fn-served-conn-archive conn))
          (equal (fn-served-conn-index (fn-served-result-conn p)) (fn-served-conn-index conn))))))
  :rule-classes
  nil)

; The same complete antecedent is reachable for a local article-number request.
(defthm
  hdt-complete-number-positive
  (let*
    ((conn
       (fn-served-make-conn-live
         (fn-wire-make-state :command nil 0 nil nil 0 510 65536)
         (fn-served-conn-session *hdt-selected*)
         (fn-served-conn-archive *hdt-selected*)
         (fn-served-conn-config *hdt-selected*)
         (fn-served-conn-observation *hdt-selected*)
         (fn-served-conn-injection *hdt-selected*)
         (fn-served-conn-verdicts *hdt-selected*)
         (fn-served-conn-index *hdt-selected*)
         (fn-served-conn-group-index *hdt-selected*)
         (fn-served-conn-control *hdt-selected*)
         (fn-served-conn-pinned *hdt-selected*)
         (fn-served-conn-live *hdt-selected*)))
     (as (fn-served-conn-session conn))
     (config (fn-served-conn-config conn))
     (archive (fn-served-conn-archive conn))
     (index (fn-served-conn-pinned-index conn))
     (observation (fn-served-conn-observation conn))
     (peer (fn-auth-view-session as config))
     (viewarchive (fn-auth-view-archive as config archive))
     (viewindex (fn-auth-view-index as config archive index))
     (viewconfig (fn-auth-view-config as (fn-auth-moderation-config as config) archive))
     (ps (fn-peer-session-base peer))
     (session (fn-post-session-base ps))
     (env (fn-post-reader-env viewconfig observation))
     (server (fn-nntp-xref-server env))
     (r
       (fn-rcompat-retrieval
         session
         viewarchive
         (fn-gidx-pin-trie viewindex)
         :head
         (list (quote (49)))
         server
         (list *hdt-payload*)))
     (p
       (fn-served-step
         conn
         (append (fn-nntp-string-octets "HEAD 1") (quote (13 10)))
         (list *hdt-payload*))))
    (and
      (and
        (fn-wire-statep (fn-served-conn-wire conn))
        (<= (len (fn-nntp-string-octets "HEAD 1")) 510)
        (fn-auth-sessionp as)
        (not (fn-auth-session-handshakingp as))
        (not (fn-auth-sasl-waitingp as))
        (or
          (not (fn-auth-config-requiredp (fn-auth-session-config as)))
          (fn-auth-session-subject as))
        (null (fn-peer-session-peer peer))
        (not (fn-post-session-awaiting ps))
        (equal (fn-nntp-session-openp session) t)
        (fn-nntp-session-projected session)
        (fn-nntp-command-inputp (fn-nntp-string-octets "HEAD 1"))
        (equal
          (fn-nntp-tokenize (fn-nntp-string-octets "HEAD 1"))
          (list *fn-hdc-head-keyword* (quote (49))))
        server
        (fn-gidx-pinp viewindex)
        (not (fn-nntp-number-withdrawn-p session viewarchive viewindex (quote (49))))
        (not
          (and
            (fn-nntp-message-id-tokenp (quote (49)))
            (fn-nntp-msgid-withdrawn-p viewindex (quote (49))))))
      (and
        (equal (fn-served-result-effects p) (fn-nntp-result-effects r))
        (equal
          (fn-post-session-base
            (fn-peer-session-base
              (fn-auth-session-base (fn-served-conn-session (fn-served-result-conn p)))))
          (fn-nntp-result-session r))
        (equal (fn-served-conn-pinned (fn-served-result-conn p)) (fn-served-conn-pinned conn))
        (equal (fn-served-conn-archive (fn-served-result-conn p)) (fn-served-conn-archive conn))
        (equal (fn-served-conn-index (fn-served-result-conn p)) (fn-served-conn-index conn)))))
  :rule-classes
  nil)
