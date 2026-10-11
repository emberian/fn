; The actual request factory's retained ARTICLE request. Parsing, selection,
; privacy, framing and selected-session commit remain ACL2 decisions.
(in-package "ACL2")
(include-book "article-stream")
(include-book "article-stream-server")
(include-book "article-select-index")
(include-book "owner-credits")
(include-book "served-plan")
(include-book "served-query-plan")

(defun fn-asto-with-wire-session (conn wire session)
  (declare (xargs :guard t))
  (fn-own-conn-make-group-indexed
   (fn-own-conn-id conn) (fn-own-conn-version conn) (fn-own-conn-frontier conn)
   wire session (fn-own-conn-archive conn) (fn-own-conn-config conn)
   (fn-own-conn-observation conn) (fn-own-conn-verdicts conn) (fn-own-conn-group-index conn) (fn-own-conn-control conn)))

(defun fn-asto-with-conn (oc conn)
  (declare (xargs :guard t))
  (let ((o (fn-ocfg-owner oc)))
    (fn-ocfg-with-owner oc
      (fn-own-set-conns o (fn-own-replace-conn conn (fn-own-conns o))))))

(defun fn-asto-selection-start (session archive index args)
  (declare (xargs :guard t))
  (let ((group (fn-nntp-session-group session)))
    (cond
     ((null args)
      (let ((number (fn-nntp-session-current session)))
        (and group (posp number) (<= number *fn-nntp-max-article-number*)
             (fn-ast-select-state :current group number (fn-state-articles archive)
                                  nil nil nil 0 :next))))
     ((and group (consp args) (null (cdr args)) (fn-nntp-number-tokenp (car args)))
      (fn-ast-select-state :number group (fn-nntp-decimal-value (car args))
                           (fn-state-articles archive) nil nil nil 0 :next))
     ((and (consp args) (null (cdr args))
           (fn-nntp-message-id-tokenp (car args)) (fn-octet-listp (car args)))
      (let ((key (fn-nntp-token-string (car args))))
        (if (fn-gidx-pinp index)
            (let ((article (fn-find-article key (fn-state-articles archive))))
              (if (consp article) (fn-ast-msgid-local-start group article)
                (fn-ast-select-state :msgid group key nil nil nil nil 0 :missing)))
          (fn-ast-select-state :msgid group key (fn-state-articles archive)
                               nil nil nil 0 :msgid-next))))
     (t nil))))

; The same selection start for a session whose read is unrestricted, answered by
; the catalog's two indexes at the connection's pinned view V: the number index
; (fn-scat-number-article, one probe) and the Message-ID column
; (fn-scat-msgid-article). The result is the state the walk above reaches (the
; KEYSTONES below), with no archive-list traversal.
(defun fn-asto-selection-start-cat (session v args fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (and (natp v)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))))
  (let ((group (fn-nntp-session-group session)))
    (cond
     ((null args)
      (let ((number (fn-nntp-session-current session)))
        (and group (posp number) (<= number *fn-nntp-max-article-number*)
             (fn-asx-done-state :current group number
                                (and (stringp group)
                                     (fn-scat-number-article group number v fn-arena fn-cat))))))
     ((and group (consp args) (null (cdr args)) (fn-nntp-number-tokenp (car args)))
      (let ((number (fn-nntp-decimal-value (car args))))
        (fn-asx-done-state :number group number
                           (and (stringp group)
                                (fn-scat-number-article group number v fn-arena fn-cat)))))
     ((and (consp args) (null (cdr args))
           (fn-nntp-message-id-tokenp (car args)) (fn-octet-listp (car args)))
      (let* ((key (fn-nntp-token-string (car args)))
             (article (fn-scat-msgid-article key v fn-arena fn-cat)))
        (if (consp article) (fn-ast-msgid-local-start group article)
          (fn-ast-select-state :msgid group key nil nil nil nil 0 :missing))))
     (t nil))))

(local
 (defthm fn-asto-start-number-unfolds
   (implies (and (fn-nntp-session-group session)
                 (consp args) (null (cdr args)) (fn-nntp-number-tokenp (car args)))
            (equal (fn-asto-selection-start session archive index args)
                   (fn-ast-select-state :number (fn-nntp-session-group session)
                                        (fn-nntp-decimal-value (car args))
                                        (fn-state-articles archive) nil nil nil 0 :next)))
   :hints (("Goal" :in-theory (e/d (fn-asto-selection-start) ())))))

(local
 (defthm fn-asto-start-cat-number-unfolds
   (implies (and (fn-nntp-session-group session)
                 (consp args) (null (cdr args)) (fn-nntp-number-tokenp (car args)))
            (equal (fn-asto-selection-start-cat session v args fn-arena fn-cat)
                   (fn-asx-done-state :number (fn-nntp-session-group session)
                                      (fn-nntp-decimal-value (car args))
                                      (and (stringp (fn-nntp-session-group session))
                                           (fn-scat-number-article (fn-nntp-session-group session)
                                                                   (fn-nntp-decimal-value (car args))
                                                                   v fn-arena fn-cat)))))
   :hints (("Goal" :in-theory (e/d (fn-asto-selection-start-cat) ())))))

(local
 (defthm fn-nntp-number-token-value-posp
   (implies (fn-nntp-number-tokenp token) (posp (fn-nntp-decimal-value token)))
   :hints (("Goal" :in-theory (enable fn-nntp-number-tokenp)))))

(local
 (defthm fn-scr-catalogp-parts
   (implies (fn-scr-catalogp archive index v fn-arena fn-cat)
            (and (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat))
                 (fn-cnx-freshp fn-cat)))
   :hints (("Goal" :in-theory (enable fn-scr-catalogp)))))

(defthm fn-asto-selection-start-cat-number
  (implies (and (fn-scr-catalogp archive index v fn-arena fn-cat)
                (fn-nntp-session-group session)
                (consp args) (null (cdr args)) (fn-nntp-number-tokenp (car args))
                (posp fuel)
                (<= (fn-asx-need (fn-asto-selection-start session archive index args)) fuel))
           (equal (fn-asx-outcome
                   (fn-ast-select-step (fn-asto-selection-start session archive index args) fuel))
                  (fn-asx-outcome (fn-asto-selection-start-cat session v args fn-arena fn-cat))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-ast-select-step fn-ast-select-one fn-asx-goodp fn-cat-view-articles
                               fn-gidx-pinp
                               fn-asx-walk-is-lookup fn-asx-walk-nonstring fn-scat-number-article
                               fn-scat-number-article-is-find-group-number fn-scr-catalogp
                               fn-asx-first fn-asx-done-state fn-asx-outcome fn-asx-need)
           :use ((:instance fn-scr-catalogp-parts)
                 (:instance fn-asx-walk-nonstring (mode :number)
                            (group (fn-nntp-session-group session))
                            (number (fn-nntp-decimal-value (car args)))
                            (articles (fn-state-articles archive)))
                 (:instance fn-asx-walk-is-lookup (mode :number)
                            (group (fn-nntp-session-group session))
                            (number (fn-nntp-decimal-value (car args)))
                            (articles (fn-state-articles archive)))
                 (:instance fn-scat-number-article-is-find-group-number
                            (group (fn-nntp-session-group session))
                            (n (fn-nntp-decimal-value (car args)))
                            (v v))
                 (:instance fn-asx-first-number-is-find-group-number
                            (group (fn-nntp-session-group session))
                            (number (fn-nntp-decimal-value (car args)))
                            (articles (fn-state-articles archive)))))))

(local
 (defthm fn-asto-start-current-unfolds
   (implies (and (fn-nntp-session-group session) (null args)
                 (posp (fn-nntp-session-current session))
                 (<= (fn-nntp-session-current session) *fn-nntp-max-article-number*))
            (equal (fn-asto-selection-start session archive index args)
                   (fn-ast-select-state :current (fn-nntp-session-group session)
                                        (fn-nntp-session-current session)
                                        (fn-state-articles archive) nil nil nil 0 :next)))
   :hints (("Goal" :in-theory (enable fn-asto-selection-start)))))

(local
 (defthm fn-asto-start-cat-current-unfolds
   (implies (and (fn-nntp-session-group session) (null args)
                 (posp (fn-nntp-session-current session))
                 (<= (fn-nntp-session-current session) *fn-nntp-max-article-number*))
            (equal (fn-asto-selection-start-cat session v args fn-arena fn-cat)
                   (fn-asx-done-state :current (fn-nntp-session-group session)
                                      (fn-nntp-session-current session)
                                      (and (stringp (fn-nntp-session-group session))
                                           (fn-scat-number-article (fn-nntp-session-group session)
                                                                   (fn-nntp-session-current session)
                                                                   v fn-arena fn-cat)))))
   :hints (("Goal" :in-theory (enable fn-asto-selection-start-cat)))))

(local
 (defthm fn-asto-view-articles-uniq
   (implies (and (fn-cnx-freshp fn-cat) group)
            (fn-scat-uniq group (fn-cat-view-articles v fn-arena fn-cat)))
   :hints (("Goal" :in-theory (e/d (fn-cat-view-articles) (fn-scat-uniq-of-view-below fn-cat-view-below))
                   :use ((:instance fn-scat-uniq-of-view-below (i (fn-cat-count fn-cat))))))))

(defthm fn-asto-selection-start-cat-current
  (implies (and (fn-scr-catalogp archive index v fn-arena fn-cat)
                (fn-nntp-session-group session) (null args)
                (posp (fn-nntp-session-current session))
                (<= (fn-nntp-session-current session) *fn-nntp-max-article-number*)
                (posp fuel)
                (<= (fn-asx-need (fn-asto-selection-start session archive index args)) fuel))
           (equal (fn-asx-outcome
                   (fn-ast-select-step (fn-asto-selection-start session archive index args) fuel))
                  (fn-asx-outcome (fn-asto-selection-start-cat session v args fn-arena fn-cat))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-ast-select-step fn-ast-select-one fn-asx-goodp fn-cat-view-articles
                               fn-gidx-pinp
                               fn-asx-walk-is-lookup fn-asx-walk-nonstring fn-scat-number-article
                               fn-scat-number-article-is-find-group-number fn-scr-catalogp
                               fn-asx-first fn-asx-done-state fn-asx-outcome fn-asx-need
                               fn-asx-first-current-is-found fn-asto-view-articles-uniq)
           :use ((:instance fn-scr-catalogp-parts)
                 (:instance fn-asx-walk-nonstring (mode :current)
                            (group (fn-nntp-session-group session))
                            (number (fn-nntp-session-current session))
                            (articles (fn-state-articles archive)))
                 (:instance fn-asx-walk-is-lookup (mode :current)
                            (group (fn-nntp-session-group session))
                            (number (fn-nntp-session-current session))
                            (articles (fn-state-articles archive)))
                 (:instance fn-scat-number-article-is-find-group-number
                            (group (fn-nntp-session-group session))
                            (n (fn-nntp-session-current session))
                            (v v))
                 (:instance fn-asto-view-articles-uniq (group (fn-nntp-session-group session)) (v v))
                 (:instance fn-asx-first-current-is-found
                            (group (fn-nntp-session-group session))
                            (number (fn-nntp-session-current session))
                            (articles (fn-state-articles archive)))))))

(local
 (defthm fn-asto-message-id-token-is-no-number-token
   (implies (fn-nntp-message-id-tokenp token)
            (not (fn-nntp-number-tokenp token)))
   :hints (("Goal" :in-theory (enable fn-nntp-message-id-tokenp fn-nntp-number-tokenp
                                      fn-nntp-decimal-tokenp)))))

; KEYSTONE (Message-ID, against the archive list): the catalog's answer starts the
; selection at the article the archive-list scan finds.
(defthm fn-asto-selection-start-cat-msgid-is-scan
  (implies (and (fn-scr-catalogp archive index v fn-arena fn-cat)
                (consp args) (null (cdr args))
                (fn-nntp-message-id-tokenp (car args)) (fn-octet-listp (car args)))
           (equal (fn-asto-selection-start-cat session v args fn-arena fn-cat)
                  (let ((article (fn-find-article (fn-nntp-token-string (car args))
                                                  (fn-state-articles archive))))
                    (if (consp article)
                        (fn-ast-msgid-local-start (fn-nntp-session-group session) article)
                      (fn-ast-select-state :msgid (fn-nntp-session-group session)
                                           (fn-nntp-token-string (car args))
                                           nil nil nil nil 0 :missing)))))
  :hints (("Goal" :in-theory (e/d (fn-asto-selection-start-cat fn-scr-catalogp
                                   fn-scat-msgid-article-is-find-article)
                                  (fn-scat-msgid-article fn-find-article fn-cat-view-articles
                                   fn-ast-msgid-local-start fn-nntp-token-string
                                   fn-nntp-message-id-tokenp fn-octet-listp)))))

; KEYSTONE (Message-ID, against the pinned trie walk): the same start state.
(defthm fn-asto-selection-start-cat-msgid
  (implies (and (fn-scr-catalogp archive index v fn-arena fn-cat)
                (fn-gidx-pinp index)
                (consp args) (null (cdr args))
                (fn-nntp-message-id-tokenp (car args)) (fn-octet-listp (car args)))
           (equal (fn-asto-selection-start session archive index args)
                  (fn-asto-selection-start-cat session v args fn-arena fn-cat)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-asto-selection-start fn-asto-selection-start-cat fn-scat-msgid-article-is-find-article)
                           (fn-scat-msgid-article fn-find-article fn-cat-view-articles
                            fn-ast-msgid-local-start fn-nntp-token-string
                            fn-nntp-message-id-tokenp fn-octet-listp fn-scr-catalogp
                            fn-nntp-number-tokenp))
           :use ((:instance fn-scr-catalogp-parts)
                 (:instance fn-nntp-message-id-token-has-nonempty-index-key (token (car args)))
                 (:instance fn-asto-message-id-token-is-no-number-token (token (car args)))))))

; KEYSTONE (Message-ID, archive with no trie): the walk over the archive list is
; the catalog's start state preceded by the work the walk spends finding it.
(defthm fn-asto-selection-start-cat-msgid-unpinned
  (implies (and (fn-scr-catalogp archive index v fn-arena fn-cat)
                (not (fn-gidx-pinp index))
                (consp args) (null (cdr args))
                (fn-nntp-message-id-tokenp (car args)) (fn-octet-listp (car args))
                (natp e))
           (equal (fn-ast-select-step
                   (fn-asto-selection-start session archive index args)
                   (+ (fn-asx-nc (fn-nntp-token-string (car args)) (fn-state-articles archive)) e))
                  (fn-ast-select-step
                   (fn-asto-selection-start-cat session v args fn-arena fn-cat) e)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-asto-selection-start fn-asto-selection-start-cat)
                           (fn-asx-msgid-walk-is-lookup fn-scat-msgid-article fn-find-article
                            fn-cat-view-articles
                            fn-ast-msgid-local-start fn-nntp-token-string fn-asx-nc
                            fn-nntp-message-id-tokenp fn-octet-listp fn-scr-catalogp
                            fn-nntp-number-tokenp fn-ast-select-step fn-ast-select-state))
           :use ((:instance fn-scr-catalogp-parts)
                 (:instance fn-nntp-message-id-token-has-nonempty-index-key (token (car args)))
                 (:instance fn-asto-message-id-token-is-no-number-token (token (car args)))
                 (:instance fn-scat-msgid-article-is-find-article
                            (msgid (fn-nntp-token-string (car args))))
                 (:instance fn-asx-msgid-walk-is-lookup
                            (group (fn-nntp-session-group session))
                            (key (fn-nntp-token-string (car args)))
                            (rem (fn-state-articles archive))
                            (fuel (+ (fn-asx-nc (fn-nntp-token-string (car args))
                                                (fn-state-articles archive)) e)))))))

; The selection the owner's capture starts: a session under a read restriction is
; answered over the view its rule projects (the catalog holds every article and
; knows no projection); every other session by the catalog's indexes at the
; connection's pinned view V. KEYSTONES: fn-asto-selection-start-cat-number,
; -current, -msgid and -msgid-unpinned equate the unrestricted arm with the walk.
(defun fn-asto-capture-selection (as config session va vi args v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (and (natp v)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))))
  (if (fn-auth-access-read as config)
      (fn-asto-selection-start session va vi args)
    (fn-asto-selection-start-cat session v args fn-arena fn-cat)))

(defthm fn-asto-view-of-unrestricted
  (implies (not (fn-auth-access-read as config))
           (and (equal (fn-auth-view-archive as config archive) archive)
                (equal (fn-auth-view-index as config archive index) index)))
  :hints (("Goal" :in-theory (enable fn-auth-view-archive fn-auth-view-index))))

(defthm fn-asto-capture-selection-restricted
  (implies (fn-auth-access-read as config)
           (equal (fn-asto-capture-selection as config session va vi args v fn-arena fn-cat)
                  (fn-asto-selection-start session va vi args))))

(defthm fn-asto-capture-selection-unrestricted
  (implies (not (fn-auth-access-read as config))
           (equal (fn-asto-capture-selection as config session va vi args v fn-arena fn-cat)
                  (fn-asto-selection-start-cat session v args fn-arena fn-cat))))

; Capture = (expected-conn auth-view-peer selection kind server scan
;            connection-configuration-pin withdrawn-articles). EXPECTED-CONN includes the installed
; post-command wire but its reader selection is unchanged until preflight.
(defun fn-asto-payload-preflight (article fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (let ((source (fn-ast-source article fn-arena)))
    (if (or (not (fn-nntp-article-idp article))
            (fn-nntp-article-tombstonep article fn-arena))
        (fn-ast-refused-preflight source)
      (fn-ast-preflight source))))

(local
 (defthm fn-asto-line-tokens-true-listp
   (true-listp (fn-nsp-line-tokens line))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-nsp-line-tokens fn-nsp-tokens-of)))))

(defun fn-asto-capture (oc id w cache fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (true-listp (fn-wsp-events w))
                              (true-listp (car (fn-wsp-events w)))
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :guard-hints (("Goal" :in-theory (disable fn-asto-capture-selection
                                                            fn-asto-payload-preflight
                                                            fn-scr-cached-view)))))
  (let* ((o (fn-ocfg-owner oc)) (conn (fn-own-find-conn id (fn-own-conns o)))
         (sc (and conn (fn-own-tls-served-conn o conn)))
         (as (fn-served-conn-session sc)) (config (fn-served-conn-config sc))
         (events (fn-wsp-events w)) (event (car events))
         ;; A3: the tokens by the fn-nsp-tokens stream (nil unless the
         ;; line passes the RFC 3977 section 3.1 preflight;
         ;; fn-nsp-line-tokens-is-tokenize).
         (tokens (and (equal (car event) :command)
                      (fn-cbor-octet-listp (cadr event))
                      (unsigned-byte-p 59 (len (cadr event)))
                      (fn-nsp-line-tokens (cadr event))))
         (keyword (car tokens))
         (kind (cond ((fn-nntp-keywordp keyword "ARTICLE") :article)
                     ((fn-nntp-keywordp keyword "HEAD") :head)
                     ((fn-nntp-keywordp keyword "BODY") :body)
                     (t nil))))
    (if (not (and conn kind (null (cdr events))
                  (fn-nntp-keyword-tokenp keyword)
                  (fn-nntp-command-arguments-at-mostp tokens)
                  (fn-scar-auth-sessionp as (fn-sn-node (fn-own-store o)))
                  (not (fn-auth-session-handshakingp as))
                  (not (fn-auth-sasl-waitingp as))
                  (not (fn-auth-command as config keyword (cdr tokens)))
                  (not (fn-post-session-awaiting (fn-auth-post-session as)))
                  (not (fn-peer-session-transfer (fn-auth-session-base as)))))
        nil
      (let* ((archive (fn-served-conn-archive sc))
             (index (fn-served-conn-pinned-index sc))
             (view (fn-scr-cached-view as config archive index cache))
             (va (if view (fn-ag-car view) (fn-auth-view-archive as config archive)))
             (vi (if view (fn-ag-cdr view) (fn-auth-view-index as config archive index)))
             (ps (fn-auth-view-session as config))
             (selection (fn-asto-capture-selection as config (fn-peer-reader-session ps) va vi (cdr tokens)
                                                   (fn-scr-view-of (fn-own-conn-version conn) fn-cat)
                                                   fn-arena fn-cat)))
        (if (not (and selection
                     (equal (fn-nntp-session-openp (fn-peer-reader-session ps)) t)
                     (fn-nntp-session-projected (fn-peer-reader-session ps)))) nil
          (let* ((server (and (not (eq kind :body))
                              (fn-asto-server-candidate config)))
                 (expected (fn-asto-with-wire-session conn (fn-wsp-state w)
                                                     (fn-own-conn-session conn))))
            (list expected ps selection kind server
                  (and (not (eq (car selection) :article-select))
                       (fn-asto-payload-preflight (car selection) fn-arena))
                  (fn-ocfg-conn-config oc id)
                  (and (eq (car selection) :article-select)
                       (member-eq (fn-ast-at 1 selection) '(:number :msgid))
                       (fn-ctl-pin-withdrawn (fn-gidx-pin-control vi))))))))))

; One wire event per request: a following NEXT/ARTICLE remains unconsumed
; while this retrieval's preflight owns its response. This is a core parser
; boundary, independent of the optional physical funding policy.
;; A1: a command-mode connection's first event by the fn-nsp-frame stream
;; into a line workspace (the partial line carried in the wire state's
;; line-rev reloaded first; adapter A1, owner Builder C, retired when a
;; connection owns its line workspace span); fn-asto-first-event-is-span-fold
;; ties it to the byte fold.  An article-mode connection (a POST body) keeps
;; fn-wire-scan, the POST family's scanner.
(local (defthm fn-asto-octet-listp-rev
  (implies (fn-cbor-octet-listp x) (fn-cbor-octet-listp (rev x)))
  :hints (("Goal" :in-theory (enable rev fn-cbor-octet-listp)))))
(defun fn-asto-frame-line (ws start end fn-octets fn-ast-ws)
  (declare (xargs :stobjs (fn-octets fn-ast-ws)
                  :guard (and (fn-wire-fast-statep ws)
                              (equal (fn-wire-state-mode ws) :command)
                              (unsigned-byte-p 55 (fn-wire-state-line-limit ws))
                              (fn-cbor-octet-listp (fn-wire-state-line-rev ws))
                              (unsigned-byte-p 58 (len (fn-wire-state-line-rev ws)))
                              (unsigned-byte-p 59 start) (unsigned-byte-p 59 end) (<= start end)
                              (<= end (fn-octets-len fn-octets)))
                  :guard-hints (("Goal" :in-theory (disable fn-nsp-frame fn-nsp-frame-wsp)))))
  (let* ((ll (fn-wire-state-line-limit ws))
         (fn-ast-ws (fn-ast-ws-from-list (fn-wire-reverse-octets (fn-wire-state-line-rev ws)) fn-ast-ws)))
    (mv-let (r s2 i2 fn-ast-ws)
      (fn-nsp-frame ll (ec-call (fn-nsp-frame-state-of ws)) start end nil (+ 1 ll) fn-octets fn-ast-ws)
      (mv (ec-call (fn-nsp-frame-wsp r s2 i2 (fn-ast-ws-list fn-ast-ws) ws)) fn-ast-ws))))
; The mode is tested first: in :article mode fn-wire-statep walks the
; accumulated body (fn-bch-body-okp over body-rev), which on every read of a
; POST body made the upload quadratic (a 3 MiB POST did not finish in 400 s on
; hbox, spans-a2-237cdbb); a command-mode state's walk is its one line.
(defun fn-asto-frame-casep (ws start end)
  (declare (xargs :guard t))
  (and (equal (fn-wire-state-mode ws) :command)
       (fn-wire-statep ws)
       (unsigned-byte-p 55 (fn-wire-state-line-limit ws))
       (fn-cbor-octet-listp (fn-wire-state-line-rev ws))
       (unsigned-byte-p 58 (len (fn-wire-state-line-rev ws)))
       (unsigned-byte-p 59 start) (unsigned-byte-p 59 end)))
(defthm fn-asto-frame-line-is-span-fold
  (implies (and (fn-octets-p fn-octets)
                (fn-asto-frame-casep ws start end) (<= start end) (<= end (fn-octets-len fn-octets)))
           (equal (mv-nth 0 (fn-asto-frame-line ws start end fn-octets fn-ast-ws))
                  (fn-wire-span-fold ws start end fn-octets)))
  :hints (("Goal" :use ((:instance fn-nsp-frame-is-wire-span-fold (i start)
                                   (fn-dss-out (fn-wire-reverse-octets (fn-wire-state-line-rev ws)))))
           :in-theory (disable fn-nsp-frame fn-nsp-frame-wsp fn-wire-span-fold
                               fn-wire-statep fn-nsp-frame-state-of))))
;; Guard t (the stobj's recognizer only), the range tested in the body: as
;; fn-nsp-line-tokens, so the local fn-ast-ws writes carry no invariant-risk
;; up the :program read chain (host/owner-host.lisp fn-asto-mca-read-span).
(defun fn-asto-first-event (oc id start end fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard-hints (("Goal" :in-theory (disable fn-asto-frame-line fn-wire-scan fn-wire-statep)))))
  (let* ((conn (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))
         (ws (and conn (fn-own-conn-wire conn))))
    (and (natp start) (natp end) (<= start end) (<= end (fn-octets-len fn-octets))
         conn (fn-wire-fast-statep ws)
         (if (fn-asto-frame-casep ws start end)
             (with-local-stobj fn-ast-ws
               (mv-let (w fn-ast-ws) (fn-asto-frame-line ws start end fn-octets fn-ast-ws)
                 w))
           (fn-wire-scan ws start end fn-octets)))))
(defthm fn-asto-first-event-is-span-fold
  (implies (and (fn-octets-p fn-octets) (natp start) (natp end) (<= start end)
                (<= end (fn-octets-len fn-octets)))
           (equal (fn-asto-first-event oc id start end fn-octets)
                  (let* ((conn (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))
                         (ws (and conn (fn-own-conn-wire conn))))
                    (and conn (fn-wire-fast-statep ws)
                         (fn-wire-span-fold ws start end fn-octets)))))
  :hints (("Goal" :use ((:instance fn-wire-scan-is-span-fold
                                   (wire-state (fn-own-conn-wire (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))))
                                   (i start)))
           :in-theory (disable fn-wire-scan-is-span-fold fn-wire-scan fn-wire-span-fold fn-asto-frame-line
                               fn-asto-frame-casep fn-wire-fast-statep))))

(defun fn-asto-captured-result (oc capture consumed)
  (declare (xargs :guard t))
  (fn-own-tls-make-result consumed (list (list :article-preflight capture))
                          (fn-asto-with-conn oc (fn-ast-at 0 capture)) nil))

(defun fn-asto-capture-with-scan (capture scan)
  (declare (xargs :guard t))
  (list (fn-ast-at 0 capture) (fn-ast-at 1 capture) (fn-ast-at 2 capture)
        (fn-ast-at 3 capture) (fn-ast-at 4 capture) scan (fn-ast-at 6 capture)
        (fn-ast-at 7 capture)))

(defun fn-asto-capture-with-selection (capture selection scan)
  (declare (xargs :guard t))
  (list (fn-ast-at 0 capture) (fn-ast-at 1 capture) selection
        (fn-ast-at 3 capture) (fn-ast-at 4 capture) scan (fn-ast-at 6 capture)
        (fn-ast-at 7 capture)))

(defun fn-asto-selection-missing (oc capture)
  (declare (xargs :guard t))
  (let* ((expected (fn-ast-at 0 capture)) (id (fn-own-conn-id expected))
         (current (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))
         (ps (fn-ast-at 1 capture)) (selection (fn-ast-at 2 capture))
         (session (fn-peer-reader-session ps)))
    (if (not (and (equal expected current)
                  (equal (fn-ocfg-conn-config oc id) (fn-ast-at 6 capture))))
        (mv :stale oc nil)
      (let* ((as (fn-auth-with-base (fn-own-conn-session expected) ps))
             (conn (fn-asto-with-wire-session current (fn-own-conn-wire current) as)))
        (mv :ready (fn-asto-with-conn oc conn)
            (fn-nntp-result-effects
             (fn-nntp-single session
               (cond ((and (eq (fn-ast-at 1 selection) :withdrawn-msgid)
                           (eq (fn-ast-at 9 selection) :selected)) "430 withdrawn")
                     ((member-eq (fn-ast-at 1 selection) '(:msgid :withdrawn-msgid))
                      "430 no article with that message-id")
                     ((eq (fn-ast-at 1 selection) :current) "420 no current article")
                     ((and (eq (fn-ast-at 1 selection) :withdrawn)
                           (eq (fn-ast-at 9 selection) :selected)) "423 withdrawn")
                     (t "423 no article with that number")))))))))

;; The READY decision over the selection state NEXT the step reached: it reads
;; only NEXT's outcome fields (mode, number, group, phase, article: fn-asx-outcome)
;; and CAPTURE's other fields (books/article-stream-owner-bridge.lisp states it).
(defun fn-asto-selection-ready-on (oc capture next fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (cond
   ((and (eq (fn-ast-at 9 next) :selected)
         (member-eq (fn-ast-at 1 next) '(:withdrawn :withdrawn-msgid)))
    (fn-asto-selection-missing oc (fn-asto-capture-with-selection capture next nil)))
   ((eq (fn-ast-at 9 next) :selected)
    (let* ((article (fn-ast-at 5 next))
           (msgidp (eq (fn-ast-at 1 next) :msgid))
           (selection (list article (fn-ast-at 3 next) (not msgidp)
                             (and (not msgidp) (fn-ast-at 2 next))))
           (capture2 (fn-asto-capture-with-selection capture selection
                        (fn-asto-payload-preflight article fn-arena))))
      (mv :yield oc (list (list :article-preflight capture2)))))
   ((eq (fn-ast-at 9 next) :missing)
    (if (and (member-eq (fn-ast-at 1 next) '(:number :msgid)) (consp (fn-ast-at 7 capture)))
        (mv :yield oc (list (list :article-preflight
          (fn-asto-capture-with-selection capture
            (fn-ast-select-state
              (if (eq (fn-ast-at 1 next) :msgid) :withdrawn-msgid :withdrawn)
              (fn-ast-at 2 next) (fn-ast-at 3 next) (fn-ast-at 7 capture) nil nil nil 0
              (if (eq (fn-ast-at 1 next) :msgid) :msgid-next :next)) nil))))
      (fn-asto-selection-missing oc (fn-asto-capture-with-selection capture next nil))))
   (t (mv :yield oc (list (list :article-preflight
                        (fn-asto-capture-with-selection capture next nil)))))))

(defun fn-asto-selection-ready (oc capture fuel fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (fn-asto-selection-ready-on oc capture
                              (fn-ast-select-step (fn-ast-at 2 capture) (nfix fuel))
                              fn-arena))

; Finish decides both the session and READY plan. No host parser, reply line,
; or framing verdict participates. The connection/configuration comparison
; fences stale captures; replaying READY has no call site for this function.
(defun fn-asto-finish (oc capture fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (let* ((expected (fn-ast-at 0 capture)) (id (fn-own-conn-id expected))
         (current (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))
         (ps (fn-ast-at 1 capture)) (selection (fn-ast-at 2 capture))
         (article (fn-ast-at 0 selection)) (number (fn-ast-at 1 selection))
         (updatep (fn-ast-at 2 selection)) (group (fn-ast-at 3 selection))
         (kind (fn-ast-at 3 capture)) (scan (fn-ast-at 5 capture))
         (session (fn-peer-reader-session ps)))
    (if (not (and (equal current expected)
                  (equal (fn-ocfg-conn-config oc id) (fn-ast-at 6 capture))
                  (fn-ast-scan-donep scan)))
        (mv :stale oc nil)
      (let* ((tomb (fn-nntp-article-tombstonep article fn-arena))
             (ok (and (fn-nntp-article-idp article) (not tomb) (fn-ast-scan-validp scan)))
             (next (if (and ok updatep) (fn-nntp-set-cursor session group number) session))
             (as (fn-auth-with-base (fn-own-conn-session expected)
                   (fn-peer-with-base ps (fn-post-make-session next nil))))
             (conn (fn-asto-with-wire-session current (fn-own-conn-wire current) as))
             (effects
              (if ok
                  (list (list :article-cursor
                         (fn-ast-ready-memberships scan kind number article (fn-ast-at 4 capture))))
                (fn-nntp-result-effects
                 (fn-nntp-single session
                  (cond ((not (fn-nntp-article-idp article)) "503 stored article identifier unavailable")
                        (tomb (if updatep "423 article reclaimed" "430 article reclaimed"))
                        (t "503 stored article framing unavailable")))))))
        (mv :ready (fn-asto-with-conn oc conn) effects)))))

;; The ARTICLE cursor effects a plan holds. FN-ASTO-CURSOR-EFFECTSP is the guard of
;; every function that renders or steps a plan's rest: each effect is a list,
;; and an :article-cursor effect carries a window the render transition accepts
;; (fn-ast-windowp). The only maker of such an effect is fn-asto-finish, through
;; fn-ast-ready-memberships (fn-asto-finish-effects-cursor-effectsp); the READY
;; and render steps keep it (fn-asto-ready-rest-keeps-cursor-effectsp,
;; fn-asto-plan-render-window-keeps-render-planp).
(defun fn-asto-cursor-effectsp (rest fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (consp rest)
      (and (true-listp (car rest))
           (or (not (eq (car (car rest)) :article-cursor))
               (and (consp (cdr (car rest)))
                    (fn-ast-windowp (car (cdr (car rest))) fn-arena)))
           (fn-asto-cursor-effectsp (cdr rest) fn-arena))
    (null rest)))

; The effects the READY steps return are lists: fn-asto-ready-rest appends the
; rest of the plan to them.
(local
 (progn
   (defthm fn-asto-single-effects-true-listp
     (true-listp (fn-nntp-result-effects (fn-nntp-single session text)))
     :hints (("Goal" :in-theory (enable fn-nntp-result-effects fn-nntp-single fn-nntp-make-result))))
   (defthm fn-asto-selection-missing-effects-true-listp
     (true-listp (mv-nth 2 (fn-asto-selection-missing oc capture)))
     :rule-classes :type-prescription
     :hints (("Goal" :in-theory (enable fn-asto-selection-missing))))
   (defthm fn-asto-selection-ready-on-effects-true-listp
     (true-listp (mv-nth 2 (fn-asto-selection-ready-on oc capture next fn-arena)))
     :rule-classes :type-prescription
     :hints (("Goal" :in-theory (enable fn-asto-selection-ready-on))))
   (defthm fn-asto-selection-ready-effects-true-listp
     (true-listp (mv-nth 2 (fn-asto-selection-ready oc capture fuel fn-arena)))
     :rule-classes :type-prescription
     :hints (("Goal" :in-theory (enable fn-asto-selection-ready))))
   (defthm fn-asto-cursor-effectsp-append
     (implies (and (true-listp x) (fn-asto-cursor-effectsp x fn-arena)
                   (fn-asto-cursor-effectsp y fn-arena))
              (fn-asto-cursor-effectsp (append x y) fn-arena)))
   (defthm fn-asto-selection-missing-cursor-effectsp
     (fn-asto-cursor-effectsp (mv-nth 2 (fn-asto-selection-missing oc capture)) fn-arena)
     :hints (("Goal" :in-theory (enable fn-asto-selection-missing fn-nntp-result-effects
                                        fn-nntp-single fn-nntp-make-result fn-asto-cursor-effectsp))))
   (defthm fn-asto-selection-ready-on-cursor-effectsp
     (fn-asto-cursor-effectsp (mv-nth 2 (fn-asto-selection-ready-on oc capture next fn-arena)) fn-arena)
     :hints (("Goal" :in-theory (enable fn-asto-selection-ready-on fn-asto-cursor-effectsp))))
   (defthm fn-asto-selection-ready-cursor-effectsp
     (fn-asto-cursor-effectsp (mv-nth 2 (fn-asto-selection-ready oc capture fuel fn-arena)) fn-arena)
     :hints (("Goal" :in-theory (enable fn-asto-selection-ready))))
   (defthm fn-asto-finish-effects-true-listp
     (true-listp (mv-nth 2 (fn-asto-finish oc capture fn-arena)))
     :rule-classes :type-prescription
     :hints (("Goal" :in-theory (enable fn-asto-finish))))
   (defthm fn-asto-finish-cursor-effectsp
     (fn-asto-cursor-effectsp (mv-nth 2 (fn-asto-finish oc capture fn-arena)) fn-arena)
     :hints (("Goal" :in-theory (e/d (fn-asto-finish fn-asto-cursor-effectsp fn-nntp-result-effects
                                      fn-nntp-single fn-nntp-make-result)
                                     (fn-ast-at fn-ast-ready-memberships fn-ast-windowp)))))))


(defun fn-asto-ready-rest (oc id rest fuel fn-arena fn-ast-ws)
  (declare (xargs :stobjs (fn-arena fn-ast-ws) :guard (fn-asto-cursor-effectsp rest fn-arena)
                  :guard-hints (("Goal" :in-theory (disable fn-asto-selection-ready
                                                            fn-asto-finish fn-ast-scan-step)))))
  (if (atom rest) (mv :ready oc rest fn-ast-ws)
    (if (eq (caar rest) :article-preflight)
        (let ((capture (cadar rest)))
          (if (eq (fn-ast-at 0 (fn-ast-at 2 capture)) :article-select)
              (if (not (equal id (fn-own-conn-id (fn-ast-at 0 capture))))
                  (mv :stale oc rest fn-ast-ws)
                (mv-let (word oc2 effects) (fn-asto-selection-ready oc capture fuel fn-arena)
                  (mv word oc2 (append effects (cdr rest)) fn-ast-ws)))
            (if (not (equal id (fn-own-conn-id (fn-ast-at 0 capture))))
                (mv :stale oc rest fn-ast-ws)
              (mv-let (scan fn-ast-ws)
                (fn-ast-scan-step (fn-ast-at 5 capture) (nfix fuel) fn-arena fn-ast-ws)
                (let ((next (fn-asto-capture-with-scan capture scan)))
                  (if (not (fn-ast-scan-donep scan))
                      (mv :yield oc (cons (list :article-preflight next) (cdr rest)) fn-ast-ws)
                    (mv-let (word oc2 effects) (fn-asto-finish oc next fn-arena)
                      (mv word oc2 (append effects (cdr rest)) fn-ast-ws))))))))
      (mv-let (word oc2 next fn-ast-ws) (fn-asto-ready-rest oc id (cdr rest) fuel fn-arena fn-ast-ws)
        (mv word oc2 (cons (car rest) next) fn-ast-ws)))))

;; Guard t (the stobj recognizers only): the plan's shape is tested here and
;; a plan without it takes fn-asto-ready-rest by ec-call (guard-checked, the
;; logic unchanged), so the fn-ast-ws writes below carry no invariant-risk
;; into the :program caller host/owner-host.lisp
;; fn-owner-article-ready-plan-step, which then runs raw.
(defun fn-asto-ready-plan-step (oc id plan fuel fn-arena fn-ast-ws)
  (declare (xargs :stobjs (fn-arena fn-ast-ws)))
  (mv-let (word oc2 rest fn-ast-ws)
    (if (fn-asto-cursor-effectsp (fn-splan-rest plan) fn-arena)
        (fn-asto-ready-rest oc id (fn-splan-rest plan) fuel fn-arena fn-ast-ws)
      (ec-call (fn-asto-ready-rest oc id (fn-splan-rest plan) fuel fn-arena fn-ast-ws)))
    (mv word oc2 (cons (fn-splan-cur plan) rest) fn-ast-ws)))

(defthm fn-asto-ready-rest-keeps-cursor-effectsp
  (implies (fn-asto-cursor-effectsp rest fn-arena)
           (fn-asto-cursor-effectsp
            (mv-nth 2 (fn-asto-ready-rest oc id rest fuel fn-arena fn-ast-ws)) fn-arena))
  :hints (("Goal" :induct (fn-asto-ready-rest oc id rest fuel fn-arena fn-ast-ws)
                  :in-theory (e/d (fn-asto-cursor-effectsp)
                                  (fn-asto-selection-ready fn-asto-finish fn-ast-at
                                   fn-ast-scan-step fn-asto-capture-with-scan)))))

(defthm fn-asto-ready-plan-step-keeps-cursor-effectsp
  (implies (fn-asto-cursor-effectsp (fn-splan-rest plan) fn-arena)
           (fn-asto-cursor-effectsp
            (fn-splan-rest (mv-nth 2 (fn-asto-ready-plan-step oc id plan fuel fn-arena fn-ast-ws)))
            fn-arena))
  :hints (("Goal" :in-theory (e/d (fn-asto-ready-plan-step fn-splan-rest)
                                  (fn-asto-ready-rest)))))

(defun fn-asto-plan-cursorp (plan)
  (declare (xargs :guard t))
  (or (fn-qplan-at-cursorp plan)
      (and (not (consp (fn-splan-cur plan)))
           (member-eq (fn-cbor-ag-car (fn-cbor-ag-car (fn-splan-rest plan)))
                      '(:article-preflight :article-cursor)) t)))

(defun fn-asto-preflight-restp (rest)
  (declare (xargs :guard t))
  (and (consp rest)
       (or (eq (fn-cbor-ag-car (car rest)) :article-preflight)
           (fn-asto-preflight-restp (cdr rest)))))

(defun fn-asto-preflight-planp (plan)
  (declare (xargs :guard t))
  (fn-asto-preflight-restp (fn-splan-rest plan)))

(defun fn-asto-plan-articlep (plan)
  (declare (xargs :guard t))
  (and (not (consp (fn-splan-cur plan)))
       (eq (fn-cbor-ag-car (fn-cbor-ag-car (fn-splan-rest plan))) :article-cursor)))

;; The scheduling delay of a yielded plan, ACL2's: an ARTICLE or LIST quantum
;; spends its whole grant of visits, so it resumes on the loop's next pass
;; (fairness is the pass order, not a sleep); only an OVER/NEWNEWS quantum that
;; may have made empty progress waits fn-splan-cursor-resume-ms.
(defun fn-asto-resume-ms (plan)
  (declare (xargs :guard t))
  (if (or (fn-asto-plan-articlep plan) (fn-asto-preflight-planp plan)
          (fn-qplan-lst-cursorp plan))
      0
    (fn-splan-cursor-resume-ms)))

(defthm fn-asto-resume-ms-natp
  (natp (fn-asto-resume-ms plan))
  :rule-classes :type-prescription)

(defthm fn-asto-resume-ms-lst-is-immediate
  (implies (fn-qplan-lst-cursorp plan)
           (equal (fn-asto-resume-ms plan) 0)))

(defthm fn-asto-resume-ms-over-waits
  (implies (and (not (fn-asto-plan-articlep plan)) (not (fn-asto-preflight-planp plan))
                (not (fn-qplan-lst-cursorp plan)))
           (posp (fn-asto-resume-ms plan))))

;; The ARTICLE quantum: how many payload octets one hold of the owner mutex
;; scans (preflight fuel) or renders (window), and so how many octets one
;; write carries.  It was the OVER cursor's 256 (a NOV line's worth of
;; work), which made a 1 MiB ARTICLE 4096 quanta, each a mutex round, a write
;; and a scheduling turn.  An article octet costs about a microsecond, so
;; 16384 (the verified window) holds the mutex for milliseconds, the same
;; order a 256-line OVER quantum does; every bound over the quantum is
;; parametric (fn-ast-render-window-byte-bound; a preflight quantum loads at
;; most the quantum's octets, fn-ast-scan-step).
(defconst *fn-asto-quantum* 16384)

(defun fn-asto-quantum (override)
  (declare (xargs :guard t))
  (if (posp override) override *fn-asto-quantum*))

(defthm fn-asto-quantum-posp
  (posp (fn-asto-quantum override))
  :rule-classes (:rewrite :type-prescription))

; One ARTICLE quantum: the window's octets are fn-dss-out's [0, len) after the
; call (the host sends exactly those; their lifetime from here to the socket
; write is the host's, books/article-stream.lisp fn-ast-render-window).
(defun fn-asto-plan-render-window (plan window fn-arena fn-ast-ws fn-dss-out)
  (declare (xargs :stobjs (fn-arena fn-ast-ws fn-dss-out)
                  :guard (fn-asto-cursor-effectsp (fn-splan-rest plan) fn-arena)
                  :guard-hints (("Goal" :in-theory (disable fn-ast-render-window fn-ast-window-donep
                                                            fn-ast-windowp fn-splan-rest-donep)))))
  (let ((rest (fn-splan-rest plan)))
    (if (and (not (consp (fn-splan-cur plan))) (eq (caar rest) :article-cursor))
        (mv-let (next fn-ast-ws fn-dss-out)
          (fn-ast-render-window (cadar rest) (nfix window) (nfix window) fn-arena fn-ast-ws fn-dss-out)
          (let ((done (fn-ast-window-donep next)))
            (mv :article
                (cons nil (if done (cdr rest) (cons (list :article-cursor next) (cdr rest))))
                (and done (fn-splan-rest-donep (cdr rest)))
                fn-ast-ws fn-dss-out)))
      (mv :ordinary plan nil fn-ast-ws fn-dss-out))))

(defthm fn-asto-plan-render-window-keeps-cursor-effectsp
  (implies (fn-asto-cursor-effectsp (fn-splan-rest plan) fn-arena)
           (fn-asto-cursor-effectsp
            (fn-splan-rest (mv-nth 1 (fn-asto-plan-render-window plan window fn-arena fn-ast-ws fn-dss-out)))
            fn-arena))
  :hints (("Goal" :in-theory (e/d (fn-asto-plan-render-window fn-asto-cursor-effectsp fn-splan-rest)
                                  (fn-ast-render-window fn-ast-window-donep fn-ast-windowp fn-splan-rest-donep))
                  :use ((:instance fn-ast-render-window-keeps-windowp
                          (window (car (cdr (car (fn-splan-rest plan)))))
                          (fuel (nfix window)) (octets (nfix window)))))))

; -----------------------------------------------------------------------------
; A retrieval whose preflight did not get its payload in time (C3: the
; dependency deadline passed, `read-dependency-ms'; or the cold pool refused
; the read by name, P12) is answered with ONE reply LINE in the preflight's
; place: the 403 of books/owner-cold-line.lisp and books/owner-resource-line.lisp
; (RFC 3977 section 3.2.1: temporarily unavailable, never 430 or 423).  The
; preflight comes before every octet of its plan (fn-asto-ready-rest resolves
; it before the host renders a window), and fn-asto-finish -- the only step
; that commits the reader's selection -- never ran, so nothing of the
; response was published and the connection's session is the one the capture
; installed: the article is not selected and the current number is unchanged.
; The effects before and after the preflight are the plan's own, untouched.
; A plan with no preflight is not this function's (NIL): a render that went
; cold after its first window was written has no reply to replace.

(defun fn-asto-preflight-entryp (e)
  (declare (xargs :guard t))
  (eq (fn-cbor-ag-car e) :article-preflight))

(in-theory (disable fn-asto-preflight-entryp))

(defun fn-asto-unavailable-rest (rest line)
  (declare (xargs :guard t))
  (if (atom rest) rest
    (if (fn-asto-preflight-entryp (car rest))
        (cons (fn-nntp-reply-effect line) (cdr rest))
      (cons (car rest) (fn-asto-unavailable-rest (cdr rest) line)))))

(defun fn-asto-plan-unavailable (plan line)
  (declare (xargs :guard t))
  (if (fn-asto-preflight-planp plan)
      (cons (fn-splan-cur plan) (fn-asto-unavailable-rest (fn-splan-rest plan) line))
    nil))

; The split of a rest at its first preflight: the entries before it, the
; entry, the entries after it.
(defun fn-asto-preflight-prefix (rest)
  (declare (xargs :guard t))
  (if (or (atom rest) (fn-asto-preflight-entryp (car rest))) nil
    (cons (car rest) (fn-asto-preflight-prefix (cdr rest)))))

(defun fn-asto-preflight-entry (rest)
  (declare (xargs :guard t))
  (if (atom rest) nil
    (if (fn-asto-preflight-entryp (car rest)) (car rest)
      (fn-asto-preflight-entry (cdr rest)))))

(defun fn-asto-preflight-suffix (rest)
  (declare (xargs :guard t))
  (if (atom rest) nil
    (if (fn-asto-preflight-entryp (car rest)) (cdr rest)
      (fn-asto-preflight-suffix (cdr rest)))))

(local
 (defthm fn-asto-preflight-split-of-a-preflight-rest
   (implies (fn-asto-preflight-restp rest)
            (and (equal (append (fn-asto-preflight-prefix rest)
                                (cons (fn-asto-preflight-entry rest)
                                      (fn-asto-preflight-suffix rest)))
                        rest)
                 (equal (fn-asto-unavailable-rest rest line)
                        (append (fn-asto-preflight-prefix rest)
                                (cons (fn-nntp-reply-effect line)
                                      (fn-asto-preflight-suffix rest))))
                 (fn-asto-preflight-entryp (fn-asto-preflight-entry rest))
                 (not (fn-asto-preflight-restp (fn-asto-preflight-prefix rest)))))
   :hints (("Goal" :induct (fn-asto-preflight-prefix rest)
            :in-theory (enable fn-asto-preflight-entryp fn-asto-preflight-restp)))))

; KEYSTONE (C3 / PRF-933 for a retrieval's preflight).  For a plan whose
; rest holds a preflight, the unavailable plan keeps the plan's current
; window, every entry before the first preflight and every entry after it,
; and puts exactly one reply of LINE in that preflight's place; the
; preflight it replaced is the first one (none precedes it).
(defthm fn-asto-an-unavailable-preflight-is-answered-in-its-place
  (implies (fn-asto-preflight-planp plan)
           (let ((p (fn-asto-plan-unavailable plan line))
                 (rest (fn-splan-rest plan)))
             (and (consp p)
                  (equal (fn-splan-cur p) (fn-splan-cur plan))
                  (equal rest (append (fn-asto-preflight-prefix rest)
                                      (cons (fn-asto-preflight-entry rest)
                                            (fn-asto-preflight-suffix rest))))
                  (fn-asto-preflight-entryp (fn-asto-preflight-entry rest))
                  (not (fn-asto-preflight-restp (fn-asto-preflight-prefix rest)))
                  (equal (fn-splan-rest p)
                         (append (fn-asto-preflight-prefix rest)
                                 (cons (fn-nntp-reply-effect line)
                                       (fn-asto-preflight-suffix rest)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-asto-plan-unavailable fn-asto-preflight-planp
                                     fn-splan-cur fn-splan-rest))))

; Only a plan with a preflight is answered so; every other plan is NIL.
(defthm fn-asto-plan-unavailable-without-a-preflight-by-definition
  (implies (not (fn-asto-preflight-planp plan))
           (equal (fn-asto-plan-unavailable plan line) nil)))

(in-theory (disable fn-asto-plan-unavailable fn-asto-unavailable-rest
                    fn-asto-preflight-prefix fn-asto-preflight-entry
                    fn-asto-preflight-suffix))
