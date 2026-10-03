; The actual request factory's retained ARTICLE request. Parsing, selection,
; privacy, framing and selected-session commit remain ACL2 decisions.
(in-package "ACL2")
(include-book "article-stream")
(include-book "article-stream-server")
(include-book "owner-credits")
(include-book "served-plan")
(include-book "served-query-plan")

(defun fn-asto-with-wire-session (conn wire session)
  (declare (xargs :guard t))
  (fn-own-conn-make-group-indexed
   (fn-own-conn-id conn) (fn-own-conn-version conn) (fn-own-conn-frontier conn)
   wire session (fn-own-conn-archive conn) (fn-own-conn-config conn)
   (fn-own-conn-observation conn) (fn-own-conn-verdicts conn)
   (fn-own-conn-index conn) (fn-own-conn-group-index conn) (fn-own-conn-control conn)))

(defun fn-asto-with-conn (oc conn)
  (declare (xargs :guard t))
  (let ((o (fn-ocfg-owner oc)))
    (fn-ocfg-with-owner oc
      (fn-own-set-conns o (fn-own-replace-conn conn (fn-own-conns o))))))

; A selection is (article number updatep group). Missing/syntax/gated arms
; return NIL and run the existing dispatcher over just this parsed event.
(defun fn-asto-selection (session archive index args)
  (declare (xargs :guard t :verify-guards nil))
  (let ((group (fn-nntp-session-group session)))
    (cond
     ((null args)
      (let* ((number (fn-nntp-session-current session))
             (article (and group number
                       (fn-nntp-available-article group number (fn-state-articles archive)))))
        (and article (list article number t group))))
     ((and (consp args) (null (cdr args)))
      (let ((token (car args)))
        (cond
         ((fn-nntp-number-tokenp token)
          (let* ((number (fn-nntp-decimal-value token))
                 (article (and group (fn-nntp-find-group-number group number
                                                (fn-state-articles archive)))))
            (and article (list article number t group))))
         ((and (fn-nntp-message-id-tokenp token) (fn-octet-listp token))
          (let ((article (if (fn-gidx-pinp index)
                             (fn-midx-lookup (fn-nntp-token-string token) (fn-gidx-pin-trie index))
                           (fn-find-article (fn-nntp-token-string token)
                                            (fn-state-articles archive)))))
            (and article (list article (fn-nntp-msgid-local-number session article) nil nil))))
         (t nil))))
     (t nil))))

(defun fn-asto-selection-start (session archive index args)
  (declare (xargs :verify-guards nil))
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
            (let ((article (fn-midx-lookup key (fn-gidx-pin-trie index))))
              (if (consp article) (fn-ast-msgid-local-start group article)
                (fn-ast-select-state :msgid group key nil nil nil nil 0 :missing)))
          (fn-ast-select-state :msgid group key (fn-state-articles archive)
                               nil nil nil 0 :msgid-next))))
     (t nil))))

; Capture = (expected-conn auth-view-peer selection kind server scan
;            connection-configuration-pin withdrawn-articles). EXPECTED-CONN includes the installed
; post-command wire but its reader selection is unchanged until preflight.
(defun fn-asto-payload-preflight (article fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let ((source (fn-ast-source article fn-arena)))
    (if (or (not (fn-nntp-article-idp article))
            (fn-nntp-article-tombstonep article fn-arena))
        (fn-ast-refused-preflight source)
      (fn-ast-preflight source))))

(defun fn-asto-capture (oc id w cache fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let* ((o (fn-ocfg-owner oc)) (conn (fn-own-find-conn id (fn-own-conns o)))
         (sc (and conn (fn-own-tls-served-conn o conn)))
         (as (fn-served-conn-session sc)) (config (fn-served-conn-config sc))
         (events (fn-wsp-events w)) (event (car events))
         (tokens (and (equal (car event) :command)
                       (fn-nntp-tokenize (cadr event))))
         (keyword (car tokens))
         (kind (cond ((fn-nntp-keywordp keyword "ARTICLE") :article)
                     ((fn-nntp-keywordp keyword "HEAD") :head)
                     ((fn-nntp-keywordp keyword "BODY") :body)
                     (t nil))))
    (if (not (and conn kind (null (cdr events))
                  (fn-nntp-command-inputp (cadr event))
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
             (selection (fn-asto-selection-start (fn-peer-reader-session ps) va vi (cdr tokens))))
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
(defun fn-asto-first-event (oc id start end fn-octets)
  (declare (xargs :stobjs fn-octets :verify-guards nil))
  (let ((conn (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))))
    (and conn (fn-wire-fast-statep (fn-own-conn-wire conn))
         (fn-wire-scan (fn-own-conn-wire conn) start end fn-octets))))

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
  (declare (xargs :verify-guards nil))
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

(defun fn-asto-selection-ready (oc capture fuel fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let ((next (fn-ast-select-step (fn-ast-at 2 capture) (nfix fuel))))
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
                          (fn-asto-capture-with-selection capture next nil))))))))

; Finish decides both the session and READY plan. No host parser, reply line,
; or framing verdict participates. The connection/configuration comparison
; fences stale captures; replaying READY has no call site for this function.
(defun fn-asto-finish (oc capture fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
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

(defun fn-asto-ready-rest (oc id rest fuel fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (if (atom rest) (mv :ready oc rest)
    (if (eq (caar rest) :article-preflight)
        (let ((capture (cadar rest)))
          (if (eq (fn-ast-at 0 (fn-ast-at 2 capture)) :article-select)
              (if (not (equal id (fn-own-conn-id (fn-ast-at 0 capture))))
                  (mv :stale oc rest)
                (mv-let (word oc2 effects) (fn-asto-selection-ready oc capture fuel fn-arena)
                  (mv word oc2 (append effects (cdr rest)))))
          (mv-let (scan used)
            (fn-ast-scan-step (fn-ast-at 5 capture) (nfix fuel) fn-arena)
            (declare (ignore used))
            (let ((next (fn-asto-capture-with-scan capture scan)))
              (if (not (equal id (fn-own-conn-id (fn-ast-at 0 capture))))
                  (mv :stale oc rest)
                (if (not (fn-ast-scan-donep scan))
                  (mv :yield oc (cons (list :article-preflight next) (cdr rest)))
                (mv-let (word oc2 effects) (fn-asto-finish oc next fn-arena)
                  (mv word oc2 (append effects (cdr rest))))))))))
      (mv-let (word oc2 next) (fn-asto-ready-rest oc id (cdr rest) fuel fn-arena)
        (mv word oc2 (cons (car rest) next))))))

(defun fn-asto-ready-plan-step (oc id plan fuel fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (word oc2 rest) (fn-asto-ready-rest oc id (fn-splan-rest plan) fuel fn-arena)
    (mv word oc2 (cons (fn-splan-cur plan) rest))))

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

(defun fn-asto-plan-render-step (plan fuel fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let ((rest (fn-splan-rest plan)))
    (if (and (not (consp (fn-splan-cur plan))) (eq (caar rest) :article-cursor))
        (mv-let (bytes next used)
          (fn-ast-render-step (cadar rest) (nfix fuel) fn-arena)
          (declare (ignore used))
          (let ((done (eq (car next) :done)))
            (mv :article bytes
                (cons nil (if done (cdr rest) (cons (list :article-cursor next) (cdr rest))))
                (and done (fn-splan-rest-donep (cdr rest))))))
      (mv :ordinary nil plan nil))))

(defun fn-asto-plan-render-window (plan window fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let ((rest (fn-splan-rest plan)))
    (if (and (not (consp (fn-splan-cur plan))) (eq (caar rest) :article-cursor))
        (mv-let (bytes next)
          (fn-ast-render-window (cadar rest) (nfix window) (nfix window) fn-arena)
          (let ((done (fn-ast-window-donep next)))
            (mv :article bytes
                (cons nil (if done (cdr rest) (cons (list :article-cursor next) (cdr rest))))
                (and done (fn-splan-rest-donep (cdr rest))))))
      (mv :ordinary nil plan nil))))
