; Literal READ witnesses: each complete retained antecedent and conclusion.
; Bounds derived by the final theorem are not separate hypotheses.
; Funding removals use a reader-reachable owner paired with an empty ledger:
; these are corrupted-credit-state witnesses, not complete native traces.
(in-package "ACL2")

(include-book "../../books/productive-read-chain")

(include-book "../../books/owner-agent")

(defconst
  *pcrt-payload*
  (append
    (fn-nntp-string-octets "From: a@x")
    (quote (13 10))
    (fn-nntp-string-octets "Newsgroups: fn.test")
    (quote (13 10))
    (fn-nntp-string-octets "Subject: productive read")
    (quote (13 10))
    (fn-nntp-string-octets "Date: Mon, 21 Sep 2026 12:00:00 +0000")
    (quote (13 10))
    (fn-nntp-string-octets "Message-ID: <pcrt@x>")
    (quote (13 10 13 10))
    (fn-nntp-string-octets ".productive")
    (quote (13 10))))

(defconst
  *pcrt-record*
  (fn-held-make
    0
    1
    1
    "<pcrt@x>"
    0
    (quote ("fn.test"))
    "o"
    "s"
    "e"
    1
    5
    (fn-held-facts-of *pcrt-payload*)
    (fn-held-context-of *pcrt-payload* nil 0)
    nil
    nil))

(defconst
  *pcrt-open*
  (fn-cpo-open-observed (list *fn-cfg-default-record*) 2 (list *pcrt-record*)))

(defconst
  *pcrt-ready*
  (fn-sn-io
    (fn-sn-io
      (fn-sn-io (fn-sn-open-state *pcrt-open*) :recovery-barrier :ok)
      :recovery-barrier
      :ok)
    :recovery-barrier
    :ok))

(defconst
  *pcrt-cfg*
  (fn-cnode-config
    (fn-replay-result-node (fn-cpr-replay (list *fn-cfg-default-record*) (list *pcrt-record*)))))

(defconst
  *pcrt-oc*
  (cdr
    (fn-ocfg-open
      (fn-ocfg-make
        (fn-own-configure (fn-own-start *pcrt-ready* 4) (fn-oag-post-config *pcrt-cfg* 32768))
        *pcrt-cfg*
        nil
        nil)
      nil)))

(defun
  pcrt-group-in
  (oc fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let
    ((fn-arena (fn-arena-seal-list *pcrt-payload* fn-arena)))
    (mv
      (fn-ocfg-read
        oc
        0
        (append (fn-nntp-string-octets "GROUP fn.test") (quote (13 10)))
        fn-arena)
      fn-arena)))

(defun
  pcrt-group
  (oc)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena (mv-let (r fn-arena) (pcrt-group-in oc fn-arena) r)))

(defconst *pcrt-selected* (cdr (pcrt-group *pcrt-oc*)))

(defconst *pcrt-cat* (list (fn-cat-assign *pcrt-record* nil)))

(defconst *pcrt-line* (fn-nntp-string-octets "ARTICLE 1"))

(defconst *pcrt-line-bytes* (append *pcrt-line* (quote (13 10))))

(defconst *pcrt-credits* (fn-mcr-make 1000000 0 0 0 0 0 nil))

(assert-event (and (equal (fn-sn-open-kind *pcrt-open*) :ok) (fn-ocl-relation *pcrt-selected*)))

(defun
  pcrt-post-in
  (oc fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let
    ((fn-arena (fn-arena-seal-list *pcrt-payload* fn-arena)))
    (mv
      (fn-ocfg-read
        oc
        0
        (append
          (fn-nntp-string-octets "POST")
          (quote (13 10))
          (fn-nntp-string-octets "From: a@x")
          (quote (13 10))
          (fn-nntp-string-octets "Newsgroups: fn.test")
          (quote (13 10))
          (fn-nntp-string-octets "Subject: queued read")
          (quote (13 10))
          (fn-nntp-string-octets "Date: Mon, 21 Sep 2026 12:00:00 +0000")
          (quote (13 10))
          (fn-nntp-string-octets "Message-ID: <pcrtqueued@x>")
          (quote (13 10 13 10))
          (fn-nntp-string-octets "queued")
          (quote (13 10 46 13 10)))
        fn-arena)
      fn-arena)))

(defun
  pcrt-post
  (oc)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena (mv-let (r fn-arena) (pcrt-post-in oc fn-arena) r)))

(defconst
  *pcrt-clocked-selected*
  (fn-ocfg-make
    (fn-own-observe (fn-ocfg-owner *pcrt-selected*) (fn-clock-observation 1000 1790000000000 0 t))
    (fn-ocfg-config *pcrt-selected*)
    (fn-ocfg-pins *pcrt-selected*)
    (fn-ocfg-staged *pcrt-selected*)))

(defconst *pcrt-clocked-queued-selected* (cdr (pcrt-post *pcrt-clocked-selected*)))

(defthm
  pcrt-complete-numbered-positive
  (let*
    ((o (fn-ocfg-owner *pcrt-selected*))
      (conn (fn-own-find-conn 0 (fn-own-conns o)))
      (sc (fn-own-tls-served-conn o conn))
      (as (fn-served-conn-session sc))
      (config (fn-served-conn-config sc))
      (archive (fn-served-conn-archive sc))
      (index (fn-served-conn-pinned-index sc))
      (observation (fn-served-conn-observation sc))
      (peer (fn-auth-view-session as config))
      (viewarchive (fn-auth-view-archive as config archive))
      (viewindex (fn-auth-view-index as config archive index))
      (viewconfig (fn-auth-view-config as (fn-auth-moderation-config as config) archive))
      (ps (fn-peer-session-base peer))
      (session (fn-post-session-base ps))
      (env (fn-post-reader-env viewconfig observation))
      (group (fn-nntp-session-group session))
      (number (fn-nntp-decimal-value (quote (49))))
      (article (fn-nntp-find-group-number group number (fn-state-articles viewarchive)))
      (server (fn-nntp-xref-server env))
      (r (fn-pcr-220-reply session article number group server (list *pcrt-payload*)))
      (p
        (car
          (fn-mca-read-span
            *pcrt-credits*
            *pcrt-selected*
            nil
            0
            0
            (len *pcrt-line-bytes*)
            nil
            (fn-otm-init)
            32
            107552
            *pcrt-line-bytes*
            (list *pcrt-payload*)
            *pcrt-cat*))))
    (and
      (and
        (equal
          (car
            (fn-mcr-resize
              *pcrt-credits*
              (fn-mca-conn-key 0)
              (fn-mca-need
                (fn-own-tls-result-owner
                  (fn-oas-read-span
                    *pcrt-selected*
                    nil
                    0
                    0
                    (len *pcrt-line-bytes*)
                    nil
                    (fn-otm-init)
                    32
                    *pcrt-line-bytes*
                    (list *pcrt-payload*)
                    *pcrt-cat*))
                0
                107552)))
          :ok)
        (not
          (fn-oas-over-p
            *pcrt-selected*
            (fn-own-tls-result-owner
              (fn-otm-read-span
                *pcrt-selected*
                nil
                0
                0
                (len *pcrt-line-bytes*)
                nil
                (fn-otm-init)
                *pcrt-line-bytes*
                (list *pcrt-payload*)
                *pcrt-cat*))
            0
            32))
        (not (eq (fn-otm-admit-post (fn-otm-init)) :shed))
        (not (consp nil))
        (fn-gacc-okp nil)
        (fn-ocl-relation *pcrt-selected*)
        (fn-scar-view-indexedp (fn-ocfg-owner *pcrt-selected*))
        (fn-scr-owner-catalogp (fn-ocfg-owner *pcrt-selected*) 0 (list *pcrt-payload*) *pcrt-cat*)
        (fn-scol-okp (list *pcrt-payload*) *pcrt-cat*)
        conn
        t
        (equal
          (fn-oct-slice-list 0 (len *pcrt-line-bytes*) *pcrt-line-bytes*)
          (append *pcrt-line* (quote (13 10))))
        (equal
          (fn-served-conn-wire sc)
          (fn-wire-make-state
            :command
            nil
            0
            nil
            nil
            0
            (fn-wire-state-line-limit
              (fn-own-conn-wire
                (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*)))))
            (fn-wire-state-body-limit
              (fn-own-conn-wire
                (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*)))))))
        (fn-wire-statep (fn-served-conn-wire sc))
        (<=
          (len *pcrt-line*)
          (fn-wire-state-line-limit
            (fn-own-conn-wire (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*))))))
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
        (fn-nntp-command-inputp *pcrt-line*)
        (equal (fn-nntp-tokenize *pcrt-line*) (list *fn-pcr-article-keyword* (quote (49))))
        (fn-nntp-number-tokenp (quote (49)))
        group
        (consp article)
        server
        (fn-gidx-pinp viewindex)
        (not (fn-nntp-number-withdrawn-p session viewarchive viewindex (quote (49))))
        (fn-nntp-response-okp-of-bytes
          article
          (fn-nntp-article-bytes article (list *pcrt-payload*))
          :article)
        (fn-nntp-response-okp-of-bytes
          article
          (fn-pcr-served-octets server article (list *pcrt-payload*))
          :article))
      (and
        (equal (fn-otb-dependency-step 0 0 2000 t) :serve)
        (equal (fn-own-tls-result-consumed p) (+ 2 (len *pcrt-line*)))
        (equal (fn-own-tls-result-effects p) (fn-nntp-result-effects r))
        (equal
          (fn-own-tls-result-owner p)
          (cdr
            (fn-ocfg-read
              *pcrt-selected*
              0
              (append *pcrt-line* (quote (13 10)))
              (list *pcrt-payload*)))))))
  :rule-classes
  nil
  :hints
  (("Goal"
     :in-theory
     (enable
       fn-scr-owner-catalogp
       fn-scr-conn-okp
       fn-scr-conn-catalogp
       fn-scr-fields-catalogp
       fn-scr-live-catalogp
       fn-scr-catalogp
       fn-scol-okp))))

(defthm
  pcrt-without-funding
  (let*
    ((o (fn-ocfg-owner *pcrt-clocked-queued-selected*))
      (conn (fn-own-find-conn 0 (fn-own-conns o)))
      (sc (fn-own-tls-served-conn o conn))
      (as (fn-served-conn-session sc))
      (config (fn-served-conn-config sc))
      (archive (fn-served-conn-archive sc))
      (index (fn-served-conn-pinned-index sc))
      (observation (fn-served-conn-observation sc))
      (peer (fn-auth-view-session as config))
      (viewarchive (fn-auth-view-archive as config archive))
      (viewindex (fn-auth-view-index as config archive index))
      (viewconfig (fn-auth-view-config as (fn-auth-moderation-config as config) archive))
      (ps (fn-peer-session-base peer))
      (session (fn-post-session-base ps))
      (env (fn-post-reader-env viewconfig observation))
      (group (fn-nntp-session-group session))
      (number (fn-nntp-decimal-value (quote (49))))
      (article (fn-nntp-find-group-number group number (fn-state-articles viewarchive)))
      (server (fn-nntp-xref-server env))
      (r (fn-pcr-220-reply session article number group server (list *pcrt-payload*)))
      (p
        (car
          (fn-mca-read-span
            (fn-mcr-make 0 0 0 0 0 0 nil)
            *pcrt-clocked-queued-selected*
            nil
            0
            0
            (len *pcrt-line-bytes*)
            nil
            (fn-otm-init)
            32
            107552
            *pcrt-line-bytes*
            (list *pcrt-payload*)
            *pcrt-cat*))))
    (and
      (and
        (not
          (fn-oas-over-p
            *pcrt-clocked-queued-selected*
            (fn-own-tls-result-owner
              (fn-otm-read-span
                *pcrt-clocked-queued-selected*
                nil
                0
                0
                (len *pcrt-line-bytes*)
                nil
                (fn-otm-init)
                *pcrt-line-bytes*
                (list *pcrt-payload*)
                *pcrt-cat*))
            0
            32))
        (not (eq (fn-otm-admit-post (fn-otm-init)) :shed))
        (not (consp nil))
        (fn-gacc-okp nil)
        (fn-ocl-relation *pcrt-clocked-queued-selected*)
        (fn-scar-view-indexedp (fn-ocfg-owner *pcrt-clocked-queued-selected*))
        (fn-scr-owner-catalogp
          (fn-ocfg-owner *pcrt-clocked-queued-selected*)
          0
          (list *pcrt-payload*)
          *pcrt-cat*)
        (fn-scol-okp (list *pcrt-payload*) *pcrt-cat*)
        conn
        t
        (equal
          (fn-oct-slice-list 0 (len *pcrt-line-bytes*) *pcrt-line-bytes*)
          (append *pcrt-line* (quote (13 10))))
        (equal
          (fn-served-conn-wire sc)
          (fn-wire-make-state
            :command
            nil
            0
            nil
            nil
            0
            (fn-wire-state-line-limit
              (fn-own-conn-wire
                (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-clocked-queued-selected*)))))
            (fn-wire-state-body-limit
              (fn-own-conn-wire
                (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-clocked-queued-selected*)))))))
        (fn-wire-statep (fn-served-conn-wire sc))
        (<=
          (len *pcrt-line*)
          (fn-wire-state-line-limit
            (fn-own-conn-wire
              (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-clocked-queued-selected*))))))
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
        (fn-nntp-command-inputp *pcrt-line*)
        (equal (fn-nntp-tokenize *pcrt-line*) (list *fn-pcr-article-keyword* (quote (49))))
        (fn-nntp-number-tokenp (quote (49)))
        group
        (consp article)
        server
        (fn-gidx-pinp viewindex)
        (not (fn-nntp-number-withdrawn-p session viewarchive viewindex (quote (49))))
        (fn-nntp-response-okp-of-bytes
          article
          (fn-nntp-article-bytes article (list *pcrt-payload*))
          :article)
        (fn-nntp-response-okp-of-bytes
          article
          (fn-pcr-served-octets server article (list *pcrt-payload*))
          :article))
      (not
        (equal
          (car
            (fn-mcr-resize
              (fn-mcr-make 0 0 0 0 0 0 nil)
              (fn-mca-conn-key 0)
              (fn-mca-need
                (fn-own-tls-result-owner
                  (fn-oas-read-span
                    *pcrt-clocked-queued-selected*
                    nil
                    0
                    0
                    (len *pcrt-line-bytes*)
                    nil
                    (fn-otm-init)
                    32
                    *pcrt-line-bytes*
                    (list *pcrt-payload*)
                    *pcrt-cat*))
                0
                107552)))
          :ok))
      (not
        (and
          (equal (fn-otb-dependency-step 0 0 2000 t) :serve)
          (equal (fn-own-tls-result-consumed p) (+ 2 (len *pcrt-line*)))
          (equal (fn-own-tls-result-effects p) (fn-nntp-result-effects r))
          (equal
            (fn-own-tls-result-owner p)
            (cdr
              (fn-ocfg-read
                *pcrt-clocked-queued-selected*
                0
                (append *pcrt-line* (quote (13 10)))
                (list *pcrt-payload*))))))))
  :rule-classes
  nil
  :hints
  (("Goal"
     :in-theory
     (enable
       fn-scr-owner-catalogp
       fn-scr-conn-okp
       fn-scr-conn-catalogp
       fn-scr-fields-catalogp
       fn-scr-live-catalogp
       fn-scr-catalogp
       fn-scol-okp))))

(defthm
  pcrt-without-completion
  (let*
    ((o (fn-ocfg-owner *pcrt-selected*))
      (conn (fn-own-find-conn 0 (fn-own-conns o)))
      (sc (fn-own-tls-served-conn o conn))
      (as (fn-served-conn-session sc))
      (config (fn-served-conn-config sc))
      (archive (fn-served-conn-archive sc))
      (index (fn-served-conn-pinned-index sc))
      (observation (fn-served-conn-observation sc))
      (peer (fn-auth-view-session as config))
      (viewarchive (fn-auth-view-archive as config archive))
      (viewindex (fn-auth-view-index as config archive index))
      (viewconfig (fn-auth-view-config as (fn-auth-moderation-config as config) archive))
      (ps (fn-peer-session-base peer))
      (session (fn-post-session-base ps))
      (env (fn-post-reader-env viewconfig observation))
      (group (fn-nntp-session-group session))
      (number (fn-nntp-decimal-value (quote (49))))
      (article (fn-nntp-find-group-number group number (fn-state-articles viewarchive)))
      (server (fn-nntp-xref-server env))
      (r (fn-pcr-220-reply session article number group server (list *pcrt-payload*)))
      (p
        (car
          (fn-mca-read-span
            *pcrt-credits*
            *pcrt-selected*
            nil
            0
            0
            (len *pcrt-line-bytes*)
            nil
            (fn-otm-init)
            32
            107552
            *pcrt-line-bytes*
            (list *pcrt-payload*)
            *pcrt-cat*))))
    (and
      (and
        (equal
          (car
            (fn-mcr-resize
              *pcrt-credits*
              (fn-mca-conn-key 0)
              (fn-mca-need
                (fn-own-tls-result-owner
                  (fn-oas-read-span
                    *pcrt-selected*
                    nil
                    0
                    0
                    (len *pcrt-line-bytes*)
                    nil
                    (fn-otm-init)
                    32
                    *pcrt-line-bytes*
                    (list *pcrt-payload*)
                    *pcrt-cat*))
                0
                107552)))
          :ok)
        (not
          (fn-oas-over-p
            *pcrt-selected*
            (fn-own-tls-result-owner
              (fn-otm-read-span
                *pcrt-selected*
                nil
                0
                0
                (len *pcrt-line-bytes*)
                nil
                (fn-otm-init)
                *pcrt-line-bytes*
                (list *pcrt-payload*)
                *pcrt-cat*))
            0
            32))
        (not (eq (fn-otm-admit-post (fn-otm-init)) :shed))
        (not (consp nil))
        (fn-gacc-okp nil)
        (fn-ocl-relation *pcrt-selected*)
        (fn-scar-view-indexedp (fn-ocfg-owner *pcrt-selected*))
        (fn-scr-owner-catalogp (fn-ocfg-owner *pcrt-selected*) 0 (list *pcrt-payload*) *pcrt-cat*)
        (fn-scol-okp (list *pcrt-payload*) *pcrt-cat*)
        conn
        (equal
          (fn-oct-slice-list 0 (len *pcrt-line-bytes*) *pcrt-line-bytes*)
          (append *pcrt-line* (quote (13 10))))
        (equal
          (fn-served-conn-wire sc)
          (fn-wire-make-state
            :command
            nil
            0
            nil
            nil
            0
            (fn-wire-state-line-limit
              (fn-own-conn-wire
                (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*)))))
            (fn-wire-state-body-limit
              (fn-own-conn-wire
                (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*)))))))
        (fn-wire-statep (fn-served-conn-wire sc))
        (<=
          (len *pcrt-line*)
          (fn-wire-state-line-limit
            (fn-own-conn-wire (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*))))))
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
        (fn-nntp-command-inputp *pcrt-line*)
        (equal (fn-nntp-tokenize *pcrt-line*) (list *fn-pcr-article-keyword* (quote (49))))
        (fn-nntp-number-tokenp (quote (49)))
        group
        (consp article)
        server
        (fn-gidx-pinp viewindex)
        (not (fn-nntp-number-withdrawn-p session viewarchive viewindex (quote (49))))
        (fn-nntp-response-okp-of-bytes
          article
          (fn-nntp-article-bytes article (list *pcrt-payload*))
          :article)
        (fn-nntp-response-okp-of-bytes
          article
          (fn-pcr-served-octets server article (list *pcrt-payload*))
          :article))
      (not nil)
      (not
        (and
          (equal (fn-otb-dependency-step 0 0 2000 nil) :serve)
          (equal (fn-own-tls-result-consumed p) (+ 2 (len *pcrt-line*)))
          (equal (fn-own-tls-result-effects p) (fn-nntp-result-effects r))
          (equal
            (fn-own-tls-result-owner p)
            (cdr
              (fn-ocfg-read
                *pcrt-selected*
                0
                (append *pcrt-line* (quote (13 10)))
                (list *pcrt-payload*))))))))
  :rule-classes
  nil
  :hints
  (("Goal"
     :in-theory
     (enable
       fn-scr-owner-catalogp
       fn-scr-conn-okp
       fn-scr-conn-catalogp
       fn-scr-fields-catalogp
       fn-scr-live-catalogp
       fn-scr-catalogp
       fn-scol-okp))))

(defthm
  pcrt-number-without-command-slice
  (let*
    ((o (fn-ocfg-owner *pcrt-selected*))
      (conn (fn-own-find-conn 0 (fn-own-conns o)))
      (sc (fn-own-tls-served-conn o conn))
      (as (fn-served-conn-session sc))
      (config (fn-served-conn-config sc))
      (archive (fn-served-conn-archive sc))
      (index (fn-served-conn-pinned-index sc))
      (observation (fn-served-conn-observation sc))
      (peer (fn-auth-view-session as config))
      (viewarchive (fn-auth-view-archive as config archive))
      (viewindex (fn-auth-view-index as config archive index))
      (viewconfig (fn-auth-view-config as (fn-auth-moderation-config as config) archive))
      (ps (fn-peer-session-base peer))
      (session (fn-post-session-base ps))
      (env (fn-post-reader-env viewconfig observation))
      (group (fn-nntp-session-group session))
      (number (fn-nntp-decimal-value (fn-nntp-string-octets "1")))
      (article (fn-nntp-find-group-number group number (fn-state-articles viewarchive)))
      (server (fn-nntp-xref-server env))
      (r (fn-pcr-220-reply session article number group server (list *pcrt-payload*)))
      (p
        (car
          (fn-mca-read-span
            *pcrt-credits*
            *pcrt-selected*
            nil
            0
            0
            0
            nil
            (fn-otm-init)
            32
            107552
            nil
            (list *pcrt-payload*)
            *pcrt-cat*))))
    (and
      (and
        (equal
          (car
            (fn-mcr-resize
              *pcrt-credits*
              (fn-mca-conn-key 0)
              (fn-mca-need
                (fn-own-tls-result-owner
                  (fn-oas-read-span
                    *pcrt-selected*
                    nil
                    0
                    0
                    0
                    nil
                    (fn-otm-init)
                    32
                    nil
                    (list *pcrt-payload*)
                    *pcrt-cat*))
                0
                107552)))
          :ok)
        (not
          (fn-oas-over-p
            *pcrt-selected*
            (fn-own-tls-result-owner
              (fn-otm-read-span
                *pcrt-selected*
                nil
                0
                0
                0
                nil
                (fn-otm-init)
                nil
                (list *pcrt-payload*)
                *pcrt-cat*))
            0
            32))
        (not (eq (fn-otm-admit-post (fn-otm-init)) :shed))
        (not (consp nil))
        (fn-gacc-okp nil)
        (fn-ocl-relation *pcrt-selected*)
        (fn-scar-view-indexedp (fn-ocfg-owner *pcrt-selected*))
        (fn-scr-owner-catalogp (fn-ocfg-owner *pcrt-selected*) 0 (list *pcrt-payload*) *pcrt-cat*)
        (fn-scol-okp (list *pcrt-payload*) *pcrt-cat*)
        conn
        t
        (equal
          (fn-served-conn-wire sc)
          (fn-wire-make-state
            :command
            nil
            0
            nil
            nil
            0
            (fn-wire-state-line-limit
              (fn-own-conn-wire
                (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*)))))
            (fn-wire-state-body-limit
              (fn-own-conn-wire
                (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*)))))))
        (fn-wire-statep (fn-served-conn-wire sc))
        (<=
          (len (fn-nntp-string-octets "ARTICLE 1"))
          (fn-wire-state-line-limit
            (fn-own-conn-wire (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*))))))
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
        (fn-nntp-command-inputp (fn-nntp-string-octets "ARTICLE 1"))
        (equal
          (fn-nntp-tokenize (fn-nntp-string-octets "ARTICLE 1"))
          (list *fn-pcr-article-keyword* (fn-nntp-string-octets "1")))
        (fn-nntp-number-tokenp (fn-nntp-string-octets "1"))
        group
        (consp article)
        server
        (fn-gidx-pinp viewindex)
        (not
          (fn-nntp-number-withdrawn-p session viewarchive viewindex (fn-nntp-string-octets "1")))
        (fn-nntp-response-okp-of-bytes
          article
          (fn-nntp-article-bytes article (list *pcrt-payload*))
          :article)
        (fn-nntp-response-okp-of-bytes
          article
          (fn-pcr-served-octets server article (list *pcrt-payload*))
          :article))
      (not
        (equal
          (fn-oct-slice-list 0 0 nil)
          (append (fn-nntp-string-octets "ARTICLE 1") (quote (13 10)))))
      (not
        (and
          (equal (fn-otb-dependency-step 0 0 2000 t) :serve)
          (equal (fn-own-tls-result-consumed p) (+ 2 (len (fn-nntp-string-octets "ARTICLE 1"))))
          (equal (fn-own-tls-result-effects p) (fn-nntp-result-effects r))
          (equal
            (fn-own-tls-result-owner p)
            (cdr
              (fn-ocfg-read
                *pcrt-selected*
                0
                (append (fn-nntp-string-octets "ARTICLE 1") (quote (13 10)))
                (list *pcrt-payload*))))))))
  :rule-classes
  nil
  :hints
  (("Goal"
     :in-theory
     (enable
       fn-scr-owner-catalogp
       fn-scr-conn-okp
       fn-scr-conn-catalogp
       fn-scr-fields-catalogp
       fn-scr-live-catalogp
       fn-scr-catalogp
       fn-scol-okp))))
