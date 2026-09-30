; Literal READ witnesses: each complete retained antecedent and conclusion.
; Bounds derived by the final theorem are not separate hypotheses.
; Funding removals use a reader-reachable owner paired with an empty ledger:
; these are corrupted-credit-state witnesses, not complete native traces.
(in-package "ACL2")

(include-book "productive-read-chain-tests")

(include-book "../../books/productive-read-absent")

(defthm
  pcra-number-positive
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
      (number (fn-nntp-decimal-value (fn-nntp-string-octets "2")))
      (article
        (if
          (fn-nntp-number-tokenp (fn-nntp-string-octets "2"))
          (fn-nntp-find-group-number group number (fn-state-articles viewarchive))
          (fn-midx-lookup
            (fn-nntp-token-string (fn-nntp-string-octets "2"))
            (fn-gidx-pin-trie viewindex))))
      (server (fn-nntp-xref-server env))
      (r (fn-pcr-absent-reply session (fn-nntp-string-octets "2")))
      (p
        (car
          (fn-mca-read-span
            *pcrt-credits*
            *pcrt-selected*
            nil
            0
            0
            (len (append (fn-nntp-string-octets "ARTICLE 2") (quote (13 10))))
            nil
            (fn-otm-init)
            32
            107552
            (append (fn-nntp-string-octets "ARTICLE 2") (quote (13 10)))
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
                    (len (append (fn-nntp-string-octets "ARTICLE 2") (quote (13 10))))
                    nil
                    (fn-otm-init)
                    32
                    (append (fn-nntp-string-octets "ARTICLE 2") (quote (13 10)))
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
                (len (append (fn-nntp-string-octets "ARTICLE 2") (quote (13 10))))
                nil
                (fn-otm-init)
                (append (fn-nntp-string-octets "ARTICLE 2") (quote (13 10)))
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
          (fn-oct-slice-list
            0
            (len (append (fn-nntp-string-octets "ARTICLE 2") (quote (13 10))))
            (append (fn-nntp-string-octets "ARTICLE 2") (quote (13 10))))
          (append (fn-nntp-string-octets "ARTICLE 2") (quote (13 10))))
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
          (len (fn-nntp-string-octets "ARTICLE 2"))
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
        (fn-nntp-command-inputp (fn-nntp-string-octets "ARTICLE 2"))
        (equal
          (fn-nntp-tokenize (fn-nntp-string-octets "ARTICLE 2"))
          (list *fn-pcr-article-keyword* (fn-nntp-string-octets "2")))
        (or
          (fn-nntp-number-tokenp (fn-nntp-string-octets "2"))
          (and
            (fn-nntp-message-id-tokenp (fn-nntp-string-octets "2"))
            (fn-octet-listp (fn-nntp-string-octets "2"))))
        (or (not (fn-nntp-number-tokenp (fn-nntp-string-octets "2"))) group)
        (not (consp article))
        server
        (fn-gidx-pinp viewindex)
        (and
          (not
            (fn-nntp-number-withdrawn-p session viewarchive viewindex (fn-nntp-string-octets "2")))
          (not
            (and
              (fn-nntp-message-id-tokenp (fn-nntp-string-octets "2"))
              (fn-nntp-msgid-withdrawn-p viewindex (fn-nntp-string-octets "2"))))))
      (and
        (equal (fn-otb-dependency-step 0 0 2000 t) :serve)
        (equal (fn-own-tls-result-consumed p) (+ 2 (len (fn-nntp-string-octets "ARTICLE 2"))))
        (equal (fn-own-tls-result-effects p) (fn-nntp-result-effects r))
        (equal
          (fn-own-tls-result-owner p)
          (cdr
            (fn-ocfg-read
              *pcrt-selected*
              0
              (append (fn-nntp-string-octets "ARTICLE 2") (quote (13 10)))
              (list *pcrt-payload*)))))
      (equal
        (fn-served-reply-octets (fn-own-tls-result-effects p))
        (append (fn-nntp-string-octets "423 no article with that number") (quote (13 10))))))
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
  pcra-number-without-completion
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
      (number (fn-nntp-decimal-value (fn-nntp-string-octets "2")))
      (article
        (if
          (fn-nntp-number-tokenp (fn-nntp-string-octets "2"))
          (fn-nntp-find-group-number group number (fn-state-articles viewarchive))
          (fn-midx-lookup
            (fn-nntp-token-string (fn-nntp-string-octets "2"))
            (fn-gidx-pin-trie viewindex))))
      (server (fn-nntp-xref-server env))
      (r (fn-pcr-absent-reply session (fn-nntp-string-octets "2")))
      (p
        (car
          (fn-mca-read-span
            *pcrt-credits*
            *pcrt-selected*
            nil
            0
            0
            (len (append (fn-nntp-string-octets "ARTICLE 2") (quote (13 10))))
            nil
            (fn-otm-init)
            32
            107552
            (append (fn-nntp-string-octets "ARTICLE 2") (quote (13 10)))
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
                    (len (append (fn-nntp-string-octets "ARTICLE 2") (quote (13 10))))
                    nil
                    (fn-otm-init)
                    32
                    (append (fn-nntp-string-octets "ARTICLE 2") (quote (13 10)))
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
                (len (append (fn-nntp-string-octets "ARTICLE 2") (quote (13 10))))
                nil
                (fn-otm-init)
                (append (fn-nntp-string-octets "ARTICLE 2") (quote (13 10)))
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
          (fn-oct-slice-list
            0
            (len (append (fn-nntp-string-octets "ARTICLE 2") (quote (13 10))))
            (append (fn-nntp-string-octets "ARTICLE 2") (quote (13 10))))
          (append (fn-nntp-string-octets "ARTICLE 2") (quote (13 10))))
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
          (len (fn-nntp-string-octets "ARTICLE 2"))
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
        (fn-nntp-command-inputp (fn-nntp-string-octets "ARTICLE 2"))
        (equal
          (fn-nntp-tokenize (fn-nntp-string-octets "ARTICLE 2"))
          (list *fn-pcr-article-keyword* (fn-nntp-string-octets "2")))
        (or
          (fn-nntp-number-tokenp (fn-nntp-string-octets "2"))
          (and
            (fn-nntp-message-id-tokenp (fn-nntp-string-octets "2"))
            (fn-octet-listp (fn-nntp-string-octets "2"))))
        (or (not (fn-nntp-number-tokenp (fn-nntp-string-octets "2"))) group)
        (not (consp article))
        server
        (fn-gidx-pinp viewindex)
        (and
          (not
            (fn-nntp-number-withdrawn-p session viewarchive viewindex (fn-nntp-string-octets "2")))
          (not
            (and
              (fn-nntp-message-id-tokenp (fn-nntp-string-octets "2"))
              (fn-nntp-msgid-withdrawn-p viewindex (fn-nntp-string-octets "2"))))))
      (not nil)
      (not
        (and
          (equal (fn-otb-dependency-step 0 0 2000 nil) :serve)
          (equal (fn-own-tls-result-consumed p) (+ 2 (len (fn-nntp-string-octets "ARTICLE 2"))))
          (equal (fn-own-tls-result-effects p) (fn-nntp-result-effects r))
          (equal
            (fn-own-tls-result-owner p)
            (cdr
              (fn-ocfg-read
                *pcrt-selected*
                0
                (append (fn-nntp-string-octets "ARTICLE 2") (quote (13 10)))
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
  pcra-number-without-funding
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
      (number (fn-nntp-decimal-value (fn-nntp-string-octets "2")))
      (article
        (if
          (fn-nntp-number-tokenp (fn-nntp-string-octets "2"))
          (fn-nntp-find-group-number group number (fn-state-articles viewarchive))
          (fn-midx-lookup
            (fn-nntp-token-string (fn-nntp-string-octets "2"))
            (fn-gidx-pin-trie viewindex))))
      (server (fn-nntp-xref-server env))
      (r (fn-pcr-absent-reply session (fn-nntp-string-octets "2")))
      (p
        (car
          (fn-mca-read-span
            (fn-mcr-make 0 0 0 0 0 0 nil)
            *pcrt-clocked-queued-selected*
            nil
            0
            0
            (len (append (fn-nntp-string-octets "ARTICLE 2") (quote (13 10))))
            nil
            (fn-otm-init)
            32
            107552
            (append (fn-nntp-string-octets "ARTICLE 2") (quote (13 10)))
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
                (len (append (fn-nntp-string-octets "ARTICLE 2") (quote (13 10))))
                nil
                (fn-otm-init)
                (append (fn-nntp-string-octets "ARTICLE 2") (quote (13 10)))
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
          (fn-oct-slice-list
            0
            (len (append (fn-nntp-string-octets "ARTICLE 2") (quote (13 10))))
            (append (fn-nntp-string-octets "ARTICLE 2") (quote (13 10))))
          (append (fn-nntp-string-octets "ARTICLE 2") (quote (13 10))))
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
          (len (fn-nntp-string-octets "ARTICLE 2"))
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
        (fn-nntp-command-inputp (fn-nntp-string-octets "ARTICLE 2"))
        (equal
          (fn-nntp-tokenize (fn-nntp-string-octets "ARTICLE 2"))
          (list *fn-pcr-article-keyword* (fn-nntp-string-octets "2")))
        (or
          (fn-nntp-number-tokenp (fn-nntp-string-octets "2"))
          (and
            (fn-nntp-message-id-tokenp (fn-nntp-string-octets "2"))
            (fn-octet-listp (fn-nntp-string-octets "2"))))
        (or (not (fn-nntp-number-tokenp (fn-nntp-string-octets "2"))) group)
        (not (consp article))
        server
        (fn-gidx-pinp viewindex)
        (and
          (not
            (fn-nntp-number-withdrawn-p session viewarchive viewindex (fn-nntp-string-octets "2")))
          (not
            (and
              (fn-nntp-message-id-tokenp (fn-nntp-string-octets "2"))
              (fn-nntp-msgid-withdrawn-p viewindex (fn-nntp-string-octets "2"))))))
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
                    (len (append (fn-nntp-string-octets "ARTICLE 2") (quote (13 10))))
                    nil
                    (fn-otm-init)
                    32
                    (append (fn-nntp-string-octets "ARTICLE 2") (quote (13 10)))
                    (list *pcrt-payload*)
                    *pcrt-cat*))
                0
                107552)))
          :ok))
      (not
        (and
          (equal (fn-otb-dependency-step 0 0 2000 t) :serve)
          (equal (fn-own-tls-result-consumed p) (+ 2 (len (fn-nntp-string-octets "ARTICLE 2"))))
          (equal (fn-own-tls-result-effects p) (fn-nntp-result-effects r))
          (equal
            (fn-own-tls-result-owner p)
            (cdr
              (fn-ocfg-read
                *pcrt-clocked-queued-selected*
                0
                (append (fn-nntp-string-octets "ARTICLE 2") (quote (13 10)))
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
  pcra-number-without-absence
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
      (article
        (if
          (fn-nntp-number-tokenp (fn-nntp-string-octets "1"))
          (fn-nntp-find-group-number group number (fn-state-articles viewarchive))
          (fn-midx-lookup
            (fn-nntp-token-string (fn-nntp-string-octets "1"))
            (fn-gidx-pin-trie viewindex))))
      (server (fn-nntp-xref-server env))
      (r (fn-pcr-absent-reply session (fn-nntp-string-octets "1")))
      (p
        (car
          (fn-mca-read-span
            *pcrt-credits*
            *pcrt-selected*
            nil
            0
            0
            (len (append (fn-nntp-string-octets "ARTICLE 1") (quote (13 10))))
            nil
            (fn-otm-init)
            32
            107552
            (append (fn-nntp-string-octets "ARTICLE 1") (quote (13 10)))
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
                    (len (append (fn-nntp-string-octets "ARTICLE 1") (quote (13 10))))
                    nil
                    (fn-otm-init)
                    32
                    (append (fn-nntp-string-octets "ARTICLE 1") (quote (13 10)))
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
                (len (append (fn-nntp-string-octets "ARTICLE 1") (quote (13 10))))
                nil
                (fn-otm-init)
                (append (fn-nntp-string-octets "ARTICLE 1") (quote (13 10)))
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
          (fn-oct-slice-list
            0
            (len (append (fn-nntp-string-octets "ARTICLE 1") (quote (13 10))))
            (append (fn-nntp-string-octets "ARTICLE 1") (quote (13 10))))
          (append (fn-nntp-string-octets "ARTICLE 1") (quote (13 10))))
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
        (or
          (fn-nntp-number-tokenp (fn-nntp-string-octets "1"))
          (and
            (fn-nntp-message-id-tokenp (fn-nntp-string-octets "1"))
            (fn-octet-listp (fn-nntp-string-octets "1"))))
        (or (not (fn-nntp-number-tokenp (fn-nntp-string-octets "1"))) group)
        server
        (fn-gidx-pinp viewindex)
        (and
          (not
            (fn-nntp-number-withdrawn-p session viewarchive viewindex (fn-nntp-string-octets "1")))
          (not
            (and
              (fn-nntp-message-id-tokenp (fn-nntp-string-octets "1"))
              (fn-nntp-msgid-withdrawn-p viewindex (fn-nntp-string-octets "1"))))))
      (not (not (consp article)))
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

(defthm
  pcra-message-id-positive
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
      (number (fn-nntp-decimal-value (fn-nntp-string-octets "<absent@x>")))
      (article
        (if
          (fn-nntp-number-tokenp (fn-nntp-string-octets "<absent@x>"))
          (fn-nntp-find-group-number group number (fn-state-articles viewarchive))
          (fn-midx-lookup
            (fn-nntp-token-string (fn-nntp-string-octets "<absent@x>"))
            (fn-gidx-pin-trie viewindex))))
      (server (fn-nntp-xref-server env))
      (r (fn-pcr-absent-reply session (fn-nntp-string-octets "<absent@x>")))
      (p
        (car
          (fn-mca-read-span
            *pcrt-credits*
            *pcrt-selected*
            nil
            0
            0
            (len (append (fn-nntp-string-octets "ARTICLE <absent@x>") (quote (13 10))))
            nil
            (fn-otm-init)
            32
            107552
            (append (fn-nntp-string-octets "ARTICLE <absent@x>") (quote (13 10)))
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
                    (len (append (fn-nntp-string-octets "ARTICLE <absent@x>") (quote (13 10))))
                    nil
                    (fn-otm-init)
                    32
                    (append (fn-nntp-string-octets "ARTICLE <absent@x>") (quote (13 10)))
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
                (len (append (fn-nntp-string-octets "ARTICLE <absent@x>") (quote (13 10))))
                nil
                (fn-otm-init)
                (append (fn-nntp-string-octets "ARTICLE <absent@x>") (quote (13 10)))
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
          (fn-oct-slice-list
            0
            (len (append (fn-nntp-string-octets "ARTICLE <absent@x>") (quote (13 10))))
            (append (fn-nntp-string-octets "ARTICLE <absent@x>") (quote (13 10))))
          (append (fn-nntp-string-octets "ARTICLE <absent@x>") (quote (13 10))))
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
          (len (fn-nntp-string-octets "ARTICLE <absent@x>"))
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
        (fn-nntp-command-inputp (fn-nntp-string-octets "ARTICLE <absent@x>"))
        (equal
          (fn-nntp-tokenize (fn-nntp-string-octets "ARTICLE <absent@x>"))
          (list *fn-pcr-article-keyword* (fn-nntp-string-octets "<absent@x>")))
        (or
          (fn-nntp-number-tokenp (fn-nntp-string-octets "<absent@x>"))
          (and
            (fn-nntp-message-id-tokenp (fn-nntp-string-octets "<absent@x>"))
            (fn-octet-listp (fn-nntp-string-octets "<absent@x>"))))
        (or (not (fn-nntp-number-tokenp (fn-nntp-string-octets "<absent@x>"))) group)
        (not (consp article))
        server
        (fn-gidx-pinp viewindex)
        (and
          (not
            (fn-nntp-number-withdrawn-p
              session
              viewarchive
              viewindex
              (fn-nntp-string-octets "<absent@x>")))
          (not
            (and
              (fn-nntp-message-id-tokenp (fn-nntp-string-octets "<absent@x>"))
              (fn-nntp-msgid-withdrawn-p viewindex (fn-nntp-string-octets "<absent@x>"))))))
      (and
        (equal (fn-otb-dependency-step 0 0 2000 t) :serve)
        (equal
          (fn-own-tls-result-consumed p)
          (+ 2 (len (fn-nntp-string-octets "ARTICLE <absent@x>"))))
        (equal (fn-own-tls-result-effects p) (fn-nntp-result-effects r))
        (equal
          (fn-own-tls-result-owner p)
          (cdr
            (fn-ocfg-read
              *pcrt-selected*
              0
              (append (fn-nntp-string-octets "ARTICLE <absent@x>") (quote (13 10)))
              (list *pcrt-payload*)))))
      (equal
        (fn-served-reply-octets (fn-own-tls-result-effects p))
        (append (fn-nntp-string-octets "430 no article with that message-id") (quote (13 10))))))
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
  pcra-message-id-without-completion
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
      (number (fn-nntp-decimal-value (fn-nntp-string-octets "<absent@x>")))
      (article
        (if
          (fn-nntp-number-tokenp (fn-nntp-string-octets "<absent@x>"))
          (fn-nntp-find-group-number group number (fn-state-articles viewarchive))
          (fn-midx-lookup
            (fn-nntp-token-string (fn-nntp-string-octets "<absent@x>"))
            (fn-gidx-pin-trie viewindex))))
      (server (fn-nntp-xref-server env))
      (r (fn-pcr-absent-reply session (fn-nntp-string-octets "<absent@x>")))
      (p
        (car
          (fn-mca-read-span
            *pcrt-credits*
            *pcrt-selected*
            nil
            0
            0
            (len (append (fn-nntp-string-octets "ARTICLE <absent@x>") (quote (13 10))))
            nil
            (fn-otm-init)
            32
            107552
            (append (fn-nntp-string-octets "ARTICLE <absent@x>") (quote (13 10)))
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
                    (len (append (fn-nntp-string-octets "ARTICLE <absent@x>") (quote (13 10))))
                    nil
                    (fn-otm-init)
                    32
                    (append (fn-nntp-string-octets "ARTICLE <absent@x>") (quote (13 10)))
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
                (len (append (fn-nntp-string-octets "ARTICLE <absent@x>") (quote (13 10))))
                nil
                (fn-otm-init)
                (append (fn-nntp-string-octets "ARTICLE <absent@x>") (quote (13 10)))
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
          (fn-oct-slice-list
            0
            (len (append (fn-nntp-string-octets "ARTICLE <absent@x>") (quote (13 10))))
            (append (fn-nntp-string-octets "ARTICLE <absent@x>") (quote (13 10))))
          (append (fn-nntp-string-octets "ARTICLE <absent@x>") (quote (13 10))))
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
          (len (fn-nntp-string-octets "ARTICLE <absent@x>"))
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
        (fn-nntp-command-inputp (fn-nntp-string-octets "ARTICLE <absent@x>"))
        (equal
          (fn-nntp-tokenize (fn-nntp-string-octets "ARTICLE <absent@x>"))
          (list *fn-pcr-article-keyword* (fn-nntp-string-octets "<absent@x>")))
        (or
          (fn-nntp-number-tokenp (fn-nntp-string-octets "<absent@x>"))
          (and
            (fn-nntp-message-id-tokenp (fn-nntp-string-octets "<absent@x>"))
            (fn-octet-listp (fn-nntp-string-octets "<absent@x>"))))
        (or (not (fn-nntp-number-tokenp (fn-nntp-string-octets "<absent@x>"))) group)
        (not (consp article))
        server
        (fn-gidx-pinp viewindex)
        (and
          (not
            (fn-nntp-number-withdrawn-p
              session
              viewarchive
              viewindex
              (fn-nntp-string-octets "<absent@x>")))
          (not
            (and
              (fn-nntp-message-id-tokenp (fn-nntp-string-octets "<absent@x>"))
              (fn-nntp-msgid-withdrawn-p viewindex (fn-nntp-string-octets "<absent@x>"))))))
      (not nil)
      (not
        (and
          (equal (fn-otb-dependency-step 0 0 2000 nil) :serve)
          (equal
            (fn-own-tls-result-consumed p)
            (+ 2 (len (fn-nntp-string-octets "ARTICLE <absent@x>"))))
          (equal (fn-own-tls-result-effects p) (fn-nntp-result-effects r))
          (equal
            (fn-own-tls-result-owner p)
            (cdr
              (fn-ocfg-read
                *pcrt-selected*
                0
                (append (fn-nntp-string-octets "ARTICLE <absent@x>") (quote (13 10)))
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
  pcra-message-id-without-funding
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
      (number (fn-nntp-decimal-value (fn-nntp-string-octets "<absent@x>")))
      (article
        (if
          (fn-nntp-number-tokenp (fn-nntp-string-octets "<absent@x>"))
          (fn-nntp-find-group-number group number (fn-state-articles viewarchive))
          (fn-midx-lookup
            (fn-nntp-token-string (fn-nntp-string-octets "<absent@x>"))
            (fn-gidx-pin-trie viewindex))))
      (server (fn-nntp-xref-server env))
      (r (fn-pcr-absent-reply session (fn-nntp-string-octets "<absent@x>")))
      (p
        (car
          (fn-mca-read-span
            (fn-mcr-make 0 0 0 0 0 0 nil)
            *pcrt-clocked-queued-selected*
            nil
            0
            0
            (len (append (fn-nntp-string-octets "ARTICLE <absent@x>") (quote (13 10))))
            nil
            (fn-otm-init)
            32
            107552
            (append (fn-nntp-string-octets "ARTICLE <absent@x>") (quote (13 10)))
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
                (len (append (fn-nntp-string-octets "ARTICLE <absent@x>") (quote (13 10))))
                nil
                (fn-otm-init)
                (append (fn-nntp-string-octets "ARTICLE <absent@x>") (quote (13 10)))
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
          (fn-oct-slice-list
            0
            (len (append (fn-nntp-string-octets "ARTICLE <absent@x>") (quote (13 10))))
            (append (fn-nntp-string-octets "ARTICLE <absent@x>") (quote (13 10))))
          (append (fn-nntp-string-octets "ARTICLE <absent@x>") (quote (13 10))))
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
          (len (fn-nntp-string-octets "ARTICLE <absent@x>"))
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
        (fn-nntp-command-inputp (fn-nntp-string-octets "ARTICLE <absent@x>"))
        (equal
          (fn-nntp-tokenize (fn-nntp-string-octets "ARTICLE <absent@x>"))
          (list *fn-pcr-article-keyword* (fn-nntp-string-octets "<absent@x>")))
        (or
          (fn-nntp-number-tokenp (fn-nntp-string-octets "<absent@x>"))
          (and
            (fn-nntp-message-id-tokenp (fn-nntp-string-octets "<absent@x>"))
            (fn-octet-listp (fn-nntp-string-octets "<absent@x>"))))
        (or (not (fn-nntp-number-tokenp (fn-nntp-string-octets "<absent@x>"))) group)
        (not (consp article))
        server
        (fn-gidx-pinp viewindex)
        (and
          (not
            (fn-nntp-number-withdrawn-p
              session
              viewarchive
              viewindex
              (fn-nntp-string-octets "<absent@x>")))
          (not
            (and
              (fn-nntp-message-id-tokenp (fn-nntp-string-octets "<absent@x>"))
              (fn-nntp-msgid-withdrawn-p viewindex (fn-nntp-string-octets "<absent@x>"))))))
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
                    (len (append (fn-nntp-string-octets "ARTICLE <absent@x>") (quote (13 10))))
                    nil
                    (fn-otm-init)
                    32
                    (append (fn-nntp-string-octets "ARTICLE <absent@x>") (quote (13 10)))
                    (list *pcrt-payload*)
                    *pcrt-cat*))
                0
                107552)))
          :ok))
      (not
        (and
          (equal (fn-otb-dependency-step 0 0 2000 t) :serve)
          (equal
            (fn-own-tls-result-consumed p)
            (+ 2 (len (fn-nntp-string-octets "ARTICLE <absent@x>"))))
          (equal (fn-own-tls-result-effects p) (fn-nntp-result-effects r))
          (equal
            (fn-own-tls-result-owner p)
            (cdr
              (fn-ocfg-read
                *pcrt-clocked-queued-selected*
                0
                (append (fn-nntp-string-octets "ARTICLE <absent@x>") (quote (13 10)))
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
  pcra-message-id-without-absence
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
      (number (fn-nntp-decimal-value (fn-nntp-string-octets "<pcrt@x>")))
      (article
        (if
          (fn-nntp-number-tokenp (fn-nntp-string-octets "<pcrt@x>"))
          (fn-nntp-find-group-number group number (fn-state-articles viewarchive))
          (fn-midx-lookup
            (fn-nntp-token-string (fn-nntp-string-octets "<pcrt@x>"))
            (fn-gidx-pin-trie viewindex))))
      (server (fn-nntp-xref-server env))
      (r (fn-pcr-absent-reply session (fn-nntp-string-octets "<pcrt@x>")))
      (p
        (car
          (fn-mca-read-span
            *pcrt-credits*
            *pcrt-selected*
            nil
            0
            0
            (len (append (fn-nntp-string-octets "ARTICLE <pcrt@x>") (quote (13 10))))
            nil
            (fn-otm-init)
            32
            107552
            (append (fn-nntp-string-octets "ARTICLE <pcrt@x>") (quote (13 10)))
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
                    (len (append (fn-nntp-string-octets "ARTICLE <pcrt@x>") (quote (13 10))))
                    nil
                    (fn-otm-init)
                    32
                    (append (fn-nntp-string-octets "ARTICLE <pcrt@x>") (quote (13 10)))
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
                (len (append (fn-nntp-string-octets "ARTICLE <pcrt@x>") (quote (13 10))))
                nil
                (fn-otm-init)
                (append (fn-nntp-string-octets "ARTICLE <pcrt@x>") (quote (13 10)))
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
          (fn-oct-slice-list
            0
            (len (append (fn-nntp-string-octets "ARTICLE <pcrt@x>") (quote (13 10))))
            (append (fn-nntp-string-octets "ARTICLE <pcrt@x>") (quote (13 10))))
          (append (fn-nntp-string-octets "ARTICLE <pcrt@x>") (quote (13 10))))
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
          (len (fn-nntp-string-octets "ARTICLE <pcrt@x>"))
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
        (fn-nntp-command-inputp (fn-nntp-string-octets "ARTICLE <pcrt@x>"))
        (equal
          (fn-nntp-tokenize (fn-nntp-string-octets "ARTICLE <pcrt@x>"))
          (list *fn-pcr-article-keyword* (fn-nntp-string-octets "<pcrt@x>")))
        (or
          (fn-nntp-number-tokenp (fn-nntp-string-octets "<pcrt@x>"))
          (and
            (fn-nntp-message-id-tokenp (fn-nntp-string-octets "<pcrt@x>"))
            (fn-octet-listp (fn-nntp-string-octets "<pcrt@x>"))))
        (or (not (fn-nntp-number-tokenp (fn-nntp-string-octets "<pcrt@x>"))) group)
        server
        (fn-gidx-pinp viewindex)
        (and
          (not
            (fn-nntp-number-withdrawn-p
              session
              viewarchive
              viewindex
              (fn-nntp-string-octets "<pcrt@x>")))
          (not
            (and
              (fn-nntp-message-id-tokenp (fn-nntp-string-octets "<pcrt@x>"))
              (fn-nntp-msgid-withdrawn-p viewindex (fn-nntp-string-octets "<pcrt@x>"))))))
      (not (not (consp article)))
      (not
        (and
          (equal (fn-otb-dependency-step 0 0 2000 t) :serve)
          (equal
            (fn-own-tls-result-consumed p)
            (+ 2 (len (fn-nntp-string-octets "ARTICLE <pcrt@x>"))))
          (equal (fn-own-tls-result-effects p) (fn-nntp-result-effects r))
          (equal
            (fn-own-tls-result-owner p)
            (cdr
              (fn-ocfg-read
                *pcrt-selected*
                0
                (append (fn-nntp-string-octets "ARTICLE <pcrt@x>") (quote (13 10)))
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
  pcra-number-without-command-slice
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
      (number (fn-nntp-decimal-value (fn-nntp-string-octets "2")))
      (article
        (if
          (fn-nntp-number-tokenp (fn-nntp-string-octets "2"))
          (fn-nntp-find-group-number group number (fn-state-articles viewarchive))
          (fn-midx-lookup
            (fn-nntp-token-string (fn-nntp-string-octets "2"))
            (fn-gidx-pin-trie viewindex))))
      (server (fn-nntp-xref-server env))
      (r (fn-pcr-absent-reply session (fn-nntp-string-octets "2")))
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
          (len (fn-nntp-string-octets "ARTICLE 2"))
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
        (fn-nntp-command-inputp (fn-nntp-string-octets "ARTICLE 2"))
        (equal
          (fn-nntp-tokenize (fn-nntp-string-octets "ARTICLE 2"))
          (list *fn-pcr-article-keyword* (fn-nntp-string-octets "2")))
        (or
          (fn-nntp-number-tokenp (fn-nntp-string-octets "2"))
          (and
            (fn-nntp-message-id-tokenp (fn-nntp-string-octets "2"))
            (fn-octet-listp (fn-nntp-string-octets "2"))))
        (or (not (fn-nntp-number-tokenp (fn-nntp-string-octets "2"))) group)
        (not (consp article))
        server
        (fn-gidx-pinp viewindex)
        (and
          (not
            (fn-nntp-number-withdrawn-p session viewarchive viewindex (fn-nntp-string-octets "2")))
          (not
            (and
              (fn-nntp-message-id-tokenp (fn-nntp-string-octets "2"))
              (fn-nntp-msgid-withdrawn-p viewindex (fn-nntp-string-octets "2"))))))
      (not
        (equal
          (fn-oct-slice-list 0 0 nil)
          (append (fn-nntp-string-octets "ARTICLE 2") (quote (13 10)))))
      (not
        (and
          (equal (fn-otb-dependency-step 0 0 2000 t) :serve)
          (equal (fn-own-tls-result-consumed p) (+ 2 (len (fn-nntp-string-octets "ARTICLE 2"))))
          (equal (fn-own-tls-result-effects p) (fn-nntp-result-effects r))
          (equal
            (fn-own-tls-result-owner p)
            (cdr
              (fn-ocfg-read
                *pcrt-selected*
                0
                (append (fn-nntp-string-octets "ARTICLE 2") (quote (13 10)))
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
  pcra-message-id-without-command-slice
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
      (number (fn-nntp-decimal-value (fn-nntp-string-octets "<absent@x>")))
      (article
        (if
          (fn-nntp-number-tokenp (fn-nntp-string-octets "<absent@x>"))
          (fn-nntp-find-group-number group number (fn-state-articles viewarchive))
          (fn-midx-lookup
            (fn-nntp-token-string (fn-nntp-string-octets "<absent@x>"))
            (fn-gidx-pin-trie viewindex))))
      (server (fn-nntp-xref-server env))
      (r (fn-pcr-absent-reply session (fn-nntp-string-octets "<absent@x>")))
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
          (len (fn-nntp-string-octets "ARTICLE <absent@x>"))
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
        (fn-nntp-command-inputp (fn-nntp-string-octets "ARTICLE <absent@x>"))
        (equal
          (fn-nntp-tokenize (fn-nntp-string-octets "ARTICLE <absent@x>"))
          (list *fn-pcr-article-keyword* (fn-nntp-string-octets "<absent@x>")))
        (or
          (fn-nntp-number-tokenp (fn-nntp-string-octets "<absent@x>"))
          (and
            (fn-nntp-message-id-tokenp (fn-nntp-string-octets "<absent@x>"))
            (fn-octet-listp (fn-nntp-string-octets "<absent@x>"))))
        (or (not (fn-nntp-number-tokenp (fn-nntp-string-octets "<absent@x>"))) group)
        (not (consp article))
        server
        (fn-gidx-pinp viewindex)
        (and
          (not
            (fn-nntp-number-withdrawn-p
              session
              viewarchive
              viewindex
              (fn-nntp-string-octets "<absent@x>")))
          (not
            (and
              (fn-nntp-message-id-tokenp (fn-nntp-string-octets "<absent@x>"))
              (fn-nntp-msgid-withdrawn-p viewindex (fn-nntp-string-octets "<absent@x>"))))))
      (not
        (equal
          (fn-oct-slice-list 0 0 nil)
          (append (fn-nntp-string-octets "ARTICLE <absent@x>") (quote (13 10)))))
      (not
        (and
          (equal (fn-otb-dependency-step 0 0 2000 t) :serve)
          (equal
            (fn-own-tls-result-consumed p)
            (+ 2 (len (fn-nntp-string-octets "ARTICLE <absent@x>"))))
          (equal (fn-own-tls-result-effects p) (fn-nntp-result-effects r))
          (equal
            (fn-own-tls-result-owner p)
            (cdr
              (fn-ocfg-read
                *pcrt-selected*
                0
                (append (fn-nntp-string-octets "ARTICLE <absent@x>") (quote (13 10)))
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
