; Partial Message-ID host READ teeth: literal full positive and two removals.
; Further retained-hypothesis removals/proved weakening remain open.
(in-package "ACL2")

(include-book "productive-read-chain-tests")

(include-book "../../books/productive-read-message-id")

(defconst *pcrm-token* (fn-nntp-string-octets "<pcrt@x>"))

(defconst *pcrm-line* (append (fn-nntp-string-octets "ARTICLE ") *pcrm-token*))

(defconst *pcrm-line-bytes* (append *pcrm-line* (quote (13 10))))

(defthm pcrm-complete-message-id-positive
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
     (article (fn-midx-lookup (fn-nntp-token-string *pcrm-token*) (fn-gidx-pin-trie viewindex)))
     (server (fn-nntp-xref-server env))
     (r (fn-pcr-msgid-220-reply session article server (list *pcrt-payload*)))
     (p
       (car
         (fn-mca-read-span *pcrt-credits* *pcrt-selected* nil 0 0
           (len *pcrm-line-bytes*)
           nil
           (fn-otm-init)
           32
           107552
           *pcrm-line-bytes*
           (list *pcrt-payload*)
           *pcrt-cat*))))
    (and
      (and
        (equal
          (car
            (fn-mcr-resize *pcrt-credits*
              (fn-mca-conn-key 0)
              (fn-mca-need
                (fn-own-tls-result-owner
                  (fn-oas-read-span *pcrt-selected* nil 0 0
                    (len *pcrm-line-bytes*)
                    nil
                    (fn-otm-init)
                    32
                    *pcrm-line-bytes*
                    (list *pcrt-payload*)
                    *pcrt-cat*))
                0
                107552)))
          :ok)
        (not
          (fn-oas-over-p *pcrt-selected*
            (fn-own-tls-result-owner
              (fn-otm-read-span *pcrt-selected* nil 0 0
                (len *pcrm-line-bytes*)
                nil
                (fn-otm-init)
                *pcrm-line-bytes*
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
        (natp 0)
        (natp (len *pcrm-line-bytes*))
        conn
        t
        (equal
          (fn-oct-slice-list 0 (len *pcrm-line-bytes*) *pcrm-line-bytes*)
          (append *pcrm-line* (quote (13 10))))
        (equal
          (fn-served-conn-wire sc)
          (fn-wire-make-state :command nil 0 nil nil 0
            (fn-wire-state-line-limit
              (fn-own-conn-wire (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*)))))
            (fn-wire-state-body-limit
              (fn-own-conn-wire (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*)))))))
        (fn-wire-statep (fn-served-conn-wire sc))
        (<=
          (len *pcrm-line*)
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
        (fn-nntp-command-inputp *pcrm-line*)
        (fn-nntp-command-arguments-at-mostp (list *fn-pcr-article-keyword* *pcrm-token*))
        (equal (fn-nntp-tokenize *pcrm-line*) (list *fn-pcr-article-keyword* *pcrm-token*))

        (and (fn-nntp-message-id-tokenp *pcrm-token*) (fn-octet-listp *pcrm-token*))
        (consp article)
        server
        (fn-gidx-pinp viewindex)
        (and
          (not (fn-nntp-number-withdrawn-p session viewarchive viewindex *pcrm-token*))
          (not (fn-nntp-msgid-withdrawn-p viewindex *pcrm-token*)))
        (fn-nntp-response-okp-of-bytes article
          (fn-nntp-article-bytes article (list *pcrt-payload*))
          :article)
        (fn-nntp-response-okp-of-bytes article
          (fn-pcr-served-octets server article (list *pcrt-payload*))
          :article))
      (and
        (equal (fn-otb-dependency-step 0 0 2000 t) :serve)
        (equal (fn-own-tls-result-consumed p) (+ 2 (len *pcrm-line*)))
        (equal (fn-own-tls-result-effects p) (fn-nntp-result-effects r))
        (equal
          (fn-own-tls-result-owner p)
          (cdr
            (fn-ocfg-read *pcrt-selected* 0
              (append *pcrm-line* (quote (13 10)))
              (list *pcrt-payload*)))))))
  :rule-classes
  nil
  :hints
  (("Goal" :in-theory
     (enable fn-scr-owner-catalogp fn-scr-conn-okp fn-scr-conn-catalogp
       fn-scr-fields-catalogp
       fn-scr-live-catalogp
       fn-scr-catalogp
       fn-scol-okp))))

(defthm pcrm-without-completion
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
     (article (fn-midx-lookup (fn-nntp-token-string *pcrm-token*) (fn-gidx-pin-trie viewindex)))
     (server (fn-nntp-xref-server env))
     (r (fn-pcr-msgid-220-reply session article server (list *pcrt-payload*)))
     (p
       (car
         (fn-mca-read-span *pcrt-credits* *pcrt-selected* nil 0 0
           (len *pcrm-line-bytes*)
           nil
           (fn-otm-init)
           32
           107552
           *pcrm-line-bytes*
           (list *pcrt-payload*)
           *pcrt-cat*))))
    (and
      (and
        (equal
          (car
            (fn-mcr-resize *pcrt-credits*
              (fn-mca-conn-key 0)
              (fn-mca-need
                (fn-own-tls-result-owner
                  (fn-oas-read-span *pcrt-selected* nil 0 0
                    (len *pcrm-line-bytes*)
                    nil
                    (fn-otm-init)
                    32
                    *pcrm-line-bytes*
                    (list *pcrt-payload*)
                    *pcrt-cat*))
                0
                107552)))
          :ok)
        (not
          (fn-oas-over-p *pcrt-selected*
            (fn-own-tls-result-owner
              (fn-otm-read-span *pcrt-selected* nil 0 0
                (len *pcrm-line-bytes*)
                nil
                (fn-otm-init)
                *pcrm-line-bytes*
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
        (natp 0)
        (natp (len *pcrm-line-bytes*))
        conn
        (equal
          (fn-oct-slice-list 0 (len *pcrm-line-bytes*) *pcrm-line-bytes*)
          (append *pcrm-line* (quote (13 10))))
        (equal
          (fn-served-conn-wire sc)
          (fn-wire-make-state :command nil 0 nil nil 0
            (fn-wire-state-line-limit
              (fn-own-conn-wire (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*)))))
            (fn-wire-state-body-limit
              (fn-own-conn-wire (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*)))))))
        (fn-wire-statep (fn-served-conn-wire sc))
        (<=
          (len *pcrm-line*)
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
        (fn-nntp-command-inputp *pcrm-line*)
        (fn-nntp-command-arguments-at-mostp (list *fn-pcr-article-keyword* *pcrm-token*))
        (equal (fn-nntp-tokenize *pcrm-line*) (list *fn-pcr-article-keyword* *pcrm-token*))

        (and (fn-nntp-message-id-tokenp *pcrm-token*) (fn-octet-listp *pcrm-token*))
        (consp article)
        server
        (fn-gidx-pinp viewindex)
        (and
          (not (fn-nntp-number-withdrawn-p session viewarchive viewindex *pcrm-token*))
          (not (fn-nntp-msgid-withdrawn-p viewindex *pcrm-token*)))
        (fn-nntp-response-okp-of-bytes article
          (fn-nntp-article-bytes article (list *pcrt-payload*))
          :article)
        (fn-nntp-response-okp-of-bytes article
          (fn-pcr-served-octets server article (list *pcrt-payload*))
          :article))
      (not nil)
      (not
        (and
          (equal (fn-otb-dependency-step 0 0 2000 nil) :serve)
          (equal (fn-own-tls-result-consumed p) (+ 2 (len *pcrm-line*)))
          (equal (fn-own-tls-result-effects p) (fn-nntp-result-effects r))
          (equal
            (fn-own-tls-result-owner p)
            (cdr
              (fn-ocfg-read *pcrt-selected* 0
                (append *pcrm-line* (quote (13 10)))
                (list *pcrt-payload*))))))))
  :rule-classes
  nil
  :hints
  (("Goal" :in-theory
     (enable fn-scr-owner-catalogp fn-scr-conn-okp fn-scr-conn-catalogp
       fn-scr-fields-catalogp
       fn-scr-live-catalogp
       fn-scr-catalogp
       fn-scol-okp))))

(defthm pcrm-without-funding
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
     (article (fn-midx-lookup (fn-nntp-token-string *pcrm-token*) (fn-gidx-pin-trie viewindex)))
     (server (fn-nntp-xref-server env))
     (r (fn-pcr-msgid-220-reply session article server (list *pcrt-payload*)))
     (p
       (car
         (fn-mca-read-span
           (fn-mcr-make 0 0 0 0 0 0 nil)
           *pcrt-clocked-queued-selected*
           nil
           0
           0
           (len *pcrm-line-bytes*)
           nil
           (fn-otm-init)
           32
           107552
           *pcrm-line-bytes*
           (list *pcrt-payload*)
           *pcrt-cat*))))
    (and
      (and
        (not
          (fn-oas-over-p *pcrt-clocked-queued-selected*
            (fn-own-tls-result-owner
              (fn-otm-read-span *pcrt-clocked-queued-selected* nil 0 0
                (len *pcrm-line-bytes*)
                nil
                (fn-otm-init)
                *pcrm-line-bytes*
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
        (natp 0)
        (natp (len *pcrm-line-bytes*))
        conn
        t
        (equal
          (fn-oct-slice-list 0 (len *pcrm-line-bytes*) *pcrm-line-bytes*)
          (append *pcrm-line* (quote (13 10))))
        (equal
          (fn-served-conn-wire sc)
          (fn-wire-make-state :command nil 0 nil nil 0
            (fn-wire-state-line-limit
              (fn-own-conn-wire
                (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-clocked-queued-selected*)))))
            (fn-wire-state-body-limit
              (fn-own-conn-wire
                (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-clocked-queued-selected*)))))))
        (fn-wire-statep (fn-served-conn-wire sc))
        (<=
          (len *pcrm-line*)
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
        (fn-nntp-command-inputp *pcrm-line*)
        (fn-nntp-command-arguments-at-mostp (list *fn-pcr-article-keyword* *pcrm-token*))
        (equal (fn-nntp-tokenize *pcrm-line*) (list *fn-pcr-article-keyword* *pcrm-token*))

        (and (fn-nntp-message-id-tokenp *pcrm-token*) (fn-octet-listp *pcrm-token*))
        (consp article)
        server
        (fn-gidx-pinp viewindex)
        (and
          (not (fn-nntp-number-withdrawn-p session viewarchive viewindex *pcrm-token*))
          (not (fn-nntp-msgid-withdrawn-p viewindex *pcrm-token*)))
        (fn-nntp-response-okp-of-bytes article
          (fn-nntp-article-bytes article (list *pcrt-payload*))
          :article)
        (fn-nntp-response-okp-of-bytes article
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
                  (fn-oas-read-span *pcrt-clocked-queued-selected* nil 0 0
                    (len *pcrm-line-bytes*)
                    nil
                    (fn-otm-init)
                    32
                    *pcrm-line-bytes*
                    (list *pcrt-payload*)
                    *pcrt-cat*))
                0
                107552)))
          :ok))
      (not
        (and
          (equal (fn-otb-dependency-step 0 0 2000 t) :serve)
          (equal (fn-own-tls-result-consumed p) (+ 2 (len *pcrm-line*)))
          (equal (fn-own-tls-result-effects p) (fn-nntp-result-effects r))
          (equal
            (fn-own-tls-result-owner p)
            (cdr
              (fn-ocfg-read *pcrt-clocked-queued-selected* 0
                (append *pcrm-line* (quote (13 10)))
                (list *pcrt-payload*))))))))
  :rule-classes
  nil
  :hints
  (("Goal" :in-theory
     (enable fn-scr-owner-catalogp fn-scr-conn-okp fn-scr-conn-catalogp
       fn-scr-fields-catalogp
       fn-scr-live-catalogp
       fn-scr-catalogp
       fn-scol-okp))))
