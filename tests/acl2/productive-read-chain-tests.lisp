; Literal READ witnesses: each complete retained antecedent and conclusion.
; Bounds derived by the final theorem are not separate hypotheses.
; Funding removals use a reader-reachable owner paired with an empty ledger:
; these are corrupted-credit-state witnesses, not complete native traces.
(in-package "ACL2")
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

(defconst *pcrt-credits* (fn-mcr-make 1000000 0 0 0 0 0 nil 0 nil))

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

; Corrupted-wire state: complete literal retained antecedent/conclusion.
(defconst
  *pcr-wire-closed-mutant*
  (fn-ocfg-with-owner
    *pcrt-selected*
    (fn-own-set-conns
      (fn-ocfg-owner *pcrt-selected*)
      (fn-own-replace-conn
        (update-nth
          3
          (fn-wire-make-state
            :closed
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
                (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*))))))
          (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*))))
        (fn-own-conns (fn-ocfg-owner *pcrt-selected*))))))
; Corrupted-session state: complete literal retained antecedent/conclusion.
(defconst
  *pcr-handshaking-mutant*
  (fn-ocfg-with-owner
    *pcrt-selected*
    (fn-own-set-conns
      (fn-ocfg-owner *pcrt-selected*)
      (fn-own-replace-conn
        (update-nth
          4
          (update-nth
            5
            t
            (fn-own-conn-session
              (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*)))))
          (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*))))
        (fn-own-conns (fn-ocfg-owner *pcrt-selected*))))))
; Corrupted-session state: complete literal retained antecedent/conclusion.
(defconst
  *pcr-sasl-waiting-mutant*
  (fn-ocfg-with-owner
    *pcrt-selected*
    (fn-own-set-conns
      (fn-ocfg-owner *pcrt-selected*)
      (fn-own-replace-conn
        (update-nth
          4
          (update-nth
            2
            (fn-sasl-initial-state :plain)
            (fn-own-conn-session
              (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*)))))
          (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*))))
        (fn-own-conns (fn-ocfg-owner *pcrt-selected*))))))
; Corrupted-session state: complete literal retained antecedent/conclusion.
(defconst
  *pcr-post-awaiting-mutant*
  (fn-ocfg-with-owner
    *pcrt-selected*
    (fn-own-set-conns
      (fn-ocfg-owner *pcrt-selected*)
      (fn-own-replace-conn
        (update-nth
          4
          (update-nth
            0
            (update-nth
              0
              (update-nth
                1
                t
                (fn-peer-session-base
                  (fn-auth-session-base
                    (fn-own-conn-session
                      (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*)))))))
              (fn-auth-session-base
                (fn-own-conn-session
                  (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*))))))
            (fn-own-conn-session
              (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*)))))
          (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*))))
        (fn-own-conns (fn-ocfg-owner *pcrt-selected*))))))
; Corrupted-state witness: every retained literal hypothesis and failed conclusion.
(defconst
  *pcr-reader-closed-mutant*
  (fn-ocfg-with-owner
    *pcrt-selected*
    (fn-own-set-conns
      (fn-ocfg-owner *pcrt-selected*)
      (fn-own-replace-conn
        (update-nth
          4
          (update-nth
            0
            (update-nth
              0
              (update-nth
                0
                (update-nth
                  0
                  nil
                  (fn-post-session-base
                    (fn-peer-session-base
                      (fn-auth-session-base
                        (fn-own-conn-session
                          (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*))))))))
                (fn-peer-session-base
                  (fn-auth-session-base
                    (fn-own-conn-session
                      (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*)))))))
              (fn-auth-session-base
                (fn-own-conn-session
                  (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*))))))
            (fn-own-conn-session
              (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*)))))
          (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*))))
        (fn-own-conns (fn-ocfg-owner *pcrt-selected*))))))
; Corrupted-state witness: every retained literal hypothesis and failed conclusion.
(defconst
  *pcr-short-line-mutant*
  (fn-ocfg-with-owner
    *pcrt-selected*
    (fn-own-set-conns
      (fn-ocfg-owner *pcrt-selected*)
      (fn-own-replace-conn
        (update-nth
          3
          (fn-wire-make-state
            :command
            nil
            0
            nil
            nil
            0
            2
            (fn-wire-state-body-limit
              (fn-own-conn-wire
                (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*))))))
          (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*))))
        (fn-own-conns (fn-ocfg-owner *pcrt-selected*))))))
; Corrupted-state witness: every retained literal hypothesis and failed conclusion.
(defconst
  *pcr-wide-line-mutant*
  (fn-ocfg-with-owner
    *pcrt-selected*
    (fn-own-set-conns
      (fn-ocfg-owner *pcrt-selected*)
      (fn-own-replace-conn
        (update-nth
          3
          (fn-wire-make-state
            :command
            nil
            0
            nil
            nil
            0
            1024
            (fn-wire-state-body-limit
              (fn-own-conn-wire
                (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*))))))
          (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*))))
        (fn-own-conns (fn-ocfg-owner *pcrt-selected*))))))
; Complete authentication hypothesis removal; corrupted-state.
(defconst
  *pcr-unauthenticated-mutant*
  (fn-ocfg-with-owner
    *pcrt-selected*
    (fn-own-set-conns
      (fn-ocfg-owner *pcrt-selected*)
      (fn-own-replace-conn
        (update-nth
          4
          (update-nth
            1
            (update-nth
              1
              t
              (fn-auth-session-config
                (fn-own-conn-session
                  (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*))))))
            (update-nth
              3
              nil
              (fn-own-conn-session
                (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*))))))
          (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*))))
        (fn-own-conns (fn-ocfg-owner *pcrt-selected*))))))
; Complete projection hypothesis removal; corrupted-state.
(defconst
  *pcr-unprojected-mutant*
  (fn-ocfg-with-owner
    *pcrt-selected*
    (fn-own-set-conns
      (fn-ocfg-owner *pcrt-selected*)
      (fn-own-replace-conn
        (update-nth
          4
          (update-nth
            0
            (update-nth
              0
              (update-nth
                0
                (update-nth
                  3
                  nil
                  (fn-post-session-base
                    (fn-peer-session-base
                      (fn-auth-session-base
                        (fn-own-conn-session
                          (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*))))))))
                (fn-peer-session-base
                  (fn-auth-session-base
                    (fn-own-conn-session
                      (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*)))))))
              (fn-auth-session-base
                (fn-own-conn-session
                  (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*))))))
            (fn-own-conn-session
              (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*)))))
          (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *pcrt-selected*))))
        (fn-own-conns (fn-ocfg-owner *pcrt-selected*))))))
