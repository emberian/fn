; Teeth for books/owner-served-invariants.lisp (v0 P2, P3, P5).
;
; For each keystone: a reachable witness at which every hypothesis and the
; conclusion hold, then per hypothesis one concrete value at which the other
; hypotheses hold, that hypothesis fails and the conclusion is false, each
; asserted positively and then closed with a must-fail on the conclusion.
; The fixtures are tests/acl2/owner-tests.lisp's served POST scenario.

(in-package "ACL2")
(local (include-book "owner-tests"))
(include-book "../../books/owner-served-invariants")
(include-book "std/testing/must-fail" :dir :system)

(assert-event (equal (symbol-class 'fn-own-finish (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-own-finish nil (w state))
                     '(fn-sn-statep (fn-own-store o))))

; -----------------------------------------------------------------------------
; P2: fn-own-240-follows-consumed-completion.

; The 240 line fn-own-outcome would render for connection `id' of `o'.
(defun osi-240-reply (o id)
  (let ((conn (fn-own-find-conn id (fn-own-conns o))))
    (fn-served-result-effects
     (fn-served-post-outcome
      (fn-served-make-conn (fn-own-conn-wire conn) (fn-own-conn-session conn)
                           (fn-own-conn-archive conn) (fn-own-conn-config conn)
                           (fn-own-conn-observation conn) (fn-own-clock o))
      :durable))))

(defun osi-p2-240p (o id)
  (equal (car (fn-own-outcome (cdr (fn-own-finish o)) id (car (fn-own-finish o))))
         (osi-240-reply (cdr (fn-own-finish o)) id)))

(defun osi-p2-conclusion (o id)
  (let* ((o2 (cdr (fn-own-finish o)))
         (word (car (fn-own-finish o)))
         (pair (fn-sf-completion (fn-sn-files (fn-own-store o))))
         (record (fn-sn-completion-record (fn-own-store o)))
         (sub (fn-own-inflight o)))
    (and (equal word :durable)
         sub
         (equal (fn-own-sub-id sub) id)
         (fn-sn-completion-enabledp (fn-own-store o))
         (equal (fn-own-store o2) (fn-sn-finish (fn-own-store o)))
         (equal (fn-sf-successes (fn-sn-files (fn-own-store o2)))
                (append (fn-sf-successes (fn-sn-files (fn-own-store o)))
                        (list pair)))
         (equal (fn-own-ledger o2) (append (fn-own-ledger o) (list pair)))
         (equal (fn-own-inflight o2) sub)
         (fn-record-p record)
         (equal (fn-record-msgid record)
                (fn-record-octets-string (fn-own-sub-msgid sub)))
         (equal (fn-record-payload record) (fn-own-sub-octets sub))
         (fn-sf-record-has-pairp pair (fn-sf-records (fn-sn-files (fn-own-store o2))))
         t)))

; The record the host should stage for the submission in flight: its
; Message-ID and octets, with the metadata own-record derives.
(defun osi-sub-record (sequence txid sub)
  (let ((msgid (fn-record-octets-string (fn-own-sub-msgid sub))))
    (fn-record-make sequence txid txid msgid (fn-own-sub-octets sub)
                    '("fn.letters")
                    (concatenate 'string "own-pin:" msgid)
                    (concatenate 'string "own-content:" msgid)
                    (concatenate 'string "own-release:" msgid)
                    2 841000000)))

(defun osi-drop-last (xs)
  (if (and (consp xs) (consp (cdr xs)))
      (cons (car xs) (osi-drop-last (cdr xs)))
    nil))

; Witness: connection 4's injected article, staged as itself, at :completing.
(defconst *osi-sub* (fn-own-inflight *own-taken*))
(defconst *osi-completing*
  (fn-own-run *own-taken*
              (osi-drop-last (own-post-events (osi-sub-record 2 2 *osi-sub*)))))
(assert-event (fn-own-relation *osi-completing*))
(assert-event (fn-sn-completion-enabledp (fn-own-store *osi-completing*)))
(assert-event (equal (car (fn-own-finish *osi-completing*)) :durable))
(assert-event (osi-p2-240p *osi-completing* 4))
(assert-event (equal (fn-served-reply-octets
                      (car (fn-own-outcome (cdr (fn-own-finish *osi-completing*)) 4
                                           (car (fn-own-finish *osi-completing*)))))
                     (append (fn-nntp-string-octets "240 article received OK") '(13 10))))
(assert-event (osi-p2-conclusion *osi-completing* 4))
; The finish is the (:complete) event on the owner.
(assert-event (equal (cdr (fn-own-finish *osi-completing*))
                     (fn-own-step *osi-completing* '(:complete))))

; FINDING (P2).  With the host's word, 240 is rendered over a completion of
; another record.  owner-tests' *own-p-done* completed <three@example> for
; the injected "Hello, news." submission of connection 4, and *own-240* is
; the 240.  fn-own-finish over the same state answers :fault, so the outcome
; is the uncertain 441.
(defconst *osi-mismatch-completing*
  (fn-own-run *own-taken*
              (osi-drop-last (own-post-events (own-record 2 2 "<three@example>")))))
(assert-event (equal (fn-own-step *osi-mismatch-completing* '(:complete)) *own-p-done*))
(assert-event (equal (fn-served-reply-octets (car *own-240*))
                     (append (fn-nntp-string-octets "240 article received OK") '(13 10))))
(assert-event (equal (fn-record-msgid (fn-sn-completion-record
                                       (fn-own-store *osi-mismatch-completing*)))
                     "<three@example>"))
(assert-event (not (equal (fn-record-octets-string (fn-own-sub-msgid *osi-sub*))
                          "<three@example>")))
(assert-event (not (equal (fn-record-payload (fn-sn-completion-record
                                              (fn-own-store *osi-mismatch-completing*)))
                          (fn-own-sub-octets *osi-sub*))))
(assert-event (equal (car (fn-own-finish *osi-mismatch-completing*)) :fault))
(assert-event (equal (fn-own-take 4 (fn-served-reply-octets
                                     (car (fn-own-outcome
                                           (cdr (fn-own-finish *osi-mismatch-completing*)) 4
                                           (car (fn-own-finish *osi-mismatch-completing*))))))
                     (fn-nntp-string-octets "441 ")))

; Hypothesis 2 (the reply is 240).  *own-taken*: related, nothing staged,
; the finish is :fault and the reply the uncertain 441.
(assert-event (fn-own-relation *own-taken*))
(assert-event (not (osi-p2-240p *own-taken* 4)))
(assert-event (not (osi-p2-conclusion *own-taken* 4)))
(must-fail (assert-event (osi-p2-conclusion *own-taken* 4)))

; Hypothesis 1 (the relation).  Connection 4's session replaced by a
; malformed one: every completion renders the same 403, so the reply equals
; the reference 240 expression while the finish word is :fault.
(defconst *osi-bad-conn*
  (let ((conn (fn-own-find-conn 4 (fn-own-conns *own-taken*))))
    (fn-own-conn-make-group-indexed 4 (fn-own-conn-version conn)
                                    (fn-own-conn-frontier conn)
                                    (fn-own-conn-wire conn) nil
                                    (fn-own-conn-archive conn)
                                    (fn-own-conn-config conn)
                                    (fn-own-conn-observation conn)
                                    (fn-own-conn-verdicts conn)
                                    (fn-own-conn-index conn)
                                    (fn-own-conn-group-index conn))))
(defconst *osi-unrelated*
  (fn-own-set-conns *own-taken*
                    (fn-own-replace-conn *osi-bad-conn* (fn-own-conns *own-taken*))))
(assert-event (not (fn-own-relation *osi-unrelated*)))
(assert-event (osi-p2-240p *osi-unrelated* 4))
(assert-event (not (osi-p2-conclusion *osi-unrelated* 4)))
(must-fail (assert-event (osi-p2-conclusion *osi-unrelated* 4)))

; -----------------------------------------------------------------------------
; P3: fn-own-pinned-view-survives-other-post.

(defun osi-oc (o) (fn-ocfg-make o *own-config* nil nil))

(defun osi-after-post (oc events sub-id word)
  (let ((oc1 (fn-ocfg-run oc events)))
    (fn-ocfg-with-owner oc1 (cdr (fn-own-outcome (fn-ocfg-owner oc1) sub-id word)))))

(defun osi-p3-conclusion (oc events sub-id word id octets)
  (let ((oc2 (osi-after-post oc events sub-id word)))
    (and (equal (fn-own-tls-result-effects (fn-ocfg-read-tls-prefix oc2 id octets))
                (fn-own-tls-result-effects (fn-ocfg-read-tls-prefix oc id octets)))
         (equal (fn-own-tls-result-consumed (fn-ocfg-read-tls-prefix oc2 id octets))
                (fn-own-tls-result-consumed (fn-ocfg-read-tls-prefix oc id octets))))))

(defun osi-reader-p (oc id)
  (not (fn-peer-session-cfg
        (fn-auth-session-base
         (fn-own-conn-session (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))))))

(defconst *osi-q* (osi-oc *own-q*))
(defconst *osi-post-events*
  (cons '(:take) (own-post-events (osi-sub-record 2 2 *osi-sub*))))
(defconst *osi-group* *own-group-octets*)

; Witness: reader 3 pinned at version 2; connection 4's POST is taken,
; staged, completed and answered 240; the view the store publishes moves to
; version 3, and reader 3's GROUP answers exactly as before.
(assert-event (fn-ocfg-writer-eventsp *osi-post-events*))
(assert-event (osi-reader-p *osi-q* 3))
(assert-event (fn-own-find-conn 3 (fn-own-conns *own-q*)))
(assert-event (equal (fn-own-conn-version (fn-own-find-conn 3 (fn-own-conns *own-q*))) 2))
(assert-event (equal (fn-own-view-version
                      (fn-own-view (fn-ocfg-owner (osi-after-post *osi-q* *osi-post-events*
                                                                  4 :durable))))
                     3))
(assert-event (equal (fn-own-take 4 (fn-served-reply-octets
                                     (car (fn-own-outcome
                                           (fn-ocfg-owner (fn-ocfg-run *osi-q* *osi-post-events*))
                                           4 :durable))))
                     (fn-nntp-string-octets "240 ")))
(assert-event (osi-p3-conclusion *osi-q* *osi-post-events* 4 :durable 3 *osi-group*))
(assert-event (consp (fn-served-reply-octets
                      (fn-own-tls-result-effects
                       (fn-ocfg-read-tls-prefix *osi-q* 3 *osi-group*)))))

; Hypothesis (not (equal id sub-id)).  The poster itself is re-pinned by
; the 240, and its GROUP now counts its own article.
(assert-event (osi-reader-p *osi-q* 4))
(assert-event (not (osi-p3-conclusion *osi-q* *osi-post-events* 4 :durable 4 *osi-group*)))
(must-fail (assert-event (osi-p3-conclusion *osi-q* *osi-post-events* 4 :durable 4 *osi-group*)))

; Hypothesis (fn-ocfg-writer-eventsp events).  An (:advance 3) among the
; events re-pins reader 3 itself.
(defconst *osi-advance-events* (append *osi-post-events* '((:advance 3))))
(assert-event (not (fn-ocfg-writer-eventsp *osi-advance-events*)))
(assert-event (not (osi-p3-conclusion *osi-q* *osi-advance-events* 4 :durable 3 *osi-group*)))
(must-fail (assert-event (osi-p3-conclusion *osi-q* *osi-advance-events* 4 :durable 3 *osi-group*)))

; Hypothesis (reader connection).  A peer connection opened before the post
; answers IHAVE from the live node: 335 before, 435 after.  The post here
; is owner-tests' CLI post by connection 1.
(defconst *osi-peered* (osi-oc *own-peered-begun*))
(defconst *osi-peer-events* (own-post-events (own-record 0 0 "<one@example>")))
(assert-event (fn-ocfg-writer-eventsp *osi-peer-events*))
(assert-event (not (osi-reader-p *osi-peered* *own-peer-id*)))
(assert-event (not (equal *own-peer-id* 1)))
(assert-event (not (osi-p3-conclusion *osi-peered* *osi-peer-events* 1 :durable
                                      *own-peer-id* *own-ihave-octets*)))
(must-fail (assert-event (osi-p3-conclusion *osi-peered* *osi-peer-events* 1 :durable
                                            *own-peer-id* *own-ihave-octets*)))

; -----------------------------------------------------------------------------
; P5: the bound, and the fault wrapper.

(defconst *osi-open0*
  (fn-ocfg-make (fn-own-start (fn-sn-initial *own-groups* 10) 2) *own-peer-cfg* nil nil))
(defconst *osi-full* (cdr (fn-ocfg-open (cdr (fn-ocfg-open *osi-open0* nil)) nil)))
(assert-event (fn-ocfg-statep *osi-full*))
(assert-event (equal (len (fn-own-conns (fn-ocfg-owner *osi-full*))) 2))
(assert-event (equal (fn-own-max-conns (fn-ocfg-owner *osi-full*)) 2))
(assert-event (equal (fn-ocfg-open *osi-full* nil) (cons nil *osi-full*)))

; Hypothesis (the bound is reached).  Below it the open succeeds: a greeting
; and a new connection.
(assert-event (fn-ocfg-statep *osi-open0*))
(assert-event (< (len (fn-own-conns (fn-ocfg-owner *osi-open0*)))
                 (fn-own-max-conns (fn-ocfg-owner *osi-open0*))))
(assert-event (consp (car (fn-ocfg-open *osi-open0* nil))))
(must-fail (assert-event (equal (fn-ocfg-open *osi-open0* nil) (cons nil *osi-open0*))))

; Hypothesis (fn-ocfg-statep).  The same full owner with its identifier
; counter wound back onto an open connection: the refused open still writes
; that connection's reader context and pin.
(defconst *osi-wound*
  (let ((o (fn-ocfg-owner *osi-full*)))
    (fn-ocfg-make (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                               0 (fn-own-max-conns o) (fn-own-pending o)
                               (fn-own-ledger o) (fn-own-clock o) (fn-own-facts o)
                               (fn-own-config o) (fn-own-queue o) (fn-own-inflight o)
                               (fn-own-feeds o))
                  (fn-ocfg-config *osi-full*) nil nil)))
(assert-event (not (fn-ocfg-statep *osi-wound*)))
(assert-event (<= (fn-own-max-conns (fn-ocfg-owner *osi-wound*))
                  (len (fn-own-conns (fn-ocfg-owner *osi-wound*)))))
(assert-event (not (equal (fn-ocfg-open *osi-wound* nil) (cons nil *osi-wound*))))
(must-fail (assert-event (equal (fn-ocfg-open *osi-wound* nil) (cons nil *osi-wound*))))

; The fault wrapper: its equation at a reachable connection, and K-FAULT-2
; over it.  The one hypothesis, other /= id: the faulted connection itself
; is gone.
(defconst *osi-faulted* (fn-ocfg-fault *osi-full* 0))
(assert-event (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *osi-full*))))
(assert-event (fn-own-find-conn 1 (fn-own-conns (fn-ocfg-owner *osi-full*))))
(assert-event (consp (car *osi-faulted*)))
(assert-event (equal (car *osi-faulted*) (car (fn-own-fault (fn-ocfg-owner *osi-full*) 0))))
(assert-event (equal (fn-ocfg-owner (cdr *osi-faulted*))
                     (cdr (fn-own-fault (fn-ocfg-owner *osi-full*) 0))))
(assert-event (equal (fn-own-find-conn 1 (fn-own-conns (fn-ocfg-owner (cdr *osi-faulted*))))
                     (fn-own-find-conn 1 (fn-own-conns (fn-ocfg-owner *osi-full*)))))
(assert-event (fn-ocfg-pin-find 1 (fn-ocfg-pins (cdr *osi-faulted*))))
(assert-event (equal (fn-ocfg-pin-find 1 (fn-ocfg-pins (cdr *osi-faulted*)))
                     (fn-ocfg-pin-find 1 (fn-ocfg-pins *osi-full*))))
(assert-event (not (equal (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner (cdr *osi-faulted*))))
                          (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *osi-full*))))))
(must-fail (assert-event
            (equal (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner (cdr *osi-faulted*))))
                   (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *osi-full*))))))
