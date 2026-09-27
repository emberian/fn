; The per-peer contact cursor (PRF-226; gpt-6's consolidation review 6,
; "per-peer ready queues/cursors ... criterion: whole operation and whole
; drain"; spec bp-node-machine 7.6).
;
; fn-bpnj-contact-next (books/bp-node-job-offer.lisp) answers one ask in one
; traversal, but every ask starts at the head of the job list, walks the
; whole list once more for the gate's ready-peer set, and re-reads every
; offered key: a contact that offers N jobs costs N traversals.  The cursor
; here is a resumable position into the job list, carried by the host
; between asks (as it carries OFFERED) and, per peer, between contacts:
;
;   (F C HELD)   F  the peer's frontier: every job ahead of it is settled
;                   for the peer (another peer's, or :forwarded/:expired,
;                   which no lifecycle record changes);
;                C  the contact's position: no job ahead of it is ready on
;                   this contact, and every key the contact offered is ahead
;                   of it;
;                HELD  the first held candidate ahead of C (the answer the
;                   head-restarting scan would remember).
;
; fn-bpnjc-contact-next examines the jobs from C on, each once, and answers
; exactly what fn-bpnj-contact-next answers (fn-bpnjc-contact-next-is-the-
; head-scan) under the relation fn-bpnjc-contact-relp, which the contact's
; opening establishes from the frontier (fn-bpnjc-open-establishes-the-
; relation), each offer re-establishes for the next ask
; (fn-bpnjc-offer-keeps-the-relation), and the machine's own change of the
; job list between asks preserves (fn-bpnjc-evolution-keeps-the-relation).
; The drain keystone (fn-bpnjc-drain-is-the-head-drain) composes them over
; a contact; the work bound: an ask examines exactly the positions its cursor
; advances over, so a contact examines each job from F on at most once.
(in-package "ACL2")
(include-book "bp-node-job-offer")

;; ---------------------------------------------------------------------
;; Positions.

(defun fn-bpnjc-prefix (n l)
  (declare (xargs :guard (natp n)))
  (if (or (zp n) (atom l))
      nil
    (cons (car l) (fn-bpnjc-prefix (1- n) (cdr l)))))

(defun fn-bpnjc-drop (n l)
  (declare (xargs :guard (natp n)))
  (if (or (zp n) (atom l))
      l
    (fn-bpnjc-drop (1- n) (cdr l))))

(defthm fn-bpnjc-prefix-and-drop
  (equal (append (fn-bpnjc-prefix n l) (fn-bpnjc-drop n l)) l))

(defthm fn-bpnjc-member-of-drop
  (implies (member-equal x (fn-bpnjc-drop n l))
           (member-equal x l)))

(defthm fn-bpnjc-member-of-prefix
  (implies (member-equal x (fn-bpnjc-prefix n l))
           (member-equal x l)))

;; ---------------------------------------------------------------------
;; The head scan's two answers without the own-entry lookup (logic only:
;; the specification the cursor scan is proved against).

(defun fn-bpnjc-first-ready (rest peer routing offered)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom rest)
      nil
    (if (fn-bpnj-readyp (car rest) peer routing offered)
        (car rest)
      (fn-bpnjc-first-ready (cdr rest) peer routing offered))))

(defun fn-bpnjc-first-held (rest peer routing offered)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom rest)
      nil
    (if (and (fn-bpnj-candidatep (car rest) peer offered)
             (not (fn-bpnj-readyp (car rest) peer routing offered)))
        (car rest)
      (fn-bpnjc-first-held (cdr rest) peer routing offered))))

(defun fn-bpnjc-own-entries-p (rest jobs)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom rest)
      t
    (and (fn-bpnj-own-entryp (car rest) jobs)
         (fn-bpnjc-own-entries-p (cdr rest) jobs))))

(defthm fn-bpnjc-sublist-entries-are-own
  (implies (and (fn-bpn-job-listp jobs)
                (subsetp-equal rest jobs))
           (fn-bpnjc-own-entries-p rest jobs))
  :hints (("Goal" :induct (fn-bpnjc-own-entries-p rest jobs)
           :in-theory (union-theories '(fn-bpnjc-own-entries-p subsetp-equal
                                        fn-bpnj-unique-keys-make-every-job-its-own-entry)
                                      (theory 'minimal-theory)))))

(defthm fn-bpnjc-select-is-first-ready
  (implies (fn-bpnjc-own-entries-p rest jobs)
           (equal (fn-bpnj-select rest jobs peer routing offered)
                  (fn-bpnjc-first-ready rest peer routing offered)))
  :hints (("Goal" :induct (fn-bpnjc-own-entries-p rest jobs)
           :in-theory (union-theories '(fn-bpnjc-own-entries-p fn-bpnj-own-entryp fn-bpnj-select
                                        fn-bpnjc-first-ready)
                                      (theory 'minimal-theory)))))

(defthm fn-bpnjc-held-is-first-held
  (implies (fn-bpnjc-own-entries-p rest jobs)
           (equal (fn-bpnj-held rest jobs peer routing offered)
                  (fn-bpnjc-first-held rest peer routing offered)))
  :hints (("Goal" :induct (fn-bpnjc-own-entries-p rest jobs)
           :in-theory (union-theories '(fn-bpnjc-own-entries-p fn-bpnj-own-entryp fn-bpnj-held
                                        fn-bpnjc-first-held)
                                      (theory 'minimal-theory)))))

(defthm fn-bpnjc-first-ready-of-append
  (equal (fn-bpnjc-first-ready (append a b) peer routing offered)
         (or (fn-bpnjc-first-ready a peer routing offered)
             (fn-bpnjc-first-ready b peer routing offered))))

(defthm fn-bpnjc-first-held-of-append
  (equal (fn-bpnjc-first-held (append a b) peer routing offered)
         (or (fn-bpnjc-first-held a peer routing offered)
             (fn-bpnjc-first-held b peer routing offered))))

;; ---------------------------------------------------------------------
;; The cursor scan: no offered keys, no own-entry lookup, a position count.

(verify-guards fn-bpnj-offerable)

(defun fn-bpnjc-candp (job peer)
  (declare (xargs :guard t))
  (and (equal (fn-bpn-job-status job) :queued)
       (equal (fn-bpn-job-peer job) peer)))

(defun fn-bpnjc-sendp (job peer routing)
  (declare (xargs :guard t))
  (equal (fn-cbor-ag-car (fn-bpnj-offerable job peer routing)) :send))

; Examine REST from position N: answer (mv READY HELD POSITION), READY the
; first job queued for PEER whose routing sends it, HELD the first queued
; one it holds (or the HELD given), POSITION one past the last job examined.
(defun fn-bpnjc-scan (rest peer routing held n)
  (declare (xargs :guard (natp n)))
  (if (atom rest)
      (mv nil held n)
    (let ((job (car rest)))
      (cond ((not (fn-bpnjc-candp job peer))
             (fn-bpnjc-scan (cdr rest) peer routing held (+ 1 n)))
            ((fn-bpnjc-sendp job peer routing)
             (mv job held (+ 1 n)))
            (t (fn-bpnjc-scan (cdr rest) peer routing (or held job) (+ 1 n)))))))

(defun fn-bpnjc-unoffered-p (rest offered)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom rest)
      t
    (and (not (member-equal (fn-bpn-job-key (car rest)) offered))
         (fn-bpnjc-unoffered-p (cdr rest) offered))))

(defthm fn-bpnjc-candidate-unoffered
  (implies (not (member-equal (fn-bpn-job-key job) offered))
           (and (equal (fn-bpnj-candidatep job peer offered)
                       (fn-bpnjc-candp job peer))
                (equal (fn-bpnj-readyp job peer routing offered)
                       (and (fn-bpnjc-candp job peer)
                            (fn-bpnjc-sendp job peer routing)))))
  :hints (("Goal" :in-theory (enable fn-bpnj-candidatep fn-bpnj-readyp))))

(defthm fn-bpnjc-scan-finds-the-first-ready
  (implies (fn-bpnjc-unoffered-p rest offered)
           (equal (mv-nth 0 (fn-bpnjc-scan rest peer routing held n))
                  (fn-bpnjc-first-ready rest peer routing offered))))

(defthm fn-bpnjc-scan-finds-the-first-held
  (implies (and (fn-bpnjc-unoffered-p rest offered)
                (not (fn-bpnjc-first-ready rest peer routing offered)))
           (equal (mv-nth 1 (fn-bpnjc-scan rest peer routing held n))
                  (or held (fn-bpnjc-first-held rest peer routing offered)))))

;; The work: an ask examines exactly the positions it advances over, never
;; more than the rest of the list, and an offer advances at least one.
(defthm fn-bpnjc-scan-position-bounds
  (implies (natp n)
           (and (natp (mv-nth 2 (fn-bpnjc-scan rest peer routing held n)))
                (<= n (mv-nth 2 (fn-bpnjc-scan rest peer routing held n)))
                (<= (mv-nth 2 (fn-bpnjc-scan rest peer routing held n))
                    (+ n (len rest)))
                (implies (mv-nth 0 (fn-bpnjc-scan rest peer routing held n))
                         (< n (mv-nth 2 (fn-bpnjc-scan rest peer routing held n))))))
  :rule-classes (:rewrite (:linear :corollary
                           (implies (natp n)
                                    (and (<= n (mv-nth 2 (fn-bpnjc-scan rest peer routing held n)))
                                         (<= (mv-nth 2 (fn-bpnjc-scan rest peer routing held n))
                                             (+ n (len rest))))))))

;; ---------------------------------------------------------------------
;; Unique keys: a key ahead of C is not a key from C on.

(defun fn-bpnjc-keys (jobs)
  (declare (xargs :guard t))
  (if (atom jobs) nil
    (cons (fn-bpn-job-key (car jobs)) (fn-bpnjc-keys (cdr jobs)))))

(defthm fn-bpnjc-key-member-is-find-job
  (implies (fn-bpn-job-listp jobs)
           (iff (member-equal key (fn-bpnjc-keys jobs))
                (fn-bpn-find-job key jobs)))
  :hints (("Goal" :induct (fn-bpnjc-keys jobs)
           :in-theory (e/d (fn-bpn-find-job fn-bpn-job-listp)
                           (fn-bpn-jobp fn-bpn-job-key)))
          ("Subgoal *1/1" :in-theory (e/d (fn-bpn-find-job fn-bpn-job-listp fn-bpn-jobp)
                                          (fn-bpn-job-key)))))

(defthm fn-bpnjc-job-list-keys-are-distinct
  (implies (fn-bpn-job-listp jobs)
           (no-duplicatesp-equal (fn-bpnjc-keys jobs)))
  :hints (("Goal" :induct (fn-bpnjc-keys jobs)
           :in-theory (e/d (fn-bpn-job-listp fn-bpn-job-key-memberp)
                           (fn-bpn-jobp fn-bpn-job-key)))))

(defthm fn-bpnjc-keys-of-append
  (equal (fn-bpnjc-keys (append a b))
         (append (fn-bpnjc-keys a) (fn-bpnjc-keys b))))

(defthm fn-bpnjc-member-of-append
  (iff (member-equal k (append x y))
       (or (member-equal k x) (member-equal k y))))

(defthm fn-bpnjc-distinct-halves
  (implies (and (no-duplicatesp-equal (append x y))
                (member-equal k x))
           (not (member-equal k y)))
  :rule-classes nil)

(defthm fn-bpnjc-prefix-key-is-not-a-drop-key
  (implies (and (fn-bpn-job-listp jobs)
                (member-equal key (fn-bpnjc-keys (fn-bpnjc-prefix c jobs))))
           (not (member-equal key (fn-bpnjc-keys (fn-bpnjc-drop c jobs)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnjc-job-list-keys-are-distinct)
                 (:instance fn-bpnjc-distinct-halves
                  (x (fn-bpnjc-keys (fn-bpnjc-prefix c jobs)))
                  (y (fn-bpnjc-keys (fn-bpnjc-drop c jobs))) (k key))
                 (:instance fn-bpnjc-keys-of-append
                  (a (fn-bpnjc-prefix c jobs)) (b (fn-bpnjc-drop c jobs))))
           :in-theory (union-theories '(fn-bpnjc-prefix-and-drop)
                                      (theory 'minimal-theory)))))

(defthm fn-bpnjc-unoffered-from-keys
  (implies (not (intersectp-equal (fn-bpnjc-keys rest) offered))
           (fn-bpnjc-unoffered-p rest offered))
  :hints (("Goal" :induct (fn-bpnjc-keys rest)
           :in-theory (e/d (intersectp-equal) (fn-bpn-job-key)))))

(defthm fn-bpnjc-distinct-halves-are-disjoint
  (implies (no-duplicatesp-equal (append x y))
           (not (intersectp-equal x y)))
  :rule-classes nil)

(defthm fn-bpnjc-disjoint-member
  (implies (and (member-equal a x) (not (intersectp-equal x y)))
           (not (member-equal a y))))

(defthm fn-bpnjc-intersectp-of-cons
  (iff (intersectp-equal y (cons a o))
       (or (member-equal a y) (intersectp-equal y o))))

(defthm fn-bpnjc-disjoint-from-a-subset
  (implies (and (subsetp-equal o x)
                (not (intersectp-equal x y)))
           (not (intersectp-equal y o)))
  :hints (("Goal" :induct (len o)))
  :rule-classes nil)

(defthm fn-bpnjc-drop-is-unoffered
  (implies (and (fn-bpn-job-listp jobs)
                (subsetp-equal offered (fn-bpnjc-keys (fn-bpnjc-prefix c jobs))))
           (fn-bpnjc-unoffered-p (fn-bpnjc-drop c jobs) offered))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnjc-job-list-keys-are-distinct)
                 (:instance fn-bpnjc-distinct-halves-are-disjoint
                  (x (fn-bpnjc-keys (fn-bpnjc-prefix c jobs)))
                  (y (fn-bpnjc-keys (fn-bpnjc-drop c jobs))))
                 (:instance fn-bpnjc-keys-of-append
                  (a (fn-bpnjc-prefix c jobs)) (b (fn-bpnjc-drop c jobs)))
                 (:instance fn-bpnjc-disjoint-from-a-subset
                  (o offered) (x (fn-bpnjc-keys (fn-bpnjc-prefix c jobs)))
                  (y (fn-bpnjc-keys (fn-bpnjc-drop c jobs))))
                 (:instance fn-bpnjc-unoffered-from-keys (rest (fn-bpnjc-drop c jobs))))
           :in-theory (union-theories '(fn-bpnjc-prefix-and-drop)
                                      (theory 'minimal-theory)))))

;; ---------------------------------------------------------------------
;; The gate without the ready-peer walk.

(defun fn-bpnjc-gatep (st peer)
  (declare (xargs :guard t))
  (let ((base (fn-bpnf-base st)))
    (and (fn-bpp-eidp peer)
         (not (fn-bpnf-issued st))
         (not (fn-bpah-delivery-uncertainp st))
         (not (fn-bpn-machine-state-fenced base))
         (not (fn-bpn-machine-state-pending base)))))

(defthm fn-bpnjc-queued-peer-is-ready
  (implies (and (member-equal job jobs)
                (fn-bpnjc-candp job peer))
           (fn-bpn-member peer (fn-bpn-ready-peers jobs)))
  :hints (("Goal" :in-theory (enable fn-bpn-ready-peers))))

(defthm fn-bpnjc-gate-is-the-contact-gate
  (iff (fn-bpnp-receipt-contact-event st peer)
       (and (fn-bpnjc-gatep st peer)
            (fn-bpn-member peer (fn-bpn-ready-peers
                                 (fn-bpn-machine-state-jobs (fn-bpnf-base st))))))
  :hints (("Goal" :in-theory (union-theories '(fn-bpnp-receipt-contact-event fn-bpnjc-gatep)
                                             (theory 'minimal-theory))))
  :rule-classes nil)

;; ---------------------------------------------------------------------
;; The ask.

(defun fn-bpnjc-contact-next (st peer routing offered cursor)
  (declare (xargs :guard t))
  (let ((f (nfix (fn-bpn-nth 0 cursor)))
        (c (nfix (fn-bpn-nth 1 cursor)))
        (held (fn-bpn-nth 2 cursor)))
    (if (not (fn-bpnjc-gatep st peer))
        (cons (list :close) (list f c held))
      (mv-let (job held2 c2)
        (fn-bpnjc-scan (fn-bpnjc-drop c (fn-bpn-machine-state-jobs (fn-bpnf-base st)))
                       peer routing held c)
        (cond (job (cons (list :offer
                               (list :contact-job peer (fn-bpn-job-key job))
                               (cons (fn-bpn-job-key job) offered)
                               (fn-bpn-nth 1 (fn-bpnj-offerable job peer routing)))
                         (list f c2 held2)))
              (held2 (cons (list :held (fn-bpn-job-key held2)
                                 (fn-bpn-nth 1 (fn-bpnj-offerable held2 peer routing)))
                           (list f c2 held2)))
              (t (cons (list :close) (list f c2 held2))))))))

; The relation the host's cursor keeps with the job list it asks at: no job
; ahead of position C is ready on this contact, HELD is the first held one
; ahead of it, and every key the contact offered is ahead of it.
(defun fn-bpnjc-cursor-relp (jobs peer routing offered c held)
  (declare (xargs :guard t :verify-guards nil))
  (let ((pre (fn-bpnjc-prefix (nfix c) jobs)))
    (and (fn-bpn-job-listp jobs)
         (<= (nfix c) (len jobs))
         (not (fn-bpnjc-first-ready pre peer routing offered))
         (equal held (fn-bpnjc-first-held pre peer routing offered))
         (subsetp-equal offered (fn-bpnjc-keys pre)))))

(defun fn-bpnjc-contact-relp (st peer routing offered cursor)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnjc-cursor-relp (fn-bpn-machine-state-jobs (fn-bpnf-base st))
                        peer routing offered
                        (nfix (fn-bpn-nth 1 cursor)) (fn-bpn-nth 2 cursor)))

(defthm fn-bpnjc-candidate-is-candp
  (implies (fn-bpnj-candidatep job peer offered)
           (fn-bpnjc-candp job peer))
  :hints (("Goal" :in-theory (enable fn-bpnj-candidatep))))

(defthm fn-bpnjc-ready-is-candidate
  (implies (fn-bpnj-readyp job peer routing offered)
           (fn-bpnj-candidatep job peer offered))
  :hints (("Goal" :in-theory (enable fn-bpnj-readyp))))

(defthm fn-bpnjc-ready-is-candp
  (implies (fn-bpnj-readyp job peer routing offered)
           (fn-bpnjc-candp job peer))
  :hints (("Goal" :in-theory (enable fn-bpnj-readyp fn-bpnj-candidatep))))

(defthm fn-bpnjc-first-ready-is-a-queued-member
  (implies (fn-bpnjc-first-ready rest peer routing offered)
           (and (member-equal (fn-bpnjc-first-ready rest peer routing offered) rest)
                (fn-bpnjc-candp (fn-bpnjc-first-ready rest peer routing offered) peer)))
  :hints (("Goal" :induct (fn-bpnjc-first-ready rest peer routing offered)
           :in-theory (disable fn-bpnjc-candp fn-bpnj-candidatep))))

(defthm fn-bpnjc-first-held-is-a-queued-member
  (implies (fn-bpnjc-first-held rest peer routing offered)
           (and (member-equal (fn-bpnjc-first-held rest peer routing offered) rest)
                (fn-bpnjc-candp (fn-bpnjc-first-held rest peer routing offered) peer)))
  :hints (("Goal" :induct (fn-bpnjc-first-held rest peer routing offered)
           :in-theory (disable fn-bpnjc-candp fn-bpnj-candidatep))))

(defthm fn-bpnjc-subsetp-reflexive
  (subsetp-equal x x))

; The scan's two answers over the whole list, split at the cursor.
(defthm fn-bpnjc-head-answers-at-the-cursor
  (implies (fn-bpnjc-cursor-relp jobs peer routing offered c held)
           (and (equal (fn-bpnj-select jobs jobs peer routing offered)
                       (fn-bpnjc-first-ready (fn-bpnjc-drop (nfix c) jobs) peer routing offered))
                (equal (fn-bpnj-held jobs jobs peer routing offered)
                       (or held
                           (fn-bpnjc-first-held (fn-bpnjc-drop (nfix c) jobs) peer routing offered)))
                (fn-bpnjc-unoffered-p (fn-bpnjc-drop (nfix c) jobs) offered)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnjc-first-ready-of-append
                  (a (fn-bpnjc-prefix (nfix c) jobs)) (b (fn-bpnjc-drop (nfix c) jobs)))
                 (:instance fn-bpnjc-first-held-of-append
                  (a (fn-bpnjc-prefix (nfix c) jobs)) (b (fn-bpnjc-drop (nfix c) jobs)))
                 (:instance fn-bpnjc-drop-is-unoffered (c (nfix c)))
                 (:instance fn-bpnjc-sublist-entries-are-own (rest jobs))
                 (:instance fn-bpnjc-select-is-first-ready (rest jobs))
                 (:instance fn-bpnjc-held-is-first-held (rest jobs))
                 (:instance fn-bpnjc-subsetp-reflexive (x jobs))
                 (:instance fn-bpnjc-prefix-and-drop (n (nfix c)) (l jobs)))
           :in-theory (union-theories '(fn-bpnjc-cursor-relp)
                                      (theory 'minimal-theory))))
  :rule-classes nil)

(defthm fn-bpnjc-nfix-nfix
  (equal (nfix (nfix x)) (nfix x)))

(defthm fn-bpnjc-position-is-natural
  (and (natp (nfix x))
       (equal (nfix (+ (nfix x) (len l))) (+ (nfix x) (len l)))))

;; The cursor scan's answers at the job-list level.
(defthm fn-bpnjc-scan-answers-the-head-scan
  (implies (fn-bpnjc-cursor-relp jobs peer routing offered c held)
           (and (equal (mv-nth 0 (fn-bpnjc-scan (fn-bpnjc-drop (nfix c) jobs) peer routing held n))
                       (fn-bpnj-select jobs jobs peer routing offered))
                (implies (not (fn-bpnj-select jobs jobs peer routing offered))
                         (equal (mv-nth 1 (fn-bpnjc-scan (fn-bpnjc-drop (nfix c) jobs)
                                                         peer routing held n))
                                (fn-bpnj-held jobs jobs peer routing offered)))
                (implies (fn-bpnj-select jobs jobs peer routing offered)
                         (fn-bpn-member peer (fn-bpn-ready-peers jobs)))
                (implies (fn-bpnj-held jobs jobs peer routing offered)
                         (fn-bpn-member peer (fn-bpn-ready-peers jobs)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnjc-head-answers-at-the-cursor)
                 (:instance fn-bpnjc-scan-finds-the-first-ready
                  (rest (fn-bpnjc-drop (nfix c) jobs)))
                 (:instance fn-bpnjc-scan-finds-the-first-held
                  (rest (fn-bpnjc-drop (nfix c) jobs)))
                 (:instance fn-bpnjc-first-ready-is-a-queued-member
                  (rest (fn-bpnjc-drop (nfix c) jobs)))
                 (:instance fn-bpnjc-first-held-is-a-queued-member
                  (rest (fn-bpnjc-drop (nfix c) jobs)))
                 (:instance fn-bpnjc-first-held-is-a-queued-member
                  (rest (fn-bpnjc-prefix (nfix c) jobs)))
                 (:instance fn-bpnjc-member-of-drop
                  (n (nfix c)) (l jobs)
                  (x (fn-bpnjc-first-ready (fn-bpnjc-drop (nfix c) jobs) peer routing offered)))
                 (:instance fn-bpnjc-member-of-drop
                  (n (nfix c)) (l jobs)
                  (x (fn-bpnjc-first-held (fn-bpnjc-drop (nfix c) jobs) peer routing offered)))
                 (:instance fn-bpnjc-member-of-prefix
                  (n (nfix c)) (l jobs) (x held))
                 (:instance fn-bpnjc-queued-peer-is-ready
                  (job (fn-bpnjc-first-ready (fn-bpnjc-drop (nfix c) jobs) peer routing offered)))
                 (:instance fn-bpnjc-queued-peer-is-ready
                  (job (fn-bpnjc-first-held (fn-bpnjc-drop (nfix c) jobs) peer routing offered)))
                 (:instance fn-bpnjc-queued-peer-is-ready (job held)))
           :in-theory (union-theories '(fn-bpnjc-cursor-relp)
                                      (theory 'minimal-theory)))))

;; KEYSTONE (the cursor answers the head scan's question).  Under the
;; relation the host's cursor keeps, the ask host/native/bp-service.lisp
;; fnn-bpc-drive-contact makes before every offer (fn-bpnjc-contact-next)
;; answers exactly what fn-bpnj-contact-next answers, so every theorem of
;; PRF-120 and PRF-079 about the head scan (the fair selection, no
;; starvation, each job offered at most once per contact, the routed hop) is
;; a theorem about the cursor's answer.
(defthm fn-bpnjc-contact-next-is-the-head-scan
  (implies (fn-bpnjc-contact-relp st peer routing offered cursor)
           (equal (car (fn-bpnjc-contact-next st peer routing offered cursor))
                  (fn-bpnj-contact-next st peer routing offered)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnjc-scan-answers-the-head-scan
                  (jobs (fn-bpn-machine-state-jobs (fn-bpnf-base st)))
                  (c (nfix (fn-bpn-nth 1 cursor))) (held (fn-bpn-nth 2 cursor))
                  (n (nfix (fn-bpn-nth 1 cursor))))
                 (:instance fn-bpnjc-gate-is-the-contact-gate))
           :in-theory (union-theories '(fn-bpnjc-contact-next fn-bpnjc-contact-relp
                                        fn-bpnj-contact-next-is-the-two-scan-selection
                                        fn-bpnjc-nfix-nfix car-cons cdr-cons)
                                      (theory 'minimal-theory)))))

;; ---------------------------------------------------------------------
;; An offer advances the cursor past the offered job and keeps the relation.

; The jobs one scan examines: through the ready job it answers, or all.
(defun fn-bpnjc-scan-seg (rest peer routing)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom rest)
      nil
    (if (and (fn-bpnjc-candp (car rest) peer)
             (fn-bpnjc-sendp (car rest) peer routing))
        (list (car rest))
      (cons (car rest) (fn-bpnjc-scan-seg (cdr rest) peer routing)))))

(defthm fn-bpnjc-scan-position-is-the-segment
  (implies (natp n)
           (equal (mv-nth 2 (fn-bpnjc-scan rest peer routing held n))
                  (+ n (len (fn-bpnjc-scan-seg rest peer routing))))))

(defthm fn-bpnjc-segment-is-a-prefix
  (equal (fn-bpnjc-prefix (len (fn-bpnjc-scan-seg rest peer routing)) rest)
         (fn-bpnjc-scan-seg rest peer routing)))

(defthm fn-bpnjc-prefix-of-sum
  (implies (and (natp a) (natp b))
           (equal (fn-bpnjc-prefix (+ a b) l)
                  (append (fn-bpnjc-prefix a l)
                          (fn-bpnjc-prefix b (fn-bpnjc-drop a l))))))

(defthm fn-bpnjc-len-of-drop
  (implies (and (natp n) (<= n (len l)))
           (equal (len (fn-bpnjc-drop n l)) (- (len l) n))))

(defthm fn-bpnjc-ready-with-more-offered
  (implies (fn-bpnj-readyp job peer routing (cons k offered))
           (fn-bpnj-readyp job peer routing offered))
  :hints (("Goal" :in-theory (enable fn-bpnj-readyp fn-bpnj-candidatep))))

(defthm fn-bpnjc-first-ready-with-more-offered
  (implies (not (fn-bpnjc-first-ready l peer routing offered))
           (not (fn-bpnjc-first-ready l peer routing (cons k offered)))))

(defthm fn-bpnjc-candidate-with-another-key
  (implies (not (equal (fn-bpn-job-key job) k))
           (and (equal (fn-bpnj-candidatep job peer (cons k offered))
                       (fn-bpnj-candidatep job peer offered))
                (equal (fn-bpnj-readyp job peer routing (cons k offered))
                       (fn-bpnj-readyp job peer routing offered))))
  :hints (("Goal" :in-theory (enable fn-bpnj-readyp fn-bpnj-candidatep))))

(defthm fn-bpnjc-first-held-without-the-key
  (implies (not (member-equal k (fn-bpnjc-keys l)))
           (equal (fn-bpnjc-first-held l peer routing (cons k offered))
                  (fn-bpnjc-first-held l peer routing offered)))
  :hints (("Goal" :in-theory (disable fn-bpn-job-key))))

(defthm fn-bpnjc-offered-key-is-not-a-candidate
  (and (not (fn-bpnj-candidatep job peer (cons (fn-bpn-job-key job) offered)))
       (not (fn-bpnj-readyp job peer routing (cons (fn-bpn-job-key job) offered))))
  :hints (("Goal" :in-theory (enable fn-bpnj-readyp fn-bpnj-candidatep))))

; The scan's answers without its position count.
(defun fn-bpnjc-find (rest peer routing held)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom rest)
      (mv nil held)
    (let ((job (car rest)))
      (cond ((not (fn-bpnjc-candp job peer))
             (fn-bpnjc-find (cdr rest) peer routing held))
            ((fn-bpnjc-sendp job peer routing) (mv job held))
            (t (fn-bpnjc-find (cdr rest) peer routing (or held job)))))))

(defthm fn-bpnjc-scan-is-find
  (and (equal (mv-nth 0 (fn-bpnjc-scan rest peer routing held n))
              (mv-nth 0 (fn-bpnjc-find rest peer routing held)))
       (equal (mv-nth 1 (fn-bpnjc-scan rest peer routing held n))
              (mv-nth 1 (fn-bpnjc-find rest peer routing held))))
  :hints (("Goal" :induct (fn-bpnjc-scan rest peer routing held n)
           :in-theory (disable fn-bpnjc-candp fn-bpnjc-sendp))))

(defthm fn-bpnjc-not-queued-is-not-a-candidate
  (implies (not (fn-bpnjc-candp job peer))
           (and (not (fn-bpnj-readyp job peer routing offered))
                (not (fn-bpnj-candidatep job peer offered))))
  :hints (("Goal" :in-theory (enable fn-bpnj-readyp fn-bpnj-candidatep))))

(defthm fn-bpnjc-member-key
  (implies (member-equal x l)
           (member-equal (fn-bpn-job-key x) (fn-bpnjc-keys l)))
  :hints (("Goal" :induct (member-equal x l)
           :in-theory (union-theories '(member-equal fn-bpnjc-keys car-cons cdr-cons)
                                      (theory 'minimal-theory)))))

(defthm fn-bpnjc-find-found-is-a-member
  (implies (mv-nth 0 (fn-bpnjc-find rest peer routing held))
           (member-equal (mv-nth 0 (fn-bpnjc-find rest peer routing held)) rest))
  :hints (("Goal" :induct (fn-bpnjc-find rest peer routing held)
           :in-theory (disable fn-bpn-job-key fn-bpnjc-candp fn-bpnjc-sendp))))

(defthm fn-bpnjc-find-found-is-in-the-segment
  (implies (mv-nth 0 (fn-bpnjc-find rest peer routing held))
           (member-equal (mv-nth 0 (fn-bpnjc-find rest peer routing held))
                         (fn-bpnjc-scan-seg rest peer routing)))
  :hints (("Goal" :induct (fn-bpnjc-find rest peer routing held)
           :in-theory (disable fn-bpn-job-key fn-bpnjc-candp fn-bpnjc-sendp))))

; The jobs a scan examined before its answer.
(defun fn-bpnjc-scan-before (rest peer routing)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom rest)
      nil
    (if (and (fn-bpnjc-candp (car rest) peer)
             (fn-bpnjc-sendp (car rest) peer routing))
        nil
      (cons (car rest) (fn-bpnjc-scan-before (cdr rest) peer routing)))))

(defthm fn-bpnjc-before-holds-nothing-ready
  (implies (fn-bpnjc-unoffered-p rest offered)
           (not (fn-bpnjc-first-ready (fn-bpnjc-scan-before rest peer routing)
                                      peer routing offered)))
  :hints (("Goal" :induct (fn-bpnjc-scan-before rest peer routing)
           :in-theory (disable fn-bpn-job-key fn-bpnjc-candp fn-bpnjc-sendp))))

(defthm fn-bpnjc-nothing-is-queued
  (not (fn-bpnjc-candp nil peer))
  :hints (("Goal" :in-theory (enable fn-bpnjc-candp fn-bpn-job-status))))

(defthm fn-bpnjc-find-held-is-the-first-held-before
  (implies (fn-bpnjc-unoffered-p rest offered)
           (equal (mv-nth 1 (fn-bpnjc-find rest peer routing held))
                  (or held (fn-bpnjc-first-held (fn-bpnjc-scan-before rest peer routing)
                                                peer routing offered))))
  :hints (("Goal" :induct (fn-bpnjc-find rest peer routing held)
           :in-theory (disable fn-bpn-job-key fn-bpnjc-candp fn-bpnjc-sendp))))

(defthm fn-bpnjc-segment-is-before-and-found
  (implies (mv-nth 0 (fn-bpnjc-find rest peer routing held))
           (equal (fn-bpnjc-scan-seg rest peer routing)
                  (append (fn-bpnjc-scan-before rest peer routing)
                          (list (mv-nth 0 (fn-bpnjc-find rest peer routing held))))))
  :hints (("Goal" :induct (fn-bpnjc-find rest peer routing held)
           :in-theory (disable fn-bpn-job-key fn-bpnjc-candp fn-bpnjc-sendp))))

(defthm fn-bpnjc-no-duplicates-of-append
  (implies (no-duplicatesp-equal (append x y))
           (and (no-duplicatesp-equal x) (no-duplicatesp-equal y))))

(defthm fn-bpnjc-prefix-keys-are-distinct
  (implies (no-duplicatesp-equal (fn-bpnjc-keys l))
           (no-duplicatesp-equal (fn-bpnjc-keys (fn-bpnjc-prefix n l))))
  :hints (("Goal" :use ((:instance fn-bpnjc-keys-of-append
                         (a (fn-bpnjc-prefix n l)) (b (fn-bpnjc-drop n l)))
                        (:instance fn-bpnjc-no-duplicates-of-append
                         (x (fn-bpnjc-keys (fn-bpnjc-prefix n l)))
                         (y (fn-bpnjc-keys (fn-bpnjc-drop n l)))))
           :in-theory (union-theories '(fn-bpnjc-prefix-and-drop)
                                      (theory 'minimal-theory)))))

(defthm fn-bpnjc-found-key-is-not-before
  (implies (and (mv-nth 0 (fn-bpnjc-find rest peer routing held))
                (no-duplicatesp-equal (fn-bpnjc-keys rest)))
           (not (member-equal (fn-bpn-job-key (mv-nth 0 (fn-bpnjc-find rest peer routing held)))
                              (fn-bpnjc-keys (fn-bpnjc-scan-before rest peer routing)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnjc-segment-is-a-prefix)
                 (:instance fn-bpnjc-segment-is-before-and-found)
                 (:instance fn-bpnjc-prefix-keys-are-distinct
                  (l rest) (n (len (fn-bpnjc-scan-seg rest peer routing))))
                 (:instance fn-bpnjc-keys-of-append
                  (a (fn-bpnjc-scan-before rest peer routing))
                  (b (list (mv-nth 0 (fn-bpnjc-find rest peer routing held)))))
                 (:instance fn-bpnjc-distinct-halves
                  (x (fn-bpnjc-keys (fn-bpnjc-scan-before rest peer routing)))
                  (y (fn-bpnjc-keys (list (mv-nth 0 (fn-bpnjc-find rest peer routing held)))))
                  (k (fn-bpn-job-key (mv-nth 0 (fn-bpnjc-find rest peer routing held))))))
           :in-theory (union-theories '(fn-bpnjc-keys member-equal car-cons cdr-cons (:e fn-bpnjc-keys))
                                      (theory 'minimal-theory)))))

; The segment an offering scan examined holds no job ready on the contact
; that has offered its answer, and the held job the scan carries is the
; segment's first held one.
(defthm fn-bpnjc-offered-segment
  (let ((found (mv-nth 0 (fn-bpnjc-find rest peer routing held))))
    (implies (and found
                  (fn-bpnjc-unoffered-p rest offered)
                  (no-duplicatesp-equal (fn-bpnjc-keys rest)))
             (and (not (fn-bpnjc-first-ready (fn-bpnjc-scan-seg rest peer routing)
                                             peer routing
                                             (cons (fn-bpn-job-key found) offered)))
                  (equal (mv-nth 1 (fn-bpnjc-find rest peer routing held))
                         (or held
                             (fn-bpnjc-first-held (fn-bpnjc-scan-seg rest peer routing)
                                                  peer routing
                                                  (cons (fn-bpn-job-key found) offered)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnjc-segment-is-before-and-found)
                 (:instance fn-bpnjc-before-holds-nothing-ready)
                 (:instance fn-bpnjc-find-held-is-the-first-held-before)
                 (:instance fn-bpnjc-found-key-is-not-before)
                 (:instance fn-bpnjc-first-ready-with-more-offered
                  (l (fn-bpnjc-scan-before rest peer routing))
                  (k (fn-bpn-job-key (mv-nth 0 (fn-bpnjc-find rest peer routing held)))))
                 (:instance fn-bpnjc-first-held-without-the-key
                  (l (fn-bpnjc-scan-before rest peer routing))
                  (k (fn-bpn-job-key (mv-nth 0 (fn-bpnjc-find rest peer routing held)))))
                 (:instance fn-bpnjc-first-ready-of-append
                  (a (fn-bpnjc-scan-before rest peer routing))
                  (b (list (mv-nth 0 (fn-bpnjc-find rest peer routing held))))
                  (offered (cons (fn-bpn-job-key (mv-nth 0 (fn-bpnjc-find rest peer routing held)))
                                 offered)))
                 (:instance fn-bpnjc-first-held-of-append
                  (a (fn-bpnjc-scan-before rest peer routing))
                  (b (list (mv-nth 0 (fn-bpnjc-find rest peer routing held))))
                  (offered (cons (fn-bpn-job-key (mv-nth 0 (fn-bpnjc-find rest peer routing held)))
                                 offered)))
                 (:instance fn-bpnjc-offered-key-is-not-a-candidate
                  (job (mv-nth 0 (fn-bpnjc-find rest peer routing held)))))
           :in-theory (union-theories '(fn-bpnjc-first-ready fn-bpnjc-first-held car-cons cdr-cons
                                        (:e fn-bpnjc-first-ready) (:e fn-bpnjc-first-held))
                                      (theory 'minimal-theory)))))

(defthm fn-bpnjc-keys-of-drop-are-distinct
  (implies (fn-bpn-job-listp jobs)
           (no-duplicatesp-equal (fn-bpnjc-keys (fn-bpnjc-drop c jobs))))
  :hints (("Goal" :use ((:instance fn-bpnjc-job-list-keys-are-distinct)
                        (:instance fn-bpnjc-keys-of-append
                         (a (fn-bpnjc-prefix c jobs)) (b (fn-bpnjc-drop c jobs))))
           :in-theory (union-theories '(fn-bpnjc-prefix-and-drop fn-bpnjc-no-duplicates-of-append)
                                      (theory 'minimal-theory)))))

(defthm fn-bpnjc-segment-is-no-longer-than-the-rest
  (<= (len (fn-bpnjc-scan-seg rest peer routing)) (len rest))
  :rule-classes :linear)

(defthm fn-bpnjc-subset-of-append
  (implies (subsetp-equal x a)
           (subsetp-equal x (append a b))))

(defthm fn-bpnjc-subset-cons
  (implies (and (member-equal k y) (subsetp-equal x y))
           (subsetp-equal (cons k x) y)))

; The positions after an offer: the new prefix is the old one and the
; examined segment, and it stays within the list.
(defthm fn-bpnjc-offer-prefix
  (let ((seg (fn-bpnjc-scan-seg (fn-bpnjc-drop c jobs) peer routing)))
    (implies (and (natp c) (<= c (len jobs)))
             (and (equal (fn-bpnjc-prefix (+ c (len seg)) jobs)
                         (append (fn-bpnjc-prefix c jobs) seg))
                  (<= (+ c (len seg)) (len jobs)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnjc-prefix-of-sum (a c) (l jobs)
                  (b (len (fn-bpnjc-scan-seg (fn-bpnjc-drop c jobs) peer routing))))
                 (:instance fn-bpnjc-segment-is-a-prefix (rest (fn-bpnjc-drop c jobs)))
                 (:instance fn-bpnjc-len-of-drop (n c) (l jobs))
                 (:instance fn-bpnjc-segment-is-no-longer-than-the-rest
                  (rest (fn-bpnjc-drop c jobs))))
           :in-theory (union-theories '(natp (:t len)) (theory 'minimal-theory))))
  :rule-classes nil)

; The answers over the new prefix, with the offered key.
(defthm fn-bpnjc-offer-answers
  (let* ((suf (fn-bpnjc-drop c jobs))
         (pre (fn-bpnjc-prefix c jobs))
         (found (mv-nth 0 (fn-bpnjc-find suf peer routing held)))
         (seg (fn-bpnjc-scan-seg suf peer routing))
         (k (fn-bpn-job-key found)))
    (implies (and (fn-bpn-job-listp jobs)
                  (not (fn-bpnjc-first-ready pre peer routing offered))
                  (equal held (fn-bpnjc-first-held pre peer routing offered))
                  (fn-bpnjc-unoffered-p suf offered)
                  found)
             (and (not (fn-bpnjc-first-ready (append pre seg) peer routing (cons k offered)))
                  (equal (fn-bpnjc-first-held (append pre seg) peer routing (cons k offered))
                         (mv-nth 1 (fn-bpnjc-find suf peer routing held)))
                  (member-equal k (fn-bpnjc-keys seg)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnjc-keys-of-drop-are-distinct)
                 (:instance fn-bpnjc-offered-segment (rest (fn-bpnjc-drop c jobs)))
                 (:instance fn-bpnjc-find-found-is-a-member (rest (fn-bpnjc-drop c jobs)))
                 (:instance fn-bpnjc-find-found-is-in-the-segment (rest (fn-bpnjc-drop c jobs)))
                 (:instance fn-bpnjc-member-key
                  (x (mv-nth 0 (fn-bpnjc-find (fn-bpnjc-drop c jobs) peer routing held)))
                  (l (fn-bpnjc-drop c jobs)))
                 (:instance fn-bpnjc-member-key
                  (x (mv-nth 0 (fn-bpnjc-find (fn-bpnjc-drop c jobs) peer routing held)))
                  (l (fn-bpnjc-scan-seg (fn-bpnjc-drop c jobs) peer routing)))
                 (:instance fn-bpnjc-prefix-key-is-not-a-drop-key
                  (key (fn-bpn-job-key
                        (mv-nth 0 (fn-bpnjc-find (fn-bpnjc-drop c jobs) peer routing held)))))
                 (:instance fn-bpnjc-first-ready-with-more-offered
                  (l (fn-bpnjc-prefix c jobs))
                  (k (fn-bpn-job-key
                      (mv-nth 0 (fn-bpnjc-find (fn-bpnjc-drop c jobs) peer routing held)))))
                 (:instance fn-bpnjc-first-held-without-the-key
                  (l (fn-bpnjc-prefix c jobs))
                  (k (fn-bpn-job-key
                      (mv-nth 0 (fn-bpnjc-find (fn-bpnjc-drop c jobs) peer routing held)))))
                 (:instance fn-bpnjc-first-ready-of-append
                  (a (fn-bpnjc-prefix c jobs))
                  (b (fn-bpnjc-scan-seg (fn-bpnjc-drop c jobs) peer routing))
                  (offered (cons (fn-bpn-job-key
                                  (mv-nth 0 (fn-bpnjc-find (fn-bpnjc-drop c jobs) peer routing held)))
                                 offered)))
                 (:instance fn-bpnjc-first-held-of-append
                  (a (fn-bpnjc-prefix c jobs))
                  (b (fn-bpnjc-scan-seg (fn-bpnjc-drop c jobs) peer routing))
                  (offered (cons (fn-bpn-job-key
                                  (mv-nth 0 (fn-bpnjc-find (fn-bpnjc-drop c jobs) peer routing held)))
                                 offered))))
           :in-theory (theory 'minimal-theory)))
  :rule-classes nil)

; The relation after an offer: the cursor one past the offered job, the
; held job the scan carried, OFFERED with the offered key.
(defthm fn-bpnjc-offer-keeps-the-cursor-relation
  (let* ((suf (fn-bpnjc-drop (nfix c) jobs))
         (found (mv-nth 0 (fn-bpnjc-find suf peer routing held)))
         (seg (fn-bpnjc-scan-seg suf peer routing)))
    (implies (and (fn-bpnjc-cursor-relp jobs peer routing offered c held)
                  found)
             (fn-bpnjc-cursor-relp jobs peer routing (cons (fn-bpn-job-key found) offered)
                                   (+ (nfix c) (len seg))
                                   (mv-nth 1 (fn-bpnjc-find suf peer routing held)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnjc-head-answers-at-the-cursor)
                 (:instance fn-bpnjc-offer-prefix (c (nfix c)))
                 (:instance fn-bpnjc-offer-answers (c (nfix c)))
                 (:instance fn-bpnjc-keys-of-append
                  (a (fn-bpnjc-prefix (nfix c) jobs))
                  (b (fn-bpnjc-scan-seg (fn-bpnjc-drop (nfix c) jobs) peer routing)))
                 (:instance fn-bpnjc-subset-of-append
                  (x offered) (a (fn-bpnjc-keys (fn-bpnjc-prefix (nfix c) jobs)))
                  (b (fn-bpnjc-keys (fn-bpnjc-scan-seg (fn-bpnjc-drop (nfix c) jobs) peer routing))))
                 (:instance fn-bpnjc-member-of-append
                  (k (fn-bpn-job-key
                      (mv-nth 0 (fn-bpnjc-find (fn-bpnjc-drop (nfix c) jobs) peer routing held))))
                  (x (fn-bpnjc-keys (fn-bpnjc-prefix (nfix c) jobs)))
                  (y (fn-bpnjc-keys (fn-bpnjc-scan-seg (fn-bpnjc-drop (nfix c) jobs) peer routing))))
                 (:instance fn-bpnjc-subset-cons
                  (k (fn-bpn-job-key
                      (mv-nth 0 (fn-bpnjc-find (fn-bpnjc-drop (nfix c) jobs) peer routing held))))
                  (x offered)
                  (y (append (fn-bpnjc-keys (fn-bpnjc-prefix (nfix c) jobs))
                             (fn-bpnjc-keys (fn-bpnjc-scan-seg (fn-bpnjc-drop (nfix c) jobs)
                                                               peer routing))))))
           :in-theory (union-theories '(fn-bpnjc-cursor-relp fn-bpnjc-nfix-nfix
                                        fn-bpnjc-position-is-natural)
                                      (theory 'minimal-theory)))))

(defthm fn-bpnjc-nth-of-a-cursor
  (and (equal (fn-bpn-nth 0 (list f c h)) f)
       (equal (fn-bpn-nth 1 (list f c h)) c)
       (equal (fn-bpn-nth 2 (list f c h)) h)
       (equal (fn-bpn-nth 0 (list* :offer ev rest)) :offer)
       (equal (fn-bpn-nth 2 (list :offer ev o eid)) o))
  :hints (("Goal" :in-theory (enable fn-bpn-nth fn-cbor-ag-car))))

;; The ask's answer re-establishes the relation for the next ask at the same
;; state: an offer's cursor and OFFERED satisfy it.
(defthm fn-bpnjc-offer-keeps-the-relation
  (let ((r (fn-bpnjc-contact-next st peer routing offered cursor)))
    (implies (and (fn-bpnjc-contact-relp st peer routing offered cursor)
                  (equal (fn-bpn-nth 0 (car r)) :offer))
             (fn-bpnjc-contact-relp st peer routing (fn-bpn-nth 2 (car r)) (cdr r))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnjc-offer-keeps-the-cursor-relation
                  (jobs (fn-bpn-machine-state-jobs (fn-bpnf-base st)))
                  (c (nfix (fn-bpn-nth 1 cursor))) (held (fn-bpn-nth 2 cursor)))
                 (:instance fn-bpnjc-scan-position-is-the-segment
                  (rest (fn-bpnjc-drop (nfix (fn-bpn-nth 1 cursor))
                                       (fn-bpn-machine-state-jobs (fn-bpnf-base st))))
                  (held (fn-bpn-nth 2 cursor)) (n (nfix (fn-bpn-nth 1 cursor))))
                 (:instance fn-bpnjc-scan-is-find
                  (rest (fn-bpnjc-drop (nfix (fn-bpn-nth 1 cursor))
                                       (fn-bpn-machine-state-jobs (fn-bpnf-base st))))
                  (held (fn-bpn-nth 2 cursor)) (n (nfix (fn-bpn-nth 1 cursor)))))
           :in-theory (union-theories '(fn-bpnjc-contact-next fn-bpnjc-contact-relp
                                        fn-bpnjc-nth-of-a-cursor fn-bpnjc-nfix-nfix
                                        car-cons cdr-cons (:e fn-bpn-nth) (:e fn-cbor-ag-car)
                                        (:e equal) nfix natp (:t len))
                                      (theory 'minimal-theory)))))

;; ---------------------------------------------------------------------
;; Between asks: the machine's change of the job list keeps the relation.

; Position by position, the jobs ahead of the cursor after a step: the same
; keys, and each job unchanged, or offered on this contact, or not queued
; for the peer before and after.
(defun fn-bpnjc-evolves-p (old new peer offered)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom old)
      (atom new)
    (and (consp new)
         (equal (fn-bpn-job-key (car new)) (fn-bpn-job-key (car old)))
         (or (equal (car new) (car old))
             (member-equal (fn-bpn-job-key (car old)) offered)
             (and (not (fn-bpnjc-candp (car old) peer))
                  (not (fn-bpnjc-candp (car new) peer))))
         (fn-bpnjc-evolves-p (cdr old) (cdr new) peer offered))))

(defthm fn-bpnjc-offered-key-is-never-a-candidate
  (implies (member-equal (fn-bpn-job-key job) offered)
           (and (not (fn-bpnj-candidatep job peer offered))
                (not (fn-bpnj-readyp job peer routing offered))))
  :hints (("Goal" :in-theory (enable fn-bpnj-readyp fn-bpnj-candidatep))))

(defthm fn-bpnjc-evolution-keeps-the-prefix-answers
  (implies (fn-bpnjc-evolves-p old new peer offered)
           (and (equal (fn-bpnjc-keys new) (fn-bpnjc-keys old))
                (implies (not (fn-bpnjc-first-ready old peer routing offered))
                         (and (not (fn-bpnjc-first-ready new peer routing offered))
                              (equal (fn-bpnjc-first-held new peer routing offered)
                                     (fn-bpnjc-first-held old peer routing offered))))))
  :hints (("Goal" :induct (fn-bpnjc-evolves-p old new peer offered)
           :in-theory (disable fn-bpn-job-key fn-bpnjc-candp))))

(defthm fn-bpnjc-evolution-keeps-the-cursor-relation
  (implies (and (fn-bpnjc-cursor-relp jobs peer routing offered c held)
                (fn-bpnjc-evolves-p (fn-bpnjc-prefix (nfix c) jobs)
                                    (fn-bpnjc-prefix (nfix c) jobs2) peer offered)
                (fn-bpn-job-listp jobs2)
                (<= (nfix c) (len jobs2)))
           (fn-bpnjc-cursor-relp jobs2 peer routing offered c held))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnjc-evolution-keeps-the-prefix-answers
                  (old (fn-bpnjc-prefix (nfix c) jobs)) (new (fn-bpnjc-prefix (nfix c) jobs2))))
           :in-theory (union-theories '(fn-bpnjc-cursor-relp) (theory 'minimal-theory)))))

;; Between two asks of a contact the host drives the offer's own events
;; (the :attempting record, the transfer, the :finished or :requeued record);
;; if the job list ahead of the cursor evolves as fn-bpnjc-evolves-p allows,
;; the relation holds at the next state.
(defthm fn-bpnjc-evolution-keeps-the-relation
  (let ((jobs (fn-bpn-machine-state-jobs (fn-bpnf-base st)))
        (jobs2 (fn-bpn-machine-state-jobs (fn-bpnf-base st2)))
        (c (nfix (fn-bpn-nth 1 cursor))))
    (implies (and (fn-bpnjc-contact-relp st peer routing offered cursor)
                  (fn-bpnjc-evolves-p (fn-bpnjc-prefix c jobs) (fn-bpnjc-prefix c jobs2)
                                      peer offered)
                  (fn-bpn-job-listp jobs2)
                  (<= c (len jobs2)))
             (fn-bpnjc-contact-relp st2 peer routing offered cursor)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnjc-evolution-keeps-the-cursor-relation
                  (jobs (fn-bpn-machine-state-jobs (fn-bpnf-base st)))
                  (jobs2 (fn-bpn-machine-state-jobs (fn-bpnf-base st2)))
                  (c (nfix (fn-bpn-nth 1 cursor))) (held (fn-bpn-nth 2 cursor))))
           :in-theory (union-theories '(fn-bpnjc-contact-relp fn-bpnjc-nfix-nfix)
                                      (theory 'minimal-theory)))))

;; What the lower machine does to the job list is such an evolution.  A
;; lifecycle record replaces the job its key names (fn-bpn-apply-record:
;; :attempting, :requeued, :finished, :expired) or appends one (:queued):
(defthm fn-bpnjc-evolves-reflexive
  (fn-bpnjc-evolves-p x x peer offered))

(defthm fn-bpnjc-replacing-an-offered-job-evolves
  (implies (and (member-equal key offered)
                (equal (fn-bpn-job-key job) key))
           (fn-bpnjc-evolves-p (fn-bpnjc-prefix c jobs)
                               (fn-bpnjc-prefix c (fn-bpn-replace-job key job jobs))
                               peer offered))
  :hints (("Goal" :induct (fn-bpnjc-prefix c jobs)
           :in-theory (e/d (fn-bpn-replace-job) (fn-bpn-job-key fn-bpnjc-candp)))))

(defthm fn-bpnjc-replacing-an-unqueued-job-evolves
  (implies (and (equal (fn-bpn-job-key job) key)
                (not (fn-bpnjc-candp (fn-bpn-find-job key jobs) peer))
                (not (fn-bpnjc-candp job peer)))
           (fn-bpnjc-evolves-p (fn-bpnjc-prefix c jobs)
                               (fn-bpnjc-prefix c (fn-bpn-replace-job key job jobs))
                               peer offered))
  :hints (("Goal" :induct (fn-bpnjc-prefix c jobs)
           :in-theory (e/d (fn-bpn-replace-job fn-bpn-find-job) (fn-bpn-job-key fn-bpnjc-candp)))))

(defthm fn-bpnjc-appending-keeps-the-prefix
  (implies (<= (nfix c) (len jobs))
           (equal (fn-bpnjc-prefix c (fn-bpn-append jobs more))
                  (fn-bpnjc-prefix c jobs)))
  :hints (("Goal" :induct (fn-bpnjc-prefix c jobs)
           :in-theory (enable fn-bpn-append))))

;; ---------------------------------------------------------------------
;; The peer's frontier, carried between contacts.

(defun fn-bpnjc-settledp (job peer)
  (declare (xargs :guard t))
  (or (not (equal (fn-bpn-job-peer job) peer))
      (equal (fn-bpn-job-status job) :forwarded)
      (equal (fn-bpn-job-status job) :expired)))

(defun fn-bpnjc-all-settled-p (l peer)
  (declare (xargs :guard t))
  (if (atom l)
      t
    (and (fn-bpnjc-settledp (car l) peer)
         (fn-bpnjc-all-settled-p (cdr l) peer))))

(defun fn-bpnjc-frontierp (jobs peer f)
  (declare (xargs :guard t :verify-guards nil))
  (and (natp f)
       (<= f (len jobs))
       (fn-bpnjc-all-settled-p (fn-bpnjc-prefix f jobs) peer)))

(defthm fn-bpnjc-settled-is-not-queued
  (implies (fn-bpnjc-settledp job peer)
           (not (fn-bpnjc-candp job peer))))

(defthm fn-bpnjc-settled-prefix-answers-nothing
  (implies (fn-bpnjc-all-settled-p l peer)
           (and (not (fn-bpnjc-first-ready l peer routing offered))
                (not (fn-bpnjc-first-held l peer routing offered))))
  :hints (("Goal" :in-theory (disable fn-bpnjc-settledp fn-bpnjc-candp))))

; A contact's first cursor: position and frontier F, nothing held.
(defun fn-bpnjc-frontier-of (table peer)
  (declare (xargs :guard t))
  (if (atom table)
      0
    (if (and (consp (car table)) (equal (car (car table)) peer))
        (nfix (cdr (car table)))
      (fn-bpnjc-frontier-of (cdr table) peer))))

(defun fn-bpnjc-contact-cursor (table peer)
  (declare (xargs :guard t))
  (let ((f (fn-bpnjc-frontier-of table peer)))
    (list f f nil)))

(defthm fn-bpnjc-open-establishes-the-cursor-relation
  (implies (and (fn-bpnjc-frontierp jobs peer f)
                (fn-bpn-job-listp jobs))
           (fn-bpnjc-cursor-relp jobs peer routing nil f nil))
  :hints (("Goal" :in-theory (disable fn-bpnjc-all-settled-p fn-bpnjc-prefix))))

;; The contact's opening establishes the relation: the host passes the
;; cursor fn-bpnjc-contact-cursor names for the peer, and OFFERED empty.
(defthm fn-bpnjc-open-establishes-the-relation
  (implies (and (fn-bpnjc-frontierp (fn-bpn-machine-state-jobs (fn-bpnf-base st)) peer
                                    (fn-bpnjc-frontier-of table peer))
                (fn-bpn-job-listp (fn-bpn-machine-state-jobs (fn-bpnf-base st))))
           (fn-bpnjc-contact-relp st peer routing nil (fn-bpnjc-contact-cursor table peer)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnjc-open-establishes-the-cursor-relation
                  (jobs (fn-bpn-machine-state-jobs (fn-bpnf-base st)))
                  (f (fn-bpnjc-frontier-of table peer))))
           :in-theory (union-theories '(fn-bpnjc-contact-relp fn-bpnjc-contact-cursor
                                        fn-bpnjc-nth-of-a-cursor fn-bpnjc-frontierp nfix natp)
                                      (theory 'minimal-theory)))))

; The contact's close advances the peer's frontier over the settled jobs the
; contact examined, one pass from F to at most C.
(defun fn-bpnjc-advance (rest peer f c)
  (declare (xargs :guard (and (natp f) (natp c)) :measure (len rest)))
  (if (or (atom rest) (<= c f) (not (fn-bpnjc-settledp (car rest) peer)))
      f
    (fn-bpnjc-advance (cdr rest) peer (+ 1 f) c)))

(defun fn-bpnjc-table-with (table peer f)
  (declare (xargs :guard t))
  (if (atom table)
      (list (cons peer f))
    (if (and (consp (car table)) (equal (car (car table)) peer))
        (cons (cons peer f) (cdr table))
      (cons (car table) (fn-bpnjc-table-with (cdr table) peer f)))))

(defun fn-bpnjc-contact-close (table st peer cursor)
  (declare (xargs :guard t))
  (let ((f (fn-bpnjc-frontier-of table peer))
        (c (nfix (fn-bpn-nth 1 cursor))))
    (fn-bpnjc-table-with
     table peer
     (fn-bpnjc-advance (fn-bpnjc-drop f (fn-bpn-machine-state-jobs (fn-bpnf-base st)))
                       peer f c))))

(defthm fn-bpnjc-frontier-of-table-with
  (equal (fn-bpnjc-frontier-of (fn-bpnjc-table-with table peer f) q)
         (if (equal q peer) (nfix f) (fn-bpnjc-frontier-of table q))))

(defthm fn-bpnjc-prefix-one-more
  (implies (and (natp f) (< f (len l)))
           (equal (fn-bpnjc-prefix (+ 1 f) l)
                  (append (fn-bpnjc-prefix f l) (list (car (fn-bpnjc-drop f l)))))))

(defthm fn-bpnjc-all-settled-of-append
  (equal (fn-bpnjc-all-settled-p (append a b) peer)
         (and (fn-bpnjc-all-settled-p a peer) (fn-bpnjc-all-settled-p b peer))))

(defthm fn-bpnjc-drop-one-more
  (implies (and (natp f) (< f (len l)))
           (equal (fn-bpnjc-drop (+ 1 f) l) (cdr (fn-bpnjc-drop f l)))))

(defthm fn-bpnjc-consp-drop
  (implies (natp f)
           (iff (consp (fn-bpnjc-drop f l)) (< f (len l)))))

(defthm fn-bpnjc-advance-keeps-the-frontier
  (implies (and (fn-bpnjc-frontierp jobs peer f)
                (equal rest (fn-bpnjc-drop f jobs)))
           (fn-bpnjc-frontierp jobs peer (fn-bpnjc-advance rest peer f c)))
  :hints (("Goal" :induct (fn-bpnjc-advance rest peer f c)
           :in-theory (disable fn-bpnjc-settledp fn-bpnjc-prefix fn-bpnjc-drop))))

(defthm fn-bpnjc-frontierp-is-natp
  (implies (fn-bpnjc-frontierp jobs peer f) (natp f))
  :rule-classes :forward-chaining)

(defthm fn-bpnjc-frontier-zero
  (fn-bpnjc-frontierp jobs peer 0))

;; The close keeps every peer's frontier: the table it answers names a
;; frontier of the same job list for every peer.
(defthm fn-bpnjc-close-keeps-the-frontiers
  (let ((jobs (fn-bpn-machine-state-jobs (fn-bpnf-base st))))
    (implies (fn-bpnjc-frontierp jobs q (fn-bpnjc-frontier-of table q))
             (fn-bpnjc-frontierp jobs q (fn-bpnjc-frontier-of
                                         (fn-bpnjc-contact-close table st peer cursor) q))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnjc-advance-keeps-the-frontier
                  (jobs (fn-bpn-machine-state-jobs (fn-bpnf-base st)))
                  (f (fn-bpnjc-frontier-of table peer)) (peer q)
                  (rest (fn-bpnjc-drop (fn-bpnjc-frontier-of table peer)
                                       (fn-bpn-machine-state-jobs (fn-bpnf-base st))))
                  (c (nfix (fn-bpn-nth 1 cursor)))))
           :in-theory (e/d (fn-bpnjc-contact-close)
                           (fn-bpnjc-advance-keeps-the-frontier fn-bpnjc-advance fn-bpnjc-frontierp
                            fn-bpnjc-drop fn-bpnjc-frontier-of)))))

;; The lower machine keeps every frontier: a lifecycle record never touches
;; a :forwarded or :expired job and never changes a job's peer.
(defthm fn-bpnjc-with-status-keeps-the-peer
  (equal (fn-bpn-job-peer (fn-bpn-job-with-status job status token))
         (fn-bpn-job-peer job))
  :hints (("Goal" :in-theory (enable fn-bpn-job-with-status))))

(defthm fn-bpnjc-len-of-replace-job
  (equal (len (fn-bpn-replace-job key job jobs)) (len jobs))
  :hints (("Goal" :in-theory (enable fn-bpn-replace-job))))

(defthm fn-bpnjc-len-of-append
  (equal (len (fn-bpn-append a b)) (+ (len a) (len b)))
  :hints (("Goal" :in-theory (enable fn-bpn-append))))

(defthm fn-bpnjc-replacing-an-unsettled-job-keeps-the-settled-prefix
  (implies (and (fn-bpnjc-all-settled-p (fn-bpnjc-prefix f jobs) peer)
                (not (equal (fn-bpn-job-status (fn-bpn-find-job key jobs)) :forwarded))
                (not (equal (fn-bpn-job-status (fn-bpn-find-job key jobs)) :expired))
                (equal (fn-bpn-job-peer job) (fn-bpn-job-peer (fn-bpn-find-job key jobs))))
           (fn-bpnjc-all-settled-p (fn-bpnjc-prefix f (fn-bpn-replace-job key job jobs)) peer))
  :hints (("Goal" :induct (fn-bpnjc-prefix f jobs)
           :in-theory (e/d (fn-bpn-replace-job fn-bpn-find-job) (fn-bpn-job-key)))))

(defthm fn-bpnjc-lifecycle-record-keeps-the-frontier
  (implies (fn-bpnjc-frontierp (fn-bpn-machine-state-jobs st) peer f)
           (fn-bpnjc-frontierp (fn-bpn-machine-state-jobs (fn-bpn-apply-record st record))
                               peer f))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bpn-apply-record fn-bpn-record-applicablep fn-bpnjc-frontierp
                            fn-bpn-state-with-accessors fn-bpn-member)
                           (fn-bpnjc-all-settled-p fn-bpnjc-prefix fn-bpn-find-job
                            fn-bpn-replace-job fn-bpn-append fn-bpn-job-with-status
                            fn-bpn-lifecycle-recordp fn-bpn-jobs-octets)))))

(defthm fn-bpnjc-with-status-keeps-the-key
  (equal (fn-bpn-job-key (fn-bpn-job-with-status job status token))
         (fn-bpn-job-key job))
  :hints (("Goal" :in-theory (enable fn-bpn-job-with-status))))

;; The records a contact's offer drives name an offered key (:attempting,
;; then :finished or :requeued), and a :queued record appends: each is an
;; evolution the relation survives.
(defthm fn-bpnjc-offered-record-evolves
  (implies (and (<= (nfix c) (len (fn-bpn-machine-state-jobs st)))
                (or (equal (fn-cbor-ag-car record) :queued)
                    (member-equal (fn-bpn-record-key record) offered)))
           (fn-bpnjc-evolves-p
            (fn-bpnjc-prefix c (fn-bpn-machine-state-jobs st))
            (fn-bpnjc-prefix c (fn-bpn-machine-state-jobs (fn-bpn-apply-record st record)))
            peer offered))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bpn-apply-record fn-bpn-record-applicablep
                            fn-bpn-state-with-accessors fn-bpnj-found-job-has-its-key)
                           (fn-bpnjc-prefix fn-bpn-find-job fn-bpnjc-evolves-p
                            fn-bpn-replace-job fn-bpn-append fn-bpn-job-with-status
                            fn-bpn-lifecycle-recordp fn-bpn-jobs-octets fn-bpn-record-key
                            fn-bpn-job-key)))))

;; ---------------------------------------------------------------------
;; The drain.

; The host's asks along one contact: the cursor's answers, threading OFFERED
; and the cursor, until the first answer that is not an offer.
(defun fn-bpnjc-drain (sts peer routing offered cursor)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom sts)
      nil
    (let* ((r (fn-bpnjc-contact-next (car sts) peer routing offered cursor))
           (d (car r)))
      (if (equal (fn-bpn-nth 0 d) :offer)
          (cons d (fn-bpnjc-drain (cdr sts) peer routing (fn-bpn-nth 2 d) (cdr r)))
        (list d)))))

; The same asks of the head-restarting scan.
(defun fn-bpnjc-head-drain (sts peer routing offered)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom sts)
      nil
    (let ((d (fn-bpnj-contact-next (car sts) peer routing offered)))
      (if (equal (fn-bpn-nth 0 d) :offer)
          (cons d (fn-bpnjc-head-drain (cdr sts) peer routing (fn-bpn-nth 2 d)))
        (list d)))))

; Positions the drain's asks examined, in all.
(defun fn-bpnjc-drain-visits (sts peer routing offered cursor)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom sts)
      0
    (let* ((r (fn-bpnjc-contact-next (car sts) peer routing offered cursor))
           (d (car r))
           (here (- (nfix (fn-bpn-nth 1 (cdr r))) (nfix (fn-bpn-nth 1 cursor)))))
      (if (equal (fn-bpn-nth 0 d) :offer)
          (+ here (fn-bpnjc-drain-visits (cdr sts) peer routing (fn-bpn-nth 2 d) (cdr r)))
        here))))

; The machine between asks: the jobs ahead of the advanced cursor evolve
; (fn-bpnjc-evolves-p), the job list keeps unique keys and reaches the cursor.
(defun fn-bpnjc-evolving-p (sts peer routing offered cursor)
  (declare (xargs :guard t :verify-guards nil :measure (len sts)
                  :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (or (atom sts) (atom (cdr sts)))
      t
    (let* ((r (fn-bpnjc-contact-next (car sts) peer routing offered cursor))
           (d (car r)))
      (if (equal (fn-bpn-nth 0 d) :offer)
          (let ((c2 (nfix (fn-bpn-nth 1 (cdr r))))
                (j1 (fn-bpn-machine-state-jobs (fn-bpnf-base (car sts))))
                (j2 (fn-bpn-machine-state-jobs (fn-bpnf-base (cadr sts)))))
            (and (fn-bpnjc-evolves-p (fn-bpnjc-prefix c2 j1) (fn-bpnjc-prefix c2 j2)
                                     peer (fn-bpn-nth 2 d))
                 (fn-bpn-job-listp j2)
                 (<= c2 (len j2))
                 (fn-bpnjc-evolving-p (cdr sts) peer routing (fn-bpn-nth 2 d) (cdr r))))
        t))))

; The last job list the drain asks at.
(defun fn-bpnjc-drain-last-jobs (sts peer routing offered cursor)
  (declare (xargs :guard t :verify-guards nil :measure (len sts)
                  :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (atom sts)
      nil
    (let* ((r (fn-bpnjc-contact-next (car sts) peer routing offered cursor))
           (d (car r)))
      (if (and (equal (fn-bpn-nth 0 d) :offer) (consp (cdr sts)))
          (fn-bpnjc-drain-last-jobs (cdr sts) peer routing (fn-bpn-nth 2 d) (cdr r))
        (fn-bpn-machine-state-jobs (fn-bpnf-base (car sts)))))))

(defthm fn-bpnjc-ask-position-bounds
  (let ((r (fn-bpnjc-contact-next st peer routing offered cursor)))
    (implies (fn-bpnjc-contact-relp st peer routing offered cursor)
             (and (<= (nfix (fn-bpn-nth 1 cursor)) (nfix (fn-bpn-nth 1 (cdr r))))
                  (<= (nfix (fn-bpn-nth 1 (cdr r)))
                      (len (fn-bpn-machine-state-jobs (fn-bpnf-base st))))
                  (implies (equal (fn-bpn-nth 0 (car r)) :offer)
                           (< (nfix (fn-bpn-nth 1 cursor)) (nfix (fn-bpn-nth 1 (cdr r))))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnjc-scan-position-bounds
                  (rest (fn-bpnjc-drop (nfix (fn-bpn-nth 1 cursor))
                                       (fn-bpn-machine-state-jobs (fn-bpnf-base st))))
                  (held (fn-bpn-nth 2 cursor)) (n (nfix (fn-bpn-nth 1 cursor))))
                 (:instance fn-bpnjc-len-of-drop (n (nfix (fn-bpn-nth 1 cursor)))
                  (l (fn-bpn-machine-state-jobs (fn-bpnf-base st)))))
           :in-theory (union-theories '(fn-bpnjc-contact-next fn-bpnjc-contact-relp fn-bpnjc-cursor-relp
                                        fn-bpnjc-nth-of-a-cursor fn-bpnjc-nfix-nfix
                                        car-cons cdr-cons (:e fn-bpn-nth) (:e fn-cbor-ag-car)
                                        (:e equal) nfix natp (:t len))
                                      (theory 'minimal-theory)))))

;; KEYSTONE (the drain).  Along a contact's asks, from a cursor the contact's
;; opening establishes (fn-bpnjc-open-establishes-the-relation) and with the
;; machine changing the jobs ahead of the cursor only as fn-bpnjc-evolves-p
;; allows (fn-bpnjc-offered-record-evolves: the offer's own records and any
;; :queued append), the cursor's answers are the head scan's answers, ask for
;; ask: the same offers in the same order, each ready job offered once
;; (PRF-120's fn-bpnp-contact-offers-each-job-at-most-once over the head
;; scan), the same close.  The work: the drain examines each position from
;; the cursor's start at most once, in all at most the job list's length
;; less that start (fn-bpnjc-drain-visits-are-linear).
; One ask of the drain: the next state's relation and evolution.
(defthm fn-bpnjc-drain-step
  (let* ((r (fn-bpnjc-contact-next (car sts) peer routing offered cursor))
         (d (car r)))
    (implies (and (fn-bpnjc-contact-relp (car sts) peer routing offered cursor)
                  (fn-bpnjc-evolving-p sts peer routing offered cursor)
                  (consp sts) (consp (cdr sts))
                  (equal (fn-bpn-nth 0 d) :offer))
             (and (fn-bpnjc-contact-relp (cadr sts) peer routing (fn-bpn-nth 2 d) (cdr r))
                  (fn-bpnjc-evolving-p (cdr sts) peer routing (fn-bpn-nth 2 d) (cdr r)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnjc-offer-keeps-the-relation (st (car sts)))
                 (:instance fn-bpnjc-evolution-keeps-the-relation
                  (st (car sts)) (st2 (cadr sts))
                  (offered (fn-bpn-nth 2 (car (fn-bpnjc-contact-next
                                                (car sts) peer routing offered cursor))))
                  (cursor (cdr (fn-bpnjc-contact-next (car sts) peer routing offered cursor)))))
           :in-theory (union-theories '(fn-bpnjc-evolving-p) (theory 'minimal-theory))))
  :rule-classes nil)

(defthm fn-bpnjc-drain-is-the-head-drain
  (implies (and (fn-bpnjc-contact-relp (car sts) peer routing offered cursor)
                (fn-bpnjc-evolving-p sts peer routing offered cursor))
           (equal (fn-bpnjc-drain sts peer routing offered cursor)
                  (fn-bpnjc-head-drain sts peer routing offered)))
  :hints (("Goal" :induct (fn-bpnjc-drain sts peer routing offered cursor)
           :do-not '(generalize fertilize eliminate-destructors)
           :in-theory (union-theories '(fn-bpnjc-drain fn-bpnjc-head-drain
                                        fn-bpnjc-contact-next-is-the-head-scan)
                                      (theory 'minimal-theory)))
          (and stable-under-simplificationp
               '(:use ((:instance fn-bpnjc-drain-step))))))

(defthm fn-bpnjc-drain-visits-are-linear
  (implies (and (consp sts)
                (fn-bpnjc-contact-relp (car sts) peer routing offered cursor)
                (fn-bpnjc-evolving-p sts peer routing offered cursor))
           (<= (+ (nfix (fn-bpn-nth 1 cursor))
                  (fn-bpnjc-drain-visits sts peer routing offered cursor))
               (len (fn-bpnjc-drain-last-jobs sts peer routing offered cursor))))
  :hints (("Goal" :induct (fn-bpnjc-drain sts peer routing offered cursor)
           :do-not '(generalize fertilize eliminate-destructors)
           :in-theory (union-theories '(fn-bpnjc-drain-visits fn-bpnjc-drain-last-jobs
                                        (:induction fn-bpnjc-drain)
                                        nfix (:t nfix) (:t len) natp)
                                      (theory 'minimal-theory)))
          (and stable-under-simplificationp
               '(:use ((:instance fn-bpnjc-drain-step)
                       (:instance fn-bpnjc-ask-position-bounds (st (car sts)))))))
  :rule-classes nil)
