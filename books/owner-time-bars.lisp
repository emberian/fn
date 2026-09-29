; fn: the adopted F4 bars -- an unresolved operation's late completion, a
; read's page dependency and the restart's clock domain (lane time-bars,
; 2026-09-28; PRF-384, HST-031; planning/design-time-model-2026-09-27.md
; section 4b, the bars ember adopted from planning/review-2026-09-28-gpt6.md
; "F4 calls").
;
; books/owner-time-model.lisp decides WHEN the node tells a poster the
; outcome of a write is unresolved (H, the stall deadline: 30,000 ms by
; default, PKT-853) and proves the notification comes at most H + L after
; the barrier's issue, L the lateness of one committer wake
; (fn-otm-f4w-stall-within-h; the adopted bar is L <= 1,000 ms, the slack
; under the stated host scheduling assumption).  A deadline is a
; NOTIFICATION EVENT, never a cancellation: the barrier keeps running, and
; its completion arrives later.  This book decides what happens to that
; late completion, and to the other two things a deadline must not break:
;
;   1. THE UNRESOLVED OPERATION'S LEDGER (G OPEN TOLD).  Every request the
;      node waits on with a deadline is issued under a GENERATION G.  While
;      it is OPEN its I/O-owned resources (the sealed batch the syncer
;      writes) belong to the request, whatever the deadline does; the
;      connections told early (at the stall, or at a stop's release) are
;      TOLD.  Its completion is consumed exactly once, into its own
;      generation: it applies only when the ledger is open at that
;      generation, answers exactly the members not already told, and
;      closes the ledger (the host releases the batch's buffer only then).
;      A completion for another generation is :stale, a second one
;      :consumed; neither answers anyone or changes anything.  The host's
;      committer (host/native/owner.lisp fnn-owner-commit-pipeline) calls
;      fn-otb-issue, fn-otb-answer-early and fn-otb-complete; the list of
;      told connections was the host's own before this lane.
;   2. A READ'S PAGE DEPENDENCY.  A served read that needs a page not in
;      memory (a cold extent: host/native/extent.lisp preads it) waits for
;      it at most the declared dependency deadline (`read-dependency-ms',
;      default 5,000 ms), then is answered by NAME: 403, the article is
;      temporarily unavailable -- never 430 or 423, which say the article
;      is absent.  A late page is not a missing one.  (The asynchronous
;      page fault outside the owner mutex that calls this is row A4's; the
;      decision and its reply are here.)
;   3. THE RESTART'S CLOCK DOMAIN.  A monotonic reading has no meaning in
;      another process (SBCL's get-internal-real-time starts near zero in
;      every process).  The decision journal's replay starts each run's
;      segment from fn-otm-init, and the start entry records the semantic
;      observation (the wall reading and whether it is usable), not a raw
;      monotonic origin: no decision of a run depends on a reading of an
;      earlier one (fn-otb-a-restart-forgets-the-previous-clock-domain).
;      The feed's back-off deadline is the same contract in
;      books/peer-feed.lisp (PRF-385, fn-feed-restart).
(in-package "ACL2")
(include-book "owner-time-journal-writer")

; -----------------------------------------------------------------------------
; Lists of connection ids, guard-free.

(defun fn-otb-in (x ys)
  (declare (xargs :guard t))
  (if (consp ys)
      (or (equal x (car ys)) (fn-otb-in x (cdr ys)))
    nil))

(defun fn-otb-minus (xs ys)
  (declare (xargs :guard t))
  (if (consp xs)
      (if (fn-otb-in (car xs) ys)
          (fn-otb-minus (cdr xs) ys)
        (cons (car xs) (fn-otb-minus (cdr xs) ys)))
    nil))

(defun fn-otb-dedup (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (if (fn-otb-in (car xs) (cdr xs))
          (fn-otb-dedup (cdr xs))
        (cons (car xs) (fn-otb-dedup (cdr xs))))
    nil))

; -----------------------------------------------------------------------------
; 1. The ledger: (GEN OPEN TOLD).

(defun fn-otb-ledger-make (gen open told)
  (declare (xargs :guard t))
  (list gen open told))

(defun fn-otb-gen (l)
  (declare (xargs :guard t))
  (if (consp l) (nfix (car l)) 0))

(defun fn-otb-open (l)
  (declare (xargs :guard t))
  (if (and (consp l) (consp (cdr l)) (cadr l)) t nil))

(defun fn-otb-told (l)
  (declare (xargs :guard t))
  (if (and (consp l) (consp (cdr l)) (consp (cddr l)) (true-listp (caddr l)))
      (caddr l)
    nil))

(defun fn-otb-ledger-init ()
  (declare (xargs :guard t))
  (fn-otb-ledger-make 0 nil nil))

; ISSUE a request: (WORD GEN L').  :issued under a fresh generation (one
; past the last), or :fault while one is open (one request in flight: the
; pipeline's one batch in flight, fn-otm-issue-only-when-none-pending).
(defun fn-otb-issue (l)
  (declare (xargs :guard t))
  (if (fn-otb-open l)
      (list :fault (fn-otb-gen l) l)
    (let ((g (+ 1 (fn-otb-gen l))))
      (list :issued g (fn-otb-ledger-make g t (fn-otb-told l))))))

; ANSWER EARLY (the stall's uncertain release, a stop's release): (NOW L'),
; NOW the connections of CIDS not already told, each once; they join TOLD.
; The generation and OPEN are unchanged: the request is still in flight
; and still owns its I/O.
(defun fn-otb-answer-early (l cids)
  (declare (xargs :guard t))
  (let ((now (fn-otb-dedup (fn-otb-minus cids (fn-otb-told l)))))
    (list now (fn-otb-ledger-make (fn-otb-gen l) (fn-otb-open l)
                                  (append (fn-otb-told l) now)))))

; COMPLETE: the request's completion, reported with the generation it was
; issued under, for the batch's members CIDS: (VERDICT ANSWER L').
;   :apply     open at this generation: ANSWER is the members not told
;              early; the ledger closes (the I/O-owned batch is released)
;              and forgets the members it answered
;   :stale     another generation's completion: nothing answered, nothing
;              changed
;   :consumed  this generation's, already applied: likewise
(defun fn-otb-complete (l gen cids)
  (declare (xargs :guard t))
  (cond ((not (equal (nfix gen) (fn-otb-gen l))) (list :stale nil l))
        ((not (fn-otb-open l)) (list :consumed nil l))
        (t (list :apply (fn-otb-minus cids (fn-otb-told l))
                 (fn-otb-ledger-make (fn-otb-gen l) nil
                                     (fn-otb-minus (fn-otb-told l) cids))))))

; Several early answers in order (a stall, then a stop's release): (ALL L').
(defun fn-otb-early-run (l xss)
  (declare (xargs :guard t))
  (if (consp xss)
      (let* ((e (fn-otb-answer-early l (car xss)))
             (r (fn-otb-early-run (cadr e) (cdr xss))))
        (list (append (car e) (car r)) (cadr r)))
    (list nil l)))

; --- The list facts.
(local
 (encapsulate ()
   (defthm fn-otb-in-is-member
     (iff (fn-otb-in x ys) (member-equal x ys)))
   (defthm fn-otb-member-minus
     (iff (member-equal x (fn-otb-minus xs ys))
          (and (member-equal x xs) (not (member-equal x ys)))))
   (defthm fn-otb-member-dedup
     (iff (member-equal x (fn-otb-dedup xs)) (member-equal x xs)))
   (defthm fn-otb-true-listp-minus (true-listp (fn-otb-minus xs ys)))
   (defthm fn-otb-true-listp-dedup (true-listp (fn-otb-dedup xs)))
   (defthm fn-otb-no-dups-dedup (no-duplicatesp-equal (fn-otb-dedup xs)))
   (defthm fn-otb-no-dups-minus
     (implies (no-duplicatesp-equal xs) (no-duplicatesp-equal (fn-otb-minus xs ys))))
   (defthm fn-otb-intersectp-append-left
     (iff (intersectp-equal (append a b) c)
          (or (intersectp-equal a c) (intersectp-equal b c))))
   (defthm fn-otb-append-assoc
     (equal (append (append a b) c) (append a (append b c))))
   (defthm fn-otb-member-append
     (iff (member-equal x (append b c))
          (or (member-equal x b) (member-equal x c))))
   (defthm fn-otb-intersectp-append-right
     (iff (intersectp-equal a (append b c))
          (or (intersectp-equal a b) (intersectp-equal a c))))
   (defthm fn-otb-no-dups-append
     (iff (no-duplicatesp-equal (append a b))
          (and (no-duplicatesp-equal a) (no-duplicatesp-equal b)
               (not (intersectp-equal a b)))))
   (defthm fn-otb-intersectp-member-cons
     (iff (intersectp-equal a (cons x b))
          (or (member-equal x a) (intersectp-equal a b))))
   (defthm fn-otb-intersectp-commutes-nil
     (implies (not (intersectp-equal b a)) (not (intersectp-equal a b))))
   (defthm fn-otb-minus-disjoint
     (not (intersectp-equal (fn-otb-minus x y) y)))
   (defthm fn-otb-dedup-intersectp
     (iff (intersectp-equal (fn-otb-dedup x) y) (intersectp-equal x y)))
   (defthm fn-otb-intersectp-dedup
     (iff (intersectp-equal y (fn-otb-dedup x)) (intersectp-equal y x)))
   (defthm fn-otb-subsetp-minus (subsetp-equal (fn-otb-minus x y) x))
   (defthm fn-otb-subsetp-cons
     (implies (subsetp-equal x y) (subsetp-equal x (cons a y))))
   (defthm fn-otb-subsetp-reflexive (subsetp-equal x x))
   (defthm fn-otb-cover-sub
     (implies (subsetp-equal z x)
              (subsetp-equal z (append a (append b (fn-otb-minus x (append a b)))))))
   (defthm fn-otb-cover
     (subsetp-equal x (append a (append b (fn-otb-minus x (append a b)))))
     :hints (("Goal" :use ((:instance fn-otb-cover-sub (z x))))))))

(defthm fn-otb-true-listp-told (true-listp (fn-otb-told l))
  :rule-classes :type-prescription)

(local
 (defthm fn-otb-accessors-of-make
   (and (equal (fn-otb-gen (fn-otb-ledger-make g o tl)) (nfix g))
        (equal (fn-otb-open (fn-otb-ledger-make g o tl)) (if o t nil))
        (equal (fn-otb-told (fn-otb-ledger-make g o tl)) (if (true-listp tl) tl nil)))))

(local (in-theory (disable fn-otb-ledger-make fn-otb-gen fn-otb-open fn-otb-told)))

(local
 (defthm fn-otb-early-run-facts
   (let ((r (fn-otb-early-run l xss)))
     (and (equal (fn-otb-gen (cadr r)) (fn-otb-gen l))
          (equal (fn-otb-open (cadr r)) (fn-otb-open l))
          (equal (fn-otb-told (cadr r)) (append (fn-otb-told l) (car r)))
          (true-listp (car r))
          (no-duplicatesp-equal (car r))
          (not (intersectp-equal (car r) (fn-otb-told l)))))
   :hints (("Goal" :in-theory (enable fn-otb-early-run fn-otb-answer-early)
            :induct (fn-otb-early-run l xss)))))

;; KEYSTONE (PRF-384).  A request's members are answered exactly once
;; across its deadline and its late completion.  From a ledger open at
;; generation G, any number of early answers XSS (the stall's, a stop's)
;; and then the completion reported for G over the batch's members CIDS:
;; the completion applies; everything told early was not told before; no
;; connection is told twice early; the completion answers only members, and
;; none of those already told (before or early) -- no second, contradictory
;; reply; and every member is answered somewhere: told before, told early,
;; or by the completion.  The subjects are fn-otb-answer-early and
;; fn-otb-complete, which host/native/owner.lisp fnn-owner-commit-pipeline
;; calls (the stall's release and every stop's; the COMPLETE after the
;; syncer's join).
(defthm fn-otb-a-member-is-answered-once
  (let* ((r (fn-otb-early-run l xss))
         (early (car r))
         (c (fn-otb-complete (cadr r) (fn-otb-gen l) cids))
         (late (cadr c)))
    (implies (and (fn-otb-open l) (no-duplicatesp-equal cids))
             (and (equal (car c) :apply)
                  (no-duplicatesp-equal early)
                  (not (intersectp-equal early (fn-otb-told l)))
                  (no-duplicatesp-equal late)
                  (subsetp-equal late cids)
                  (not (intersectp-equal late (append (fn-otb-told l) early)))
                  (subsetp-equal cids (append (fn-otb-told l) early late)))))
  :hints (("Goal" :in-theory (enable fn-otb-complete))))

;; KEYSTONE (PRF-384).  A late completion is consumed exactly once, into
;; its own generation.  A completion applies iff the ledger is open at the
;; generation it names; one that does not apply answers no one and changes
;; nothing; once one applied, every later completion -- its own again, or
;; any other generation's -- is refused; and the next request is issued
;; under a generation no earlier completion names, so a completion that
;; arrives after its request's successor was issued is :stale.  The
;; subject is fn-otb-complete (and fn-otb-issue), host-called in
;; host/native/owner.lisp fnn-owner-commit-pipeline, which faults on any
;; verdict but :apply.
(defthm fn-otb-a-late-completion-is-consumed-once
  (let ((c (fn-otb-complete l g cids)))
    (and (iff (equal (car c) :apply)
              (and (fn-otb-open l) (equal (nfix g) (fn-otb-gen l))))
         (implies (not (equal (car c) :apply))
                  (and (null (cadr c)) (equal (caddr c) l)))
         (implies (equal (car c) :apply)
                  (let ((c2 (fn-otb-complete (caddr c) g2 cids2)))
                    (and (not (equal (car c2) :apply))
                         (null (cadr c2))
                         (not (fn-otb-open (caddr c))))))
         (implies (and (equal (car c) :apply)
                       (equal (car (fn-otb-issue (caddr c))) :issued))
                  (and (< (nfix g) (cadr (fn-otb-issue (caddr c))))
                       (equal (car (fn-otb-complete (caddr (fn-otb-issue (caddr c))) g cids3))
                              :stale)))))
  :hints (("Goal" :in-theory (enable fn-otb-complete fn-otb-issue))))

;; KEYSTONE (PRF-384).  A deadline never frees what the I/O owns.  Early
;; answers keep the request open at its generation (the sealed batch stays
;; the syncer's until the completion applies; the host releases it only
;; after fn-otb-complete's :apply, host/native/owner.lisp
;; fnn-log-sync-collected), and no second request is issued while one is
;; open.
(defthm fn-otb-a-deadline-keeps-the-io-owned
  (let ((r (fn-otb-early-run l xss)))
    (and (equal (fn-otb-open (cadr r)) (fn-otb-open l))
         (equal (fn-otb-gen (cadr r)) (fn-otb-gen l))
         (iff (equal (car (fn-otb-issue l)) :issued) (not (fn-otb-open l)))
         (implies (equal (car (fn-otb-issue l)) :issued)
                  (and (fn-otb-open (caddr (fn-otb-issue l)))
                       (equal (fn-otb-gen (caddr (fn-otb-issue l)))
                              (cadr (fn-otb-issue l)))))))
  :hints (("Goal" :in-theory (enable fn-otb-issue))))

(in-theory (disable fn-otb-issue fn-otb-answer-early fn-otb-complete fn-otb-early-run))

; -----------------------------------------------------------------------------
; 2. A read's page dependency: a declared deadline, then a named outcome.
;
; The operator's `read-dependency-ms' limit row (D27: the profile's), or the
; adopted default, 5,000 ms.  SINCE is the recorded time the read began
; waiting for its page, NOW the recorded time of the decision (design
; section 3.7: both are clock events the host appended; ACL2 compares
; them), COMPLETED whether the page's read has completed (its completion
; event consumed into this read's generation, section 1).

(defconst *fn-otb-dependency-default-ms* 5000)

(defun fn-otb-dependency-of-limit (n)
  (declare (xargs :guard t))
  (if (posp n) n *fn-otb-dependency-default-ms*))

(defun fn-otb-dependency-elapsed (since now)
  (declare (xargs :guard t))
  (if (< (nfix since) (nfix now)) (- (nfix now) (nfix since)) 0))

; :serve (the page is here), :unavailable (the deadline passed without it),
; or (:wait MS), MS the time left to the deadline (at least 1).
(defun fn-otb-dependency-step (since now limit completed)
  (declare (xargs :guard t))
  (let ((d (fn-otb-dependency-of-limit limit))
        (e (fn-otb-dependency-elapsed since now)))
    (cond (completed :serve)
          ((<= d e) :unavailable)
          (t (list :wait (- d e))))))

; The reply to a read whose page did not come: RFC 3977 section 3.2.1's
; 403 ("internal fault or problem preventing action from being taken"),
; with the reason.  Never 430 or 423: those say there is no such article,
; and a page that is late is not an article that is absent (NNT-019: 430
; and 423 are visibility observations).
(defun fn-otb-unavailable-line (since now limit)
  (declare (xargs :guard t))
  (append (fn-osch-text "403 article temporarily unavailable; a page it needs was not read within ")
          (fn-osch-decimal (fn-otb-dependency-of-limit limit))
          (fn-osch-text " ms (waited ")
          (fn-osch-decimal (fn-otb-dependency-elapsed since now))
          (fn-osch-text " ms): it is not absent, try again later")
          (list 13 10)))

;; KEYSTONE (PRF-384).  A late page is named, never absence.  The read is
;; answered unavailable exactly when its page has not completed and the
;; declared deadline has passed; a completed page is served whenever it
;; completed; the wait never reaches past the deadline; and the
;; unavailable reply's code is 403 -- not 430 and not 423.  The subjects are
;; fn-otb-dependency-step and fn-otb-unavailable-line: the interface the
;; served read's asynchronous page fault calls (row A4 of
;; build/coordinator/COMPLETE-BEFORE-6.6.0.md; until it lands a cold extent
;; read is synchronous under the owner, host/native/extent.lisp).
(local
 (defthm fn-otb-dependency-step-facts
   (let ((step (fn-otb-dependency-step since now limit completed)))
     (and (iff (equal step :unavailable)
               (and (not completed)
                    (<= (fn-otb-dependency-of-limit limit)
                        (fn-otb-dependency-elapsed since now))))
          (implies completed (equal step :serve))
          (implies (and (consp step) (natp since) (natp now) (<= since now))
                   (and (equal (car step) :wait)
                        (posp (cadr step))
                        (equal (+ now (cadr step))
                               (+ since (fn-otb-dependency-of-limit limit)))))))
   :hints (("Goal" :in-theory (enable fn-otb-dependency-elapsed)))))

(local
 (defthm fn-otb-unavailable-line-code
   (let ((line (fn-otb-unavailable-line since now limit)))
     (and (equal (nth 0 line) 52) (equal (nth 1 line) 48)
          (equal (nth 2 line) 51) (equal (nth 3 line) 32)))
   :hints (("Goal" :in-theory (disable fn-osch-decimal fn-otb-dependency-of-limit
                                       fn-otb-dependency-elapsed)))))

(defthm fn-otb-a-late-page-is-unavailable-never-absent
  (let ((step (fn-otb-dependency-step since now limit completed))
        (code (list (nth 0 (fn-otb-unavailable-line since now limit))
                    (nth 1 (fn-otb-unavailable-line since now limit))
                    (nth 2 (fn-otb-unavailable-line since now limit)))))
    (and (iff (equal step :unavailable)
              (and (not completed)
                   (<= (fn-otb-dependency-of-limit limit)
                       (fn-otb-dependency-elapsed since now))))
         (implies completed (equal step :serve))
         (implies (and (consp step) (natp since) (natp now) (<= since now))
                  (and (equal (car step) :wait)
                       (posp (cadr step))
                       (equal (+ now (cadr step))
                              (+ since (fn-otb-dependency-of-limit limit)))))
         (equal code '(52 48 51))
         (not (equal code '(52 51 48)))
         (not (equal code '(52 50 51)))))
  :hints (("Goal" :use (fn-otb-dependency-step-facts fn-otb-unavailable-line-code)
           :in-theory (disable fn-otb-dependency-step-facts fn-otb-unavailable-line-code
                               fn-otb-dependency-step fn-otb-unavailable-line
                               fn-otb-dependency-of-limit fn-otb-dependency-elapsed))))

(in-theory (disable fn-otb-dependency-step fn-otb-unavailable-line))

; -----------------------------------------------------------------------------
; 3. The restart's clock domain.
;
; A run's decision journal segment begins with its start entry; the entry
; records the semantic observation -- the wall reading and whether it is
; usable (books/owner-time-journal.lisp fn-otm-start-line) -- never a
; monotonic origin, and the replay starts the segment from fn-otm-init.

(local
 (defthm fn-otb-replay-of-a-start-shape
   (implies (and (nat-listp e) (equal (len e) 7) (equal (nth 0 e) 0) (equal (nth 1 e) 0))
            (equal (fn-otm-replay r (cons e e2))
                   (fn-otm-replay (fn-otm-init) e2)))
   :hints (("Goal" :expand ((fn-otm-replay r (cons e e2)))
            :in-theory (disable fn-otm-init (:e fn-otm-init))))))

(local
 (defthm fn-otb-start-entry-shape
   (let ((e (fn-otm-start-entry wall usable)))
     (and (nat-listp e) (equal (len e) 7) (equal (nth 0 e) 0) (equal (nth 1 e) 0)))
   :hints (("Goal" :in-theory (enable fn-otm-start-entry)))))

(local
 (defthm fn-otb-replay-of-a-start
   (equal (fn-otm-replay r (cons (fn-otm-start-entry wall usable) e2))
          (fn-otm-replay (fn-otm-init) e2))
   :hints (("Goal" :use ((:instance fn-otb-replay-of-a-start-shape
                                    (e (fn-otm-start-entry wall usable))))
            :in-theory (disable fn-otb-replay-of-a-start-shape fn-otm-start-entry
                                fn-otm-init (:e fn-otm-init))))))

;; KEYSTONE (PRF-384).  A restart forgets the previous clock domain.
;; Whatever a run's segment E1 held -- its monotonic readings, its pending
;; barrier, its recorded time -- once it replayed to agreement, the next
;; run's segment (its start entry, then E2) replays exactly as it would
;; from nothing: every decision of the new run reads only readings of its
;; own process.  The subject is fn-otm-replay, which the operator's
;; `store ROOT journal' verb calls (host/native/io.lisp, through
;; fn-otm-journal-report and fn-otm-journal-exit), over the start entry
;; host/native/owner.lisp fnn-owner-journal-open writes (fn-otm-start-line).
(defthm fn-otb-a-restart-forgets-the-previous-clock-domain
  (implies (equal (mv-nth 0 (fn-otm-replay s e1)) :agrees)
           (equal (fn-otm-replay s (append e1 (cons (fn-otm-start-entry wall usable) e2)))
                  (fn-otm-replay (fn-otm-init) e2)))
  :hints (("Goal" :use ((:instance fn-otm-jw-replay-append
                                   (r s) (a e1)
                                   (b (cons (fn-otm-start-entry wall usable) e2))))
           :in-theory (disable fn-otm-jw-replay-append fn-otm-start-entry
                               fn-otm-init (:e fn-otm-init)))))

;; KEYSTONE (PRF-951).  The early answer the host calls (host/native/owner.lisp
;; fnn-owner-commit-pipeline, the stall's uncertain release and a stop's)
;; answers each untold member exactly once: NOW has no duplicates, is drawn
;; from CIDS and is disjoint from the connections already told; afterwards
;; every member of CIDS is told, the told list is the old one extended by NOW,
;; and the generation and OPEN are unchanged (the request is still in flight
;; and still owns its I/O).  fn-otb-a-member-is-answered-once above states
;; this over a run of early answers; this theorem is about the entry itself.
(local (defthm fn-otb-in-is-member
         (iff (fn-otb-in x ys) (member-equal x ys))
         :hints (("Goal" :in-theory (enable fn-otb-in)))))
(local (defthm fn-otb-member-of-dedup
         (iff (member-equal x (fn-otb-dedup xs)) (member-equal x xs))
         :hints (("Goal" :induct (fn-otb-dedup xs) :in-theory (enable fn-otb-dedup)))))
(local (defthm fn-otb-member-of-minus
         (iff (member-equal x (fn-otb-minus xs ys))
              (and (member-equal x xs) (not (member-equal x ys))))
         :hints (("Goal" :induct (fn-otb-minus xs ys) :in-theory (enable fn-otb-minus)))))
(local (defthm fn-otb-member-of-append
         (iff (member-equal x (append a b))
              (or (member-equal x a) (member-equal x b)))))
(local (defthm fn-otb-subsetp-cons-weaken
         (implies (subsetp-equal x y) (subsetp-equal x (cons a y)))))
(local (defthm fn-otb-subsetp-reflexive
         (subsetp-equal xs xs)
         :hints (("Goal" :induct (len xs)))))
(local (defthm fn-otb-subsetp-of-dedup
         (subsetp-equal (fn-otb-dedup xs) xs)
         :hints (("Goal" :induct (fn-otb-dedup xs) :in-theory (enable fn-otb-dedup)))))
(local (defthm fn-otb-subsetp-of-minus
         (subsetp-equal (fn-otb-minus xs ys) xs)
         :hints (("Goal" :induct (fn-otb-minus xs ys) :in-theory (enable fn-otb-minus)))))
(local (defthm fn-otb-subsetp-transitive
         (implies (and (subsetp-equal x y) (subsetp-equal y z)) (subsetp-equal x z))))
(local (defthm fn-otb-subsetp-of-dedup-minus
         (subsetp-equal (fn-otb-dedup (fn-otb-minus xs ys)) xs)
         :hints (("Goal" :do-not-induct t
                  :use ((:instance fn-otb-subsetp-transitive
                                   (x (fn-otb-dedup (fn-otb-minus xs ys)))
                                   (y (fn-otb-minus xs ys)) (z xs)))))))
(local (defthm fn-otb-every-member-is-told-or-answered
         (implies (subsetp-equal xs zs)
                  (subsetp-equal xs (append ys (fn-otb-dedup (fn-otb-minus zs ys)))))
         :hints (("Goal" :induct (len xs)))))
(defthm fn-otb-answer-early-answers-each-untold-member-once
  (let* ((r (fn-otb-answer-early l cids))
         (now (car r))
         (l2 (cadr r)))
    (and (no-duplicatesp-equal now)
         (subsetp-equal now cids)
         (not (intersectp-equal now (fn-otb-told l)))
         (subsetp-equal cids (fn-otb-told l2))
         (equal (fn-otb-told l2) (append (fn-otb-told l) now))
         (equal (fn-otb-gen l2) (fn-otb-gen l))
         (equal (fn-otb-open l2) (fn-otb-open l))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (enable fn-otb-answer-early)
           :use ((:instance fn-otb-subsetp-of-dedup-minus (xs cids) (ys (fn-otb-told l)))
                 (:instance fn-otb-every-member-is-told-or-answered
                            (xs cids) (zs cids) (ys (fn-otb-told l)))))))
