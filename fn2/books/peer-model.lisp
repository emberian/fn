; Layer E4: the reference model of peering and BP custody (fn2/docs/
; e-surface.md section 13), the meaning the served peer path and the bundle
; machine are checked against. Nodes hold local acceptance receipts
; (attributed), portable evidence (union by evidence identity), imported
; foreign receipts (never selecting), gaps, a funded admission budget,
; custody obligations and feed work. Its fixtures are executable obligations
; and checker oracles, not served acceptance evidence (section 13.8).
(in-package "ACL2")
(include-book "consumer-model")
(fn2-book-layer :e)

(defconst *fn2-pm-faults*
  '(:first-arrival :evidence-suppresses :false-complete :resurrect :ack-releases
    :no-loop-check :double-terminal :count-deferrals))
(defconst *fn2-pm-loss-bound* 3)

(defun fn2-pm-get (k st) (declare (xargs :verify-guards nil)) (cdr (assoc-eq k st)))
(defun fn2-pm-put (k v st) (declare (xargs :verify-guards nil)) (put-assoc-eq k v st))
(defun fn2-pm-fault (f st) (declare (xargs :verify-guards nil)) (member-eq f (fn2-pm-get :faults st)))
(defun fn2-pm-node (id budget faults)
  (declare (xargs :verify-guards nil))
  (list (cons :id id) (cons :accepted nil) (cons :evidence nil) (cons :foreign nil) (cons :gaps nil)
        (cons :budget budget) (cons :allocations 0) (cons :reclaimed nil) (cons :obligations nil)
        (cons :work nil) (cons :terminals nil) (cons :faults faults)))

;; Evidence: (:ev EID NAME SUBJECT ISSUER DEPS). Union by EID; a fact whose
;; dependencies are absent is held as a gap, never promoted (ruling 5).
(defun fn2-pm-eid (f) (declare (xargs :verify-guards nil)) (nth 1 f))
(defun fn2-pm-fname (f) (declare (xargs :verify-guards nil)) (nth 2 f))
(defun fn2-pm-fsubject (f) (declare (xargs :verify-guards nil)) (nth 3 f))
(defun fn2-pm-fdeps (f) (declare (xargs :verify-guards nil)) (nth 5 f))
(defun fn2-pm-has-eid (eid facts)
  (declare (xargs :verify-guards nil))
  (cond ((atom facts) nil) ((equal (fn2-pm-eid (car facts)) eid) t) (t (fn2-pm-has-eid eid (cdr facts)))))
(defun fn2-pm-deps-in (deps facts)
  (declare (xargs :verify-guards nil))
  (or (atom deps) (and (fn2-pm-has-eid (car deps) facts) (fn2-pm-deps-in (cdr deps) facts))))
(defun fn2-pm-admit (f st)
  ; (mv VERDICT ST): :known, :admitted, or :gap (unfunded or a dependency absent).
  (declare (xargs :verify-guards nil))
  (let ((facts (fn2-pm-get :evidence st)))
    (cond ((fn2-pm-has-eid (fn2-pm-eid f) facts) (mv :known st))
          ((or (zp (fn2-pm-get :budget st)) (not (fn2-pm-deps-in (fn2-pm-fdeps f) facts)))
           (mv :gap (if (member-equal f (fn2-pm-get :gaps st)) st
                      (fn2-pm-put :gaps (append (fn2-pm-get :gaps st) (list f)) st))))
          (t (mv :admitted
                 (fn2-pm-put :budget (- (fn2-pm-get :budget st) 1)
                   (fn2-pm-put :gaps (remove-equal f (fn2-pm-get :gaps st))
                     (fn2-pm-put :evidence (append facts (list f)) st))))))))

;; The served binding: a fold over evidence alone (sorted subjects per name).
;; FAULT :first-arrival folds the local acceptance instead (a tie-break by
;; arrival, forbidden by ruling 4).
(defun fn2-pm-insert (x xs)
  (declare (xargs :verify-guards nil))
  (cond ((atom xs) (list x)) ((equal x (car xs)) xs)
        ((lexorder x (car xs)) (cons x xs)) (t (cons (car xs) (fn2-pm-insert x (cdr xs))))))
(defun fn2-pm-fold (facts acc)
  (declare (xargs :verify-guards nil))
  (if (atom facts) acc
    (let* ((n (fn2-pm-fname (car facts))) (old (cdr (assoc-equal n acc))))
      (fn2-pm-fold (cdr facts) (put-assoc-equal n (fn2-pm-insert (fn2-pm-fsubject (car facts)) old) acc)))))
(defun fn2-pm-sort-names (al)
  (declare (xargs :verify-guards nil))
  (if (atom al) nil (fn2-pm-insert (car al) (fn2-pm-sort-names (cdr al)))))
(defun fn2-pm-fold-accepted (acc)
  (declare (xargs :verify-guards nil))
  (if (atom acc) nil (cons (list (car (car acc)) (cadr (car acc))) (fn2-pm-fold-accepted (cdr acc)))))
(defun fn2-pm-bindings (st)
  (declare (xargs :verify-guards nil))
  (if (fn2-pm-fault :first-arrival st)
      (fn2-pm-sort-names (fn2-pm-fold-accepted (fn2-pm-get :accepted st)))
    (fn2-pm-sort-names (fn2-pm-fold (fn2-pm-get :evidence st) nil))))
(defun fn2-pm-conflict-p (name st)
  (declare (xargs :verify-guards nil))
  (consp (cdr (cdr (assoc-equal name (fn2-pm-bindings st))))))

;; Local acceptance (POST or transit, after carrier preparation). ACCEPTED
;; rows are (NAME SUBJECT POSITION): this node's attributed receipts.
(defun fn2-pm-local (name st) (declare (xargs :verify-guards nil)) (assoc-equal name (fn2-pm-get :accepted st)))
(defun fn2-pm-accept (name subject eid deps st)
  ; (mv OUTCOME ST): :accepted, :duplicate (evidence still admitted, nothing
  ; allocated), or :conflict (the evidence commits; the article is refused).
  (declare (xargs :verify-guards nil))
  (b* ((fact (list :ev eid name subject (fn2-pm-get :id st) deps))
       (local (fn2-pm-local name st))
       (reclaimed (member-equal name (fn2-pm-get :reclaimed st)))
       ((mv & st) (fn2-pm-admit fact st)))
    (cond ((and local (equal (cadr local) subject))
           (mv :duplicate
               (if (and reclaimed (fn2-pm-fault :resurrect st))
                   (fn2-pm-put :allocations (+ 1 (fn2-pm-get :allocations st))
                     (fn2-pm-put :reclaimed (remove-equal name (fn2-pm-get :reclaimed st)) st))
                 st)))
          (local (mv :conflict st))
          (t (let ((pos (+ 1 (fn2-pm-get :allocations st))))
               (mv :accepted
                   (fn2-pm-put :allocations pos
                     (fn2-pm-put :accepted (append (fn2-pm-get :accepted st) (list (list name subject pos))) st))))))))
(defun fn2-pm-reclaim (name st)
  ; The body goes; identity, the receipt and evidence stay (ruling 9).
  (declare (xargs :verify-guards nil))
  (fn2-pm-put :reclaimed (cons name (fn2-pm-get :reclaimed st)) st))
;; The offer: suppressed only by local acceptance history.
(defun fn2-pm-offer (name st)
  (declare (xargs :verify-guards nil))
  (cond ((fn2-pm-local name st) :have)
        ((and (fn2-pm-fault :evidence-suppresses st) (assoc-equal name (fn2-pm-bindings st))) :have)
        (t :want)))

;; The evidence page: facts and receipts, with the two completion claims.
(defun fn2-pm-receipts (id acc)
  (declare (xargs :verify-guards nil))
  (if (atom acc) nil (cons (cons id (car acc)) (fn2-pm-receipts id (cdr acc)))))
(defun fn2-pm-page (st)
  (declare (xargs :verify-guards nil))
  (list :facts (fn2-pm-get :evidence st)
        :receipts (fn2-pm-receipts (fn2-pm-get :id st) (fn2-pm-get :accepted st))
        :incorporated (or (null (fn2-pm-get :gaps st)) (fn2-pm-fault :false-complete st))))
(defun fn2-pm-admit-all (facts st)
  (declare (xargs :verify-guards nil))
  (if (atom facts) st (mv-let (v st) (fn2-pm-admit (car facts) st) (declare (ignore v)) (fn2-pm-admit-all (cdr facts) st))))
(defun fn2-pm-import (page st)
  ; Facts admitted by identity (retrying held gaps first); foreign receipts
  ; recorded, never selecting.
  (declare (xargs :verify-guards nil))
  (let* ((st (fn2-pm-admit-all (fn2-pm-get :gaps st) st))
         (st (fn2-pm-admit-all (cadr (member-eq :facts page)) st)))
    (fn2-pm-put :foreign (union-equal (cadr (member-eq :receipts page)) (fn2-pm-get :foreign st)) st)))
(defun fn2-pm-fund (n st) (declare (xargs :verify-guards nil)) (fn2-pm-put :budget (+ n (fn2-pm-get :budget st)) st))
(defun fn2-pm-complete-p (st)
  ; The incorporation claim this node makes about its own state.
  (declare (xargs :verify-guards nil))
  (cadr (member-eq :incorporated (fn2-pm-page st))))

;; Custody: (OID SUBJECT AUTHORITY STATE). Released only by a receipt naming
;; this OID from its authority, or an authorized waiver. FAULT :ack-releases
;; lets a transport acknowledgement release.
(defun fn2-pm-oblige (oid subject authority st)
  (declare (xargs :verify-guards nil))
  (fn2-pm-put :obligations (append (fn2-pm-get :obligations st) (list (list oid subject authority :held))) st))
(defun fn2-pm-release-ok (o proof st)
  (declare (xargs :verify-guards nil))
  (or (and (eq (car proof) :receipt) (equal (cadr proof) (car o)) (equal (caddr proof) (caddr o)))
      (and (eq (car proof) :waiver) (equal (cadr proof) (car o)) (equal (caddr proof) :operator))
      (and (eq (car proof) :ack) (fn2-pm-fault :ack-releases st) (equal (cadr proof) (car o)))))
(defun fn2-pm-release-list (oid proof os st)
  (declare (xargs :verify-guards nil))
  (cond ((atom os) (mv :unknown nil))
        ((equal (car (car os)) oid)
         (if (and (eq (cadddr (car os)) :held) (fn2-pm-release-ok (car os) proof st))
             (mv :released (cons (list oid (cadr (car os)) (caddr (car os)) (list :released proof)) (cdr os)))
           (mv :refused os)))
        (t (mv-let (v rest) (fn2-pm-release-list oid proof (cdr os) st) (mv v (cons (car os) rest))))))
(defun fn2-pm-release (oid proof st)
  (declare (xargs :verify-guards nil))
  (mv-let (v os) (fn2-pm-release-list oid proof (fn2-pm-get :obligations st) st)
    (mv v (if (eq v :released) (fn2-pm-put :obligations os st) st))))

;; Feed work: rows (DID PEER STATE LOSSES DEFERRALS) keyed by the delivery
;; identity DID = (epoch . occurrence); STATE is :pending, :offered, or a
;; terminal (:accepted :not-wanted :rejected :dropped :withdrawn). Installed
;; from the selection minus loops (an occurrence whose PATH names the peer).
(defun fn2-pm-install (peer epoch occs st)
  ; OCCS: (OCCURRENCE . PATH) in position order.
  (declare (xargs :verify-guards nil))
  (if (atom occs) st
    (let ((loop (and (member-equal peer (cdar occs)) (not (fn2-pm-fault :no-loop-check st)))))
      (fn2-pm-install peer epoch (cdr occs)
        (if loop st
          (fn2-pm-put :work (append (fn2-pm-get :work st)
                                    (list (list (cons epoch (caar occs)) peer :pending 0 0)))
                      st))))))
(defun fn2-pm-terminal-p (s) (declare (xargs :guard t)) (member-eq s '(:accepted :not-wanted :rejected :dropped :withdrawn)))
(defun fn2-pm-reply-state (code row st)
  ; The row after a reply; a terminal row is unchanged unless the fault.
  (declare (xargs :verify-guards nil))
  (b* (((list did peer s losses deferrals) row)
       (inflight (eq s :offered)))
    (cond ((and (fn2-pm-terminal-p s) (not (fn2-pm-fault :double-terminal st))) row)
          ((member code '(235 239)) (list did peer :accepted losses deferrals))
          ((member code '(435 438)) (list did peer :not-wanted losses deferrals))
          ((member code '(437 439)) (list did peer :rejected losses deferrals))
          ((member code '(431 436))
           (let ((l (if (fn2-pm-fault :count-deferrals st) (+ 1 losses) losses)))
             (list did peer (if (>= l *fn2-pm-loss-bound*) :dropped :pending) l (+ 1 deferrals))))
          ((eq code :withdrawn) (list did peer :withdrawn losses deferrals))
          (t (let ((l (if inflight (+ 1 losses) losses)))
               (list did peer (if (>= l *fn2-pm-loss-bound*) :dropped :pending) l deferrals))))))
(defun fn2-pm-reply-rows (did code rows st)
  (declare (xargs :verify-guards nil))
  (cond ((atom rows) nil)
        ((equal (car (car rows)) did) (cons (fn2-pm-reply-state code (car rows) st) (cdr rows)))
        (t (cons (car rows) (fn2-pm-reply-rows did code (cdr rows) st)))))
(defun fn2-pm-row (did rows) (declare (xargs :verify-guards nil)) (assoc-equal did rows))
(defun fn2-pm-reply (did code st)
  ; Applies one reply and logs each new terminal disposition.
  (declare (xargs :verify-guards nil))
  (let* ((before (fn2-pm-row did (fn2-pm-get :work st)))
         (rows (fn2-pm-reply-rows did code (fn2-pm-get :work st) st))
         (after (fn2-pm-row did rows))
         (st (fn2-pm-put :work rows st)))
    (if (and after (fn2-pm-terminal-p (nth 2 after))
             (not (and before (equal (nth 2 before) (nth 2 after)))))
        (fn2-pm-put :terminals (append (fn2-pm-get :terminals st) (list (cons did (nth 2 after)))) st)
      st)))
(defun fn2-pm-reply-rows-set (did s rows)
  (declare (xargs :verify-guards nil))
  (cond ((atom rows) nil)
        ((equal (car (car rows)) did) (cons (list did (nth 1 (car rows)) s (nth 3 (car rows)) (nth 4 (car rows))) (cdr rows)))
        (t (cons (car rows) (fn2-pm-reply-rows-set did s (cdr rows))))))
(defun fn2-pm-offer-row (did st)
  (declare (xargs :verify-guards nil))
  (let ((row (fn2-pm-row did (fn2-pm-get :work st))))
    (if (and row (eq (nth 2 row) :pending))
        (fn2-pm-put :work (fn2-pm-reply-rows-set did :offered (fn2-pm-get :work st)) st)
      st)))
(defun fn2-pm-restart-rows (rows)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil
    (cons (if (eq (nth 2 (car rows)) :offered)
              (list (nth 0 (car rows)) (nth 1 (car rows)) :pending (nth 3 (car rows)) (nth 4 (car rows)))
            (car rows))
          (fn2-pm-restart-rows (cdr rows)))))
(defun fn2-pm-restart (st)
  ; Every unresolved attempt is retired; its row is re-offered by CHECK/IHAVE.
  (declare (xargs :verify-guards nil))
  (fn2-pm-put :work (fn2-pm-restart-rows (fn2-pm-get :work st)) st))
;; The fair selector: the oldest pending row whose deferrals are below the
;; offered bound, so a deferred head does not block later work.
(defun fn2-pm-next (rows)
  (declare (xargs :verify-guards nil))
  (cond ((atom rows) nil)
        ((and (eq (nth 2 (car rows)) :pending) (< (nth 4 (car rows)) 2)) (car (car rows)))
        (t (fn2-pm-next (cdr rows)))))

;; ---------------------------------------------------------------------------
;; Keystone checkers (owed-peer.lisp states them).
(defun fn2-pm-kp1 (a b)
  ; Equal incorporated evidence, no gaps: equal bindings and conflict predicates.
  (declare (xargs :verify-guards nil))
  (implies (and (equal (fn2-pm-sort-names (fn2-pm-get :evidence a)) (fn2-pm-sort-names (fn2-pm-get :evidence b)))
                (null (fn2-pm-get :gaps a)) (null (fn2-pm-get :gaps b)))
           (equal (fn2-pm-bindings a) (fn2-pm-bindings b))))
(defun fn2-pm-count (did ts)
  (declare (xargs :verify-guards nil))
  (cond ((atom ts) 0) ((equal (car (car ts)) did) (+ 1 (fn2-pm-count did (cdr ts)))) (t (fn2-pm-count did (cdr ts)))))
(defun fn2-pm-kp4-list (ts all)
  (declare (xargs :verify-guards nil))
  (or (atom ts) (and (<= (fn2-pm-count (car (car ts)) all) 1) (fn2-pm-kp4-list (cdr ts) all))))
(defun fn2-pm-kp4 (st)
  ; At most one terminal disposition per delivery identity, ever.
  (declare (xargs :verify-guards nil))
  (fn2-pm-kp4-list (fn2-pm-get :terminals st) (fn2-pm-get :terminals st)))
(defun fn2-pm-kp3a-rows (rows ts)
  (declare (xargs :verify-guards nil))
  (or (atom rows)
      (and (if (fn2-pm-terminal-p (nth 2 (car rows)))
               (equal (cdr (assoc-equal (car (car rows)) ts)) (nth 2 (car rows)))
             (member-eq (nth 2 (car rows)) '(:pending :offered)))
           (fn2-pm-kp3a-rows (cdr rows) ts))))
(defun fn2-pm-kp3a (installed st)
  ; Every installed responsibility is still a row, pending or with its one
  ; logged terminal disposition.
  (declare (xargs :verify-guards nil))
  (and (equal (len (fn2-pm-get :work st)) installed)
       (fn2-pm-kp3a-rows (fn2-pm-get :work st) (fn2-pm-get :terminals st))))

;; A run of operations over one node, for the keystones' statements:
;; (:accept NAME SUBJECT EID DEPS) (:reclaim NAME) (:import PAGE) (:fund N)
;; (:oblige OID SUBJECT AUTHORITY) (:release OID PROOF) (:install PEER EPOCH OCCS)
;; (:offer DID) (:reply DID CODE) (:restart).
(defun fn2-pm-step (op st)
  (declare (xargs :verify-guards nil))
  (case (car op)
    (:accept (mv-let (o st) (fn2-pm-accept (nth 1 op) (nth 2 op) (nth 3 op) (nth 4 op) st) (declare (ignore o)) st))
    (:reclaim (fn2-pm-reclaim (nth 1 op) st))
    (:import (fn2-pm-import (nth 1 op) st))
    (:fund (fn2-pm-fund (nfix (nth 1 op)) st))
    (:oblige (fn2-pm-oblige (nth 1 op) (nth 2 op) (nth 3 op) st))
    (:release (mv-let (o st) (fn2-pm-release (nth 1 op) (nth 2 op) st) (declare (ignore o)) st))
    (:install (fn2-pm-install (nth 1 op) (nth 2 op) (nth 3 op) st))
    (:offer (fn2-pm-offer-row (nth 1 op) st))
    (:reply (fn2-pm-reply (nth 1 op) (nth 2 op) st))
    (:restart (fn2-pm-restart st))
    (otherwise st)))
(defun fn2-pm-run (ops st)
  (declare (xargs :verify-guards nil))
  (if (atom ops) st (fn2-pm-run (cdr ops) (fn2-pm-step (car ops) st))))
;; K-P5's checker: every released obligation names a proof that releases it.
(defun fn2-pm-kp5-list (os)
  (declare (xargs :verify-guards nil))
  (or (atom os)
      (and (let ((s (cadddr (car os))))
             (or (eq s :held)
                 (and (consp s) (eq (car s) :released)
                      (let ((proof (cadr s)))
                        (or (and (eq (car proof) :receipt) (equal (cadr proof) (car (car os)))
                                 (equal (caddr proof) (caddr (car os))))
                            (and (eq (car proof) :waiver) (equal (cadr proof) (car (car os)))
                                 (equal (caddr proof) :operator)))))))
           (fn2-pm-kp5-list (cdr os)))))
(defun fn2-pm-kp5 (st) (declare (xargs :verify-guards nil)) (fn2-pm-kp5-list (fn2-pm-get :obligations st)))
