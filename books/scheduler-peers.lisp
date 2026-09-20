; fn: the per-peer scheduler table (specs/peering.md section 3.1).
;
; A transit feed needs one contact window, one retry budget and one queue PER
; PEER: the owner opens a connection to each configured outbound peer and
; ticks each one under its own contact.  This book is that layer, and it is a
; TABLE of schedulers rather than a peer field inside one scheduler.
;
; Why a table and not a peer field on `fn-sched-item' (the shape the feed
; lane's proposal carried).  With one queue holding items for several peers,
; selection has to skip the items whose peer is not the open contact's, and
; two of books/scheduler-invariants' keystones become FALSE as stated:
;
;   fn-sched-promotion-position-decreases  --- its hypothesis is
;     `(fn-sched-eligiblep (fn-sched-find w (fn-sched-queue ss)) wf)', which
;     is peer-blind, so a promoted work for peer B while the open contact is
;     peer A is neither selected nor moved closer to the head: the conclusion
;     fails on a reachable state.
;   fn-sched-aging-bound --- likewise through `fn-sched-eligible-runp', which
;     is that same peer-blind test iterated.
;
; Making the test peer-aware means adding an argument to `fn-sched-eligiblep',
; which is in the KEYSTONE's statement: that is a weakened keystone, which
; this lane may not ship.  With one `fn-sched-statep' per peer every existing
; keystone stands verbatim and applies to each peer's own tick, which is what
; `fn-sched-table-tick-is-the-peer-tick' below says: the function the host
; calls IS `fn-sched-tick-step' on that peer's state (AGENTS.md, the theorem
; subject is the function the host calls).  The aging bound is then a
; per-contact bound, which is what it always meant.
;
; The table's keys are peer names (`fn-cfg-peer-name', books/peer-config), so
; a configured peer's feed state is found by the name the configuration
; record carries and by nothing else.

(in-package "ACL2")
(include-book "scheduler-invariants")

(local (in-theory (enable fn-sched-vocabulary)))

; -----------------------------------------------------------------------------
; The table
;
; An alist of (peer-name . scheduler-state) with distinct keys.  `find' is the
; lookup, `put' replaces in place and appends at the end otherwise, so the
; order of the table is the order the peers were first opened and no
; transition reorders it.

(defun fn-sched-table-find (peer tbl)
  (declare (xargs :guard t))
  (if (consp tbl)
      (if (and (consp (car tbl)) (equal (car (car tbl)) peer))
          (cdr (car tbl))
        (fn-sched-table-find peer (cdr tbl)))
    nil))

(defun fn-sched-table-boundp (peer tbl)
  (declare (xargs :guard t))
  (if (consp tbl)
      (or (and (consp (car tbl)) (equal (car (car tbl)) peer))
          (fn-sched-table-boundp peer (cdr tbl)))
    nil))

(defun fn-sched-tablep (tbl)
  (declare (xargs :guard t))
  (if (consp tbl)
      (and (consp (car tbl))
           (stringp (car (car tbl)))
           (fn-sched-statep (cdr (car tbl)))
           (not (fn-sched-table-boundp (car (car tbl)) (cdr tbl)))
           (fn-sched-tablep (cdr tbl)))
    (null tbl)))

(defthm fn-sched-tablep-forward-true-listp
  (implies (fn-sched-tablep tbl) (true-listp tbl))
  :rule-classes :forward-chaining)

(defun fn-sched-table-put (peer ss tbl)
  (declare (xargs :guard t))
  (if (consp tbl)
      (if (and (consp (car tbl)) (equal (car (car tbl)) peer))
          (cons (cons peer ss) (cdr tbl))
        (cons (car tbl) (fn-sched-table-put peer ss (cdr tbl))))
    (list (cons peer ss))))

(defun fn-sched-table-peers (tbl)
  (declare (xargs :guard t))
  (if (consp tbl)
      (if (consp (car tbl))
          (cons (car (car tbl)) (fn-sched-table-peers (cdr tbl)))
        (fn-sched-table-peers (cdr tbl)))
    nil))

; -----------------------------------------------------------------------------
; Lookup and update facts

(defthm fn-sched-table-find-of-put-same
  (equal (fn-sched-table-find peer (fn-sched-table-put peer ss tbl)) ss))

(defthm fn-sched-table-find-of-put-other
  (implies (not (equal other peer))
           (equal (fn-sched-table-find other (fn-sched-table-put peer ss tbl))
                  (fn-sched-table-find other tbl))))

(defthm fn-sched-table-boundp-of-put
  (implies (not (equal other peer))
           (equal (fn-sched-table-boundp other (fn-sched-table-put peer ss tbl))
                  (fn-sched-table-boundp other tbl))))

(defthm fn-sched-tablep-of-put
  (implies (and (fn-sched-tablep tbl) (stringp peer) (fn-sched-statep ss))
           (fn-sched-tablep (fn-sched-table-put peer ss tbl)))
  :hints (("Goal" :in-theory (disable fn-sched-statep))))

(defthm fn-sched-table-boundp-when-find
  (implies (fn-sched-table-find peer tbl)
           (fn-sched-table-boundp peer tbl)))

; The key a transition writes back is already bound, so `stringp' comes from
; the entry that is there and not from a fresh hypothesis.
(defthm fn-sched-tablep-of-put-when-bound
  (implies (and (fn-sched-tablep tbl)
                (fn-sched-table-boundp peer tbl)
                (fn-sched-statep ss))
           (fn-sched-tablep (fn-sched-table-put peer ss tbl)))
  :hints (("Goal" :in-theory (disable fn-sched-statep))))

(defthm fn-sched-statep-of-table-find
  (implies (and (fn-sched-tablep tbl) (fn-sched-table-find peer tbl))
           (fn-sched-statep (fn-sched-table-find peer tbl)))
  :hints (("Goal" :in-theory (disable fn-sched-statep))))

; -----------------------------------------------------------------------------
; The transitions: each one is the single-peer transition on that peer's own
; state and nothing else.  A peer with no entry is a no-op: the owner installs
; an entry with `fn-sched-table-install' when it reads the peer record, and a
; removed peer's entry is dropped by `fn-sched-table-forget'.

(defun fn-sched-table-install (peer config next-tx tbl)
  (declare (xargs :guard t))
  (if (or (not (stringp peer))
          (not (fn-sched-configp config))
          (not (natp next-tx))
          (fn-sched-table-boundp peer tbl))
      tbl
    (fn-sched-table-put peer (fn-sched-initial-state config next-tx) tbl)))

(defun fn-sched-table-forget (peer tbl)
  (declare (xargs :guard t))
  (if (consp tbl)
      (if (and (consp (car tbl)) (equal (car (car tbl)) peer))
          (cdr tbl)
        (cons (car tbl) (fn-sched-table-forget peer (cdr tbl))))
    nil))

(defun fn-sched-table-step (peer tbl wf event)
  (declare (xargs :guard t))
  (let ((ss (fn-sched-table-find peer tbl)))
    (if (null ss)
        (fn-sched-result tbl wf nil)
      (let ((r (fn-sched-step ss wf event)))
        (fn-sched-result (fn-sched-table-put peer (fn-sched-result-ss r) tbl)
                         (fn-sched-result-wf r)
                         (fn-sched-result-effects r))))))

; One peer's contact tick.  The result triple is books/scheduler's
; `fn-sched-result' with the TABLE in the state slot: the workflow and the
; effects are the peer tick's own, unchanged.
(defun fn-sched-table-tick (peer tbl wf attempt-id)
  (declare (xargs :guard t))
  (let ((ss (fn-sched-table-find peer tbl)))
    (if (null ss)
        (fn-sched-result tbl wf nil)
      (let ((r (fn-sched-tick-step ss wf attempt-id)))
        (fn-sched-result (fn-sched-table-put peer (fn-sched-result-ss r) tbl)
                         (fn-sched-result-wf r)
                         (fn-sched-result-effects r))))))

; -----------------------------------------------------------------------------
; KEYSTONE.  The subject rule.  The function the host calls once per peer per
; tick is `fn-sched-tick-step' on that peer's own scheduler state: the same
; workflow, the same effects, and the peer's new state under its own key.
; Every keystone of books/scheduler-invariants therefore holds of the per-peer
; tick with no restatement --- in particular `fn-sched-aging-bound' and
; `fn-sched-retries-stay-within-the-contact-bound', which are per contact and
; are now per peer because each peer owns its contact.

(defthm fn-sched-table-tick-is-the-peer-tick
  (implies (fn-sched-table-find peer tbl)
           (and (equal (fn-sched-result-effects
                        (fn-sched-table-tick peer tbl wf attempt-id))
                       (fn-sched-result-effects
                        (fn-sched-tick-step (fn-sched-table-find peer tbl)
                                            wf attempt-id)))
                (equal (fn-sched-result-wf
                        (fn-sched-table-tick peer tbl wf attempt-id))
                       (fn-sched-result-wf
                        (fn-sched-tick-step (fn-sched-table-find peer tbl)
                                            wf attempt-id)))
                (equal (fn-sched-table-find
                        peer (fn-sched-result-ss
                              (fn-sched-table-tick peer tbl wf attempt-id)))
                       (fn-sched-result-ss
                        (fn-sched-tick-step (fn-sched-table-find peer tbl)
                                            wf attempt-id)))))
  :hints (("Goal" :in-theory (disable fn-sched-tick-step fn-sched-table-put
                                      fn-sched-table-find))))

; KEYSTONE.  A tick for one peer touches no other peer's queue, contact,
; retries or promotion queue: the other entry is the one that was there.
(defthm fn-sched-table-tick-touches-only-its-peer
  (implies (not (equal other peer))
           (equal (fn-sched-table-find
                   other (fn-sched-result-ss
                          (fn-sched-table-tick peer tbl wf attempt-id)))
                  (fn-sched-table-find other tbl)))
  :hints (("Goal" :in-theory (disable fn-sched-tick-step fn-sched-table-put
                                      fn-sched-table-find))))

; KEYSTONE.  The table is a table after a tick, an install, a forget and a
; step: every peer's state stays an `fn-sched-statep', which is the hypothesis
; every scheduler keystone carries.
(defthm fn-sched-tablep-of-table-tick
  (implies (fn-sched-tablep tbl)
           (fn-sched-tablep (fn-sched-result-ss
                             (fn-sched-table-tick peer tbl wf attempt-id))))
  :hints (("Goal" :in-theory (disable fn-sched-tick-step fn-sched-statep
                                      fn-sched-table-put fn-sched-table-find)
           :use ((:instance fn-sched-statep-of-tick-step
                            (ss (fn-sched-table-find peer tbl)))
                 (:instance fn-sched-statep-of-table-find)
                 (:instance fn-sched-tablep-of-put-when-bound
                            (ss (fn-sched-result-ss
                                 (fn-sched-tick-step
                                  (fn-sched-table-find peer tbl)
                                  wf attempt-id))))))))

(defthm fn-sched-tablep-of-install
  (implies (fn-sched-tablep tbl)
           (fn-sched-tablep (fn-sched-table-install peer config next-tx tbl)))
  :hints (("Goal" :in-theory (disable fn-sched-statep fn-sched-table-put
                                      fn-sched-initial-state))))

(defthm fn-sched-tablep-of-forget
  (implies (fn-sched-tablep tbl)
           (fn-sched-tablep (fn-sched-table-forget peer tbl)))
  :hints (("Goal" :in-theory (disable fn-sched-statep))))

(defthm fn-sched-tablep-of-table-step
  (implies (fn-sched-tablep tbl)
           (fn-sched-tablep (fn-sched-result-ss
                             (fn-sched-table-step peer tbl wf event))))
  :hints (("Goal" :in-theory (disable fn-sched-statep fn-sched-step
                                      fn-sched-table-put fn-sched-table-find)
           :use ((:instance fn-sched-step-preserves-state
                            (ss (fn-sched-table-find peer tbl)))
                 (:instance fn-sched-statep-of-table-find)
                 (:instance fn-sched-tablep-of-put-when-bound
                            (ss (fn-sched-result-ss
                                 (fn-sched-step (fn-sched-table-find peer tbl)
                                                wf event))))))))

; A step for one peer touches no other peer's state either.
(defthm fn-sched-table-step-touches-only-its-peer
  (implies (not (equal other peer))
           (equal (fn-sched-table-find
                   other (fn-sched-result-ss
                          (fn-sched-table-step peer tbl wf event)))
                  (fn-sched-table-find other tbl)))
  :hints (("Goal" :in-theory (disable fn-sched-step fn-sched-table-put
                                      fn-sched-table-find))))

; The per-peer retry bound, transported.  This is NOT a new registry event: it
; is `fn-sched-retries-stay-within-the-contact-bound' (books/scheduler-invariants)
; read through the subject rule above, and it is named for what it is.
(defthm fn-sched-table-retries-stay-within-each-peers-bound
  (implies (and (fn-sched-tablep tbl)
                (fn-sched-table-find peer tbl)
                (<= (fn-sched-retries (fn-sched-table-find peer tbl))
                    (fn-sched-retry-bound
                     (fn-sched-conf (fn-sched-table-find peer tbl)))))
           (<= (fn-sched-retries
                (fn-sched-table-find
                 peer (fn-sched-result-ss
                       (fn-sched-table-tick peer tbl wf attempt-id))))
               (fn-sched-retry-bound
                (fn-sched-conf (fn-sched-table-find peer tbl)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-sched-tick-step fn-sched-statep
                                      fn-sched-table-put fn-sched-table-find
                                      fn-sched-retries fn-sched-conf
                                      fn-sched-retry-bound)
           :use ((:instance fn-sched-retries-stay-within-the-contact-bound
                            (ss (fn-sched-table-find peer tbl)))
                 (:instance fn-sched-statep-of-table-find)))))

; -----------------------------------------------------------------------------
; Export policy: the table's own vocabulary is withdrawn on include; the
; lookup facts and the three keystones above stay.

(deftheory fn-sched-table-vocabulary
  '(fn-sched-table-find fn-sched-table-boundp fn-sched-tablep
    fn-sched-table-put fn-sched-table-peers fn-sched-table-install
    fn-sched-table-forget fn-sched-table-step fn-sched-table-tick))

(in-theory (disable fn-sched-table-vocabulary))
