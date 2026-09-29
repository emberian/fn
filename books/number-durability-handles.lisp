; fn: local article numbering is independent of payload handles
; (PKT-886; PRF-903, lane correctness-i4-2).
;
; books/number-durability.lisp states its extension premise over Store ROWS
; (held records, a payload HANDLE at the payload position).  A live arena
; that sealed a payload for a POST refused after its seal numbers later
; handles differently from the fresh intern at the open, so the live rows
; of the fenced prefix and the recovered rows can be the same Store events
; with different handles.  This book removes that gap: the configured
; replay reads a handle only to carry it, so its result up to handles is a
; function of the history up to handles.
;
; FN-NDH-EVENTS replaces every handle (a natural at a held record's payload
; position, or in a retained composite's held part) by 0 and leaves every
; other event alone; FN-NDH-CNODE / -NODE / -STATE do the same to the
; articles and the pending proposal of a node.  A non-natural payload is
; kept, so every recognizer answers the same on both sides.
;
;   fn-ndh-cpr-loop: the configured replay fold (fn-cpr-loop, the fold
;   fn-cpo-open-observed's open replays) of the events up to handles ends
;   in the same kind, at the node up to handles.  fn-ndh-cst-replay-node:
;   so is the replayed, advanced node (fn-cst-replay-node).  Every step
;   commutes: fn-ndh-cpr-apply-event, fn-ndh-cnode-apply-config,
;   fn-ndh-replay-apply-record, fn-ndh-node-prepare, fn-ndh-node-complete.
;
;   KEYSTONE fn-ndh-replay-extension-keeps-every-number: the extension
;   keystone (fn-ndur-replay-extension-keeps-every-number) with its premise
;   up to handles, (fn-sf-prefixp (fn-ndh-events xs) (fn-ndh-events ys)).
;
;   KEYSTONE fn-ndh-recovery-keeps-every-visible-number: the host open's
;   keystone (fn-ndur-recovery-keeps-every-visible-number; the subject is
;   fn-cpo-open-observed, reached from host/store-node-host.lisp
;   fn-store-sn-recover-rows through fn-rii-sco-extend-open, as there) with
;   the premise that the recovered rows extend the fenced live rows UP TO
;   HANDLES.  Rows that extend exactly also extend up to handles
;   (fn-ndh-prefixp-of-prefixp), so this is the stronger theorem.
;
; Teeth: tests/acl2/number-durability-tests.lisp (a live history whose
; arena sealed a refused POST's payload first: its rows are not a prefix of
; the recovered rows, they are one up to handles, and every visible number
; is kept).  PRF-903.
(in-package "ACL2")
(include-book "number-durability")

(defun fn-ndh-handle (p)
  (declare (xargs :guard t))
  (if (natp p) 0 p))

(defun fn-ndh-article (a)
  (declare (xargs :guard t))
  (if (fn-article-shapep a)
      (fn-make-article (fn-article-msgid a) (fn-ndh-handle (fn-article-payload a))
                       (fn-article-groups a) (fn-article-memberships a)
                       (fn-article-pin a) (fn-article-stamp a))
    a))

(defun fn-ndh-articles (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (cons (fn-ndh-article (car xs)) (fn-ndh-articles (cdr xs)))
    xs))

(defun fn-ndh-pending (p)
  (declare (xargs :guard t))
  (if (fn-pending-shapep p)
      (fn-make-pending (fn-pending-txid p) (fn-pending-generation p)
                       (fn-pending-msgid p) (fn-ndh-handle (fn-pending-payload p))
                       (fn-pending-groups p) (fn-pending-memberships p)
                       (fn-pending-pin p) (fn-pending-stamp p))
    p))

(defun fn-ndh-state (s)
  (declare (xargs :guard t))
  (if (fn-state-shapep s)
      (fn-make-state (fn-state-groups s) (fn-state-nexts s)
                     (fn-ndh-articles (fn-state-articles s))
                     (fn-state-next-txid s)
                     (fn-ndh-pending (fn-state-pending s))
                     (fn-state-fenced s))
    s))

(defun fn-ndh-node (n)
  (declare (xargs :guard t))
  (if (fn-node-state-shapep n)
      (fn-node-make-state (fn-ndh-state (fn-node-acceptance n))
                          (fn-node-retention n) (fn-node-stage n)
                          (fn-node-bindings n))
    n))

(defun fn-ndh-cnode (cn)
  (declare (xargs :guard t))
  (if (fn-cnode-shapep cn)
      (fn-cnode-make (fn-ndh-node (fn-cnode-node cn)) (fn-cnode-config cn))
    cn))

(defun fn-ndh-held (h)
  (declare (xargs :guard t))
  (if (fn-held-shapep h)
      (fn-held-make (fn-held-sequence h) (fn-held-txid h) (fn-held-generation h)
                    (fn-held-msgid h) (fn-ndh-handle (fn-held-payload h))
                    (fn-held-groups h) (fn-held-obligation-id h)
                    (fn-held-content-subject h) (fn-held-release-evidence h)
                    (fn-held-charge h) (fn-held-stamp h) (fn-held-facts h)
                    (fn-held-context h) (fn-held-numbers h) (fn-held-withdrawn h))
    h))

(defun fn-ndh-event (e)
  (declare (xargs :guard t))
  (cond ((fn-held-p e) (fn-ndh-held e))
        ((fn-hstxa-p e) (fn-hstxa-make (fn-hstxa-stxa e) (fn-ndh-held (fn-hstxa-held e))))
        (t e)))

(defun fn-ndh-events (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (cons (fn-ndh-event (car xs)) (fn-ndh-events (cdr xs)))
    xs))

(defthm fn-ndh-held-p-of-held
  (equal (fn-held-p (fn-ndh-held h)) (fn-held-p h))
  :hints (("Goal" :in-theory (enable fn-held-p))))

(defthm fn-ndh-handle-natp
  (equal (natp (fn-ndh-handle p)) (natp p)))

(defthm fn-ndh-article-fields
  (and (equal (fn-article-msgid (fn-ndh-article a)) (fn-article-msgid a))
       (equal (fn-article-groups (fn-ndh-article a)) (fn-article-groups a))
       (equal (fn-article-memberships (fn-ndh-article a)) (fn-article-memberships a))
       (equal (fn-article-pin (fn-ndh-article a)) (fn-article-pin a))
       (equal (fn-article-stamp (fn-ndh-article a)) (fn-article-stamp a))
       (equal (fn-article-shapep (fn-ndh-article a)) (fn-article-shapep a)))
  :hints (("Goal" :in-theory (enable fn-article-internals))))

(defthm fn-ndh-articlep
  (equal (fn-articlep configured (fn-ndh-article a)) (fn-articlep configured a))
  :hints (("Goal" :in-theory (e/d (fn-articlep fn-article-internals fn-payload-handle-p) (fn-ndh-handle)))))

(in-theory (disable fn-ndh-article))

(defthm fn-ndh-articles-msgids
  (equal (fn-article-msgids (fn-ndh-articles xs)) (fn-article-msgids xs))
  :hints (("Goal" :in-theory (enable fn-article-msgids fn-article-msgids-rev))))

(defthm fn-ndh-article-listp
  (equal (fn-article-listp configured (fn-ndh-articles xs)) (fn-article-listp configured xs))
  :hints (("Goal" :in-theory (enable fn-article-listp))))

(defthm fn-ndh-acceptedp
  (equal (fn-acceptedp msgid (fn-ndh-articles xs)) (fn-acceptedp msgid xs))
  :hints (("Goal" :in-theory (enable fn-acceptedp))))

(defthm fn-ndh-all-article-memberships
  (equal (fn-all-article-memberships (fn-ndh-articles xs)) (fn-all-article-memberships xs))
  :hints (("Goal" :in-theory (enable fn-all-article-memberships))))

(defthm fn-ndh-memberships-conflictsp
  (equal (fn-memberships-conflictsp m (fn-ndh-articles xs)) (fn-memberships-conflictsp m xs))
  :hints (("Goal" :in-theory (enable fn-memberships-conflictsp))))

(defthm fn-ndh-articles-freshp
  (equal (fn-articles-freshp (fn-ndh-articles xs)) (fn-articles-freshp xs))
  :hints (("Goal" :in-theory (enable fn-articles-freshp))))

(defthm fn-ndh-articles-below-nextsp
  (equal (fn-articles-below-nextsp (fn-ndh-articles xs) nexts) (fn-articles-below-nextsp xs nexts))
  :hints (("Goal" :in-theory (enable fn-articles-below-nextsp))))

(defthm fn-ndh-holder
  (equal (fn-ndur-holder g n (fn-ndh-articles xs)) (fn-ndur-holder g n xs))
  :hints (("Goal" :in-theory (enable fn-ndur-holder))))

(defthm fn-ndh-pending-fields
  (and (equal (fn-pending-txid (fn-ndh-pending p)) (fn-pending-txid p))
       (equal (fn-pending-generation (fn-ndh-pending p)) (fn-pending-generation p))
       (equal (fn-pending-msgid (fn-ndh-pending p)) (fn-pending-msgid p))
       (equal (fn-pending-groups (fn-ndh-pending p)) (fn-pending-groups p))
       (equal (fn-pending-memberships (fn-ndh-pending p)) (fn-pending-memberships p))
       (equal (fn-pending-pin (fn-ndh-pending p)) (fn-pending-pin p))
       (equal (fn-pending-stamp (fn-ndh-pending p)) (fn-pending-stamp p))
       (equal (fn-pending-shapep (fn-ndh-pending p)) (fn-pending-shapep p))
       (equal (consp (fn-ndh-pending p)) (consp p))
       (equal (null (fn-ndh-pending p)) (null p)))
  :hints (("Goal" :in-theory (enable fn-pending-internals))))

(defthm fn-ndh-pendingp
  (equal (fn-pendingp configured nexts next-txid (fn-ndh-pending p))
         (fn-pendingp configured nexts next-txid p))
  :hints (("Goal" :in-theory (e/d (fn-pendingp fn-pending-internals) (fn-ndh-handle)))))

(defthm fn-ndh-pending-matchesp
  (equal (fn-pending-matchesp (fn-ndh-pending p) txid generation)
         (fn-pending-matchesp p txid generation))
  :hints (("Goal" :in-theory (enable fn-pending-matchesp))))

(in-theory (disable fn-ndh-pending))

(defthm fn-ndh-state-fields
  (and (equal (fn-state-groups (fn-ndh-state s)) (fn-state-groups s))
       (equal (fn-state-nexts (fn-ndh-state s)) (fn-state-nexts s))
       (equal (fn-state-next-txid (fn-ndh-state s)) (fn-state-next-txid s))
       (equal (fn-state-fenced (fn-ndh-state s)) (fn-state-fenced s))
       (equal (fn-state-shapep (fn-ndh-state s)) (fn-state-shapep s))
       (implies (fn-state-shapep s)
                (and (equal (fn-state-articles (fn-ndh-state s)) (fn-ndh-articles (fn-state-articles s)))
                     (equal (fn-state-pending (fn-ndh-state s)) (fn-ndh-pending (fn-state-pending s))))))
  :hints (("Goal" :in-theory (enable fn-state-internals))))

(defthm fn-ndh-statep
  (equal (fn-statep (fn-ndh-state s)) (fn-statep s))
  :hints (("Goal" :in-theory (e/d (fn-statep) (fn-ndh-state)))))

(defthm fn-ndh-pending-of-make
  (equal (fn-ndh-pending (fn-make-pending txid g m p gr ms pin st))
         (fn-make-pending txid g m (fn-ndh-handle p) gr ms pin st))
  :hints (("Goal" :in-theory (enable fn-ndh-pending))))

(defthm fn-ndh-pending-nil (equal (fn-ndh-pending nil) nil)
  :hints (("Goal" :in-theory (enable fn-ndh-pending))))

(defthm fn-ndh-state-of-make
  (equal (fn-ndh-state (fn-make-state gr nx arts txid pend fenced))
         (fn-make-state gr nx (fn-ndh-articles arts) txid (fn-ndh-pending pend) fenced)))

(defthm fn-ndh-article-from-pending
  (implies (fn-pending-shapep p)
           (equal (fn-article-from-pending (fn-ndh-pending p))
                  (fn-ndh-article (fn-article-from-pending p))))
  :hints (("Goal" :in-theory (enable fn-ndh-pending fn-ndh-article fn-article-from-pending fn-pending-internals fn-article-internals))))

(in-theory (disable fn-ndh-state))

(defthm fn-ndh-accept-prepare
  (equal (fn-accept-prepare (fn-ndh-state s) generation msgid (fn-ndh-handle payload) groups stamp)
         (fn-ndh-state (fn-accept-prepare s generation msgid payload groups stamp)))
  :hints (("Goal" :in-theory (e/d (fn-accept-prepare) (fn-statep fn-ndh-handle)))))

(defthm fn-ndh-statep-pending-shapep
  (implies (and (fn-statep s) (consp (fn-state-pending s)))
           (fn-pending-shapep (fn-state-pending s)))
  :hints (("Goal" :in-theory (enable fn-statep))))

(defthm fn-ndh-accept-complete
  (equal (fn-accept-complete (fn-ndh-state s) txid generation status)
         (fn-ndh-state (fn-accept-complete s txid generation status)))
  :hints (("Goal" :in-theory (e/d (fn-accept-complete fn-install-pending fn-clear-pending) (fn-statep fn-article-from-pending)))))

(defthm fn-ndh-articles-have-archive-bindingsp
  (equal (fn-node-articles-have-archive-bindingsp (fn-ndh-articles xs) bindings pins)
         (fn-node-articles-have-archive-bindingsp xs bindings pins))
  :hints (("Goal" :in-theory (enable fn-node-articles-have-archive-bindingsp))))

(defthm fn-ndh-node-stagep
  (implies (fn-state-shapep acc)
           (equal (fn-node-stagep (fn-ndh-state acc) committed stage)
                  (fn-node-stagep acc committed stage)))
  :hints (("Goal" :in-theory (enable fn-node-stagep))))

(defthm fn-ndh-node-fields
  (and (equal (fn-node-retention (fn-ndh-node n)) (fn-node-retention n))
       (equal (fn-node-stage (fn-ndh-node n)) (fn-node-stage n))
       (equal (fn-node-bindings (fn-ndh-node n)) (fn-node-bindings n))
       (equal (fn-node-state-shapep (fn-ndh-node n)) (fn-node-state-shapep n))
       (implies (fn-node-state-shapep n)
                (equal (fn-node-acceptance (fn-ndh-node n)) (fn-ndh-state (fn-node-acceptance n)))))
  :hints (("Goal" :in-theory (enable fn-node-state-internals))))

(defthm fn-ndh-node-of-make
  (equal (fn-ndh-node (fn-node-make-state a r st b))
         (fn-node-make-state (fn-ndh-state a) r st b)))

(defthm fn-ndh-node-nil (equal (fn-ndh-node nil) nil))

(in-theory (disable fn-ndh-node))

(defthm fn-ndh-node-statep
  (equal (fn-node-statep (fn-ndh-node n)) (fn-node-statep n))
  :hints (("Goal" :in-theory (e/d (fn-node-statep) (fn-statep)))))

(defthm fn-ndh-node-statep-shape
  (implies (fn-node-statep n)
           (and (fn-node-state-shapep n) (fn-state-shapep (fn-node-acceptance n))))
  :hints (("Goal" :in-theory (enable fn-node-statep fn-statep))))

(defthm fn-ndh-node-pending-matchesp
  (equal (fn-node-pending-matchesp (fn-ndh-node n) txid generation)
         (fn-node-pending-matchesp n txid generation))
  :hints (("Goal" :in-theory (e/d (fn-node-pending-matchesp) (fn-node-statep)))))

(defthm fn-ndh-replay-advance-txid
  (equal (fn-replay-advance-txid (fn-ndh-node n) txid)
         (fn-ndh-node (fn-replay-advance-txid n txid)))
  :hints (("Goal" :in-theory (e/d (fn-replay-advance-txid) (fn-node-statep)))))

(in-theory (disable fn-ndh-handle))

(defthmd fn-ndh-accept-prepare-moves-the-txid
  (implies (and (fn-statep a)
                (not (equal (fn-accept-prepare a generation msgid payload groups stamp) a)))
           (equal (fn-state-next-txid (fn-accept-prepare a generation msgid payload groups stamp))
                  (+ 1 (fn-state-next-txid a))))
  :hints (("Goal" :in-theory (e/d (fn-accept-prepare) (fn-statep)))))

(defthm fn-ndh-statep-txid-natp
  (implies (fn-statep a) (natp (fn-state-next-txid a)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-statep))))

(defthm fn-ndh-accept-prepare-unchanged-iff
  (implies (fn-statep a)
           (equal (equal (fn-ndh-state (fn-accept-prepare a generation msgid payload groups stamp))
                         (fn-ndh-state a))
                  (equal (fn-accept-prepare a generation msgid payload groups stamp) a)))
  :hints (("Goal" :in-theory (e/d () (fn-statep fn-accept-prepare fn-ndh-state-fields))
                  :use (fn-ndh-accept-prepare-moves-the-txid
                        (:instance fn-ndh-state-fields (s (fn-accept-prepare a generation msgid payload groups stamp)))
                        (:instance fn-ndh-state-fields (s a))))))

(defthm fn-ndh-node-prepare
  (equal (fn-node-prepare (fn-ndh-node n) generation msgid (fn-ndh-handle payload) groups
                          obligation-id subject evidence charge stamp)
         (fn-ndh-node (fn-node-prepare n generation msgid payload groups
                                       obligation-id subject evidence charge stamp)))
  :hints (("Goal" :in-theory (e/d (fn-node-prepare) (fn-node-statep fn-accept-prepare fn-ndh-handle)))))

(defthm fn-ndh-node-pending-matchesp-statep
  (implies (fn-node-pending-matchesp n txid generation) (fn-node-statep n))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d (fn-node-pending-matchesp) (fn-node-statep)))))

(defthm fn-ndh-node-complete
  (equal (fn-node-complete (fn-ndh-node n) txid generation status)
         (fn-ndh-node (fn-node-complete n txid generation status)))
  :hints (("Goal" :in-theory (e/d (fn-node-complete) (fn-node-statep fn-accept-complete fn-node-pending-matchesp)))))

(defthm fn-ndh-held-fields
  (implies (fn-held-shapep h)
           (and (equal (fn-record-sequence (fn-ndh-held h)) (fn-record-sequence h))
                (equal (fn-record-txid (fn-ndh-held h)) (fn-record-txid h))
                (equal (fn-record-generation (fn-ndh-held h)) (fn-record-generation h))
                (equal (fn-record-msgid (fn-ndh-held h)) (fn-record-msgid h))
                (equal (fn-record-payload (fn-ndh-held h)) (fn-ndh-handle (fn-record-payload h)))
                (equal (fn-record-groups (fn-ndh-held h)) (fn-record-groups h))
                (equal (fn-record-obligation-id (fn-ndh-held h)) (fn-record-obligation-id h))
                (equal (fn-record-content-subject (fn-ndh-held h)) (fn-record-content-subject h))
                (equal (fn-record-release-evidence (fn-ndh-held h)) (fn-record-release-evidence h))
                (equal (fn-record-charge (fn-ndh-held h)) (fn-record-charge h))
                (equal (fn-record-stamp (fn-ndh-held h)) (fn-record-stamp h))))
  :hints (("Goal" :in-theory (enable fn-held-internals fn-record-internals))))

(defthm fn-ndh-held-p-shape
  (implies (fn-held-p h) (fn-held-shapep h))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-held-p))))

(in-theory (disable fn-ndh-held))

(defthm fn-ndh-held-disjoint
  (implies (fn-held-p x)
           (and (not (fn-store-retention-event-p x)) (not (fn-stxe-p x)) (not (fn-stxk-p x))
                (not (fn-cpe-eventp x)) (not (fn-th-topic-eventp x)) (not (fn-hstxa-p x)))))

(defthm fn-ndh-hstxa-disjoint
  (implies (fn-hstxa-p x)
           (and (not (fn-held-p x)) (not (fn-store-retention-event-p x)) (not (fn-stxe-p x)) (not (fn-stxk-p x))
                (not (fn-cpe-eventp x)) (not (fn-th-topic-eventp x)))))

(defthm fn-ndh-event-kinds
  (and (equal (fn-held-p (fn-ndh-event e)) (fn-held-p e))
       (equal (fn-hstxa-p (fn-ndh-event e)) (fn-hstxa-p e))
       (equal (fn-store-retention-event-p (fn-ndh-event e)) (fn-store-retention-event-p e))
       (equal (fn-stxe-p (fn-ndh-event e)) (fn-stxe-p e))
       (equal (fn-stxk-p (fn-ndh-event e)) (fn-stxk-p e))
       (equal (fn-cpe-eventp (fn-ndh-event e)) (fn-cpe-eventp e))
       (equal (fn-th-topic-eventp (fn-ndh-event e)) (fn-th-topic-eventp e)))
  :hints (("Goal" :in-theory (disable fn-held-p fn-hstxa-p fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-cpe-eventp fn-th-topic-eventp))))

(defthm fn-ndh-event-other
  (implies (and (not (fn-held-p e)) (not (fn-hstxa-p e)))
           (equal (fn-ndh-event e) e)))

(defthm fn-ndh-event-held
  (implies (fn-held-p e) (equal (fn-ndh-event e) (fn-ndh-held e))))

(defthm fn-ndh-event-hstxa-parts
  (implies (fn-hstxa-p e)
           (and (equal (fn-hstxa-stxa (fn-ndh-event e)) (fn-hstxa-stxa e))
                (equal (fn-hstxa-held (fn-ndh-event e)) (fn-ndh-held (fn-hstxa-held e)))
                (equal (fn-replay-composite-held (fn-ndh-event e))
                       (fn-ndh-held (fn-replay-composite-held e)))))
  :hints (("Goal" :in-theory (disable fn-held-p fn-stxa-p))))

(in-theory (disable fn-ndh-event))

(defthm fn-ndh-event-coordinates
  (and (equal (fn-store-event-p (fn-ndh-event e)) (fn-store-event-p e))
       (equal (fn-store-event-sequence (fn-ndh-event e)) (fn-store-event-sequence e))
       (equal (fn-store-event-txid (fn-ndh-event e)) (fn-store-event-txid e)))
  :hints (("Goal" :cases ((fn-held-p e) (fn-hstxa-p e))
                  :in-theory (e/d (fn-store-event-p fn-store-event-sequence fn-store-event-txid)
                                  (fn-held-p fn-hstxa-p fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-cpe-eventp fn-th-topic-eventp)))))

(defthm fn-ndh-replay-advance-txid-of-make
  (equal (fn-replay-advance-txid (fn-node-make-state (fn-ndh-state a) r st b) txid)
         (fn-ndh-node (fn-replay-advance-txid (fn-node-make-state a r st b) txid)))
  :hints (("Goal" :use ((:instance fn-ndh-replay-advance-txid (n (fn-node-make-state a r st b))))
                  :in-theory (disable fn-ndh-replay-advance-txid fn-replay-advance-txid))))

(defthm fn-ndh-replay-apply-retention-event
  (equal (fn-replay-apply-retention-event (fn-ndh-node n) e)
         (fn-ndh-node (fn-replay-apply-retention-event n e)))
  :hints (("Goal" :in-theory (e/d (fn-replay-apply-retention-event fn-replay-complete-retention
                                   fn-replay-node-with-retention)
                                  (fn-node-statep fn-replay-advance-txid)))))

(defthm fn-ndh-node-of-non-node
  (implies (not (fn-node-state-shapep n)) (equal (fn-ndh-node n) n))
  :hints (("Goal" :in-theory (enable fn-ndh-node))))

(defthm fn-ndh-state-of-non-state
  (implies (not (fn-state-shapep s)) (equal (fn-ndh-state s) s))
  :hints (("Goal" :in-theory (enable fn-ndh-state))))

(defthm fn-ndh-node-acceptance-coordinates
  (and (equal (fn-state-next-txid (fn-node-acceptance (fn-ndh-node n)))
              (fn-state-next-txid (fn-node-acceptance n)))
       (equal (fn-state-fenced (fn-node-acceptance (fn-ndh-node n)))
              (fn-state-fenced (fn-node-acceptance n)))
       (equal (fn-state-groups (fn-node-acceptance (fn-ndh-node n)))
              (fn-state-groups (fn-node-acceptance n)))
       (equal (fn-state-nexts (fn-node-acceptance (fn-ndh-node n)))
              (fn-state-nexts (fn-node-acceptance n))))
  :hints (("Goal" :cases ((fn-node-state-shapep n)))))

(defthm fn-ndh-advance-of-non-node
  (implies (not (fn-node-state-shapep n)) (equal (fn-replay-advance-txid n x) n))
  :hints (("Goal" :in-theory (enable fn-replay-advance-txid))))

(defthm fn-ndh-replay-apply-identity-neutral
  (equal (fn-replay-apply-identity-neutral (fn-ndh-node n) e)
         (fn-ndh-node (fn-replay-apply-identity-neutral n e)))
  :hints (("Goal" :cases ((fn-node-state-shapep (fn-replay-advance-txid n (fn-store-event-txid e))))
                  :in-theory (e/d (fn-replay-apply-identity-neutral)
                                  (fn-node-statep fn-replay-advance-txid)))))

(defthm fn-ndh-held-coordinates
  (implies (fn-held-p e)
           (and (equal (fn-store-event-txid (fn-ndh-held e)) (fn-store-event-txid e))
                (equal (fn-store-event-sequence (fn-ndh-held e)) (fn-store-event-sequence e))))
  :hints (("Goal" :use ((:instance fn-ndh-event-coordinates))
                  :in-theory (disable fn-ndh-event-coordinates fn-held-p))))

(defthm fn-ndh-replay-apply-record
  (equal (fn-replay-apply-record (fn-ndh-node n) (fn-ndh-event e))
         (fn-ndh-node (fn-replay-apply-record n e)))
  :hints (("Goal" :cases ((fn-held-p e) (fn-hstxa-p e))
                  :in-theory (e/d (fn-replay-apply-record)
                                  (fn-node-statep fn-replay-advance-txid fn-node-prepare fn-node-complete
                                   fn-node-pending-matchesp fn-replay-apply-retention-event
                                   fn-replay-apply-identity-neutral
                                   fn-held-p fn-hstxa-p fn-store-retention-event-p fn-stxe-p fn-stxk-p
                                   fn-cpe-eventp fn-th-topic-eventp)))))

(defthm fn-ndh-cnode-fields
  (and (equal (fn-cnode-config (fn-ndh-cnode cn)) (fn-cnode-config cn))
       (equal (fn-cnode-shapep (fn-ndh-cnode cn)) (fn-cnode-shapep cn))
       (implies (fn-cnode-shapep cn)
                (equal (fn-cnode-node (fn-ndh-cnode cn)) (fn-ndh-node (fn-cnode-node cn))))))

(defthm fn-ndh-cnode-of-make
  (equal (fn-ndh-cnode (fn-cnode-make n c)) (fn-cnode-make (fn-ndh-node n) c)))

(defthm fn-ndh-cnode-of-non-cnode
  (implies (not (fn-cnode-shapep cn)) (equal (fn-ndh-cnode cn) cn)))

(in-theory (disable fn-ndh-cnode))

(defthm fn-ndh-cnode-domain
  (equal (fn-cnode-domain (fn-ndh-cnode cn)) (fn-cnode-domain cn))
  :hints (("Goal" :cases ((fn-cnode-shapep cn)) :in-theory (enable fn-cnode-domain))))

(defthm fn-ndh-cnode-statep
  (equal (fn-cnode-statep (fn-ndh-cnode cn)) (fn-cnode-statep cn))
  :hints (("Goal" :cases ((fn-cnode-shapep cn)) :in-theory (e/d (fn-cnode-statep) (fn-node-statep fn-cnode-domain)))))

(defthm fn-ndh-cpr-event-servedp
  (equal (fn-cpr-event-servedp (fn-ndh-cnode cn) (fn-ndh-event e))
         (fn-cpr-event-servedp cn e))
  :hints (("Goal" :cases ((fn-held-p e) (fn-hstxa-p e))
                  :in-theory (e/d (fn-cpr-event-servedp)
                                  (fn-held-p fn-hstxa-p fn-cnode-selection-servedp)))))

(defthm fn-ndh-cnode-statep-shape
  (implies (fn-cnode-statep cn) (fn-cnode-shapep cn))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-cnode-statep))))

(defthm fn-ndh-cpr-apply-event
  (equal (fn-cpr-apply-event (fn-ndh-cnode cn) (fn-ndh-event e))
         (fn-ndh-cnode (fn-cpr-apply-event cn e)))
  :hints (("Goal" :cases ((fn-cnode-shapep cn))
                  :in-theory (e/d (fn-cpr-apply-event)
                                  (fn-cnode-statep fn-node-statep fn-replay-apply-record fn-store-event-p
                                   fn-cpr-event-servedp)))))

(defthm fn-ndh-cnode-node-coordinates
  (and (equal (fn-node-retention (fn-cnode-node (fn-ndh-cnode cn))) (fn-node-retention (fn-cnode-node cn)))
       (equal (fn-node-stage (fn-cnode-node (fn-ndh-cnode cn))) (fn-node-stage (fn-cnode-node cn)))
       (equal (fn-node-bindings (fn-cnode-node (fn-ndh-cnode cn))) (fn-node-bindings (fn-cnode-node cn))))
  :hints (("Goal" :cases ((fn-cnode-shapep cn)))))

(defthm fn-ndh-cnode-record-acceptablep
  (equal (fn-cnode-record-acceptablep (fn-ndh-cnode cn) record ceiling)
         (fn-cnode-record-acceptablep cn record ceiling))
  :hints (("Goal" :in-theory (e/d (fn-cnode-record-acceptablep) (fn-cfg-record-acceptablep)))))

(defthm fn-ndh-cnode-statep-node
  (implies (fn-cnode-statep cn) (fn-node-statep (fn-cnode-node cn)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-cnode-statep))))

(defthm fn-ndh-node-statep-shape-forward
  (implies (fn-node-statep n)
           (and (fn-node-state-shapep n) (fn-state-shapep (fn-node-acceptance n))))
  :rule-classes :forward-chaining)

(defthm fn-ndh-cnode-apply-config
  (equal (fn-cnode-apply-config (fn-ndh-cnode cn) record ceiling)
         (fn-ndh-cnode (fn-cnode-apply-config cn record ceiling)))
  :hints (("Goal" :cases ((fn-cnode-shapep cn))
                  :in-theory (e/d (fn-cnode-apply-config)
                                  (fn-cnode-statep fn-cnode-record-acceptablep fn-cfg-apply-record)))))

(defthm fn-ndh-replay-advance-okp
  (equal (fn-replay-advance-okp (fn-ndh-node n) txid) (fn-replay-advance-okp n txid))
  :hints (("Goal" :in-theory (e/d (fn-replay-advance-okp) (fn-node-statep)))))

(defthm fn-ndh-cpr-config-firstp
  (equal (fn-cpr-config-firstp configs (fn-ndh-events evs)) (fn-cpr-config-firstp configs evs))
  :hints (("Goal" :in-theory (enable fn-cpr-config-firstp))))

(defthmd fn-ndh-cnode-make-folds
  (equal (fn-cnode-make (fn-ndh-node n) c) (fn-ndh-cnode (fn-cnode-make n c))))

(defthm fn-ndh-events-list
  (and (equal (consp (fn-ndh-events evs)) (consp evs))
       (equal (car (fn-ndh-events evs)) (if (consp evs) (fn-ndh-event (car evs)) (car evs)))
       (equal (cdr (fn-ndh-events evs)) (if (consp evs) (fn-ndh-events (cdr evs)) (cdr evs)))
       (implies (not (consp evs)) (equal (fn-ndh-events evs) evs))))

(defthm fn-ndh-cpr-loop
  (and (equal (fn-replay-result-kind (fn-cpr-loop (fn-ndh-cnode cn) configs (fn-ndh-events evs) cs es))
              (fn-replay-result-kind (fn-cpr-loop cn configs evs cs es)))
       (equal (fn-replay-result-node (fn-cpr-loop (fn-ndh-cnode cn) configs (fn-ndh-events evs) cs es))
              (fn-ndh-cnode (fn-replay-result-node (fn-cpr-loop cn configs evs cs es)))))
  :hints (("Goal" :induct (fn-cpr-loop cn configs evs cs es)
                  :expand ((:free (configs evs cs es) (fn-cpr-loop cn configs evs cs es))
                           (:free (configs evs cs es) (fn-cpr-loop (fn-ndh-cnode cn) configs evs cs es)))
                  :in-theory (e/d (fn-ndh-cnode-make-folds (:induction fn-cpr-loop)) 
                                  (fn-ndh-events (:definition fn-cpr-loop) fn-ndh-cnode-of-make fn-cnode-statep fn-cpr-apply-event fn-cnode-apply-config
                                   fn-cnode-record-acceptablep fn-replay-advance-okp fn-replay-advance-txid
                                   fn-store-event-p fn-cpr-config-firstp fn-cfg-recordp)))))

(defthm fn-ndh-cnode-initial
  (equal (fn-ndh-cnode (fn-cnode-initial config)) (fn-cnode-initial config))
  :hints (("Goal" :in-theory (enable fn-cnode-initial fn-node-initial-state fn-initial-state fn-ndh-state))))

(defthm fn-ndh-cpr-replay
  (and (equal (fn-replay-result-kind (fn-cpr-replay configs (fn-ndh-events evs)))
              (fn-replay-result-kind (fn-cpr-replay configs evs)))
       (equal (fn-replay-result-node (fn-cpr-replay configs (fn-ndh-events evs)))
              (fn-ndh-cnode (fn-replay-result-node (fn-cpr-replay configs evs)))))
  :hints (("Goal" :in-theory (e/d (fn-cpr-replay) (fn-ndh-cpr-loop fn-cnode-initial fn-cpr-loop fn-ndh-events (fn-cnode-initial) (fn-cfg-initial)))
                  :use ((:instance fn-ndh-cpr-loop (cn (fn-cnode-initial (fn-cfg-initial))) (cs 0) (es 0))))))

(defthm fn-ndh-cnode-statep-shape-rewrite
  (implies (fn-cnode-statep cn) (fn-cnode-shapep cn)))

(defthm fn-ndh-cst-replay-node
  (equal (fn-cst-replay-node configs (fn-ndh-events evs) frontier)
         (fn-ndh-node (fn-cst-replay-node configs evs frontier)))
  :hints (("Goal" :cases ((fn-cnode-shapep (fn-replay-result-node (fn-cpr-replay configs evs))))
                  :in-theory (e/d (fn-cst-replay-node) (fn-cpr-replay fn-cnode-statep fn-replay-advance-okp fn-replay-advance-txid)))))

(defthm fn-ndh-node-holder
  (equal (fn-ndur-holder g n (fn-state-articles (fn-node-acceptance (fn-ndh-node node))))
         (fn-ndur-holder g n (fn-state-articles (fn-node-acceptance node))))
  :hints (("Goal" :cases ((fn-node-state-shapep node)))
          ("Subgoal 1" :cases ((fn-state-shapep (fn-node-acceptance node))))))

(defthm fn-ndh-node-iff
  (iff (fn-ndh-node n) n)
  :hints (("Goal" :cases ((fn-node-state-shapep n)))))

(defthm fn-ndh-replay-extension-keeps-every-number
  (implies (and (fn-sf-prefixp (fn-ndh-events xs) (fn-ndh-events ys))
                (fn-cst-replay-node configs ys f2)
                (fn-ndur-holder g n (fn-state-articles
                                     (fn-node-acceptance (fn-cst-replay-node configs xs f1)))))
           (and (equal (fn-ndur-holder g n (fn-state-articles
                                            (fn-node-acceptance (fn-cst-replay-node configs ys f2))))
                       (fn-ndur-holder g n (fn-state-articles
                                            (fn-node-acceptance (fn-cst-replay-node configs xs f1)))))
                (< n (fn-next-number g (fn-state-nexts
                                        (fn-node-acceptance (fn-cst-replay-node configs ys f2)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-ndur-replay-extension-keeps-every-number
                            (xs (fn-ndh-events xs)) (ys (fn-ndh-events ys))))
           :in-theory (disable fn-ndur-replay-extension-keeps-every-number fn-cst-replay-node
                               fn-ndur-holder fn-sf-prefixp fn-ndh-events fn-next-number))))

(defthm fn-ndh-events-of-take
  (equal (fn-ndh-events (fn-own-take n xs)) (fn-own-take n (fn-ndh-events xs)))
  :hints (("Goal" :in-theory (enable fn-own-take))))

(defthm fn-ndh-recovery-keeps-every-visible-number
  (let* ((st (fn-own-store o))
         (live (fn-sf-records (fn-sn-files st)))
         (raw (fn-own-view-raw (fn-own-view o)))
         (node (fn-sn-node (fn-sn-open-state
                            (fn-cpo-open-observed (fn-sn-config-history st)
                                                  frontier recovered))))
         (articles (fn-state-articles (fn-node-acceptance node))))
    (implies (and (fn-ocl-view-historyp o)
                  (<= (fn-own-view-version (fn-own-view o)) (nfix fenced))
                  (fn-sf-prefixp (fn-ndh-events (fn-own-take fenced live))
                                 (fn-ndh-events recovered))
                  (fn-sn-open-okp (fn-cpo-open-observed (fn-sn-config-history st)
                                                        frontier recovered))
                  (fn-ndur-holder g n raw))
             (and (equal (fn-ndur-holder g n articles) (fn-ndur-holder g n raw))
                  (< n (fn-next-number g (fn-state-nexts (fn-node-acceptance node)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-ndh-replay-extension-keeps-every-number
                            (configs (fn-sn-config-history (fn-own-store o)))
                            (xs (fn-own-take (fn-own-view-version (fn-own-view o))
                                             (fn-sf-records (fn-sn-files (fn-own-store o)))))
                            (ys recovered)
                            (f1 (fn-own-view-frontier (fn-own-view o)))
                            (f2 frontier))
                 (:instance fn-ndur-take-prefix-of-take
                            (v (fn-own-view-version (fn-own-view o)))
                            (c fenced)
                            (xs (fn-ndh-events (fn-sf-records (fn-sn-files (fn-own-store o))))))
                 (:instance fn-ndur-prefixp-transitive
                            (xs (fn-own-take (fn-own-view-version (fn-own-view o))
                                             (fn-ndh-events (fn-sf-records (fn-sn-files (fn-own-store o))))))
                            (ys (fn-own-take fenced (fn-ndh-events (fn-sf-records (fn-sn-files (fn-own-store o))))))
                            (zs (fn-ndh-events recovered)))
                 (:instance fn-ndur-host-open-replay-node-exists
                            (configs (fn-sn-config-history (fn-own-store o)))
                            (events recovered))
                 (:instance fn-ndur-host-open-node-is-the-replay
                            (configs (fn-sn-config-history (fn-own-store o)))
                            (events recovered)))
           :in-theory (e/d (fn-ocl-view-historyp)
                           (fn-ndh-replay-extension-keeps-every-number
                            fn-ndur-take-prefix-of-take fn-ndur-prefixp-transitive
                            fn-ndur-host-open-node-is-the-replay fn-ndur-host-open-replay-node-exists
                            fn-ndur-cst-replay-node-articles fn-cst-replay-node fn-cpo-open-observed fn-node-statep
                            fn-ndur-holder fn-own-take fn-sf-prefixp fn-sn-open-okp fn-ndh-events
                            fn-ctl-visible-state)))))

(defthm fn-ndh-prefixp-of-prefixp
  (implies (fn-sf-prefixp xs ys)
           (fn-sf-prefixp (fn-ndh-events xs) (fn-ndh-events ys)))
  :hints (("Goal" :in-theory (enable fn-sf-prefixp))))
