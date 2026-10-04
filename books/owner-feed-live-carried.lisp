; Installed owner FNFD boundary over the carried table relation.
(in-package "ACL2")
(include-book "owner-feed-counts")
(include-book "feed-live-carried")
(include-book "owner-feed-port")

(defun fn-own-feed-port-peer-carried (peer tbl event)
  (declare (xargs :guard (and (fn-own-feed-tablep tbl)
                              (fn-ofct-table-relationp tbl))
                  :verify-guards nil))
  (mbe
   :logic (fn-own-feed-port-peer peer tbl event)
   :exec
   (let ((e (fn-own-feed-entry-of peer tbl)))
     (if (null e)
         (fn-own-feed-port-result :ignored tbl nil nil)
       (let ((step (fn-feed-live-port-step-carried
                    (fn-own-feed-entry-feed e) event)))
         (if (equal (fn-feed-port-step-status step) :accepted)
             (let ((effects (fn-feed-port-step-effects step)))
               (fn-own-feed-port-result-counted
                :accepted
                (fn-own-feed-put peer (fn-own-feed-entry-record e)
                                 (fn-feed-port-step-feed step) tbl)
                (fn-feed-port-step-records step)
                (if (null effects) nil (list (cons peer effects)))
                (fn-own-feed-pending-delta
                 (fn-own-feed-entry-feed e) (fn-feed-port-step-feed step))))
           (fn-own-feed-port-result :refused tbl nil nil)))))))

(local
 (defthm fn-ofcv-found-feed-is-valid
   (implies (and (fn-own-feed-tablep tbl) (fn-own-feed-entry-of peer tbl))
            (fn-feedp (fn-own-feed-entry-feed (fn-own-feed-entry-of peer tbl))))
   :hints (("Goal" :use fn-own-feed-entry-of-is-okp
            :in-theory (e/d (fn-own-feed-entry-okp fn-own-feed-feed-okp)
                             (fn-own-feed-tablep fn-own-feed-entry-of
                              fn-own-feed-entry-of-is-okp fn-feedp))))))


(defun fn-ofcv-enqueue-one (peer tbl msgid tick pending)
  (declare (xargs :guard (and (fn-own-feed-tablep tbl)
                              (fn-ofct-table-relationp tbl)
                              (acl2-numberp pending)) :verify-guards nil))
  (let ((e (fn-own-feed-entry-of peer tbl)))
    (if (null e) (cons tbl pending)
      (let* ((old (fn-own-feed-entry-feed e))
             (new (fn-fcv-raw-enqueue old msgid tick)))
        (cons (fn-own-feed-put peer (fn-own-feed-entry-record e) new tbl)
              (+ pending (fn-own-feed-pending-delta old new)))))))

(local
 (defthm fn-ofcv-raw-enqueue-is-enqueue
   (implies (and (fn-feedp f) (fn-feed-count-relationp f))
            (equal (fn-fcv-raw-enqueue f id tick) (fn-feed-enqueue f id tick)))
   :hints (("Goal" :in-theory
            (e/d (fn-fcv-raw-enqueue fn-feed-enqueue fn-feed-count-relationp)
                 (fn-feedp fn-feed-undelivered fn-feed-queue))))))

(defthm fn-ofcv-enqueue-one-is-counted-singleton
  (implies (and (fn-own-feed-tablep tbl) (fn-ofct-table-relationp tbl))
           (equal (fn-ofcv-enqueue-one peer tbl id tick pending)
                  (fn-own-feed-enqueue-all-counted (list peer) tbl id tick pending)))
  :hints (("Goal" :in-theory
           (e/d (fn-ofcv-enqueue-one fn-own-feed-enqueue-all-counted)
                (fn-own-feed-tablep fn-ofct-table-relationp fn-own-feed-entry-of
                 fn-fcv-raw-enqueue fn-feed-enqueue fn-own-feed-put)))))

(defthm fn-ofcv-enqueue-one-preserves-tablep
  (implies (and (fn-own-feed-tablep tbl) (fn-ofct-table-relationp tbl))
           (fn-own-feed-tablep (car (fn-ofcv-enqueue-one peer tbl id tick pending))))
  :hints (("Goal" :in-theory (disable fn-ofcv-enqueue-one
                                     fn-own-feed-tablep fn-own-feed-enqueue-all))))

(defthm fn-ofcv-enqueue-one-preserves-count-relation
  (implies (and (fn-own-feed-tablep tbl) (fn-ofct-table-relationp tbl))
           (fn-ofct-table-relationp (car (fn-ofcv-enqueue-one peer tbl id tick pending))))
  :hints (("Goal" :in-theory
           (e/d (fn-ofcv-enqueue-one)
                (fn-ofcv-enqueue-one-is-counted-singleton
                 fn-fcv-raw-enqueue fn-feed-enqueue fn-own-feed-put
                 fn-own-feed-entry-of fn-own-feed-tablep fn-ofct-table-relationp)))))

(verify-guards fn-ofcv-enqueue-one
 :hints (("Goal" :in-theory (disable fn-own-feed-tablep fn-ofct-table-relationp
                                    fn-own-feed-entry-of fn-feedp))))

(defun fn-own-feed-enqueue-all-carried (names tbl msgid tick pending)
  (declare (xargs :guard (and (fn-own-feed-tablep tbl)
                              (fn-ofct-table-relationp tbl)
                              (acl2-numberp pending)) :verify-guards nil))
  (if (consp names)
      (let ((one (fn-ofcv-enqueue-one (car names) tbl msgid tick pending)))
        (fn-own-feed-enqueue-all-carried (cdr names) (car one) msgid tick (cdr one)))
    (cons tbl pending)))

(defthm fn-ofcv-enqueue-one-pending-is-numeric
  (implies (acl2-numberp pending)
           (acl2-numberp (cdr (fn-ofcv-enqueue-one peer tbl id tick pending))))
  :hints (("Goal" :in-theory (enable fn-ofcv-enqueue-one))))

(verify-guards fn-own-feed-enqueue-all-carried
  :hints (("Goal" :in-theory (disable fn-ofcv-enqueue-one fn-ofcv-enqueue-one-is-counted-singleton
                                     fn-own-feed-tablep fn-ofct-table-relationp))))

(defthm fn-own-feed-enqueue-all-carried-is-counted-reference
  (implies (and (fn-own-feed-tablep tbl) (fn-ofct-table-relationp tbl))
           (equal (fn-own-feed-enqueue-all-carried names tbl id tick pending)
                  (fn-own-feed-enqueue-all-counted names tbl id tick pending)))
  :hints (("Goal" :induct (fn-own-feed-enqueue-all-carried names tbl id tick pending)
           :in-theory (e/d (fn-own-feed-enqueue-all-carried
                             fn-own-feed-enqueue-all-counted)
                            (fn-ofcv-enqueue-one fn-own-feed-entry-of
                             fn-own-feed-tablep fn-ofct-table-relationp
                             fn-own-feed-put fn-feed-enqueue)))
          ("Subgoal *1/1"
           :use ((:instance fn-ofcv-enqueue-one-preserves-tablep (peer (car names)))
                 (:instance fn-ofcv-enqueue-one-preserves-count-relation (peer (car names)))))))

(defun fn-own-feed-enqueue-all-counted-carried (names tbl id tick pending)
  (declare (xargs :guard (and (fn-own-feed-tablep tbl)
                              (fn-ofct-table-relationp tbl)
                              (acl2-numberp pending))))
  (mbe :logic (fn-own-feed-enqueue-all-counted names tbl id tick pending)
       :exec (fn-own-feed-enqueue-all-carried names tbl id tick pending)))

(defthm fn-own-feed-enqueue-all-counted-carried-is-reference-by-definition
  (equal (fn-own-feed-enqueue-all-counted-carried names tbl id tick pending)
         (fn-own-feed-enqueue-all-counted names tbl id tick pending)))

(verify-guards fn-own-feed-port-peer-carried
  :hints (("Goal"
           :in-theory (e/d (fn-own-feed-port-peer-carried
                             fn-own-feed-port-peer fn-own-feed-entry-okp
                             fn-own-feed-feed-okp fn-feed-live-port-step-carried)
                            (fn-own-feed-tablep fn-ofct-table-relationp fn-own-feed-entry-of
                             fn-feed-live-port-step fn-feedp)))))

; Projection equality is the MBE logic, not the keystone. The guard proof
; above establishes the actual scan-free branch's full result equivalence.
(defthm fn-own-feed-port-peer-carried-is-reference-by-definition
  (equal (fn-own-feed-port-peer-carried peer tbl event)
         (fn-own-feed-port-peer peer tbl event)))

(in-theory (disable fn-own-feed-port-peer-carried fn-ofcv-enqueue-one
                    fn-own-feed-enqueue-all-carried fn-own-feed-enqueue-all-counted-carried))

; -----------------------------------------------------------------------------
; KEYSTONES over the host-called feed port (rp-feed-defer-drop,
; rp-feed-dropped-holds-capacity, rp-feed-reply-msgid)
;
; The subject is `fn-own-feed-port-peer-carried', which the host calls for
; every feed event (host/owner-host.lisp fn-owner-feed-octets for a reply,
; fn-owner-feed-tick, fn-owner-feed-lost); it is `fn-own-feed-port-peer' by
; `fn-own-feed-port-peer-carried-is-reference-by-definition'.  The capacity
; subject is `fn-own-feed-target-capacityp', which the owner's submission
; intent asks before any article transaction (books/owner.lisp
; fn-own-submission-intent-result, :capacity -> POST 441, transfer 436).

(local
 (defthm fn-ofcv-port-feedp-of-a-table-entry
   (implies (and (fn-own-feed-tablep tbl) (fn-own-feed-entry-of peer tbl))
            (fn-feedp (fn-own-feed-find peer tbl)))
   :hints (("Goal" :use fn-own-feed-entry-of-is-okp
            :in-theory (e/d (fn-own-feed-entry-okp fn-own-feed-feed-okp
                             fn-own-feed-find)
                            (fn-own-feed-tablep fn-own-feed-entry-of
                             fn-own-feed-entry-of-is-okp fn-feedp))))))

(local
 (defthm fn-ofcv-port-relation-of-a-table-entry
   (implies (and (fn-ofct-table-relationp tbl) (fn-own-feed-entry-of peer tbl))
            (fn-feed-count-relationp (fn-own-feed-find peer tbl)))
   :hints (("Goal" :induct (fn-own-feed-entry-of peer tbl)
            :in-theory (e/d (fn-own-feed-find fn-own-feed-entry-of
                             fn-ofct-table-relationp)
                            (fn-feed-count-relationp))))))

(local
 (defthm fn-ofcv-port-step-cases
   (implies (fn-own-feed-entry-of peer tbl)
            (equal (fn-own-feed-find
                    peer (fn-own-feed-port-table (fn-own-feed-port-peer peer tbl event)))
                   (if (and (fn-feedp (fn-own-feed-find peer tbl))
                            (fn-feed-records-portp
                             (fn-feed-live-records (fn-own-feed-find peer tbl) event)))
                       (fn-feed-live-next (fn-own-feed-find peer tbl) event)
                     (fn-own-feed-find peer tbl))))
   :hints (("Goal" :in-theory (e/d (fn-own-feed-find fn-own-feed-port-table
                                    fn-own-feed-port-result
                                    fn-own-feed-port-result-counted fn-frame-item)
                                   (fn-own-feed-port-peer fn-feedp
                                    fn-feed-live-next fn-feed-live-records
                                    fn-feed-records-portp fn-own-feed-entry-of))
            :cases ((and (fn-feedp (fn-own-feed-find peer tbl))
                         (fn-feed-records-portp
                          (fn-feed-live-records (fn-own-feed-find peer tbl) event))))
            :use (fn-own-feed-port-peer-ready-is-live-port-step
                  fn-own-feed-port-peer-refusal-preserves-table)))))

(local
 (defthm fn-ofcv-port-records-cases
   (implies (fn-own-feed-entry-of peer tbl)
            (equal (fn-own-feed-port-records (fn-own-feed-port-peer peer tbl event))
                   (if (and (fn-feedp (fn-own-feed-find peer tbl))
                            (fn-feed-records-portp
                             (fn-feed-live-records (fn-own-feed-find peer tbl) event)))
                       (fn-feed-live-records (fn-own-feed-find peer tbl) event)
                     nil)))
   :hints (("Goal" :in-theory (e/d (fn-own-feed-find fn-own-feed-port-records
                                    fn-own-feed-port-result
                                    fn-own-feed-port-result-counted fn-frame-item)
                                   (fn-own-feed-port-peer fn-feedp
                                    fn-feed-live-next fn-feed-live-records
                                    fn-feed-records-portp fn-own-feed-entry-of))
            :cases ((and (fn-feedp (fn-own-feed-find peer tbl))
                         (fn-feed-records-portp
                          (fn-feed-live-records (fn-own-feed-find peer tbl) event))))
            :use (fn-own-feed-port-peer-ready-is-live-port-step
                  fn-own-feed-port-peer-refusal-preserves-table)))))

(local
 (defthm fn-ofcv-port-effects-cases
   (implies (fn-own-feed-entry-of peer tbl)
            (equal (fn-own-feed-port-effects (fn-own-feed-port-peer peer tbl event))
                   (if (and (fn-feedp (fn-own-feed-find peer tbl))
                            (fn-feed-records-portp
                             (fn-feed-live-records (fn-own-feed-find peer tbl) event)))
                       (let ((effects (fn-feed-live-effects (fn-own-feed-find peer tbl) event)))
                         (if (null effects) nil (list (cons peer effects))))
                     nil)))
   :hints (("Goal" :in-theory (e/d (fn-own-feed-find fn-own-feed-port-effects
                                    fn-own-feed-port-result
                                    fn-own-feed-port-result-counted fn-frame-item)
                                   (fn-own-feed-port-peer fn-feedp
                                    fn-feed-live-next fn-feed-live-records
                                    fn-feed-live-effects
                                    fn-feed-records-portp fn-own-feed-entry-of))
            :cases ((and (fn-feedp (fn-own-feed-find peer tbl))
                         (fn-feed-records-portp
                          (fn-feed-live-records (fn-own-feed-find peer tbl) event))))
            :use (fn-own-feed-port-peer-ready-is-live-port-step
                  fn-own-feed-port-peer-refusal-preserves-table)))))

; (a) rp-feed-defer-drop.  A 431/436 for the entry in flight suspends the
; attempt and never discharges a delivery obligation: it removes no entry,
; the peer's count of owed entries is unchanged, and it writes no record
; that would discharge one -- no final outcome, no drop.
(defthm fn-own-feed-port-deferral-keeps-every-entry
  (implies (and (fn-own-feed-tablep tbl)
                (fn-own-feed-entry-of peer tbl)
                (member-equal (fn-feed-response-code response) '(431 436))
                (fn-feed-inflightp (fn-feed-response-msgid response)
                                   (fn-own-feed-find peer tbl))
                (fn-feed-presentp m (fn-own-feed-find peer tbl)))
           (let ((r (fn-own-feed-port-peer-carried
                     peer tbl (list :reply response article obs))))
             (and (fn-feed-presentp
                   m (fn-own-feed-find peer (fn-own-feed-port-table r)))
                  (equal (fn-feed-undelivered
                          (fn-own-feed-find peer (fn-own-feed-port-table r)))
                         (fn-feed-undelivered (fn-own-feed-find peer tbl)))
                  (not (fn-feed-has-leave-recordp
                        (fn-feed-peer (fn-own-feed-find peer tbl)) m
                        (fn-own-feed-port-records r))))))
  :hints (("Goal"
           :use ((:instance fn-feed-deferral-keeps-every-entry
                            (f (fn-own-feed-find peer tbl))))
           :in-theory (e/d (fn-feed-live-next fn-feed-live-records
                            fn-feed-observe-records fn-frame-item
                            fn-feed-journal-entry fn-feed-journal-kind
                            fn-feed-journal-values fn-feed-record-peer
                            fn-feed-record-msgid)
                           (fn-own-feed-port-peer fn-feedp fn-own-feed-find
                            fn-feed-observe fn-feed-presentp
                            fn-feed-deferral-keeps-every-entry
                            fn-feed-records-portp fn-feed-reply-class
                            fn-own-feed-entry-of fn-own-feed-tablep))
           :expand ((fn-feed-reply-class (fn-own-feed-find peer tbl) response)))))

; (b) rp-feed-dropped-holds-capacity.  After any event the peer's carried
; count -- what every capacity test reads -- is the number of entries still
; owed delivery: no entry that will never be sent holds a queue slot.
(defthm fn-own-feed-port-holds-only-owed-entries
  (implies (and (fn-own-feed-tablep tbl)
                (fn-ofct-table-relationp tbl)
                (fn-own-feed-entry-of peer tbl))
           (let ((g (fn-own-feed-find
                     peer (fn-own-feed-port-table
                           (fn-own-feed-port-peer-carried peer tbl event)))))
             (equal (fn-feed-undelivered g)
                    (fn-feed-owed-count (fn-feed-queue g)))))
  :hints (("Goal"
           :in-theory (e/d ()
                           (fn-own-feed-port-peer fn-feedp fn-own-feed-find
                            fn-feed-live-next fn-feed-live-records
                            fn-feed-records-portp fn-feed-owed-count
                            fn-own-feed-entry-of fn-own-feed-tablep
                            fn-ofct-table-relationp))
           :use ((:instance fn-feed-undelivered-is-the-owed-count
                            (f (fn-feed-live-next (fn-own-feed-find peer tbl) event)))
                 (:instance fn-feed-undelivered-is-the-owed-count
                            (f (fn-own-feed-find peer tbl)))
                 (:instance fn-feed-live-next-preserves-feedp
                            (f (fn-own-feed-find peer tbl)))
                 (:instance fn-fct-live-next-preserves-count-relation
                            (f (fn-own-feed-find peer tbl)))))))

; (c) rp-feed-dropped-holds-capacity.  The capacity verdict refuses only for
; owed work: when it refuses, some target peer lacks the Message-ID and the
; entries it still owes fill its max-queue.  (A target name with no feed
; reads as a full zero-length queue, the refusal it always was.)
(defun fn-own-feed-some-target-fullp (names tbl msgid)
  (declare (xargs :guard t))
  (if (consp names)
      (or (let ((f (fn-own-feed-find (car names) tbl)))
            (and (not (consp (fn-feed-find msgid (fn-feed-queue f))))
                 (<= (nfix (fn-feed-max-queue (fn-feed-limits-of f)))
                     (fn-feed-owed-count (fn-feed-queue f)))))
          (fn-own-feed-some-target-fullp (cdr names) tbl msgid))
    nil))

(local
 (defthm fn-ofcv-find-of-an-unbound-peer
   (implies (not (fn-own-feed-entry-of p tbl))
            (equal (fn-own-feed-find p tbl) nil))
   :hints (("Goal" :in-theory (enable fn-own-feed-find fn-own-feed-entry-feed
                                      fn-frame-item)))))

(local
 (defthm fn-ofcv-owed-count-of-a-table-entry
   (implies (fn-own-feed-tablep tbl)
            (equal (fn-feed-owed-count (fn-feed-queue (fn-own-feed-find p tbl)))
                   (len (fn-feed-queue (fn-own-feed-find p tbl)))))
   :hints (("Goal" :cases ((fn-own-feed-entry-of p tbl))
            :in-theory (disable fn-own-feed-find fn-feedp fn-own-feed-tablep
                                fn-own-feed-entry-of fn-feed-owed-count)
            :use ((:instance fn-ofcv-port-feedp-of-a-table-entry (peer p))
                  (:instance fn-feedp-forward-components
                             (f (fn-own-feed-find p tbl)))
                  (:instance fn-feed-owed-count-of-an-entry-list
                             (xs (fn-feed-queue (fn-own-feed-find p tbl)))))))))

(defthm fn-own-feed-capacity-refusal-is-owed-work
  (implies (and (fn-own-feed-tablep tbl)
                (not (fn-own-feed-target-capacityp names tbl msgid)))
           (fn-own-feed-some-target-fullp names tbl msgid))
  :hints (("Goal" :induct (fn-own-feed-target-capacityp names tbl msgid)
           :in-theory (e/d (fn-own-feed-target-capacityp)
                           (fn-feedp fn-own-feed-tablep fn-own-feed-entry-of
                            fn-own-feed-find fn-feed-owed-count)))))

; (d) rp-feed-reply-msgid.  A reply that names any Message-ID but the one in
; flight -- the subject `fn-own-feed-parse-response' gives an echoing reply
; (`fn-own-feed-parse-response-names-the-echo') -- is a loss: the port step
; is the feed's own loss (the in-flight entry requeued, never retired, sent
; or deferred), and ACL2's word tells the host to drop the link.
(local
 (defthm fn-ofcv-inflight-count-positive
   (implies (fn-feed-state-inflightp (fn-feed-state-of m xs))
            (< 0 (fn-feed-inflight-count xs)))
   :rule-classes :linear
   :hints (("Goal" :induct (fn-feed-find m xs)
            :in-theory (enable fn-feed-state-of)))))

(local
 (defthm fn-ofcv-the-inflight-msgid-is-the-one-inflight
   (implies (and (<= (fn-feed-inflight-count xs) 1)
                 (fn-feed-state-inflightp (fn-feed-state-of m xs)))
            (equal (fn-own-feed-inflight-msgid xs) m))
   :hints (("Goal" :induct (fn-feed-find m xs)
            :in-theory (e/d (fn-feed-state-of) (fn-feed-state-inflightp))))))

(local
 (defthm fn-feedp-inflight-at-most-one
   (implies (fn-feedp f) (<= (fn-feed-inflight-count (fn-feed-queue f)) 1))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-feedp)))))

(defthm fn-own-feed-port-stray-reply-is-a-loss
  (implies (and (fn-own-feed-tablep tbl)
                (fn-own-feed-entry-of peer tbl)
                (not (equal (fn-feed-response-msgid response)
                            (fn-own-feed-inflight-msgid
                             (fn-feed-queue (fn-own-feed-find peer tbl))))))
           (let ((r (fn-own-feed-port-peer-carried
                     peer tbl (list :reply response article obs)))
                 (f (fn-own-feed-find peer tbl)))
             (and (equal (fn-feed-reply-class f response) :lost)
                  (equal (fn-own-feed-find peer (fn-own-feed-port-table r))
                         (if (fn-feed-records-portp (fn-feed-lost-records f obs))
                             (fn-feed-lost f obs)
                           f))
                  (equal (fn-own-feed-reply-word tbl peer response
                                                 (fn-own-feed-port-effects r))
                         :lost))))
  :hints (("Goal"
           :in-theory (e/d (fn-feed-live-next fn-feed-live-records
                            fn-feed-live-effects fn-feed-observe-records
                            fn-feed-observe fn-feed-reply-class fn-frame-item
                            fn-own-feed-reply-word)
                           (fn-own-feed-port-peer fn-feedp fn-own-feed-find
                            fn-feed-lost fn-feed-lost-records
                            fn-feed-records-portp fn-feed-state-inflightp
                            fn-own-feed-entry-of fn-own-feed-tablep))
           :use ((:instance fn-ofcv-the-inflight-msgid-is-the-one-inflight
                            (xs (fn-feed-queue (fn-own-feed-find peer tbl)))
                            (m (fn-feed-response-msgid response)))
                 (:instance fn-ofcv-port-feedp-of-a-table-entry)
                 (:instance fn-feedp-inflight-at-most-one
                            (f (fn-own-feed-find peer tbl)))))))
