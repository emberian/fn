; General properties of fn-wire-next, the event-yield framing API that
; host/reader-host.lisp:91 calls, and of the chunk loop the Python adapter
; runs around it.
;
; These results describe one call made with a valid wire state and a proper
; octet chunk, and then the loop that tools/run_reader.py:167-181 performs:
; feed a chunk, take at most one event, and re-feed the returned unconsumed
; suffix until nothing is left.  fn-wire-drive is the ACL2 transcription of
; that loop; it is not a second framing implementation, and the partition
; theorem below is stated about it rather than about fn-wire-feed, which the
; host never calls.  The caller is still responsible for dispatching a yielded
; command before calling fn-wire-begin-article.
(in-package "ACL2")
(include-book "wire")

; books/wire.lisp made its three records opaque and withdrew its step
; vocabulary at its export event.  This book is the one place that reasons
; about how a step composes -- how the result record's state and events and the
; next record's state, event and unconsumed suffix split across a chunk
; boundary -- so it opens both the transitions and the records, locally and
; only locally.  Every includer above (books/nntp-syntax.lisp,
; tests/acl2/wire-tests.lisp, host/reader-host.lisp) still sees them closed.
(local (in-theory (enable fn-wire-step-vocabulary
                          fn-wire-state-shapep fn-wire-make-state
                          fn-wire-state-mode fn-wire-state-line-rev
                          fn-wire-state-line-len fn-wire-state-body-rev
                          fn-wire-state-pending-crp fn-wire-state-body-size
                          fn-wire-state-line-limit fn-wire-state-body-limit
                          fn-wire-result-shapep fn-wire-make-result
                          fn-wire-result-state fn-wire-result-events
                          fn-wire-next-shapep fn-wire-make-next
                          fn-wire-next-state fn-wire-next-event
                          fn-wire-next-unconsumed)))

(defun fn-wire-suffixp (suffix octets)
  (if (equal suffix octets)
      t
    (if (consp octets)
        (fn-wire-suffixp suffix (cdr octets))
      nil)))

(defthm fn-wire-suffixp-refl
  (fn-wire-suffixp octets octets))

(defthm fn-wire-suffixp-cdr
  (implies (fn-wire-suffixp suffix octets)
           (fn-wire-suffixp suffix (cons byte octets))))

(defthm fn-wire-suffixp-implies-length-bound
  (implies (and (true-listp octets)
                (fn-wire-suffixp suffix octets))
           (<= (len suffix) (len octets)))
  :hints (("Goal" :induct (fn-wire-suffixp suffix octets))))

(defthm fn-wire-suffixp-reconstruct
  (implies (and (true-listp octets)
                (fn-wire-suffixp suffix octets))
           (equal (append (take (- (len octets) (len suffix)) octets)
                          suffix)
                  octets))
  :hints (("Goal" :induct (fn-wire-suffixp suffix octets))))

(defthm fn-wire-result-state-of-make-result
  (equal (fn-wire-result-state (fn-wire-make-result wire-state events))
         wire-state))

(defthm fn-wire-result-events-of-make-result
  (equal (fn-wire-result-events (fn-wire-make-result wire-state events))
         events))

(defthm fn-wire-octet-list-is-true-list
  (implies (fn-wire-octet-listp octets)
           (true-listp octets))
  :hints (("Goal" :induct (fn-wire-octet-listp octets))))

; One byte yields at most one framing event, so the pull API's single event and
; the fixed-mode composition's event list carry the same information.
(defthm fn-wire-feed-byte-emits-at-most-one-event
  (equal (cdr (fn-wire-result-events (fn-wire-feed-byte wire-state byte)))
         nil)
  :hints (("Goal" :in-theory (enable fn-wire-feed-byte
                                      fn-wire-after-line
                                      fn-wire-close
                                      fn-wire-result-events
                                      fn-wire-make-result))))

; A yielded event is a nonempty list, so "no event" in the pull API and "no
; event in the composition" are the same condition.
(defthm fn-wire-feed-byte-event-is-not-nil
  (implies (consp (fn-wire-result-events (fn-wire-feed-byte wire-state byte)))
           (car (fn-wire-result-events
                 (fn-wire-feed-byte wire-state byte))))
  :hints (("Goal" :in-theory (enable fn-wire-feed-byte
                                      fn-wire-after-line
                                      fn-wire-close
                                      fn-wire-result-events
                                      fn-wire-make-result
                                      fn-wire-command-event
                                      fn-wire-article-event
                                      fn-wire-reject-event))))

; The same two facts after fn-wire-result-events has been expanded; the
; framing loops leave both forms behind depending on which accessors are open.
(defthm fn-wire-feed-byte-emits-at-most-one-event-cons-form
  (equal (cdr (cdr (fn-wire-feed-byte wire-state byte))) nil)
  :hints (("Goal"
           :use ((:instance fn-wire-feed-byte-emits-at-most-one-event))
           :in-theory (e/d (fn-wire-result-events)
                           (fn-wire-feed-byte
                            fn-wire-feed-byte-emits-at-most-one-event)))))

(defthm fn-wire-feed-byte-event-is-not-nil-cons-form
  (implies (consp (cdr (fn-wire-feed-byte wire-state byte)))
           (car (cdr (fn-wire-feed-byte wire-state byte))))
  :hints (("Goal"
           :use ((:instance fn-wire-feed-byte-event-is-not-nil))
           :in-theory (e/d (fn-wire-result-events)
                           (fn-wire-feed-byte
                            fn-wire-feed-byte-event-is-not-nil)))))

(defthm fn-wire-feed-byte-silent-step-stays-open
  (implies (and (fn-wire-statep wire-state)
                (not (equal (fn-wire-state-mode wire-state) :closed))
                (not (consp (fn-wire-result-events
                             (fn-wire-feed-byte wire-state byte)))))
           (not (equal (fn-wire-state-mode
                        (fn-wire-result-state
                         (fn-wire-feed-byte wire-state byte)))
                       :closed)))
  :hints (("Goal" :in-theory (enable fn-wire-feed-byte
                                      fn-wire-after-line
                                      fn-wire-close
                                      fn-wire-result-events
                                      fn-wire-result-state
                                      fn-wire-make-result
                                      fn-wire-make-state
                                      fn-wire-statep))))

; -----------------------------------------------------------------------------
; One call of the served path.

(defthm fn-wire-next-loop-preserves-statep
  (implies (fn-wire-statep wire-state)
           (fn-wire-statep
            (fn-wire-next-state (fn-wire-next-loop wire-state octets))))
  :hints (("Goal"
           :induct (fn-wire-next-loop wire-state octets)
           :in-theory (e/d (fn-wire-next-loop
                            fn-wire-next-state
                            fn-wire-make-next)
                           (fn-wire-feed-byte fn-wire-statep
                            fn-wire-close fn-wire-make-state)))))

(defthm fn-wire-next-preserves-statep
  (implies (fn-wire-statep wire-state)
           (fn-wire-statep
            (fn-wire-next-state (fn-wire-next wire-state octets))))
  :hints (("Goal"
           :use ((:instance fn-wire-next-loop-preserves-statep))
           :in-theory (e/d (fn-wire-next)
                                  (fn-wire-next-loop fn-wire-statep
                                   fn-wire-next-state fn-wire-next-event
                                   fn-wire-next-unconsumed)))))

(defthm fn-wire-next-loop-unconsumed-is-suffix
  (implies (and (fn-wire-statep wire-state)
                (fn-wire-octet-listp octets))
           (fn-wire-suffixp
            (fn-wire-next-unconsumed (fn-wire-next-loop wire-state octets))
            octets))
  :hints (("Goal"
           :induct (fn-wire-next-loop wire-state octets)
           :in-theory (e/d (fn-wire-next-loop
                            fn-wire-next-unconsumed
                            fn-wire-make-next)
                           (fn-wire-feed-byte fn-wire-statep fn-wire-close
                            fn-wire-make-state)))))

(defthm fn-wire-next-unconsumed-is-suffix
  (implies (and (fn-wire-statep wire-state)
                (fn-wire-octet-listp octets))
           (fn-wire-suffixp
            (fn-wire-next-unconsumed (fn-wire-next wire-state octets))
            octets))
  :hints (("Goal"
           :use ((:instance fn-wire-next-loop-unconsumed-is-suffix))
           :in-theory (e/d (fn-wire-next)
                                  (fn-wire-next-loop fn-wire-statep
                                   fn-wire-next-state fn-wire-next-event
                                   fn-wire-next-unconsumed)))))

(defthm fn-wire-next-consumed-prefix-reconstructs-input
  (implies (and (fn-wire-statep wire-state)
                (fn-wire-octet-listp octets))
           (equal
            (append
             (take (- (len octets)
                      (len (fn-wire-next-unconsumed
                            (fn-wire-next wire-state octets))))
                   octets)
             (fn-wire-next-unconsumed (fn-wire-next wire-state octets)))
            octets))
  :hints (("Goal"
           :use ((:instance fn-wire-suffixp-reconstruct
                  (suffix (fn-wire-next-unconsumed
                           (fn-wire-next wire-state octets))))
                 (:instance fn-wire-octet-list-is-true-list)
                 (:instance fn-wire-next-unconsumed-is-suffix))
           :in-theory (disable fn-wire-next fn-wire-statep fn-wire-suffixp
                               fn-wire-next-unconsumed fn-wire-octet-listp
                               fn-wire-next-unconsumed-is-suffix))))

(defthm fn-wire-next-unconsumed-is-bounded
  (implies (and (fn-wire-statep wire-state)
                (fn-wire-octet-listp octets))
           (<= (len (fn-wire-next-unconsumed
                     (fn-wire-next wire-state octets)))
               (len octets)))
  :hints (("Goal"
           :use ((:instance fn-wire-suffixp-implies-length-bound
                  (suffix (fn-wire-next-unconsumed
                           (fn-wire-next wire-state octets))))
                 (:instance fn-wire-octet-list-is-true-list)
                 (:instance fn-wire-next-unconsumed-is-suffix))
           :in-theory (disable fn-wire-next fn-wire-statep fn-wire-suffixp
                               fn-wire-next-unconsumed fn-wire-octet-listp
                               fn-wire-next-unconsumed-is-suffix))))

; An open valid-state call reports an event only after consuming input.  Thus a
; yielded boundary cannot be manufactured from an empty socket chunk; when no
; event is found, every supplied proper octet has been consumed into the
; returned framing state.
(defthm fn-wire-next-loop-event-needs-input
  (implies (and (fn-wire-statep wire-state)
                (not (equal (fn-wire-state-mode wire-state) :closed))
                (fn-wire-octet-listp octets)
                (fn-wire-next-event (fn-wire-next-loop wire-state octets)))
           (consp octets))
  :hints (("Goal"
           :induct (fn-wire-next-loop wire-state octets)
           :in-theory (e/d (fn-wire-next-loop
                            fn-wire-next-event
                            fn-wire-make-next)
                           (fn-wire-feed-byte fn-wire-statep fn-wire-close
                            fn-wire-make-state)))))

(defthm fn-wire-next-event-needs-input
  (implies (and (fn-wire-statep wire-state)
                (not (equal (fn-wire-state-mode wire-state) :closed))
                (fn-wire-octet-listp octets)
                (fn-wire-next-event (fn-wire-next wire-state octets)))
           (consp octets))
  :hints (("Goal"
           :use ((:instance fn-wire-next-loop-event-needs-input))
           :in-theory (e/d (fn-wire-next)
                                  (fn-wire-next-loop fn-wire-statep
                                   fn-wire-next-state fn-wire-next-event
                                   fn-wire-next-unconsumed)))))

(defthm fn-wire-next-loop-no-event-consumes-proper-chunk
  (implies (and (fn-wire-statep wire-state)
                (not (equal (fn-wire-state-mode wire-state) :closed))
                (fn-wire-octet-listp octets)
                (not (fn-wire-next-event (fn-wire-next-loop wire-state octets))))
           (equal (fn-wire-next-unconsumed (fn-wire-next-loop wire-state octets))
                  nil))
  :hints (("Goal"
           :induct (fn-wire-next-loop wire-state octets)
           :in-theory (e/d (fn-wire-next-loop
                            fn-wire-next-event
                            fn-wire-next-unconsumed
                            fn-wire-make-next)
                           (fn-wire-feed-byte fn-wire-statep fn-wire-close
                            fn-wire-make-state fn-wire-result-state
                            fn-wire-result-events fn-wire-state-mode)))))

(defthm fn-wire-next-no-event-consumes-proper-chunk
  (implies (and (fn-wire-statep wire-state)
                (not (equal (fn-wire-state-mode wire-state) :closed))
                (fn-wire-octet-listp octets)
                (not (fn-wire-next-event (fn-wire-next wire-state octets))))
           (equal (fn-wire-next-unconsumed (fn-wire-next wire-state octets))
                  nil))
  :hints (("Goal"
           :use ((:instance fn-wire-next-loop-no-event-consumes-proper-chunk))
           :in-theory (e/d (fn-wire-next)
                                  (fn-wire-next-loop fn-wire-statep
                                   fn-wire-next-state fn-wire-next-event
                                   fn-wire-next-unconsumed)))))

; -----------------------------------------------------------------------------
; The chunk loop the adapter runs, and its partition law.

(defthm fn-wire-next-loop-strictly-consumes
  (implies (and (fn-wire-statep wire-state)
                (not (equal (fn-wire-state-mode wire-state) :closed))
                (consp octets))
           (< (len (fn-wire-next-unconsumed
                    (fn-wire-next-loop wire-state octets)))
              (len octets)))
  :hints (("Goal"
           :induct (fn-wire-next-loop wire-state octets)
           :in-theory (e/d (fn-wire-next-loop
                            fn-wire-next-unconsumed
                            fn-wire-make-next)
                           (fn-wire-feed-byte fn-wire-statep
                            fn-wire-close fn-wire-make-state
                            fn-wire-result-state fn-wire-result-events
                            fn-wire-state-mode)))))

(defthm fn-wire-next-strictly-consumes
  (implies (and (fn-wire-statep wire-state)
                (not (equal (fn-wire-state-mode wire-state) :closed))
                (consp octets))
           (< (len (fn-wire-next-unconsumed (fn-wire-next wire-state octets)))
              (len octets)))
  :hints (("Goal"
           :use ((:instance fn-wire-next-loop-strictly-consumes))
           :in-theory (e/d (fn-wire-next)
                                  (fn-wire-next-loop fn-wire-statep
                                   fn-wire-next-state fn-wire-next-event
                                   fn-wire-next-unconsumed)))))

(defthm fn-wire-next-loop-unconsumed-octet-listp
  (implies (and (fn-wire-statep wire-state)
                (fn-wire-octet-listp octets))
           (fn-wire-octet-listp
            (fn-wire-next-unconsumed (fn-wire-next-loop wire-state octets))))
  :hints (("Goal"
           :induct (fn-wire-next-loop wire-state octets)
           :in-theory (e/d (fn-wire-next-loop
                            fn-wire-next-unconsumed
                            fn-wire-make-next)
                           (fn-wire-feed-byte fn-wire-statep fn-wire-close
                            fn-wire-make-state)))))

(defthm fn-wire-next-unconsumed-octet-listp
  (implies (and (fn-wire-statep wire-state)
                (fn-wire-octet-listp octets))
           (fn-wire-octet-listp
            (fn-wire-next-unconsumed (fn-wire-next wire-state octets))))
  :hints (("Goal"
           :use ((:instance fn-wire-next-loop-unconsumed-octet-listp))
           :in-theory (e/d (fn-wire-next)
                                  (fn-wire-next-loop fn-wire-statep
                                   fn-wire-next-state fn-wire-next-event
                                   fn-wire-next-unconsumed)))))

; The adapter's loop: call fn-wire-next, take at most one event, then re-feed
; the returned unconsumed suffix until the chunk is exhausted or the connection
; closes.  This mirrors tools/run_reader.py:167-181 exactly, including its
; closing-connection exit.
(defun fn-wire-drive (wire-state octets)
  (declare (xargs :guard t
                  :verify-guards nil
                  :measure (len octets)
                  :hints (("Goal"
                           :use ((:instance fn-wire-next-strictly-consumes))
                           :in-theory (disable fn-wire-next)))))
  (if (or (not (fn-wire-statep wire-state))
          (equal (fn-wire-state-mode wire-state) :closed)
          (not (consp octets)))
      (fn-wire-make-result wire-state nil)
    (let* ((next (fn-wire-next wire-state octets))
           (tail (fn-wire-drive (fn-wire-next-state next)
                                (fn-wire-next-unconsumed next))))
      (fn-wire-make-result
       (fn-wire-result-state tail)
       (append (if (fn-wire-next-event next)
                   (list (fn-wire-next-event next))
                 nil)
               (fn-wire-result-events tail))))))

(verify-guards fn-wire-drive)

; One call of the served path is the first event of the fixed-mode composition,
; and the composition is that event followed by the composition of the rest.
; One call of the served path is the first event of the fixed-mode composition,
; and the composition is that event followed by the composition of the rest.
; Stated as a rewrite from the split form to the composition, which is the
; direction the adapter-loop proof below needs and which terminates.
(defthm fn-wire-next-loop-splits-feed-proper
  (implies (and (fn-wire-statep wire-state)
                (fn-wire-octet-listp octets))
           (equal (fn-wire-make-result
                   (fn-wire-result-state
                    (fn-wire-feed-proper
                     (fn-wire-next-state (fn-wire-next-loop wire-state octets))
                     (fn-wire-next-unconsumed
                      (fn-wire-next-loop wire-state octets))))
                   (append
                    (if (fn-wire-next-event (fn-wire-next-loop wire-state octets))
                        (list (fn-wire-next-event
                               (fn-wire-next-loop wire-state octets)))
                      nil)
                    (fn-wire-result-events
                     (fn-wire-feed-proper
                      (fn-wire-next-state (fn-wire-next-loop wire-state octets))
                      (fn-wire-next-unconsumed
                       (fn-wire-next-loop wire-state octets))))))
                  (fn-wire-feed-proper wire-state octets)))
  :hints (("Goal"
           :induct (fn-wire-next-loop wire-state octets)
           :in-theory (e/d (fn-wire-next-loop
                            fn-wire-feed-proper
                            fn-wire-next-state
                            fn-wire-next-event
                            fn-wire-next-unconsumed
                            fn-wire-make-next
                            fn-wire-result-state
                            fn-wire-result-events
                            fn-wire-make-result)
                           (fn-wire-feed-byte fn-wire-statep
                            fn-wire-close fn-wire-make-state)))))

; The same split in the two shapes the adapter-loop proof leaves behind, after
; the event list has been simplified in each case.  Restatements, not new
; properties.
(defthm fn-wire-next-loop-splits-feed-proper-with-event
  (implies (and (fn-wire-statep wire-state)
                (fn-wire-octet-listp octets)
                (fn-wire-next-event (fn-wire-next-loop wire-state octets)))
           (equal (fn-wire-make-result
                   (fn-wire-result-state
                    (fn-wire-feed-proper
                     (fn-wire-next-state (fn-wire-next-loop wire-state octets))
                     (fn-wire-next-unconsumed
                      (fn-wire-next-loop wire-state octets))))
                   (cons (fn-wire-next-event
                          (fn-wire-next-loop wire-state octets))
                         (fn-wire-result-events
                          (fn-wire-feed-proper
                           (fn-wire-next-state
                            (fn-wire-next-loop wire-state octets))
                           (fn-wire-next-unconsumed
                            (fn-wire-next-loop wire-state octets))))))
                  (fn-wire-feed-proper wire-state octets)))
  :hints (("Goal"
           :use ((:instance fn-wire-next-loop-splits-feed-proper))
           :in-theory (disable fn-wire-next-loop-splits-feed-proper
                               fn-wire-feed-proper fn-wire-next-loop
                               fn-wire-statep))))

(defthm fn-wire-next-loop-splits-feed-proper-without-event
  (implies (and (fn-wire-statep wire-state)
                (fn-wire-octet-listp octets)
                (not (fn-wire-next-event (fn-wire-next-loop wire-state octets))))
           (equal (fn-wire-make-result
                   (fn-wire-result-state
                    (fn-wire-feed-proper
                     (fn-wire-next-state (fn-wire-next-loop wire-state octets))
                     (fn-wire-next-unconsumed
                      (fn-wire-next-loop wire-state octets))))
                   (fn-wire-result-events
                    (fn-wire-feed-proper
                     (fn-wire-next-state (fn-wire-next-loop wire-state octets))
                     (fn-wire-next-unconsumed
                      (fn-wire-next-loop wire-state octets)))))
                  (fn-wire-feed-proper wire-state octets)))
  :hints (("Goal"
           :use ((:instance fn-wire-next-loop-splits-feed-proper))
           :in-theory (disable fn-wire-next-loop-splits-feed-proper
                               fn-wire-feed-proper fn-wire-next-loop
                               fn-wire-statep))))

(defthm fn-wire-feed-proper-preserves-statep
  (implies (fn-wire-statep wire-state)
           (fn-wire-statep
            (fn-wire-result-state (fn-wire-feed-proper wire-state octets))))
  :hints (("Goal"
           :induct (fn-wire-feed-proper wire-state octets)
           :in-theory (e/d (fn-wire-feed-proper
                            fn-wire-result-state
                            fn-wire-make-result)
                           (fn-wire-feed-byte fn-wire-statep
                            fn-wire-close fn-wire-make-state)))))

; The adapter's loop computes exactly the fixed-mode composition of the same
; octets.  This is the bridge from the served pull API to the append law.
(defthm fn-wire-feed-proper-closed-is-noop
  (implies (equal (fn-wire-state-mode wire-state) :closed)
           (equal (fn-wire-feed-proper wire-state octets)
                  (fn-wire-make-result wire-state nil)))
  :hints (("Goal" :expand ((fn-wire-feed-proper wire-state octets)))))

(defthm fn-wire-feed-proper-of-empty-chunk
  (implies (not (consp octets))
           (equal (fn-wire-feed-proper wire-state octets)
                  (fn-wire-make-result wire-state nil)))
  :hints (("Goal" :expand ((fn-wire-feed-proper wire-state octets)))))

(defthm fn-wire-next-loop-of-empty-chunk
  (implies (not (equal (fn-wire-state-mode wire-state) :closed))
           (equal (fn-wire-next-loop wire-state nil)
                  (fn-wire-make-next wire-state nil nil)))
  :hints (("Goal" :expand ((fn-wire-next-loop wire-state nil)))))

; A chunk that yields no event is consumed whole, so the fixed-mode
; composition of it is just the framing state it leaves.
(defthm fn-wire-next-loop-silent-chunk-is-feed-proper
  (implies (and (fn-wire-statep wire-state)
                (not (equal (fn-wire-state-mode wire-state) :closed))
                (fn-wire-octet-listp octets)
                (not (fn-wire-next-event (fn-wire-next-loop wire-state octets))))
           (equal (fn-wire-feed-proper wire-state octets)
                  (fn-wire-make-result
                   (fn-wire-next-state (fn-wire-next-loop wire-state octets))
                   nil)))
  :hints (("Goal"
           :use ((:instance fn-wire-next-loop-splits-feed-proper)
                 (:instance fn-wire-next-loop-no-event-consumes-proper-chunk))
           :in-theory (disable fn-wire-next-loop-splits-feed-proper
                               fn-wire-next-loop-no-event-consumes-proper-chunk
                               fn-wire-next-loop-splits-feed-proper-with-event
                               fn-wire-next-loop-splits-feed-proper-without-event
                               fn-wire-feed-proper fn-wire-next-loop
                               fn-wire-statep))))

(defthm fn-wire-drive-of-empty-chunk
  (implies (not (consp octets))
           (equal (fn-wire-drive wire-state octets)
                  (fn-wire-make-result wire-state nil)))
  :hints (("Goal" :expand ((fn-wire-drive wire-state octets)))))

(defthm fn-wire-drive-closed-is-noop
  (implies (equal (fn-wire-state-mode wire-state) :closed)
           (equal (fn-wire-drive wire-state octets)
                  (fn-wire-make-result wire-state nil)))
  :hints (("Goal" :expand ((fn-wire-drive wire-state octets)))))

(defthm fn-wire-drive-is-feed-proper
  (implies (and (fn-wire-statep wire-state)
                (fn-wire-octet-listp octets))
           (equal (fn-wire-drive wire-state octets)
                  (fn-wire-feed-proper wire-state octets)))
  :hints (("Goal"
           :induct (fn-wire-drive wire-state octets)
           :expand ((fn-wire-drive wire-state octets))
           :in-theory (e/d (fn-wire-next)
                           (fn-wire-drive
                            fn-wire-feed-proper
                            fn-wire-next-loop
                            fn-wire-feed-byte
                            fn-wire-statep
                            fn-wire-close
                            fn-wire-make-state
                            fn-wire-make-result
                            fn-wire-result-state
                            fn-wire-result-events
                            fn-wire-next-state
                            fn-wire-next-event
                            fn-wire-next-unconsumed
                            fn-wire-state-mode)
                           ((:induction fn-wire-drive)))
           :do-not '(generalize))))

(defthm fn-wire-octet-listp-append
  (implies (and (fn-wire-octet-listp left)
                (fn-wire-octet-listp right))
           (fn-wire-octet-listp (append left right)))
  :hints (("Goal" :induct (fn-wire-octet-listp left))))

(defthm fn-wire-drive-preserves-statep
  (implies (and (fn-wire-statep wire-state)
                (fn-wire-octet-listp octets))
           (fn-wire-statep
            (fn-wire-result-state (fn-wire-drive wire-state octets))))
  :hints (("Goal"
           :use ((:instance fn-wire-drive-is-feed-proper)
                 (:instance fn-wire-feed-proper-preserves-statep))
           :in-theory (disable fn-wire-drive fn-wire-feed-proper
                               fn-wire-statep))))

; Partition independence for the served path, in the form the adapter loops.
; Driving the concatenation is the same state and the same event sequence as
; driving the left part and then driving the right part from the state it
; left.  The subject is fn-wire-next (host/reader-host.lisp:91) composed by the
; adapter's own loop; fn-wire-feed-proper-append supplies the induction through
; fn-wire-drive-is-feed-proper.
(defthm fn-wire-drive-partition-independence
  (implies (and (fn-wire-statep wire-state)
                (fn-wire-octet-listp left)
                (fn-wire-octet-listp right))
           (equal (fn-wire-drive wire-state (append left right))
                  (fn-wire-make-result
                   (fn-wire-result-state
                    (fn-wire-drive
                     (fn-wire-result-state (fn-wire-drive wire-state left))
                     right))
                   (append
                    (fn-wire-result-events (fn-wire-drive wire-state left))
                    (fn-wire-result-events
                     (fn-wire-drive
                      (fn-wire-result-state (fn-wire-drive wire-state left))
                      right))))))
  :hints (("Goal"
           :use ((:instance fn-wire-drive-is-feed-proper
                            (octets (append left right)))
                 (:instance fn-wire-drive-is-feed-proper (octets left))
                 (:instance fn-wire-drive-is-feed-proper
                            (wire-state (fn-wire-result-state
                                         (fn-wire-feed-proper wire-state left)))
                            (octets right))
                 (:instance fn-wire-drive-preserves-statep (octets left))
                 (:instance fn-wire-feed-proper-preserves-statep
                            (octets left))
                 (:instance fn-wire-feed-proper-append))
           :in-theory (disable fn-wire-drive fn-wire-feed-proper
                               fn-wire-statep
                               fn-wire-drive-is-feed-proper
                               fn-wire-feed-proper-append))))

; ---------------------------------------------------------------------------
; Export theory
;
; The keystones leave enabled (fn-wire-drive-partition-independence,
; fn-wire-drive-is-feed-proper, fn-wire-drive-preserves-statep and the
; fn-wire-next-* results the reader host relies on).  The suffix vocabulary and
; the drive definition are proof vocabulary, withdrawn under one name.

(deftheory fn-wire-invariants-vocabulary
  '(fn-wire-suffixp fn-wire-suffixp-refl fn-wire-suffixp-cdr
    fn-wire-suffixp-implies-length-bound fn-wire-octet-list-is-true-list))

(in-theory (disable fn-wire-invariants-vocabulary fn-wire-drive))
