; Copied for fn2 squares E2 from acl2aiguide/examples/transport/read-state-transport.lisp
; Source commit: 2283433658784eb4767192508f0e5135a8c939b1
; Original content follows unchanged; all includes resolve inside this copy.
; examples/transport/read-state-transport.lisp
;
; What it shows: summary adequacy as transport (Experiment A).  The
; contract's relation is instantiated as RS-SAME-READS, a DEFUN-SK saying
; the history and the summary agree on "is N read?" for EVERY article N.
; The work is one lemma per event kind (RS-SAME-READS-OF-READ, -OF-CATCHUP,
; and -OF-OTHER for malformed events, which both sides ignore), the count
; observation from the pointwise one (RS-OBS-COUNT-AGREE, by induction on
; the bound), and then RS-SUMMARY-ADEQUATE costs one :functional-instance
; hint per conclusion.  The converter's correctness RS-SUMMARIZE-RELATED is
; a separate obligation, proved separately: the contract says related
; states stay related, not that the converter produces a related state.
;
; Cited by examples/transport/README.md, "Experiment A".

(in-package "ACL2")
(include-book "fold-contract")
(include-book "read-state-summary")

(defun-sk rs-same-reads (h s)
  (forall n (equal (rs-h-obs-read h n) (rs-s-obs-read s n))))

(in-theory (disable rs-same-reads))

; The per-event lemmas reason about the observations only through the
; step lemmas of the two representation books.
(local (in-theory (disable rs-h-obs-read rs-s-obs-read rs-event-covers)))

; ---------------------------------------------------------------------------
; One lemma per event kind.

(defthm rs-same-reads-of-read
  (implies (and (rs-s-ok s) (rs-same-reads h s)
                (rs-eventp e) (eq (car e) :read))
           (rs-same-reads (rs-h-step h e) (rs-s-step s e)))
  :hints (("Goal"
           :expand ((rs-same-reads (rs-h-step h e) (rs-s-step s e)))
           :use ((:instance rs-same-reads-necc
                            (n (rs-same-reads-witness (rs-h-step h e)
                                                      (rs-s-step s e))))))))

(defthm rs-same-reads-of-catchup
  (implies (and (rs-s-ok s) (rs-same-reads h s)
                (rs-eventp e) (eq (car e) :catchup))
           (rs-same-reads (rs-h-step h e) (rs-s-step s e)))
  :hints (("Goal"
           :expand ((rs-same-reads (rs-h-step h e) (rs-s-step s e)))
           :use ((:instance rs-same-reads-necc
                            (n (rs-same-reads-witness (rs-h-step h e)
                                                      (rs-s-step s e))))))))

(defthm rs-same-reads-of-other
  (implies (and (rs-same-reads h s) (not (rs-eventp e)))
           (rs-same-reads (rs-h-step h e) (rs-s-step s e)))
  :hints (("Goal"
           :expand ((rs-same-reads (rs-h-step h e) (rs-s-step s e)))
           :use ((:instance rs-same-reads-necc
                            (n (rs-same-reads-witness (rs-h-step h e)
                                                      (rs-s-step s e))))))))

(defthm rs-same-reads-of-step
  (implies (and (rs-s-ok s) (rs-same-reads h s))
           (rs-same-reads (rs-h-step h e) (rs-s-step s e)))
  :hints (("Goal" :use (rs-same-reads-of-read rs-same-reads-of-catchup
                         rs-same-reads-of-other)
                  :in-theory (e/d (rs-eventp)
                                  (rs-same-reads-of-read rs-same-reads-of-catchup
                                   rs-same-reads-of-other rs-s-ok)))))

; ---------------------------------------------------------------------------
; Observations.  The count is not pointwise; it follows from agreement on
; every article by induction on the bound.

(defthm rs-obs-count-agree
  (implies (rs-same-reads h s)
           (equal (rs-h-obs-count h b) (rs-s-obs-count s b)))
  :hints (("Goal" :induct (rs-h-obs-count h b))
          ("Subgoal *1/2" :use ((:instance rs-same-reads-necc (n b))))))

(defthm rs-obs-agree
  (implies (rs-same-reads h s)
           (equal (rs-h-obs h q) (rs-s-obs s q)))
  :hints (("Goal" :use ((:instance rs-same-reads-necc
                                   (n (and (consp q) (consp (cdr q))
                                           (cadr q))))))))

(defthm rs-same-reads-init
  (rs-same-reads (rs-h-init) (rs-s-init))
  :hints (("Goal" :in-theory (enable rs-same-reads rs-h-obs-read rs-s-obs-read))))

; ---------------------------------------------------------------------------
; The transport: from any related pair, both observations agree after
; every suffix.  Only the functional instance and the lemmas above.

(defthm rs-summary-adequate
  (implies (and (rs-h-ok h) (rs-s-ok s) (rs-same-reads h s))
           (and (rs-same-reads (rs-h-fold h j) (rs-s-fold s j))
                (equal (rs-h-obs (rs-h-fold h j) q)
                       (rs-s-obs (rs-s-fold s j) q))))
  :hints (("Goal"
           :in-theory (disable rs-h-ok rs-s-ok rs-h-obs rs-s-obs)
           :use ((:functional-instance fc-rel-fold
                                       (fc1-init rs-h-init) (fc2-init rs-s-init)
                                       (fc1-step rs-h-step) (fc2-step rs-s-step)
                                       (fc1-obs rs-h-obs) (fc2-obs rs-s-obs)
                                       (fc1-ok rs-h-ok) (fc2-ok rs-s-ok)
                                       (fc-rel rs-same-reads)
                                       (fc1-fold rs-h-fold) (fc2-fold rs-s-fold))
                 (:functional-instance fc-obs-fold
                                       (fc1-init rs-h-init) (fc2-init rs-s-init)
                                       (fc1-step rs-h-step) (fc2-step rs-s-step)
                                       (fc1-obs rs-h-obs) (fc2-obs rs-s-obs)
                                       (fc1-ok rs-h-ok) (fc2-ok rs-s-ok)
                                       (fc-rel rs-same-reads)
                                       (fc1-fold rs-h-fold) (fc2-fold rs-s-fold))))))

; ---------------------------------------------------------------------------
; The converter, a separate obligation.

(defthm rs-summarize-related
  (rs-same-reads h (rs-summarize h))
  :hints (("Goal" :induct (rs-summarize h))
          ("Subgoal *1/2" :use ((:instance rs-same-reads-of-step
                                           (h (cdr h)) (e (car h))
                                           (s (rs-summarize (cdr h)))))
                          :in-theory (enable rs-h-step))
          ("Subgoal *1/1" :in-theory (enable rs-same-reads rs-h-obs-read
                                              rs-s-obs-read))))

; Together: a history and its summary answer every query alike, now and
; after any further events.
(defthm rs-summarize-adequate
  (implies (rs-h-ok h)
           (equal (rs-s-obs (rs-s-fold (rs-summarize h) j) q)
                  (rs-h-obs (rs-h-fold h j) q)))
  :hints (("Goal" :use ((:instance rs-summary-adequate (s (rs-summarize h))))
                  :in-theory (disable rs-summary-adequate rs-h-ok rs-s-ok
                                      rs-h-obs rs-s-obs))))
