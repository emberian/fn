; fn: an FNFD journal replays alike whether a batch's resolutions follow the
; next batch's intents or precede them (lane owner-offlock, 2026-10-03).
;
; Before this lane the committer wrote a batch N's intent frames in its
; START, the next batch's (N+1) in the START-NEXT behind N's barrier, and N's
; resolution frames in N's COMPLETE: intents N, intents N+1, resolutions N.
; Since this lane every frame of a batch is written by its own off-owner job
; (books/owner-queued-work.lisp, KIND :batch: intents, then after the
; barrier resolutions), so the journal reads intents N, resolutions N,
; intents N+1.  A journal a running node wrote under the old order is read
; at its upgrade by the new build (no migration), so both orders must replay
; to the same state.  The open replays each frame through two folds, one
; frame per call of the host-called host/owner-host.lisp
; fn-owner-feed-journal-scan:
;   - the unresolved-intent set, fn-own-feed-intent-apply (an intent adds
;     its key, a commit or abort removes it);
;   - the peer's offerable feed, fn-feed-replay (fn-own-feed-port-replay-
;     peer), in which an intent does nothing.
; The two orders differ only by moving intent frames of batch N+1 past
; resolution frames of batch N, and the keys differ (a key names its
; submission's generation and txid, one per member).  Both folds are
; unchanged by such a move (KEYSTONE fn-fjo-an-intent-moved-past-another-
; resolution-replays-alike).
(in-package "ACL2")
(include-book "owner-feed")

(defthm fn-fjo-memberp-of-remove
  (iff (fn-own-feed-intent-memberp a (fn-own-feed-intent-remove b xs))
       (and (not (equal a b)) (fn-own-feed-intent-memberp a xs)))
  :hints (("Goal" :in-theory (enable fn-own-feed-intent-memberp fn-own-feed-intent-remove)
           :induct (fn-own-feed-intent-memberp a xs))))

; One intent and one resolution of another key commute in the intent fold.
(defthm fn-fjo-intent-commutes-with-another-resolution
  (implies (and (member-equal rkind '(:feed-commit :feed-abort))
                (not (equal (fn-own-feed-intent-key ivals)
                            (fn-own-feed-intent-key rvals))))
           (equal (fn-own-feed-intent-apply
                   (fn-own-feed-intent-apply intents :feed-intent ivals) rkind rvals)
                  (fn-own-feed-intent-apply
                   (fn-own-feed-intent-apply intents rkind rvals) :feed-intent ivals)))
  :hints (("Goal" :in-theory (enable fn-own-feed-intent-apply fn-own-feed-intent-remove
                                     fn-own-feed-intent-memberp))))

; The offerable feed ignores an intent.
(defthm fn-fjo-feed-replay-ignores-an-intent-unfolds
  (equal (fn-feed-apply-record f :feed-intent values) f)
  :hints (("Goal" :in-theory (enable fn-feed-apply-record))))

; The intent fold over a journal's entries, as the open applies them one by
; one (fn-owner-feed-journal-scan, then fn-owner-feed-reconcile-apply).
(defun fn-fjo-intents-run (intents es)
  (declare (xargs :guard t))
  (if (atom es)
      intents
    (fn-fjo-intents-run (fn-own-feed-intent-apply intents
                                                  (fn-feed-journal-kind (car es))
                                                  (fn-feed-journal-values (car es)))
                        (cdr es))))

(defthm fn-fjo-intents-run-of-append
  (equal (fn-fjo-intents-run intents (append xs ys))
         (fn-fjo-intents-run (fn-fjo-intents-run intents xs) ys)))

(defthm fn-fjo-feed-replay-of-append
  (equal (fn-feed-replay f (append xs ys))
         (fn-feed-replay (fn-feed-replay f xs) ys)))

; KEYSTONE.  An intent frame I moved past a resolution frame R of another
; key -- the only difference between the old and the new batch order --
; leaves both of the open's folds unchanged, whatever comes before (XS) and
; after (YS).  Repeated, it carries every intent of batch N+1 past every
; resolution of batch N.  The subjects are fn-own-feed-intent-apply and
; fn-feed-replay, called per frame by the host-called
; host/owner-host.lisp fn-owner-feed-journal-scan (fn-owner-feed-replay-
; counted -> fn-own-feed-port-replay-peer -> fn-feed-replay).
(defthm fn-fjo-an-intent-moved-past-another-resolution-replays-alike
  (implies (and (equal (fn-feed-journal-kind i) :feed-intent)
                (member-equal (fn-feed-journal-kind r) '(:feed-commit :feed-abort))
                (not (equal (fn-own-feed-intent-key (fn-feed-journal-values i))
                            (fn-own-feed-intent-key (fn-feed-journal-values r)))))
           (and (equal (fn-fjo-intents-run intents (append xs (list* i r ys)))
                       (fn-fjo-intents-run intents (append xs (list* r i ys))))
                (equal (fn-feed-replay f (append xs (list* i r ys)))
                       (fn-feed-replay f (append xs (list* r i ys))))))
  :hints (("Goal" :in-theory (disable fn-own-feed-intent-apply fn-feed-apply-record
                                      fn-own-feed-intent-key)
           :use ((:instance fn-fjo-intent-commutes-with-another-resolution
                            (intents (fn-fjo-intents-run intents xs))
                            (ivals (fn-feed-journal-values i))
                            (rkind (fn-feed-journal-kind r))
                            (rvals (fn-feed-journal-values r)))
                 (:instance fn-fjo-feed-replay-ignores-an-intent-unfolds
                            (f (fn-feed-replay f xs))
                            (values (fn-feed-journal-values i)))
                 (:instance fn-fjo-feed-replay-ignores-an-intent-unfolds
                            (f (fn-feed-apply-record (fn-feed-replay f xs)
                                                     (fn-feed-journal-kind r)
                                                     (fn-feed-journal-values r)))
                            (values (fn-feed-journal-values i)))))))
