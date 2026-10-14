; The rows and non-catalogue event directory preserve the normalized prefix.
(in-package "ACL2")
(include-book "log-checkpoint-control")
(include-book "owner-checkpoint-open")
(local (include-book "std/lists/append" :dir :system))
(defthm fn-lc-hstxa-reconstructs
 (implies (fn-hstxa-p x)
          (equal (fn-hstxa-make (fn-hstxa-stxa x) (fn-hstxa-held x)) x))
 :hints (("Goal" :in-theory (enable fn-hstxa-p fn-hstxa-make fn-hstxa-stxa fn-hstxa-held))))
(defthm fn-lc-history-partition-is-lossless
 (equal (fn-lc-recompose-history (fn-lc-event-directory events)
                                 (fn-lc-history-rows configs events))
        (true-list-fix events))
 :hints (("Goal" :induct (fn-lc-history-rows configs events)
  :in-theory (e/d (fn-lc-history-rows fn-lc-event-directory fn-lc-recompose-history
                  fn-replay-composite-held)
                 (fn-held-p fn-hstxa-p fn-hstxa-make fn-hstxa-stxa fn-hstxa-held)))))
(defthm fn-lc-equal-control-gives-equal-event-directories
 (implies (equal (fn-lc-control-of (fn-lc-history-at configs prefix))
                 (fn-lc-control-of (fn-lc-history-at configs other-prefix)))
          (equal (fn-lc-event-directory prefix) (fn-lc-event-directory other-prefix)))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-lc-control-of fn-lc-history-at)
  (fn-sco-capture fn-lc-cpr-control fn-sco-cpr fn-sco-identity fn-sco-consumer
   fn-sco-topic fn-lc-event-directory)))))
(defthm fn-lc-control-and-rows-determine-normalized-prefix
 (implies (and (equal (fn-lc-history-rows configs prefix)
                      (fn-lc-history-rows configs other-prefix))
               (equal (fn-lc-control-of (fn-lc-history-at configs prefix))
                      (fn-lc-control-of (fn-lc-history-at configs other-prefix))))
          (equal (true-list-fix prefix) (true-list-fix other-prefix)))
 :rule-classes nil
 :hints (("Goal" :use
  (fn-lc-equal-control-gives-equal-event-directories
   (:instance fn-lc-history-partition-is-lossless (events prefix))
   (:instance fn-lc-history-partition-is-lossless (events other-prefix)))
  :in-theory (disable fn-lc-control-of fn-lc-history-at fn-lc-history-rows
                     fn-lc-event-directory fn-lc-recompose-history
                     fn-lc-history-partition-is-lossless true-list-fix))))

(defthm fn-lc-append-normalizes-first-argument
 (equal (append (true-list-fix x) tail) (append x tail)))
(defthm fn-lc-append-of-equal-normalized-prefixes
 (implies (equal (true-list-fix x) (true-list-fix y))
          (equal (append x tail) (append y tail)))
 :rule-classes nil
 :hints (("Goal" :use
  (fn-lc-append-normalizes-first-argument
   (:instance fn-lc-append-normalizes-first-argument (x y)))
  :in-theory (disable append true-list-fix fn-lc-append-normalizes-first-argument))))
; Standing rule: append normalizes both prefixes; the suffix is an arbitrary tail.
(defthm fn-lc-control-of-determines-the-rest
 (implies (and (equal (fn-lc-history-rows configs prefix)
                       (fn-lc-history-rows configs other-prefix))
                (equal (fn-lc-control-of (fn-lc-history-at configs prefix))
                       (fn-lc-control-of (fn-lc-history-at configs other-prefix))))
           (equal (fn-ock-recover-full configs frontier (append prefix suffix) max-conns)
                  (fn-ock-recover-full configs frontier (append other-prefix suffix) max-conns)))
 :rule-classes nil
 :hints (("Goal" :use
  (fn-lc-control-and-rows-determine-normalized-prefix
   (:instance fn-lc-append-of-equal-normalized-prefixes
              (x prefix) (y other-prefix) (tail suffix)))
  :in-theory (disable fn-ock-recover-full fn-lc-history-rows fn-lc-control-of
                     fn-lc-history-at append true-list-fix))))
