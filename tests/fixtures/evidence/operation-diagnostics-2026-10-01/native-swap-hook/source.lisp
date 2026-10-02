(when (eq w :swap)
                                     (fnn-owner-core 'fn-owner-report-writer-enter)
                                     (handler-case
                                      (progn
                                     ;; the commit point, then the swap, in one quantum
                                     (fnn-state-checkpoint-install store stage)
                                     (setq installed t)
                                     (fnn-reclaim-cut :installed)
                                     (fnn-owner-core 'fn-owner-orcp-swap rebuilt)
                                     (fnn-install-stobj 'fn-cat cat)
                                     (fnn-install-stobj 'fn-hist hist)
                                     (setq swapped t)
                                     ;; The swapped owner is the open's owner
                                     ;; before its recovery barriers: :ready
                                     ;; only after them, in this quantum
                                     ;; (fn-orrd-a-post-after-the-swap-is-
                                     ;; taken-as-before).
                                     (fnn-owner-reclaim-barriers store)
                                       (fnn-owner-core 'fn-owner-report-writer-leave))
                                      (error (condition)
                                       (fnn-owner-core 'fn-owner-report-writer-fault)
                                       (error condition))))
