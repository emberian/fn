; Not a book yet: the strong statement of commit durability (ember, 2026-11-07), over every
; execution and environment, of which FN2-COMMIT-ACK-IMPLIES-DURABLE (the simulator run) is
; to become a tested instance. Components marked OWED are still to be defined; nothing here
; is admitted. Planned home: books/commit-durable-all.lisp + books/assumptions-device.lisp.

;; ENVIRONMENT. ACTIONS is any list over the host vocabulary of books/host-boundary.lisp;
;; FN2-ENV-RUN interprets it over a live core (genesis by fn2-init-executor on PROFILE):
;;   (:turn)                                   fn2-turn
;;   (:take)                                   fn2-host-outbox-peek/-ack: the device receives
;;                                             the head descriptor and its payload bytes
;;   (:post-result cell slot gen evkind outcome reason count aux0 aux1)
;;                                             fn2-host-post-result (completions, including
;;                                             failed, short, torn-in-flight and fail-slow:
;;                                             any order, any delay, any outcome)
;;   (:accept-result ...) (:loan-write op gen offset octets)
;;                                             network: arbitrary octets into posted loans
;;   (:clock mono real flags) (:signal bits)   fn2-host-post-clock / -signal
;; An action the vocabulary contract forbids (a completion for an op the device never took,
;; a second completion, a loan write outside its span) is SKIPPED, not assumed away: the
;; statement has no hypothesis on ACTIONS. The run records the device log: (:write token
;; offset octets) at take, (:result token outcome count) at post, (:fence token) /
;; (:fence-result token outcome).

;; DEVICE ASSUMPTION (books/assumptions-device.lisp; the only fact about the environment).
(encapsulate
 (((fn2-a-crash-image * *) => *))
 ;; local witness: the honest device, every completed write applied in completion order
 (local (defun fn2-a-crash-image (log choice)
          (declare (ignore choice)) (fn2-dev-completed-image log)))          ; OWED: defun
 ;; A-FENCE-PERSISTS: a write whose :done completion precedes a successful fence result
 ;; issued after it is in every crash image, unless a later completed write to the same
 ;; range replaced it. Unfenced writes may be lost or torn; CHOICE picks the image.
 (defthm fn2-a-fence-persists
   (implies (fn2-dev-fenced-write-p w log)                                  ; OWED: defun
            (fn2-dev-image-keeps-p w log (fn2-a-crash-image log choice)))    ; OWED: defun
   :rule-classes nil))

;; THE STATEMENT.
(defthm-owed fn2-commit-ack-implies-recoverable (profile actions choice recovery-actions)
 (let* ((run (fn2-env-run profile actions))                                   ; OWED
        (image (fn2-a-crash-image (fn2-env-device-log run) choice))
        (rec (fn2-env-recover profile image recovery-actions)))               ; OWED
  (implies (and (fn2-profile-supportedp profile)                               ; OWED: B profiles
                (fn2-env-recovery-done-p rec))                                 ; OWED
           (subsetp-equal (fn2-env-acknowledged-batches run)                   ; OWED
                          (fn2-env-recovered-batches rec))))                   ; OWED
 :teeth (fn2-commit-recoverable-positive fn2-commit-recoverable-fence-removal)
 :schema :crash
 :doc "Every acknowledged commit batch (a member reply observed at the commit rows'
 visibility after any fn2-turn) is in the history recovery reconstructs, by fn2-turn over a
 fresh core whose reads (RECOVERY-ACTIONS, the same vocabulary; read results must be image
 octets) see any crash image the device can produce. Only A-FENCE-PERSISTS is assumed.")

;; RECOVERY. FN2-ENV-RECOVER: fresh core, genesis, then RECOVERY-ACTIONS interleaved with
;; fn2-turn; a read completion carries the IMAGE's octets for its range (reads are honest by
;; the same device assumption). DONE-P: the recovery machine reached :done. RECOVERED: the
;; batch numbers of the history it reports.

;; TEETH (OWED, both evaluate with a concrete device in place of fn2-a-crash-image):
;;  positive: profile tiny, the vocabulary image of fn2-commit-proof-positive's 600-step
;;   trace, the honest device: acknowledged (1 2) within recovered (1 2).
;;  removal: same trace, a device that drops the last fenced write (lying flush, the
;;   fn2-commit-proof-fence-removal case): acknowledged (1 2), recovered (1).
