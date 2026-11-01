(in-package "ACL2")
(include-book "../sim/check-history")

(defconst *fn2-history-unit-profile* (fn2-cm-profile :crash-only t t nil 0 0))
(defconst *fn2-history-unit-b1* '(1 0 ((:put key-a value-a)) (dep-a dep-b)))
(defconst *fn2-history-unit-b2* '(2 1 ((:put key-b value-b)) (dep-c)))
(defconst *fn2-history-unit-h1* (list *fn2-history-unit-b1*))
(defconst *fn2-history-unit-h2* (list *fn2-history-unit-b1* *fn2-history-unit-b2*))
(defconst *fn2-history-unit-submit1*
  (list (list :batch *fn2-history-unit-b1* '(log-a log-b))))
(defconst *fn2-history-unit-submit2*
  (list (list :batch *fn2-history-unit-b2* '(log-c))))
(defconst *fn2-history-unit-dep-issue*
  '((:write (0 1) 1 :dependency dep-a 64)
    (:write (1 1) 1 :dependency dep-b 128)))
(defconst *fn2-history-unit-dep-done*
  '((:write-result (1 1) :done 128) (:write-result (0 1) :done 64)))
(defconst *fn2-history-unit-log-issue*
  '((:write (2 1) 1 :log log-a 4096) (:write (3 1) 1 :log log-b 4096)))
(defconst *fn2-history-unit-log-done*
  '((:write-result (3 1) :done 4096) (:write-result (2 1) :done 4096)))
(defconst *fn2-history-unit-deps*
  (append *fn2-history-unit-submit1* *fn2-history-unit-dep-issue*
          *fn2-history-unit-dep-done*))
(defconst *fn2-history-unit-writes*
  (append *fn2-history-unit-deps* *fn2-history-unit-log-issue*
          *fn2-history-unit-log-done*))
(defconst *fn2-history-unit-fence*
  (append *fn2-history-unit-writes* '((:fence (4 1) 1))))
(defconst *fn2-history-unit-durable*
  (append *fn2-history-unit-fence* '((:fence-result (4 1) :done))))
(defconst *fn2-history-unit-published*
  (append *fn2-history-unit-durable* '((:publish 1))))
(defconst *fn2-history-unit-acked*
  (append *fn2-history-unit-published* '((:ack 1))))
(defconst *fn2-history-unit-second-writes*
  (append *fn2-history-unit-submit2*
          '((:write (5 1) 2 :dependency dep-c 32)
            (:write-result (5 1) :done 32)
            (:write (6 1) 2 :log log-c 4096)
            (:write-result (6 1) :done 4096))))
; Slot two writes while slot one's fence is outstanding. Its own fence is
; withheld until the first result is harvested, and replies may reorder.
(defconst *fn2-history-unit-two*
  (append *fn2-history-unit-fence* *fn2-history-unit-second-writes*
          '((:fence-result (4 1) :done) (:publish 1)
            (:fence (7 1) 2) (:fence-result (7 1) :done)
            (:publish 2) (:ack 2) (:ack 1))))
(defconst *fn2-history-unit-late*
  (append *fn2-history-unit-fence*
          '((:timeout 1) (:fence-result (4 1) :done))))

; Positive fixtures are (name events classification recovered-history).
; These lists are independently evaluated checker units, not simulator runs.
(defconst *fn2-history-unit-positive*
  (list
   (list :explicit-fence-zero
         (append *fn2-history-unit-fence* '((:fence-result (4 1) :done 0) (:publish 1) (:ack 1) (:crash)))
         :intact *fn2-history-unit-h1*)
   (list :empty '((:crash)) :intact nil)
   (list :reordered-writes (append *fn2-history-unit-acked* '((:crash)))
         :intact *fn2-history-unit-h1*)
   (list :two-slots-replies-reorder (append *fn2-history-unit-two* '((:crash)))
         :intact *fn2-history-unit-h2*)
   (list :timeout-late-success (append *fn2-history-unit-late* '((:crash)))
         :intact *fn2-history-unit-h1*)
   (list :timeout-no-completion (append *fn2-history-unit-fence* '((:timeout 1) (:crash)))
         :intact nil)
   (list :short-write (append *fn2-history-unit-submit1* *fn2-history-unit-dep-issue*
                             '((:write-result (0 1) :short 16)
                               (:write-result (1 1) :done 128) (:crash))) :intact nil)
   (list :done-short-count (append *fn2-history-unit-submit1* *fn2-history-unit-dep-issue*
                                  '((:write-result (0 1) :done 16) (:crash))) :intact nil)
   (list :eio (append *fn2-history-unit-submit1* *fn2-history-unit-dep-issue*
                     '((:write-result (0 1) :eio 0) (:crash))) :intact nil)
   (list :enospc (append *fn2-history-unit-submit1* *fn2-history-unit-dep-issue*
                        '((:write-result (0 1) :enospc 0) (:crash))) :intact nil)
   (list :failed-fence-readable-complete
         (append *fn2-history-unit-fence* '((:fence-result (4 1) :failed) (:crash)))
         :intact *fn2-history-unit-h1*)
   (list :refused-unrelated
         (append '((:refuse (:put refused-key value))) *fn2-history-unit-acked* '((:crash)))
         :intact *fn2-history-unit-h1*)
   (list :physical-survivor
         (append *fn2-history-unit-deps* *fn2-history-unit-log-issue*
                 '((:crash) (:evidence (:survives 1)))) :intact *fn2-history-unit-h1*)
   (list :torn-tail
         (append *fn2-history-unit-submit1* '((:crash) (:evidence (:bad-tail 1))))
         :torn-tail nil)
   (list :repeated-recovery-crash
         (append *fn2-history-unit-acked* '((:crash) (:crash))) :intact *fn2-history-unit-h1*)
   (list :late-writes-after-timeout
         (append *fn2-history-unit-deps* *fn2-history-unit-log-issue*
                 '((:timeout 1)) *fn2-history-unit-log-done* '((:crash)))
         :intact *fn2-history-unit-h1*)))

; Negative action fixtures assert exact refusal codes; merely obtaining NIL
; from recovery does not establish that the action checker saw the defect.
(defconst *fn2-history-unit-negative*
  (list
   (list :nonzero-fence-count
         (append *fn2-history-unit-fence* '((:fence-result (4 1) :done 1))) :stray-fence-result)
   (list :duplicate-dependency
         '((:batch (1 0 ((:put k v)) (dep dep)) (log))) :bad-manifest)
   (list :duplicate-log
         '((:batch (1 0 ((:put k v)) (dep)) (log log))) :bad-manifest)
   (list :overlapping-role-identity
         '((:batch (1 0 ((:put k v)) (same)) (same))) :bad-manifest)
   (list :empty-log '((:batch (1 0 ((:put k v)) (dep)) ())) :bad-manifest)
   (list :duplicate-record
         '((:batch (1 0 ((:put k v) (:put k v)) (dep)) (log))) :bad-manifest)
   (list :cross-batch-identity
         (append *fn2-history-unit-submit1*
                 '((:batch (2 1 ((:put k v)) (dep-a)) (other-log)))) :bad-manifest)
   (list :wrong-predecessor '((:batch (1 7 ((:put k v)) (dep)) (log))) :log-model-refused)
   (list :unsubmitted-write '((:write op 1 :dependency dep-a 64)) :bad-write)
   (list :extra-write (append *fn2-history-unit-submit1*
                            '((:write op 1 :dependency extra 64))) :bad-write)
   (list :wrong-role (append *fn2-history-unit-submit1*
                            '((:write op 1 :log dep-a 64))) :bad-write)
   (list :zero-write (append *fn2-history-unit-submit1*
                            '((:write op 1 :dependency dep-a 0))) :bad-write)
   (list :duplicate-op (append *fn2-history-unit-submit1* *fn2-history-unit-dep-issue*
                              '((:write (0 1) 1 :dependency dep-b 128))) :bad-write)
   (list :duplicate-identity (append *fn2-history-unit-submit1* *fn2-history-unit-dep-issue*
                                   '((:write other 1 :dependency dep-a 64))) :bad-write)
   (list :log-before-dep-result
         (append *fn2-history-unit-submit1* *fn2-history-unit-dep-issue*
                 *fn2-history-unit-log-issue*) :bad-write)
   (list :log-with-missing-dep
         (append *fn2-history-unit-submit1*
                 '((:write (0 1) 1 :dependency dep-a 64)
                   (:write-result (0 1) :done 64)) *fn2-history-unit-log-issue*) :bad-write)
   (list :unknown-completion '((:write-result stray :done 64)) :stray-write-result)
   (list :wrong-generation
         (append *fn2-history-unit-submit1* *fn2-history-unit-dep-issue*
                 '((:write-result (0 2) :done 64))) :stray-write-result)
   (list :duplicate-completion
         (append *fn2-history-unit-deps* '((:write-result (0 1) :done 64))) :stray-write-result)
   (list :impossible-count
         (append *fn2-history-unit-submit1* *fn2-history-unit-dep-issue*
                 '((:write-result (0 1) :done 65))) :stray-write-result)
   (list :write-completion-for-fence
         (append *fn2-history-unit-fence* '((:write-result (4 1) :done 0))) :stray-write-result)
   (list :fence-completion-for-write
         (append *fn2-history-unit-submit1* *fn2-history-unit-dep-issue*
                 '((:fence-result (0 1) :done))) :stray-fence-result)
   (list :fence-before-log-result
         (append *fn2-history-unit-deps* *fn2-history-unit-log-issue*
                 '((:fence f 1))) :bad-fence)
   (list :second-domain-fence
         (append *fn2-history-unit-fence* *fn2-history-unit-second-writes*
                 '((:fence (7 1) 2))) :bad-fence)
   (list :duplicate-fence-result
         (append *fn2-history-unit-durable* '((:fence-result (4 1) :done))) :stray-fence-result)
   (list :publish-before-fence-result
         (append *fn2-history-unit-fence* '((:publish 1))) :unsafe-visibility)
   (list :ack-before-publish
         (append *fn2-history-unit-durable* '((:ack 1))) :unsafe-visibility)
   (list :duplicate-publish
         (append *fn2-history-unit-published* '((:publish 1))) :unsafe-visibility)
   (list :duplicate-ack
         (append *fn2-history-unit-acked* '((:ack 1))) :unsafe-visibility)
   (list :late-success-does-not-resolve
         (append *fn2-history-unit-late* '((:publish 1))) :unsafe-visibility)
   (list :failed-fence-no-publication
         (append *fn2-history-unit-fence* '((:fence-result (4 1) :failed) (:publish 1)))
         :unsafe-visibility)
   (list :short-write-blocks-log
         (append *fn2-history-unit-submit1* *fn2-history-unit-dep-issue*
                 '((:write-result (0 1) :short 16)) *fn2-history-unit-log-issue*) :bad-write)
   (list :domain-uncertainty-blocks-other-writes
         (append *fn2-history-unit-fence* '((:timeout 1)) *fn2-history-unit-second-writes*)
         :bad-write)
   (list :domain-uncertainty-blocks-other-fence
         (append *fn2-history-unit-fence* *fn2-history-unit-second-writes*
                 '((:timeout 1) (:fence-result (4 1) :done) (:fence (7 1) 2))) :bad-fence)
   (list :cannot-pass-unpublished-predecessor
         (append *fn2-history-unit-durable* *fn2-history-unit-second-writes*
                 '((:fence (7 1) 2) (:fence-result (7 1) :done) (:publish 2))) :unsafe-visibility)
   (list :refuse-member-after-submit
         (append *fn2-history-unit-submit1* '((:refuse (:put key-a value-a)))) :refused-member)
   (list :refused-member-before-submit
         (append '((:refuse (:put key-a value-a))) *fn2-history-unit-submit1*) :bad-manifest)
   (list :postcrash-completion
         (append *fn2-history-unit-fence* '((:crash) (:fence-result (4 1) :done))) :after-crash)
   (list :precrash-physical-evidence
         (append *fn2-history-unit-submit1* '((:evidence (:survives 1)))) :bad-evidence)
   (list :forged-fence-evidence
         (append *fn2-history-unit-writes* '((:crash) (:evidence (:fence-ok 1)))) :bad-evidence)
   (list :forged-complete-evidence
         (append *fn2-history-unit-submit1*
                 '((:crash) (:evidence (:batch-writes-complete 1 (dep-a dep-b))))) :bad-evidence)
   (list :direct-model-event '((:fence-ok 1)) :unknown-event)
   (list :improper-event-list '((:crash) . tail) :malformed)))

; Recovery negatives exercise the exact B1 verdict, after valid translation.
(defconst *fn2-history-unit-recovery-negative*
  (list
   (list :lost-ack (append *fn2-history-unit-acked* '((:crash))) :intact nil)
   (list :incomplete-not-survivor
         (append *fn2-history-unit-deps* *fn2-history-unit-log-issue* '((:crash)))
         :intact *fn2-history-unit-h1*)
   (list :wrong-recovered-record
         (append *fn2-history-unit-acked* '((:crash))) :intact
         '((1 0 ((:put forged-key value)) (dep-a dep-b))))
   (list :no-crash *fn2-history-unit-acked* :intact *fn2-history-unit-h1*)
   (list :wrong-classification
         (append *fn2-history-unit-acked* '((:crash))) :torn-tail *fn2-history-unit-h1*)))

(fn2-cm-defreaders fn2-history-action-fixture-name
                   fn2-history-action-fixture-events
                   fn2-history-action-fixture-code)
(fn2-cm-defreaders fn2-history-recovery-fixture-name
                   fn2-history-recovery-fixture-events
                   fn2-history-recovery-fixture-classification
                   fn2-history-recovery-fixture-history)

(defun fn2-history-unit-action-count (fixtures)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp fixtures)
      (mv-let (passed total) (fn2-history-unit-action-count (cdr fixtures))
        (mv-let (code trace) (fn2-history-translate (fn2-history-action-fixture-events (car fixtures)))
          (declare (ignore trace))
          (mv (+ passed (if (equal code (fn2-history-action-fixture-code (car fixtures))) 1 0)) (+ 1 total))))
    (mv 0 0)))

(defun fn2-history-unit-recovery-count (fixtures expected)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp fixtures)
      (mv-let (passed total) (fn2-history-unit-recovery-count (cdr fixtures) expected)
        (let* ((fixture (car fixtures)) (events (fn2-history-recovery-fixture-events fixture))
               (verdict (fn2-check-history events *fn2-history-unit-profile*
                                           (fn2-history-recovery-fixture-classification fixture) (fn2-history-recovery-fixture-history fixture))))
          (mv-let (code trace) (fn2-history-translate events)
            (declare (ignore trace))
            (mv (+ passed (if (and (eq code :ok) (iff verdict expected)) 1 0)) (+ 1 total)))))
    (mv 0 0)))

(assert-event
 (mv-let (passed total) (fn2-history-unit-recovery-count *fn2-history-unit-positive* t)
   (equal passed total)))
(assert-event
 (mv-let (passed total) (fn2-history-unit-action-count *fn2-history-unit-negative*)
   (equal passed total)))
(assert-event
 (mv-let (passed total) (fn2-history-unit-recovery-count *fn2-history-unit-recovery-negative* nil)
   (equal passed total)))
; Translation emits exactly one completed/fenced/ack event, preserving the
; manifest despite reordered completion arrival. The effect is not inferred
; merely from publication or a successful recovered-history verdict.
(assert-event
 (mv-let (code trace) (fn2-history-translate (append *fn2-history-unit-acked* '((:crash))))
   (and (eq code :ok)
        (equal trace (list (list :submit-batch *fn2-history-unit-b1*)
                           '(:batch-writes-complete 1 (dep-a dep-b))
                           '(:fence-ok 1) '(:acknowledge 1) '(:crash))))))
(assert-event
 (mv-let (code trace) (fn2-history-translate (append *fn2-history-unit-late* '((:crash))))
   (and (eq code :ok)
        (equal trace (list (list :submit-batch *fn2-history-unit-b1*)
                           '(:batch-writes-complete 1 (dep-a dep-b))
                           '(:fence-ok 1) '(:crash))))))

; The alternate contract is successful dependency preflush, then ALL log
; writes FUA; a successful preflush alone has no batch durability effect.
(defconst *fn2-history-unit-fua-submit*
  (list (list :batch *fn2-history-unit-b1* '(log-a log-b) :preflush-fua)))
(defconst *fn2-history-unit-fua-deps*
  (append *fn2-history-unit-fua-submit* *fn2-history-unit-dep-issue*
          *fn2-history-unit-dep-done*))
(defconst *fn2-history-unit-preflush*
  (append *fn2-history-unit-fua-deps* '((:preflush (4 1) 1))))
(defconst *fn2-history-unit-preflushed*
  (append *fn2-history-unit-preflush* '((:fence-result (4 1) :done))))
(defconst *fn2-history-unit-fua-issue*
  '((:write (2 1) 1 :log log-a 4096 1) (:write (3 1) 1 :log log-b 4096 1)))
(defconst *fn2-history-unit-fua-durable*
  (append *fn2-history-unit-preflushed* *fn2-history-unit-fua-issue*
          *fn2-history-unit-log-done*))
(defconst *fn2-history-unit-fua-acked*
  (append *fn2-history-unit-fua-durable* '((:publish 1) (:ack 1))))
(defconst *fn2-history-unit-fua-late*
  (append *fn2-history-unit-preflushed* *fn2-history-unit-fua-issue*
          '((:timeout 1)) *fn2-history-unit-log-done*))
(defconst *fn2-history-unit-fua-positive*
  (list
   (list :fua-reordered-results (append *fn2-history-unit-fua-acked* '((:crash)))
         :intact *fn2-history-unit-h1*)
   (list :preflush-alone (append *fn2-history-unit-preflushed* '((:crash))) :intact nil)
   (list :preflush-timeout-late
         (append *fn2-history-unit-preflush* '((:timeout 1) (:fence-result (4 1) :done) (:crash)))
         :intact nil)
   (list :fua-timeout-late (append *fn2-history-unit-fua-late* '((:crash)))
         :intact *fn2-history-unit-h1*)
   (list :preflush-failed
         (append *fn2-history-unit-preflush* '((:fence-result (4 1) :failed) (:crash))) :intact nil)
   (list :fua-short
         (append *fn2-history-unit-preflushed* *fn2-history-unit-fua-issue*
                 '((:write-result (2 1) :short 512) (:write-result (3 1) :done 4096) (:crash)))
         :intact nil)))
(defconst *fn2-history-unit-fua-negative*
  (list
   (list :nonzero-preflush-count
         (append *fn2-history-unit-preflush* '((:fence-result (4 1) :done 1))) :stray-fence-result)
   (list :preflush-before-dependencies
         (append *fn2-history-unit-fua-submit* *fn2-history-unit-dep-issue*
                 '((:preflush (4 1) 1))) :bad-fence)
   (list :fua-log-before-preflush
         (append *fn2-history-unit-fua-deps* *fn2-history-unit-fua-issue*) :bad-write)
   (list :fua-log-before-preflush-result
         (append *fn2-history-unit-preflush* *fn2-history-unit-fua-issue*) :bad-write)
   (list :fua-log-missing-fua
         (append *fn2-history-unit-preflushed* *fn2-history-unit-log-issue*) :bad-write)
   (list :fua-log-explicit-zero
         (append *fn2-history-unit-preflushed* '((:write (2 1) 1 :log log-a 4096 0))) :bad-write)
   (list :invalid-fua-bit
         (append *fn2-history-unit-preflushed* '((:write (2 1) 1 :log log-a 4096 2))) :bad-write)
   (list :preflush-not-publishable
         (append *fn2-history-unit-preflushed* '((:publish 1))) :unsafe-visibility)
   (list :fua-missing-one-completion
         (append *fn2-history-unit-preflushed* *fn2-history-unit-fua-issue*
                 '((:write-result (3 1) :done 4096) (:publish 1))) :unsafe-visibility)
   (list :fua-short-not-publishable
         (append *fn2-history-unit-preflushed* *fn2-history-unit-fua-issue*
                 '((:write-result (2 1) :done 512) (:write-result (3 1) :done 4096) (:publish 1)))
         :unsafe-visibility)
   (list :late-fua-still-uncertain
         (append *fn2-history-unit-fua-late* '((:publish 1))) :unsafe-visibility)
   (list :late-preflush-still-uncertain
         (append *fn2-history-unit-preflush* '((:timeout 1) (:fence-result (4 1) :done))
                 *fn2-history-unit-fua-issue*) :bad-write)
   (list :failed-preflush-blocks-log
         (append *fn2-history-unit-preflush* '((:fence-result (4 1) :failed))
                 *fn2-history-unit-fua-issue*) :bad-write)
   (list :baseline-cannot-preflush
         (append *fn2-history-unit-deps* '((:preflush (4 1) 1))) :bad-fence)
   (list :fua-cannot-baseline-fence
         (append *fn2-history-unit-fua-deps* '((:fence (4 1) 1))) :bad-fence)
   (list :preflush-token-is-not-write
         (append *fn2-history-unit-preflush* '((:write-result (4 1) :done 0))) :stray-write-result)
   (list :preflush-duplicate-result
         (append *fn2-history-unit-preflushed* '((:fence-result (4 1) :done))) :stray-fence-result)
   (list :mixed-domain-fence
         (append *fn2-history-unit-preflush* *fn2-history-unit-second-writes*
                 '((:fence (7 1) 2))) :bad-fence)
   (list :timeout-keeps-domain-fence
         (append *fn2-history-unit-preflush* *fn2-history-unit-second-writes*
                 '((:timeout 1) (:fence (7 1) 2))) :bad-fence)))
(defconst *fn2-history-unit-fua-recovery-negative*
  (list
   (list :lost-fua-ack (append *fn2-history-unit-fua-acked* '((:crash))) :intact nil)
   (list :preflush-not-complete
         (append *fn2-history-unit-preflushed* '((:crash))) :intact *fn2-history-unit-h1*)))
(assert-event
 (mv-let (passed total) (fn2-history-unit-recovery-count *fn2-history-unit-fua-positive* t)
   (equal passed total)))
(assert-event
 (mv-let (passed total) (fn2-history-unit-action-count *fn2-history-unit-fua-negative*)
   (equal passed total)))
(assert-event
 (mv-let (passed total) (fn2-history-unit-recovery-count *fn2-history-unit-fua-recovery-negative* nil)
   (equal passed total)))
(assert-event
 (mv-let (code trace) (fn2-history-translate *fn2-history-unit-preflushed*)
   (and (eq code :ok) (equal trace (list (list :submit-batch *fn2-history-unit-b1*))))))
(assert-event
 (mv-let (code trace) (fn2-history-translate *fn2-history-unit-fua-acked*)
   (and (eq code :ok)
        (equal trace (list (list :submit-batch *fn2-history-unit-b1*)
                           '(:batch-writes-complete 1 (dep-a dep-b))
                           '(:fence-ok 1) '(:acknowledge 1))))))

; Actual admission identities are separate from canonical persisted records.
(defconst *fn2-history-unit-request* '(:request 1 ((:operation 0 7)) :baseline))
(defconst *fn2-history-unit-bound-batch*
 (list :batch *fn2-history-unit-b1* '(log-a log-b) :baseline '((:operation 0 7))))
(defconst *fn2-history-unit-request-positive*
 (list
  (list :admitted (append (list *fn2-history-unit-request* *fn2-history-unit-bound-batch*)
                          (cdr *fn2-history-unit-acked*) '((:crash))) :intact *fn2-history-unit-h1*)
  (list :request-death (list *fn2-history-unit-request* '(:crash)) :intact nil)
  (list :terminal-refusal '((:refuse (:operation 0 99)) (:crash)) :intact nil)))
(defconst *fn2-history-unit-request-negative*
 (list
  (list :unrequested (list *fn2-history-unit-bound-batch*) :bad-manifest)
  (list :wrong-identity (list *fn2-history-unit-request*
         (update-nth 4 '((:operation 0 8)) *fn2-history-unit-bound-batch*)) :bad-manifest)
  (list :wrong-mode (list *fn2-history-unit-request*
         (update-nth 3 :preflush-fua *fn2-history-unit-bound-batch*)) :bad-manifest)
  (list :duplicate-request (list *fn2-history-unit-request* *fn2-history-unit-request*) :bad-request)
  (list :reuse-identity (list *fn2-history-unit-request*
         '(:request 2 ((:operation 0 7)) :baseline)) :bad-request)
  (list :refused-then-requested (list '(:refuse (:operation 0 7)) *fn2-history-unit-request*) :bad-request)
  (list :requested-then-refused (list *fn2-history-unit-request* '(:refuse (:operation 0 7))) :refused-member)
  (list :erase-identity (append (list *fn2-history-unit-request*) *fn2-history-unit-submit1*) :bad-manifest)))
(assert-event
 (mv-let (passed total) (fn2-history-unit-recovery-count *fn2-history-unit-request-positive* t)
  (equal passed total)))
(assert-event
 (mv-let (passed total) (fn2-history-unit-action-count *fn2-history-unit-request-negative*)
  (equal passed total)))
