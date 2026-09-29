(in-package "ACL2")
(include-book "../../books/anchor-replace")
(include-book "std/testing/assert-bang" :dir :system)

(defconst *fn-anchor-rp-publish-events*
  '((:stage-result :ok)
    :replace-issued
    (:replace-result :ok)
    (:directory-result :ok)))

(assert! (equal (fn-anchor-rp-trace (fn-anchor-rp-start)
                                    *fn-anchor-rp-publish-events*)
                :durable))
(assert! (fn-anchor-rp-has-directory-okp *fn-anchor-rp-publish-events*))

; Post-syscall death is represented before the host enters rename: neither
; issued nor returned-success-before-directory is durable.
(assert! (equal (fn-anchor-rp-trace
                 (fn-anchor-rp-start)
                 '((:stage-result :ok) :replace-issued))
                :replace-issued))
(assert! (equal (fn-anchor-rp-outcome :replace-issued) :pending))
(assert! (equal (fn-anchor-rp-trace
                 (fn-anchor-rp-start)
                 '((:stage-result :ok) :replace-issued
                   (:replace-result :ok)))
                :replace-visible))
(assert! (equal (fn-anchor-rp-outcome :replace-visible) :pending))
(assert! (equal (fn-anchor-rp-trace
                 (fn-anchor-rp-start)
                 '((:stage-result :ok) :replace-issued
                   (:replace-result :uncertain)))
                :fenced))
(assert! (equal (fn-anchor-rp-outcome :fenced) :uncertain))

; Reachable non-degenerate witnesses for the two host-called step keystones.
(assert! (equal (fn-anchor-rp-step
                 :replace-visible '(:directory-result :ok))
                :durable))
(assert! (not (equal (fn-anchor-rp-step
                      :replace-issued '(:directory-result :ok))
                     :durable)))
; Dropping the "not already durable" hypothesis makes the keystone's
; conclusion false: terminal phases deliberately self-loop on unrelated input.
(assert! (and (equal (fn-anchor-rp-step :durable :unrelated) :durable)
              (not (equal :durable :replace-visible))))

; A present final name is not decoded as held until both recovery barriers.
(assert! (equal (fn-anchor-rp-action
                 (fn-anchor-rp-recover-start t))
                :recovery-file-barrier))
(assert! (equal (fn-anchor-rp-trace
                 (fn-anchor-rp-recover-start t)
                 '((:recovery-file-result :ok)))
                :recover-directory))
(assert! (equal (fn-anchor-rp-trace
                 (fn-anchor-rp-recover-start t)
                 '((:recovery-file-result :ok)
                   (:recovery-directory-result :ok)))
                :recovered))
(assert! (equal (fn-anchor-rp-step
                 :recover-directory '(:recovery-directory-result :ok))
                :recovered))
(assert! (not (equal (fn-anchor-rp-step
                      :recover-file '(:recovery-directory-result :ok))
                     :recovered)))
(assert! (and (equal (fn-anchor-rp-step :recovered :unrelated) :recovered)
              (not (equal :recovered :recover-directory))))
(assert! (equal (fn-anchor-rp-trace
                 (fn-anchor-rp-recover-start t)
                 '((:recovery-file-result :uncertain)))
                :fenced))
(assert! (equal (fn-anchor-rp-trace
                 (fn-anchor-rp-recover-start nil)
                 '((:recovery-directory-result :ok)))
                :recovered))

; Teeth for fn-anchor-rp-outcome-is-terminal-only-after-the-directory-barrier
; (PRF-955).  Reachable positive witness: the visible replace with its
; directory barrier :ok is :durable.  Hypothesis removal: the same barrier
; from the issued phase, and a failed barrier from the visible phase, are
; not :durable (pending; uncertain when fenced).
(assert! (equal (fn-anchor-rp-outcome
                 (fn-anchor-rp-step :replace-visible (list :directory-result :ok)))
                :durable))
(assert! (not (equal (fn-anchor-rp-outcome
                      (fn-anchor-rp-step :replace-issued (list :directory-result :ok)))
                     :durable)))
(assert! (not (equal (fn-anchor-rp-outcome
                      (fn-anchor-rp-step :replace-visible (list :directory-result :fail)))
                     :durable)))
(assert! (equal (fn-anchor-rp-outcome
                 (fn-anchor-rp-step :recover-directory
                                    (list :recovery-directory-result :ok)))
                :recovered))
