; Executable live-node/file-kernel composition and spoofed-completion checks.
(in-package "ACL2")
(include-book "../../books/store-node-invariants")
(include-book "../../books/codec-attach")

(defconst *sn-groups* '("fn.letters" "fn.test"))
(defconst *sn-record*
  (fn-record-make 0 0 0 "<sn@example>" '(65 66) *sn-groups*
                  "sn-pin" "sn-content" "sn-release" 2 841000000))
(defun fn-sn-test-reserve (s)
  (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier nil)
                                :frontier-file :ok)
                      :frontier-replace :ok)
            :frontier-directory :ok))
(defun fn-sn-test-publish (s)
  (fn-sn-io (fn-sn-io (fn-sn-io s :record-file :ok)
                      :record-link :ok)
            :record-directory :ok))
(defun fn-sn-test-barriers (s n)
  (if (zp n) s
    (fn-sn-test-barriers (fn-sn-io s :recovery-barrier :ok) (1- n))))
(defconst *sn-initial* (fn-sn-initial *sn-groups* 10))
(defconst *sn-reserved* (fn-sn-test-reserve *sn-initial*))
(defconst *sn-prepared* (fn-sn-prepare *sn-reserved* *sn-record*))
(assert-event (fn-sn-statep *sn-prepared*))
(assert-event (equal (fn-sf-phase (fn-sn-files *sn-prepared*)) :record-staged))
(assert-event (fn-sn-record-bindsp (fn-sn-node *sn-prepared*) *sn-record*))
(assert-event (not (fn-state-articles (fn-node-acceptance (fn-sn-node *sn-prepared*)))))
(assert-event (not (fn-retain-pins (fn-node-retention (fn-sn-node *sn-prepared*)))))
(assert-event (equal (fn-sn-finish *sn-prepared*) *sn-prepared*))
; Host words cannot bypass the real completion operation.
(assert-event (equal (fn-sn-io *sn-prepared* :core-completion :matching) *sn-prepared*))
(assert-event (equal (fn-sn-io *sn-prepared* :emit-success :matching) *sn-prepared*))

(defconst *sn-completing* (fn-sn-test-publish *sn-prepared*))
(assert-event (equal (fn-sf-phase (fn-sn-files *sn-completing*)) :completing))
(assert-event (not (fn-sf-successes (fn-sn-files *sn-completing*))))
(defconst *sn-finished* (fn-sn-finish *sn-completing*))
(assert-event (fn-sn-statep *sn-finished*))
(assert-event (equal (fn-sf-successes (fn-sn-files *sn-finished*)) '((0 . 0))))
(assert-event (fn-sn-committed-recordp (fn-sn-node *sn-finished*) *sn-record*))
(assert-event (equal (fn-sn-node *sn-finished*)
                     (fn-sf-replay-node *sn-groups* 10 (list *sn-record*) 1)))
(assert-event (equal (fn-sn-finish *sn-finished*) *sn-finished*))

; A real but different pending node with the same sequence/txid/generation is
; insufficient: payload, groups, archive ID, subject, evidence and charge bind.
(defun fn-sn-test-mismatched-pending (payload groups id subject evidence charge)
  (fn-sn-update *sn-completing* (fn-sn-files *sn-completing*)
    (fn-node-prepare (fn-sn-node *sn-initial*) 0 "<sn@example>" payload groups
                     id subject evidence charge 841000000)))
(assert-event (let ((s (fn-sn-test-mismatched-pending
                        '(99) *sn-groups* "sn-pin" "sn-content" "sn-release" 2)))
                (and (fn-sn-statep s) (equal (fn-sn-finish s) s))))
(assert-event (let ((s (fn-sn-test-mismatched-pending
                        '(65 66) '("fn.letters") "sn-pin" "sn-content" "sn-release" 2)))
                (and (fn-sn-statep s) (equal (fn-sn-finish s) s))))
(assert-event (let ((s (fn-sn-test-mismatched-pending
                        '(65 66) *sn-groups* "other-pin" "sn-content" "sn-release" 2)))
                (and (fn-sn-statep s) (equal (fn-sn-finish s) s))))
(assert-event (let ((s (fn-sn-test-mismatched-pending
                        '(65 66) *sn-groups* "sn-pin" "other-content" "sn-release" 2)))
                (and (fn-sn-statep s) (equal (fn-sn-finish s) s))))
(assert-event (let ((s (fn-sn-test-mismatched-pending
                        '(65 66) *sn-groups* "sn-pin" "sn-content" "other-release" 2)))
                (and (fn-sn-statep s) (equal (fn-sn-finish s) s))))
(assert-event (let ((s (fn-sn-test-mismatched-pending
                        '(65 66) *sn-groups* "sn-pin" "sn-content" "sn-release" 3)))
                (and (fn-sn-statep s) (equal (fn-sn-finish s) s))))

; Acknowledged content survives crash/replay and all five recovery barriers.
(defconst *sn-recovered*
  (fn-sn-test-barriers (fn-sn-recover (fn-sn-crash *sn-finished* :old :absent)) 5))
(assert-event (fn-sn-statep *sn-recovered*))
(assert-event (equal (fn-sf-phase (fn-sn-files *sn-recovered*)) :ready))
(assert-event (equal (fn-sn-node *sn-recovered*) (fn-sn-node *sn-finished*)))
(assert-event (equal (fn-sf-successes (fn-sn-files *sn-recovered*)) '((0 . 0))))

; An uncertain link can recover the exact article without inventing an ACK;
; its absent outcome burns the allocated txid and leaves no partial article.
(defconst *sn-link-error*
  (fn-sn-io (fn-sn-io *sn-prepared* :record-file :ok) :record-link :error))
(defconst *sn-present*
  (fn-sn-recover (fn-sn-crash *sn-link-error* :old :present)))
(defconst *sn-absent*
  (fn-sn-recover (fn-sn-crash *sn-link-error* :old :absent)))

; Process death after os.link returned but before the link result was
; observed (the final-link cut) leaves the composition in :record-data-durable
; with the same two outcomes; both replay to the same nodes as the fenced
; link above, and neither invents an acknowledgement.
(defconst *sn-data-durable* (fn-sn-io *sn-prepared* :record-file :ok))
(assert-event (equal (fn-sf-phase (fn-sn-files *sn-data-durable*)) :record-data-durable))
(assert-event (equal (fn-sn-node (fn-sn-recover (fn-sn-crash *sn-data-durable* :old :present)))
                     (fn-sn-node *sn-present*)))
(assert-event (equal (fn-sn-node (fn-sn-recover (fn-sn-crash *sn-data-durable* :old :absent)))
                     (fn-sn-node *sn-absent*)))
(assert-event (not (fn-sf-successes
                    (fn-sn-files (fn-sn-recover (fn-sn-crash *sn-data-durable* :old :present))))))
; Death after the record file barrier returned but before it was observed
; (the staged-data-barrier cut) is in :record-staged: no link was issued, so
; the present choice selects nothing.
(assert-event (equal (fn-sf-records (fn-sn-files (fn-sn-crash *sn-prepared* :old :present)))
                     nil))
(assert-event (fn-sn-committed-recordp (fn-sn-node *sn-present*) *sn-record*))
(assert-event (not (fn-sf-successes (fn-sn-files *sn-present*))))
(assert-event (not (fn-state-articles (fn-node-acceptance (fn-sn-node *sn-absent*)))))
(assert-event (equal (fn-state-next-txid (fn-node-acceptance (fn-sn-node *sn-absent*))) 1))
(assert-event (equal (fn-sn-finish *sn-present*) *sn-present*))
; unreachable-in-composition: fn-sn-fence-node/fn-sn-resolve-node have no host
; caller; these two checks document the in-process correspondence only.
(assert-event (equal (fn-sn-node *sn-present*)
                     (fn-sn-resolve-node
                      (fn-sn-fence-node (fn-sn-node *sn-prepared*) *sn-record*)
                      *sn-record* t)))
(assert-event (equal (fn-sn-node *sn-absent*)
                     (fn-sn-resolve-node
                      (fn-sn-fence-node (fn-sn-node *sn-prepared*) *sn-record*)
                      *sn-record* nil)))
