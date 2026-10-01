; SOURCE MODEL: synthetic ledger funding and constructed RC, actual same local stobjs.
; No native copy, serialized STATE, constructor envelope or terminal authority.
(in-package "ACL2")
(include-book "../../books/receiver-output-association")
(include-book "../../host/receiver-capacity-current-host")

; MODEL funding/constructed RC only. Actual functions and same local stobjs.
; No serialized STATE producer, native copy, constructor allowance or terminal receipt.
(defun fn-rxo-chain-fill-v2 (fn-rx-provider)
 (declare (xargs :stobjs fn-rx-provider))
 (stobj-let ((fn-octets-rx (fn-rxp-octets fn-rx-provider)))
  (fn-octets-rx) (fn-octets-rx-from-list '(81 82) fn-octets-rx) fn-rx-provider))

(defun fn-rxo-chain-run-v2 (fn-rx-provider fn-receiver-turn fn-rx-capacity-current fn-page-read-pool fn-output-storage)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-rx-capacity-current fn-page-read-pool fn-output-storage) :verify-guards nil))
 (let* ((fn-page-read-pool (fn-owner-page-read-keep-ledger
 (fn-prl-build '(1000000 0 0 0 100) '(0 0 0 0 0) 7 '((:borrowed . :bindings)) '(1000 0 0 0 0)) fn-page-read-pool))
 (fn-page-read-pool (update-fn-prp-mode :served fn-page-read-pool))
 (fn-page-read-pool (update-fn-prp-alloc-mode :active fn-page-read-pool))) (mv-let (reserve capToken fn-rx-capacity-current fn-page-read-pool)
 (fn-owner-rx-current-reserve '(8192 0 0 0 1) fn-rx-capacity-current fn-page-read-pool)
 (mv-let (allocate fn-rx-capacity-current fn-page-read-pool)
 (fn-owner-rx-current-allocation-begin capToken fn-rx-capacity-current fn-page-read-pool)
 (mv-let (install fn-rx-provider fn-receiver-turn fn-rx-capacity-current fn-page-read-pool)
 (fn-owner-rx-current-install capToken fn-rx-provider fn-receiver-turn fn-rx-capacity-current fn-page-read-pool)
 (mv-let (begin ticket fn-receiver-turn fn-page-read-pool)
 (fn-owner-rx-turn-start capToken '(1024 0 0 0 1) fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (mv-let (next start end left fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (fn-owner-rx-turn-copy-next ticket 2 nil 10 fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (let ((fn-rx-provider (fn-rxo-chain-fill-v2 fn-rx-provider)))
 (mv-let (ack fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (fn-owner-rx-turn-copy-ack ticket start end :copied fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (mv-let (acquire fn-receiver-turn fn-page-read-pool)
 (fn-owner-rx-turn-parser-acquire ticket '(:model-preOC) '(:model-wire) fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (mv-let (stage fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (fn-owner-rx-turn-parser-stage ticket '(:constructed-model-RC) fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (mv-let (finish episode fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (fn-owner-rx-turn-parser-finish ticket '(:model-wire-after) '(:served-step nil t nil nil 2 nil nil) fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (mv-let (output token fn-receiver-turn fn-page-read-pool fn-output-storage)
 (fn-rxo-reserve-initial-current episode '(256 0 0 0 1) fn-rx-provider fn-receiver-turn fn-page-read-pool fn-output-storage)
 (let ((ledger (fn-owner-page-read-ledger fn-page-read-pool))
             (bundle (fn-rxt-output-bundle fn-receiver-turn)))
 (mv-let (busy busyToken fn-receiver-turn fn-page-read-pool fn-output-storage)
  (fn-rxo-reserve-initial-current episode '(256 0 0 0 1) fn-rx-provider fn-receiver-turn fn-page-read-pool fn-output-storage)
  (mv (list reserve allocate install begin next ack acquire stage finish output busy
       ticket episode token start end left (fn-rxp-capacity fn-rx-provider)
       (fn-rxt-phase fn-receiver-turn) (fn-ros-phase fn-output-storage)
       (equal (fn-prl-nth 3 bundle) (fn-ros-job fn-output-storage))
       (equal ledger (fn-owner-page-read-ledger fn-page-read-pool))
       (equal bundle (fn-rxt-output-bundle fn-receiver-turn)) busyToken ledger
       (fn-prl-nth 7 (fn-rxt-job fn-receiver-turn))) fn-rx-provider fn-receiver-turn fn-rx-capacity-current fn-page-read-pool fn-output-storage))))))))))))))))

(defun fn-rxo-chain-local-v2 () (declare (xargs :verify-guards nil)) (with-local-stobj fn-rx-provider
 (mv-let (answer fn-rx-provider) (with-local-stobj fn-receiver-turn
 (mv-let (answer fn-rx-provider fn-receiver-turn) (with-local-stobj fn-rx-capacity-current
 (mv-let (answer fn-rx-provider fn-receiver-turn fn-rx-capacity-current) (with-local-stobj fn-page-read-pool
 (mv-let (answer fn-rx-provider fn-receiver-turn fn-rx-capacity-current fn-page-read-pool) (with-local-stobj fn-output-storage
 (mv-let (answer fn-rx-provider fn-receiver-turn fn-rx-capacity-current fn-page-read-pool fn-output-storage) (fn-rxo-chain-run-v2 fn-rx-provider fn-receiver-turn fn-rx-capacity-current fn-page-read-pool fn-output-storage)
 (mv answer fn-rx-provider fn-receiver-turn fn-rx-capacity-current fn-page-read-pool)))
 (mv answer fn-rx-provider fn-receiver-turn fn-rx-capacity-current)))
 (mv answer fn-rx-provider fn-receiver-turn)))
 (mv answer fn-rx-provider)))
 answer)))


(assert-event
 (let ((a (fn-rxo-chain-local-v2)))
  (and
   (equal (take 11 a) '(:admitted :allocate :installed :admitted :receive-copy
       :receive-recorded :parser-acquired :parser-staged :response-recorded
       :output-reserved :output-busy))
   (equal (fn-prl-nth 11 a) '(:receiver-turn 8))
   (equal (fn-prl-nth 12 a) '(:receiver-response (:receiver-turn 8) 1))
   (equal (fn-prl-nth 13 a)
     '(:reader-output-window (:receiver-response (:receiver-turn 8) 1) 0 9 :fn-output-storage))
   (equal (fn-prl-nth 14 a) 0) (equal (fn-prl-nth 15 a) 2)
   (equal (fn-prl-nth 16 a) 8) (null (fn-prl-nth 17 a))
   (eq (fn-prl-nth 18 a) :response-owned) (eq (fn-prl-nth 19 a) :reserved)
   (eq (fn-prl-nth 20 a) t) (eq (fn-prl-nth 21 a) t)
   (eq (fn-prl-nth 22 a) t) (null (fn-prl-nth 23 a))
   (equal (fn-prl-nth 24 a)
    '((1000000 0 0 0 100) (1280 0 0 0 3) 10 ((:borrowed . :bindings)) (9192 0 0 0 0)))
   (equal (fn-prl-nth 25 a) '(:constructed-model-RC)))))
; MODEL seed and actual same-state transitions; no native/factory/terminal credit.
(defun fn-rxo-current-model-run (fn-rx-provider fn-receiver-turn fn-rx-capacity-current fn-page-read-pool fn-output-storage) (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-rx-capacity-current fn-page-read-pool fn-output-storage) :verify-guards nil)) (mv-let (chain fn-rx-provider fn-receiver-turn fn-rx-capacity-current fn-page-read-pool fn-output-storage) (fn-rxo-chain-run-v2 fn-rx-provider fn-receiver-turn fn-rx-capacity-current fn-page-read-pool fn-output-storage)
 (let* ((token (fn-prl-nth 13 chain))
        (bundle (fn-rxt-output-bundle fn-receiver-turn))
        (job (fn-ros-job fn-output-storage))
        (ledger (fn-owner-page-read-ledger fn-page-read-pool)))
  (mv-let (foreign obs fn-receiver-turn fn-page-read-pool fn-output-storage)
   (fn-rxo-paired-current-step '(:reader-output-window (:receiver-response (:receiver-turn 8) 2) 0 9 :fn-output-storage)
      :prepare nil 0 fn-rx-provider fn-receiver-turn fn-page-read-pool fn-output-storage)
   (declare (ignore obs))
   (let ((foreign-unchanged (and (equal bundle (fn-rxt-output-bundle fn-receiver-turn))
                                 (equal job (fn-ros-job fn-output-storage))
                                 (equal ledger (fn-owner-page-read-ledger fn-page-read-pool)))))
    (mv-let (prepare obs fn-receiver-turn fn-page-read-pool fn-output-storage)
     (fn-rxo-paired-current-step token :prepare nil 0 fn-rx-provider fn-receiver-turn fn-page-read-pool fn-output-storage)
     (declare (ignore obs))
     (let* ((nextbundle (fn-rxt-output-bundle fn-receiver-turn))
            (nextjob (fn-ros-job fn-output-storage))
            (nextledger (fn-owner-page-read-ledger fn-page-read-pool)))
      (mv-let (repeat obs fn-receiver-turn fn-page-read-pool fn-output-storage)
       (fn-rxo-paired-current-step token :prepare nil 0 fn-rx-provider fn-receiver-turn fn-page-read-pool fn-output-storage)
       (declare (ignore obs))
       (mv (list (fn-prl-nth 9 chain) foreign foreign-unchanged prepare repeat
             (fn-ros-phase fn-output-storage) (fn-prl-nth 3 (fn-ros-job fn-output-storage))
             (equal (fn-prl-nth 3 nextbundle) nextjob)
             (equal (fn-prl-nth 1 bundle) (fn-prl-nth 1 nextbundle))
             (equal ledger nextledger)
             (and (equal nextbundle (fn-rxt-output-bundle fn-receiver-turn))
                  (equal nextjob (fn-ros-job fn-output-storage))
                  (equal nextledger (fn-owner-page-read-ledger fn-page-read-pool)))
             (fn-rxp-capacity fn-rx-provider)
             (fn-ros-local-receipt fn-output-storage)) fn-rx-provider fn-receiver-turn fn-rx-capacity-current fn-page-read-pool fn-output-storage)))))))))

(defun fn-rxo-current-model-local () (declare (xargs :verify-guards nil)) (with-local-stobj fn-rx-provider (mv-let (answer fn-rx-provider) (with-local-stobj fn-receiver-turn (mv-let (answer fn-rx-provider fn-receiver-turn) (with-local-stobj fn-rx-capacity-current (mv-let (answer fn-rx-provider fn-receiver-turn fn-rx-capacity-current) (with-local-stobj fn-page-read-pool (mv-let (answer fn-rx-provider fn-receiver-turn fn-rx-capacity-current fn-page-read-pool) (with-local-stobj fn-output-storage (mv-let (answer fn-rx-provider fn-receiver-turn fn-rx-capacity-current fn-page-read-pool fn-output-storage) (fn-rxo-current-model-run fn-rx-provider fn-receiver-turn fn-rx-capacity-current fn-page-read-pool fn-output-storage) (mv answer fn-rx-provider fn-receiver-turn fn-rx-capacity-current fn-page-read-pool))) (mv answer fn-rx-provider fn-receiver-turn fn-rx-capacity-current))) (mv answer fn-rx-provider fn-receiver-turn))) (mv answer fn-rx-provider))) answer)))

(assert-event (equal (fn-rxo-current-model-local) '(:output-reserved :retained-output t :constructing :retained-output :constructing :constructing t t t t nil nil)))