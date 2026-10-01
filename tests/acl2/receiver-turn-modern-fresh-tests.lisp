; Unfunded local-storage mutation witness for the modern seven-field carry.
; This is not a live output producer, capacity grant or native alias receipt.
(in-package "ACL2")
(include-book "../../host/receiver-turn-resource-host")

(defun fn-rxt-modern-fresh-storage-fixture (fn-receiver-turn)
  (declare (xargs :stobjs fn-receiver-turn :guard t))
  (let* ((initial-fresh (fn-rxt-installation-freshp fn-receiver-turn))
         (fn-receiver-turn
          (update-fn-rxt-output-bundle '(:storage-mutation-retained-output)
                                       fn-receiver-turn)))
    (mv (and initial-fresh
             (eq (fn-rxt-phase fn-receiver-turn) :idle)
             (null (fn-rxt-ticket fn-receiver-turn))
             (null (fn-rxt-source fn-receiver-turn))
             (null (fn-rxt-demand fn-receiver-turn))
             (null (fn-rxt-job fn-receiver-turn))
             (null (fn-rxt-receipt fn-receiver-turn))
             (not (null (fn-rxt-output-bundle fn-receiver-turn)))
             (not (fn-rxt-installation-freshp fn-receiver-turn)))
        fn-receiver-turn)))

(defun fn-rxt-modern-fresh-storage-test ()
  (declare (xargs :guard t))
  (with-local-stobj fn-receiver-turn
    (mv-let (ok fn-receiver-turn)
      (fn-rxt-modern-fresh-storage-fixture fn-receiver-turn)
      ok)))

(assert-event (fn-rxt-modern-fresh-storage-test))
