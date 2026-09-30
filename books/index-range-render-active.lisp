; Actual internal same-child held row ONE boundary.
; Registered source/runtime/physical custody and native activation stay open.
(in-package "ACL2")
(include-book "index-range-render-demand")

(defun fn-ibr-joint-segment-held-one
 (token fn-ibp-query-segment fn-query-payload-grants fn-arena)
 (declare (xargs :stobjs (fn-ibp-query-segment fn-query-payload-grants fn-arena)
  :guard (and (fn-ibp-query-tokenp token)
          (implies (fn-ibp-query-slot-livep token fn-ibp-query-segment)
           (fn-ibr-held-current-ready-p
             (fn-ibp-qs-controlsi (nth 3 token) fn-ibp-query-segment) fn-arena)))))
 (if (not (fn-ibp-query-slot-livep token fn-ibp-query-segment))
     (mv nil :stale fn-ibp-query-segment)
  (mv-let (word demand)
  (fn-ibr-joint-segment-demand token fn-ibp-query-segment fn-query-payload-grants fn-arena)
  (declare (ignore demand))
  (if (not (or (eq word :payload) (eq word :none)))
      (mv nil word fn-ibp-query-segment)
    (let* ((slot (nth 3 token))
           (control (fn-ibp-qs-controlsi slot fn-ibp-query-segment)))
     (mv-let (out phase next)
      (fn-ibr-held-one control fn-arena)
      (if (eq phase :recovery-required)
          (mv out phase fn-ibp-query-segment)
        (let ((fn-ibp-query-segment
               (update-fn-ibp-qs-controlsi slot next fn-ibp-query-segment)))
         (mv out phase fn-ibp-query-segment)))))))))

(local
 (defthm fn-ibr-held-one-nth-update
  (implies (and (natp i) (natp j))
   (equal (nth i (update-nth j value xs))
          (if (equal i j) value (nth i xs))))
  :hints (("Goal" :induct (update-nth j value xs)))))
(defthm fn-ibr-joint-held-one-preserves-current-cell-carry
 (implies
  (fn-ibr-held-current-ready-p
    (fn-ibp-qs-controlsi (nth 3 token) fn-ibp-query-segment) fn-arena)
  (let* ((answer (fn-ibr-joint-segment-held-one
                  token fn-ibp-query-segment fn-query-payload-grants fn-arena))
         (next (mv-nth 2 answer)))
   (implies (eq (mv-nth 1 answer) :held)
    (fn-ibr-held-current-ready-p
       (fn-ibp-qs-controlsi (nth 3 token) next) fn-arena))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-ibr-held-one-preserves-current-cell-carry
          (control (fn-ibp-qs-controlsi (nth 3 token) fn-ibp-query-segment))))
  :in-theory
  (e/d (fn-ibr-joint-segment-held-one fn-ibp-query-tokenp fn-ibp-query-slot-livep)
       (fn-ibr-joint-segment-demand fn-ibr-held-one
        fn-ibr-held-current-ready-p nth update-nth nth-add1)))))
(defthm fn-ibr-joint-held-one-retains-same-context
 (let* ((answer (fn-ibr-joint-segment-held-one
                 token fn-ibp-query-segment fn-query-payload-grants fn-arena))
        (next (mv-nth 2 answer)))
  (equal (fn-ibp-qs-inputsi (nth 3 token) next)
         (fn-ibp-qs-inputsi (nth 3 token) fn-ibp-query-segment)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory
  (e/d (fn-ibr-joint-segment-held-one)
       (fn-ibr-joint-segment-demand fn-ibr-held-one
        fn-ibp-query-slot-livep nth update-nth nth-add1)))))
