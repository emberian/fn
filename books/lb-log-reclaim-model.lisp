; Temporary LB-LOG-MODEL reclaim adapter; owner C, retires with LA1/LA6.
; Match actual ORCS prediction: evolving identity, fresh handles, decoded
; tombstone payloads. LOG is never manufactured from arena reads.
(in-package "ACL2")
(include-book "lb-log-open-model")
(include-book "owner-reclaim-seal")

(local (defthm fn-lbr-record-payload-proper
 (implies (fn-record-p w) (true-listp (fn-record-payload w)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-cbor-octet-listp-implies-true-listp (xs (fn-record-payload w))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-record-p fn-record-payloadp))))))

(defun fn-lb-reclaim-records-guardp (rows id h)
 (declare (xargs :guard (natp h)
 :guard-hints (("Goal" :in-theory (enable fn-ssr-statep)))))
 (if (consp rows)
  (let* ((w (car rows)) (seed (fn-ssr-seed id))
         (row (if (fn-record-p w) (fn-intern-row-at w (fn-ssr-at 1 seed) (fn-ssr-at 2 seed) h) w)))
   (and (or (not (fn-record-p w))
            (and (fn-cat-rowp row) (fn-lb-value-treep (fn-lb-log-model-homes row))))
        (fn-lb-reclaim-records-guardp (cdr rows) (fn-replay-identity-loop (list row) id)
          (if (fn-record-p w) (+ 1 h) h))))
  t))

(with-prover-time-limit 60 (def-loop fn-lb-log-model-reclaim-events (rows id h target log)
  :shape :step :over (rows id h log) :done (atom rows) :skip t :body :unused
  :let ((w (car rows)) (seed (fn-ssr-seed id))
        (row (if (fn-record-p w) (fn-intern-row-at w (fn-ssr-at 1 seed) (fn-ssr-at 2 seed) h) w)))
  :next ((cdr rows) (fn-replay-identity-loop (list row) id)
         (if (fn-record-p w) (+ 1 h) h)
         (if (fn-record-p w) (fn-lb-log-model-append row (fn-record-payload w) target log) log))
  :skip-next ((cdr rows) (fn-replay-identity-loop (list row) id)
         (if (fn-record-p w) (+ 1 h) h)
         (if (fn-record-p w) (fn-lb-log-model-append row (fn-record-payload w) target log) log))
  :tail log
  :guard (and (natp h) (fn-lb-reclaim-records-guardp rows id h) (fn-lb-log-append-guardp log))
  :guard-hints (("Goal" :in-theory (e/d (fn-lb-reclaim-records-guardp fn-ssr-statep)
    (fn-intern-row-at fn-record-p fn-lb-log-model-homes fn-lb-log-model-append
     fn-prin-keyringp fn-replay-identity-loop))))))
