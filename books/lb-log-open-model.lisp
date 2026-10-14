; Temporary LB-LOG-MODEL open adapter: bytes come from decoded wire events.
; No payload byte is obtained from an arena while constructing LOG.
(in-package "ACL2")
(include-book "catalog-columns-guards")
(include-book "store-intern")

(local (defthm fn-lbop-digest-proper
 (true-listp (fn-blake3-stobj prefix))
 :hints (("Goal" :use ((:instance fn-blake3-stobj-satisfies-fn-frame-digest-octet-listp (octets prefix)))
 :in-theory (disable fn-blake3-stobj fn-cbor-octet-listp)))))

(local (defthm fn-lbop-append-proper
 (implies (true-listp b) (true-listp (append a b)))
 :hints (("Goal" :induct (append a b) :in-theory (union-theories (theory 'ground-zero) '(binary-append true-listp))))))

(local (defthm fn-lbop-appended-segment-guard
 (implies (and (true-listp segment) (true-listp (cadr segment)) (true-listp (caddr segment)))
 (and (true-listp (fn-lb-log-model-append-to-segment row payload segment))
      (true-listp (cadr (fn-lb-log-model-append-to-segment row payload segment)))
      (true-listp (caddr (fn-lb-log-model-append-to-segment row payload segment)))))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-append-to-segment fn-lbop-digest-proper fn-lbop-append-proper true-listp))))))

(defthm fn-lb-log-append-guardp-of-append
 (implies (fn-lb-log-append-guardp log)
 (fn-lb-log-append-guardp (fn-lb-log-model-append row payload target log)))
 :hints (("Goal" :induct (fn-lb-log-model-append row payload target log)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-append fn-lb-log-append-guardp fn-lbop-appended-segment-guard true-listp)))))

(defun fn-lb-open-wire-article (w)
 (declare (xargs :guard t))
 (cond ((fn-record-p w) w)
       ((fn-stxa-p w) (let ((a (fn-replay-composite-record w))) (and (fn-record-p a) a)))
       (t nil)))

(defthm fn-lb-open-wire-article-is-record
 (implies (fn-lb-open-wire-article w) (fn-record-p (fn-lb-open-wire-article w)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero) '(fn-lb-open-wire-article)))))

(defun fn-lb-open-records-guardp (ws keyring generation h)
 (declare (xargs :guard (and (fn-prin-keyringp keyring) (natp generation) (natp h))))
 (if (consp ws)
  (let* ((a (fn-lb-open-wire-article (car ws)))
         (row (and a (fn-intern-row-at a keyring generation h))))
   (and (or (not a) (and (fn-cat-rowp row) (fn-lb-value-treep (fn-lb-log-model-homes row))))
        (fn-lb-open-records-guardp (cdr ws) keyring generation (if a (+ 1 h) h))))
  t))

(local (defthm fn-lbop-record-payload-proper
 (implies (fn-record-p w) (true-listp (fn-record-payload w)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-cbor-octet-listp-implies-true-listp (xs (fn-record-payload w))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-record-p fn-record-payloadp))))))

(with-prover-time-limit 60
(def-loop fn-lb-log-model-open-events (ws keyring generation h target log)
 :shape :step :over (ws h log) :done (atom ws) :skip t :body :unused
 :let ((a (fn-lb-open-wire-article (car ws))))
 :next ((cdr ws) (if a (+ 1 h) h)
         (if a (fn-lb-log-model-append (fn-intern-row-at a keyring generation h) (fn-record-payload a) target log) log))
 :skip-next ((cdr ws) (if a (+ 1 h) h)
         (if a (fn-lb-log-model-append (fn-intern-row-at a keyring generation h) (fn-record-payload a) target log) log))
 :tail log
 :guard (and (fn-prin-keyringp keyring) (natp generation) (natp h)
             (fn-lb-open-records-guardp ws keyring generation h) (fn-lb-log-append-guardp log))
 :guard-hints (("Goal" :in-theory (e/d (fn-lb-open-records-guardp fn-lb-open-wire-article) (fn-intern-row-at fn-cat-rowp fn-lb-log-model-homes fn-lb-log-model-append fn-prin-keyringp)))))
)
