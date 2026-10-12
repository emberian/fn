; The checkpoint open establishes the retained-prefix premises before a suffix is seeded.
; The raw decode fn-scka-load remains unchanged.
(in-package "ACL2")
(include-book "store-checkpoint-arena-load")
(include-book "reclaim-fold-contexts")

(defun fn-scka-premises-okp (tables fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (let ((prefix (fn-sco-records (fn-sct-capture-of-tables tables))))
    (and (fn-rows-handles-inp prefix fn-arena)
         (fn-orcr-fold-contexts-okp prefix (fn-stxk-initial-context 0)
                                  (fn-arena-count fn-arena) fn-arena)
         (equal (fn-sco-identity (fn-sct-capture-of-tables tables))
                (fn-replay-identity-loop prefix (fn-stxk-initial-context 0))))))
(defun fn-scka-open-checked (plan fn-octets fn-arena)
  (declare (xargs :stobjs (fn-octets fn-arena) :guard t :verify-guards nil))
  (mv-let (answer fn-arena) (fn-scka-load plan fn-octets fn-arena)
    (if (and (eq (car answer) :ok) (not (fn-scka-premises-okp (cadr answer) fn-arena)))
        (mv (list :refused :checkpoint-premises) fn-arena)
      (mv answer fn-arena))))

(verify-guards fn-scka-premises-okp)
(verify-guards fn-scka-open-checked)

; KEYSTONE: an :ok checked open carries all three prefix premises.
(defthm fn-scka-open-checked-establishes-the-prefix-premises
  (let* ((out (fn-scka-open-checked plan fn-octets fn-arena))
         (prefix (fn-sco-records (fn-sct-capture-of-tables (cadr (mv-nth 0 out))))))
    (implies (equal (car (mv-nth 0 out)) :ok)
             (and (fn-rows-handles-inp prefix (mv-nth 1 out))
                  (fn-orcr-fold-contexts-okp prefix (fn-stxk-initial-context 0)
                                             (fn-arena-count (mv-nth 1 out)) (mv-nth 1 out))
                  (equal (fn-sco-identity (fn-sct-capture-of-tables (cadr (mv-nth 0 out))))
                         (fn-replay-identity-loop prefix (fn-stxk-initial-context 0))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-scka-open-checked fn-scka-premises-okp)
                                   (fn-scka-load fn-sct-capture-of-tables fn-sco-records
                                    fn-sco-identity fn-rows-handles-inp fn-orcr-fold-contexts-okp
                                    fn-replay-identity-loop)))))

(defthm fn-scka-open-checked-is-the-load-or-the-premises-refusal
  (let ((v (fn-scka-open-checked plan fn-octets fn-arena))
        (l (fn-scka-load plan fn-octets fn-arena)))
    (and (equal (mv-nth 1 v) (mv-nth 1 l))
         (or (equal (mv-nth 0 v) (mv-nth 0 l))
             (and (equal (car (mv-nth 0 l)) :ok)
                  (equal (mv-nth 0 v) (list :refused :checkpoint-premises))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-scka-open-checked)
                                   (fn-scka-load fn-scka-premises-okp)))))

(local
 (defthm fn-sckv-handles-of-append
  (equal (fn-rows-handles-inp (append x y) fn-arena)
         (and (fn-rows-handles-inp x fn-arena) (fn-rows-handles-inp y fn-arena)))
  :hints (("Goal" :induct (len x) :in-theory (enable fn-rows-handles-inp)))))
(local
 (defthm fn-sckv-handles-survive-seal
  (implies (fn-rows-handles-inp rows fn-arena)
           (fn-rows-handles-inp rows (fn-arena-seal-list p fn-arena)))
  :hints (("Goal" :induct (fn-rows-handles-inp rows fn-arena)
           :in-theory (enable fn-rows-handles-inp fn-row-handle-inp)))))
(local
 (defthm fn-sckv-arena-p-of-intern-event
  (implies (fn-arena-p fn-arena)
           (fn-arena-p (mv-nth 1 (fn-intern-event w keyring generation fn-arena))))
  :hints (("Goal" :in-theory (e/d (fn-intern-event-arena fn-arena-p-is-payload-listp
                                    fn-record-p fn-record-payloadp)
                                   (fn-intern-event fn-stxa-p fn-replay-composite-record))))))
(local
 (defthm fn-sckv-handles-survive-intern-event
  (implies (fn-rows-handles-inp rows fn-arena)
           (fn-rows-handles-inp rows (mv-nth 1 (fn-intern-event w k g fn-arena))))
  :hints (("Goal" :in-theory (e/d (fn-intern-event-arena)
                                  (fn-intern-event fn-rows-handles-inp))))))
(local
 (defthm fn-sckv-rev-onto
  (equal (fn-ag-rev-onto x acc) (revappend x acc))))
(local
 (defthm fn-sckv-rows-of-publish
  (equal (fn-ssr-rows (fn-ssr-publish acc row wire id))
         (append (fn-ssr-rows acc) (list row)))
  :hints (("Goal" :in-theory (enable fn-ssr-publish fn-ssr-rows fn-ssr-state fn-ssr-at)))))
(local
 (defthm fn-sckv-handles-of-atom
  (implies (atom rows) (fn-rows-handles-inp rows fn-arena))
  :hints (("Goal" :in-theory (enable fn-rows-handles-inp)))))
(local
 (defthm fn-sckv-handles-of-bad-rows
  (fn-rows-handles-inp (fn-ssr-rows :bad) fn-arena)
  :hints (("Goal" :in-theory (enable fn-ssr-rows fn-rows-handles-inp)))))
(local
 (defthm fn-sckv-resident-step-handles-in
  (implies (and (fn-arena-p fn-arena) (fn-ssr-statep acc)
                (fn-rows-handles-inp (fn-ssr-rows acc) fn-arena))
           (fn-rows-handles-inp
            (fn-ssr-rows (mv-nth 0 (fn-ssr-intern-step acc ws nil nil :resident dicts fn-arena)))
            (mv-nth 1 (fn-ssr-intern-step acc ws nil nil :resident dicts fn-arena))))
  :hints (("Goal" :induct (fn-ssr-intern-step acc ws nil nil :resident dicts fn-arena)
           :in-theory (e/d (fn-ssr-intern-step fn-ssr-statep)
                           (fn-intern-event fn-ssr-publish fn-ssr-rows fn-ssr-at
                            fn-replay-identity-step fn-rows-handles-inp fn-arena-p
                            fn-scka-fold-at-is-the-ssr-step fn-scka-intern-event-row)))
          ("Subgoal *1/4"
           :use ((:instance fn-intern-event-handle-in
                   (w (car ws)) (keyring (fn-ssr-at 1 acc))
                   (generation (fn-ssr-at 2 acc))))))))

(local
 (defthm fn-sckv-intern-at-has-the-prefix-premises
  (implies (not (equal (fn-scka-intern-at ws id 0) :bad))
           (and (fn-rows-handles-inp (fn-scka-intern-at ws id 0) (fn-scka-payloads ws))
                (fn-orcr-fold-contexts-okp (fn-scka-intern-at ws id 0) id h (fn-scka-payloads ws))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-rfc-the-open-interns-at-the-fold-contexts
                   (fn-arena nil) (dicts nil))
                 (:instance fn-sckv-resident-step-handles-in
                   (acc (fn-ssr-seed id)) (fn-arena nil) (dicts nil))
                 (:instance fn-scka-fold-at-arena-is-payloads
                   (acc (fn-ssr-seed id)) (fn-arena nil) (dicts nil)))
           :in-theory (e/d (fn-scka-intern-at fn-arena-p-is-payload-listp)
                           (fn-ssr-intern-step fn-scka-fold-at fn-ssr-seed fn-ssr-rows
                            fn-scka-payloads fn-rows-handles-inp fn-orcr-fold-contexts-okp))))))
(local
 (defthm fn-sckv-records-of-capture-unfolds
  (equal (fn-sco-records (fn-sco-capture configs records)) (true-list-fix records))
  :hints (("Goal" :in-theory
           (e/d (fn-sco-records fn-sco-capture fn-sco-make fn-sco-at)
                (fn-sco-cpr-prefix fn-replay-identity-loop fn-cpe-projection-replay
                 fn-th-prefix-loop fn-cei-build-aux))))))
(local
 (defthm fn-sckv-canonical-tables-premises
  (let* ((records (fn-scka-canon-rows r a 0 (fn-stxk-initial-context 0)))
         (c (fn-sco-capture configs records))
         (tables (fn-sct-tables-of-capture c frontier revision log)))
    (implies (not (equal records :bad))
             (fn-scka-premises-okp tables (fn-scka-canon-payloads r a))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-sckv-intern-at-has-the-prefix-premises
                   (ws (fn-rows-wire-of r a)) (id (fn-stxk-initial-context 0))
                   (h (fn-arena-count (fn-scka-canon-payloads r a))))
                 (:instance fn-scka-identity-of-capture
                   (records (fn-scka-canon-rows r a 0 (fn-stxk-initial-context 0)))))
           :in-theory (e/d (fn-scka-premises-okp)
                           (fn-sco-records fn-sco-capture fn-sco-make fn-sco-at
                            fn-sct-capture-of-tables fn-sct-tables-of-capture
                            fn-scka-canon-rows fn-scka-canon-payloads
                            fn-scka-intern-at fn-scka-fold-at fn-scka-intern-at-bad-iff
                            fn-sckv-intern-at-has-the-prefix-premises
                            fn-scka-payloads fn-rows-wire-of fn-rows-handles-inp
                            fn-orcr-fold-contexts-okp fn-sco-cpr-prefix fn-sco-identity
                            fn-cpe-projection-replay fn-th-prefix-loop fn-cei-build-aux
                            fn-replay-identity-loop))))))

; KEYSTONE: canonical writer rows and payloads pass the same check.
(defthm fn-scka-open-checked-of-a-canonical-written-file
  (let* ((records (fn-scka-canon-rows r a 0 (fn-stxk-initial-context 0)))
         (ps (fn-scka-canon-payloads r a))
         (c (fn-sco-capture configs records))
         (tables (fn-sct-tables-of-capture c frontier revision log))
         (progs (fn-sct-table-programs tables (fn-sco-event-index c)))
         (s (len records)))
    (implies (and (not (equal records :bad))
                  (fn-octets-p fn-octets)
                  (fn-sccr-planp plan (if (consp plan) (fn-sccr-at 1 (car plan)) 0) fn-octets)
                  (equal (fn-sccr-plan-segments plan fn-octets)
                         (append (fn-scka-run-segments ps ks s)
                                 (fn-sct-file-segments progs seg s)))
                  (true-list-listp ps) (equal (fn-scka-sum ks) (len ps))
                  (fn-scc-chunk-listp (fn-scka-run-chunks ps ks))
                  (< (+ 1 (len ks)) *fn-scc-u64-bound*) (< s *fn-scc-u64-bound*)
                  (fn-sct-tables-treep tables)
                  (fn-sct-log-positionp log)
                  (<= (len records) (1+ *fn-cbor-max-uint*))
                  (fn-sct-programs-widthp progs))
             (and (equal (mv-nth 0 (fn-scka-open-checked plan fn-octets fn-arena)) (list :ok tables))
                  (equal (mv-nth 1 (fn-scka-open-checked plan fn-octets fn-arena)) ps))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-scka-load-of-written-file
                   (records (fn-scka-canon-rows r a 0 (fn-stxk-initial-context 0)))
                   (ps (fn-scka-canon-payloads r a)))
                 (:instance fn-sckv-canonical-tables-premises))
           :in-theory (e/d (fn-scka-open-checked)
                           (fn-scka-load fn-scka-load-of-written-file
                            fn-sckv-canonical-tables-premises fn-scka-premises-okp
                            fn-scka-canon-rows fn-scka-canon-payloads
                            fn-scka-canon-rows-is-intern-at-of-alpha
                            fn-scka-canon-payloads-is-payloads-of-alpha
                            fn-scka-intern-at fn-scka-fold-at fn-scka-payloads fn-rows-wire-of
                            fn-sco-capture fn-sct-tables-of-capture
                            fn-sct-table-programs fn-sco-event-index fn-sccr-planp
                            fn-sccr-plan-segments fn-scka-run-segments fn-sct-file-segments
                            fn-scka-sum fn-scka-run-chunks fn-scc-chunk-listp
                            fn-sct-tables-treep fn-sct-log-positionp fn-sct-programs-widthp)))))
