; Ground witnesses and mutations for the checked checkpoint open.
(in-package "ACL2")
(include-book "../../books/store-checkpoint-arena-checked")

; The real wire below is reclaim-fold-contexts-live-tests.lisp's *rfcllive-wire*,
; byte for byte, with its *sit-groups* expanded as '("example").
(with-guard-checking-event :none
 (defconst *lckv-wire*
  (fn-record-make 1 1 1 "<rfcllive@example.invalid>" '(76 13 10) '("example")
                  "rfcllive-obligation" "rfcllive-subject" "rfcllive-release" 2 841000000)))
(with-guard-checking-event :none
 (defconst *lckv-e0*
  (fn-store-retention-event-make :undertake 0 0 0 "lckv-obligation" "subject" "release" 2)))
(with-guard-checking-event :none
 (defconst *lckv-held* (fn-intern-row-at *lckv-wire* nil 0 0)))

(defun lckv-plan-segments (segments fn-octets)
  (declare (xargs :stobjs fn-octets :verify-guards nil))
  (if (atom segments) (mv nil fn-octets)
    (let* ((segment (car segments))
           (header (take *fn-scc-segment-header-octets* segment))
           (h (fn-scc-parse-header header))
           (chunk (take (nth 2 h) (nthcdr *fn-scc-segment-header-octets* segment)))
           (trailer (nthcdr (+ *fn-scc-segment-header-octets* (nth 2 h)) segment))
           (a (fn-octets-len fn-octets))
           (fn-octets (fn-octets-append-list chunk fn-octets)))
      (mv-let (rest fn-octets) (lckv-plan-segments (cdr segments) fn-octets)
        (mv (cons (list header a (+ a (len chunk)) trailer) rest) fn-octets)))))

(defun lckv-check-in (tables ps fn-octets fn-arena)
  (declare (xargs :stobjs (fn-octets fn-arena) :verify-guards nil))
  (let* ((s (len (fn-sct-tables-e tables)))
         (ks (if (consp ps) (list (len ps)) nil))
         (progs (fn-sct-table-programs tables
                 (fn-sco-event-index (fn-sct-capture-of-tables tables))))
         (segments (append (fn-scka-run-segments ps ks s)
                           (fn-sct-file-segments progs 65536 s))))
    (mv-let (plan fn-octets) (lckv-plan-segments segments fn-octets)
      (mv-let (raw fn-arena) (fn-scka-load plan fn-octets fn-arena)
        (let* ((rp (fn-sco-records (fn-sct-capture-of-tables (cadr raw))))
               (raw-premises
                (list (fn-rows-handles-inp rp fn-arena)
                      (fn-orcr-fold-contexts-okp rp (fn-stxk-initial-context 0)
                                                (fn-arena-count fn-arena) fn-arena)
                      (equal (fn-sco-identity (fn-sct-capture-of-tables (cadr raw)))
                             (fn-replay-identity-loop rp (fn-stxk-initial-context 0))))))
        (mv-let (checked fn-arena) (fn-scka-open-checked plan fn-octets fn-arena)
          (let ((prefix (fn-sco-records (fn-sct-capture-of-tables (cadr checked)))))
            (mv (list :raw raw :checked checked
                      :premises (and (fn-rows-handles-inp prefix fn-arena)
                                     (fn-orcr-fold-contexts-okp prefix (fn-stxk-initial-context 0)
                                         (fn-arena-count fn-arena) fn-arena)
                                     (equal (fn-sco-identity (fn-sct-capture-of-tables (cadr checked)))
                                            (fn-replay-identity-loop prefix (fn-stxk-initial-context 0))))
                      :count (fn-arena-count fn-arena)
                      :antecedent
                      (and (fn-octets-p fn-octets)
                           (fn-sccr-planp plan (if (consp plan) (fn-sccr-at 1 (car plan)) 0) fn-octets)
                           (equal (fn-sccr-plan-segments plan fn-octets) segments)
                           (true-list-listp ps) (equal (fn-scka-sum ks) (len ps))
                           (fn-scc-chunk-listp (fn-scka-run-chunks ps ks))
                           (< (+ 1 (len ks)) *fn-scc-u64-bound*) (< s *fn-scc-u64-bound*)
                           (fn-sct-tables-treep tables) (fn-sct-log-positionp nil)
                           (<= s (1+ *fn-cbor-max-uint*)) (fn-sct-programs-widthp progs))
                      :raw-premises raw-premises)
                fn-octets fn-arena))))))))

(defun lckv-run-tables (tables ps)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (answer fn-octets)
      (with-local-stobj fn-arena
        (mv-let (answer fn-octets fn-arena) (lckv-check-in tables ps fn-octets fn-arena)
          (mv answer fn-octets)))
      answer)))

(with-guard-checking-event :none
 (defconst *lckv-missing-tables*
  (fn-sct-tables-of-capture
   (fn-sco-capture nil
    (list (fn-intern-row-at
           (fn-record-make 0 0 0 "<r0@example.invalid>" '(76 13 10) '("example")
                           "r0-obligation" "r0-subject" "r0-release" 2 841000000)
           nil 0 0))) 0 0 nil)))

(with-guard-checking-event :none
 (defconst *lckv-rows* (list *lckv-e0* *lckv-held*)))
(with-guard-checking-event :none
 (defconst *lckv-tables*
  (fn-sct-tables-of-capture (fn-sco-capture nil *lckv-rows*) 0 0 nil)))
(with-guard-checking-event :none
 (defconst *lckv-stale-tables*
  (fn-sct-tables-of-capture
   (fn-sco-capture nil (list *lckv-e0*
    (fn-held-with-context *lckv-held* (fn-held-context-of '(76 13 10) nil 1)))) 0 0 nil)))
(with-guard-checking-event :none
 (defconst *lckv-identity-tables*
  (update-nth 3 (update-nth 1 (update-nth 4 1 (fn-sco-at 1 (fn-sct-tables-r *lckv-tables*)))
                              (fn-sct-tables-r *lckv-tables*)) *lckv-tables*)))

(defun lckv-summary (diagnostic tables)
 (declare (xargs :guard t :verify-guards nil))
 (list :raw-ok (equal (cadr diagnostic) (list :ok tables))
       :checked (if (equal (nth 3 diagnostic) (list :ok tables)) :ok (nth 3 diagnostic))
       :premises (nth 5 diagnostic) :count (nth 7 diagnostic) :antecedent (nth 9 diagnostic)
       :raw-premises (nth 11 diagnostic)))

(defun lckv-canonical-in (fn-octets fn-arena)
 (declare (xargs :stobjs (fn-octets fn-arena) :verify-guards nil))
 (let* ((r (list *lckv-e0* *lckv-wire*))
        (records (fn-scka-canon-rows r fn-arena 0 (fn-stxk-initial-context 0)))
        (ps (fn-scka-canon-payloads r fn-arena))
        (tables (fn-sct-tables-of-capture (fn-sco-capture nil records) 0 0 nil)))
  (mv-let (diagnostic fn-octets fn-arena) (lckv-check-in tables ps fn-octets fn-arena)
    (mv (list :canonical-not-bad (not (equal records :bad))
              :rows-are-held (and (consp records) (fn-held-p (cadr records)))
              :result (lckv-summary diagnostic tables)) fn-octets fn-arena))))

(defun lckv-run-canonical ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-octets
  (mv-let (answer fn-octets)
   (with-local-stobj fn-arena
    (mv-let (answer fn-octets fn-arena) (lckv-canonical-in fn-octets fn-arena)
      (mv answer fn-octets))) answer)))

; T1: a retained handle 0 with zero arena payloads; removing the check accepts it.
(with-guard-checking-event :none
 (assert-event (equal (lckv-summary (lckv-run-tables *lckv-missing-tables* nil) *lckv-missing-tables*)
                      '(:raw-ok t :checked (:refused :checkpoint-premises) :premises nil :count 0 :antecedent t :raw-premises (nil t t)))))

; T2: the bytes are in range but the frozen context is from generation 1.
(with-guard-checking-event :none
 (assert-event (equal (lckv-summary (lckv-run-tables *lckv-stale-tables* (list '(76 13 10))) *lckv-stale-tables*)
                      '(:raw-ok t :checked (:refused :checkpoint-premises) :premises nil :count 1 :antecedent t :raw-premises (t nil t)))))

; T2b: correct rows and bytes, but the stored identity generation is altered.
(with-guard-checking-event :none
 (assert-event (equal (lckv-summary (lckv-run-tables *lckv-identity-tables* (list '(76 13 10))) *lckv-identity-tables*)
                      '(:raw-ok t :checked (:refused :checkpoint-premises) :premises nil :count 1 :antecedent t :raw-premises (t t nil)))))

; T3: the complete V3 antecedent holds, the writer-made file opens, and V1 holds.
(with-guard-checking-event :none
 (assert-event (equal (lckv-run-canonical)
                      '(:canonical-not-bad t :rows-are-held t :result (:raw-ok t :checked :ok :premises t :count 1 :antecedent t :raw-premises (t t t))))))

