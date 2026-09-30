; Same actual dispatch and chunk loop, with aligned snapshot row carries.
; Actual composed source/include qualification remains a separate boundary.
(in-package "ACL2")
(include-book "store-recover-stream")
(include-book "stx-keyring-size-reader")

(defun fn-srss-event-decode (octets)
 (declare (xargs :guard t :verify-guards nil))
 (let ((legacy (ec-call (fn-record-decode-exact octets))))
  (if (fn-record-result-okp legacy) (mv legacy nil)
   (let ((retention (ec-call (fn-store-retention-event-decode-exact octets))))
    (if (equal (fn-ag-car retention) :ok) (mv retention nil)
     (let ((verdict (ec-call (fn-stxe-decode-exact octets))))
      (if (fn-stmt-okp verdict) (mv verdict nil)
       (mv-let (snapshot carry) (fn-stxks-decode octets)
        (if (fn-stmt-okp snapshot) (mv snapshot carry)
         (let ((accepted (ec-call (fn-stxa-decode-exact octets))))
          (if (fn-stmt-okp accepted) (mv accepted nil)
           (let ((consumer (ec-call (fn-cpe-decode-exact octets))))
            (if (fn-stmt-okp consumer) (mv consumer nil)
             (mv (ec-call (fn-th-topic-event-decode-exact octets)) nil))))))))))))))

(verify-guards fn-srss-event-decode)

(defthm fn-srss-event-first-result-is-actual-dispatch
 (equal (mv-nth 0 (fn-srss-event-decode octets)) (fn-store-event-decode-exact octets))
 :rule-classes nil
 :hints (("Goal" :use fn-stxks-first-result-is-public-decoder
  :in-theory (union-theories
   '(fn-srss-event-decode fn-store-event-decode-exact fn-ag-car mv-nth car-cons cdr-cons)
   (theory 'minimal-theory)))))

(defthm fn-srss-event-present-carry-is-whole-row
 (implies (mv-nth 1 (fn-srss-event-decode octets))
  (and (fn-stmt-okp (mv-nth 0 (fn-srss-event-decode octets)))
       (equal (mv-nth 1 (fn-srss-event-decode octets))
              (fn-scs-summary (fn-stmt-value (mv-nth 0 (fn-srss-event-decode octets)))))))
 :rule-classes nil
 :hints (("Goal" :use fn-stxks-success-carry-is-whole-row-carry :in-theory
  (e/d (fn-srss-event-decode)
   (fn-record-result-okp fn-store-retention-event-decode-exact
    fn-stxe-decode-exact fn-stxks-decode fn-stxa-decode-exact
    fn-cpe-decode-exact fn-th-topic-event-decode-exact fn-stmt-okp fn-stmt-value
    fn-scs-summary)))))

; Ghost alignment/relation only. The native caller never runs this walk.
(defun fn-srss-carries-correspondsp (rows carries)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp rows)
  (and (consp carries)
       (or (null (car carries)) (equal (car carries) (fn-scs-summary (car rows))))
       (fn-srss-carries-correspondsp (cdr rows) (cdr carries)))
  (and (null rows) (null carries))))

(local (defthm fn-srss-rev-onto-length
 (equal (len (fn-ag-rev-onto x tail)) (+ (len x) (len tail)))
 :hints (("Goal" :induct (fn-ag-rev-onto x tail)
  :in-theory (enable fn-ag-rev-onto)))))

; Proof-only paired reverse induction; never called by the decoder.
(local (defun fn-srss-reverse-pairs-induct (rows carries tail tail-carries)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp rows)
  (fn-srss-reverse-pairs-induct (cdr rows) (cdr carries)
                              (cons (car rows) tail) (cons (car carries) tail-carries))
  (list carries tail tail-carries))))

(local
 (defthm fn-srss-correspondence-rev-onto
  (implies (and (fn-srss-carries-correspondsp rows carries)
                (fn-srss-carries-correspondsp tail tail-carries))
   (fn-srss-carries-correspondsp (fn-ag-rev-onto rows tail)
                                (fn-ag-rev-onto carries tail-carries)))
  :hints (("Goal" :induct (fn-srss-reverse-pairs-induct rows carries tail tail-carries)
   :in-theory (union-theories
    '(fn-srss-carries-correspondsp fn-ag-rev-onto car-cons cdr-cons
      (:induction fn-srss-reverse-pairs-induct))
    (theory 'minimal-theory))))))

(local (defthm fn-srss-event-result-rewrites-by-definition
 (equal (mv-nth 0 (fn-srss-event-decode octets)) (fn-store-event-decode-exact octets))
 :hints (("Goal" :use fn-srss-event-first-result-is-actual-dispatch))))

(defun fn-srss-decode-loop (octet-records acc carries)
 (declare (xargs :guard t))
 (if (consp octet-records)
  (mv-let (decoded carry) (ec-call (fn-srss-event-decode (car octet-records)))
   (if (and (consp decoded) (equal (car decoded) :ok)
            (consp (cdr decoded)) (fn-rcon-wire-event-p (car (cdr decoded))))
    (fn-srss-decode-loop (cdr octet-records) (cons (car (cdr decoded)) acc)
                         (cons carry carries))
    (mv :bad nil)))
  (if (null octet-records)
   (mv (fn-ag-rev-onto acc nil) (fn-ag-rev-onto carries nil))
   (mv :bad nil))))

(defthm fn-srss-loop-first-result-is-actual-loop
 (equal (mv-nth 0 (fn-srss-decode-loop octet-records acc carries))
        (fn-srs-decode-loop octet-records acc))
 :rule-classes nil
 :hints (("Goal" :induct (fn-srss-decode-loop octet-records acc carries)
  :in-theory (e/d (fn-srss-decode-loop fn-srs-decode-loop)
   (fn-store-event-decode-exact fn-srss-event-decode fn-rcon-wire-event-p)))))

(defun fn-srss-decode (octet-records)
 (declare (xargs :guard t))
 (fn-srss-decode-loop octet-records nil nil))

(local
 (defthm fn-srss-old-loop-is-public-decode
  (equal (fn-srs-decode-loop octet-records acc)
         (if (equal (fn-srs-decode octet-records) :bad) :bad
          (fn-ag-rev-onto acc (fn-srs-decode octet-records))))
  :hints (("Goal" :induct (fn-srs-decode-loop octet-records acc)
   :in-theory (disable fn-store-event-decode-exact fn-rcon-wire-event-p)))))

(defthm fn-srss-first-result-is-actual-chunk-decode
 (equal (mv-nth 0 (fn-srss-decode octet-records)) (fn-srs-decode octet-records))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-srss-loop-first-result-is-actual-loop
                       (acc nil) (carries nil))
                      (:instance fn-srss-old-loop-is-public-decode (acc nil)))
  :in-theory (e/d (fn-srss-decode fn-ag-rev-onto)
   (fn-srss-decode-loop fn-srs-decode-loop fn-srs-decode)))))


(defthm fn-srss-loop-preserves-aligned-width
 (implies (equal (len acc) (len carries))
  (and (true-listp (mv-nth 1 (fn-srss-decode-loop octet-records acc carries)))
       (equal (len (mv-nth 1 (fn-srss-decode-loop octet-records acc carries)))
              (len (mv-nth 0 (fn-srss-decode-loop octet-records acc carries))))))
 :rule-classes nil
 :hints (("Goal" :induct (fn-srss-decode-loop octet-records acc carries)
  :in-theory (e/d (fn-srss-decode-loop fn-ag-rev-onto)
   (fn-srss-event-decode fn-rcon-wire-event-p fn-store-event-decode-exact
    fn-srss-event-result-rewrites-by-definition)))))

(defthm fn-srss-has-aligned-snapshot-carries
 (and (true-listp (mv-nth 1 (fn-srss-decode octet-records)))
       (equal (len (mv-nth 1 (fn-srss-decode octet-records)))
              (len (mv-nth 0 (fn-srss-decode octet-records)))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-srss-loop-preserves-aligned-width (acc nil) (carries nil)))
  :in-theory (e/d (fn-srss-decode) (fn-srss-decode-loop)))))

(local (defthm fn-srss-event-carry-rewrites
 (implies (and (mv-nth 1 (fn-srss-event-decode octets))
               (consp (mv-nth 0 (fn-srss-event-decode octets)))
               (consp (cdr (mv-nth 0 (fn-srss-event-decode octets)))))
  (equal (mv-nth 1 (fn-srss-event-decode octets))
         (fn-scs-summary (cadr (mv-nth 0 (fn-srss-event-decode octets))))))
 :hints (("Goal" :use fn-srss-event-present-carry-is-whole-row
  :in-theory (union-theories '(fn-stmt-value fn-stmt-okp fn-ag-car fn-ag-cdr)
                            (theory 'minimal-theory))))))

(defthm fn-srss-loop-preserves-whole-row-correspondence
 (implies (and (fn-srss-carries-correspondsp acc carries)
               (not (equal (mv-nth 0 (fn-srss-decode-loop octet-records acc carries)) :bad)))
  (fn-srss-carries-correspondsp
   (mv-nth 0 (fn-srss-decode-loop octet-records acc carries))
   (mv-nth 1 (fn-srss-decode-loop octet-records acc carries))))
 :rule-classes nil
 :hints (("Goal" :induct (fn-srss-decode-loop octet-records acc carries)
  :in-theory (e/d (fn-srss-decode-loop fn-srss-carries-correspondsp)
                 (fn-srss-event-decode fn-rcon-wire-event-p fn-scs-summary fn-ag-rev-onto
                  fn-store-event-decode-exact fn-srss-event-result-rewrites-by-definition)))))

(defthm fn-srss-success-carries-correspond-to-actual-rows
 (implies (not (equal (mv-nth 0 (fn-srss-decode octet-records)) :bad))
  (fn-srss-carries-correspondsp (mv-nth 0 (fn-srss-decode octet-records))
                               (mv-nth 1 (fn-srss-decode octet-records))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-srss-loop-preserves-whole-row-correspondence
                        (acc nil) (carries nil)))
  :in-theory (e/d (fn-srss-decode fn-srss-carries-correspondsp)
                 (fn-srss-decode-loop fn-scs-summary)))))
