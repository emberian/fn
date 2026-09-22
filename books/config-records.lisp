; fn: the journal as a two-kind stream, and replay over it.
;
; Today the journal carries one kind of record.  A reconfiguration is a
; transaction in the SAME journal, so the stream becomes two-kind: `:article'
; records go to `fn-replay-apply-record' exactly as before, `:config' records
; fold into the configuration by `fn-cfg-apply-record'.
;
; `books/replay' is not edited.  `fn-config-aware-loop' is an independently
; written loop over the two-kind stream, and the keystone below says the two
; agree: on a history that carries only transaction records, the node this
; loop reaches is the node `fn-replay' reaches, fault reasons included.  That
; is the statement that lets the two-kind stream be adopted without reproving
; anything about article replay -- and it is not vacuous, because neither loop
; is defined in terms of the other.

(in-package "ACL2")
(include-book "config")
(include-book "replay")
(include-book "records-seam")

; `fn-jrec-p' must conclude `true-listp' of a record body to discharge
; `fn-replay-apply-record's guard, and `books/records' exports the shape
; recognizer withdrawn.  Opened locally, for that guard obligation only.
(local (in-theory (enable fn-record-record-vocabulary
                          fn-record-shape-vocabulary)))

; The two total selectors `books/config' withdraws on export; the journal
; record's accessor lemmas and the `(result config)' pair selectors below are
; written over them.
(local (in-theory (enable fn-cfg-ag-car fn-cfg-ag-cdr)))

; -----------------------------------------------------------------------------
; A journal record

(defun fn-jrec-shapep (j)
  (declare (xargs :guard t))
  (and (true-listp j) (equal (len j) 3)))
(defun fn-jrec-kind (j)
  (declare (xargs :guard t))
  (fn-cfg-ag-car j))
(defun fn-jrec-sequence (j)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-ag-cdr j)))
(defun fn-jrec-body (j)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr j))))
(defun fn-jrec-make (kind sequence body)
  (declare (xargs :guard t))
  (list kind sequence body))

(defthm fn-jrec-shapep-of-jrec-make
  (fn-jrec-shapep (fn-jrec-make kind sequence body)))
(defthm fn-jrec-kind-of-jrec-make
  (equal (fn-jrec-kind (fn-jrec-make kind sequence body)) kind))
(defthm fn-jrec-sequence-of-jrec-make
  (equal (fn-jrec-sequence (fn-jrec-make kind sequence body)) sequence))
(defthm fn-jrec-body-of-jrec-make
  (equal (fn-jrec-body (fn-jrec-make kind sequence body)) body))

(in-theory (disable (:d fn-jrec-shapep) (:d fn-jrec-make) (:d fn-jrec-kind)
                    (:d fn-jrec-sequence) (:d fn-jrec-body)))

(defun fn-jrec-p (j)
  (declare (xargs :guard t))
  (and (fn-jrec-shapep j)
       (fn-record-uint32p (fn-jrec-sequence j))
       (cond ((equal (fn-jrec-kind j) :article)
              (and (fn-record-p (fn-jrec-body j))
                   (equal (fn-record-sequence (fn-jrec-body j))
                          (fn-jrec-sequence j))))
             ((equal (fn-jrec-kind j) :config)
              (and (fn-cfg-recordp (fn-jrec-body j))
                   (equal (fn-cfg-record-sequence (fn-jrec-body j))
                          (fn-jrec-sequence j))))
             (t nil))))

(defthm fn-jrec-article-body-is-a-true-list
  (implies (and (fn-jrec-p j) (equal (fn-jrec-kind j) :article))
           (and (fn-record-p (fn-jrec-body j))
                (true-listp (fn-jrec-body j)))))

; `fn-store-event-p' is withdrawn on export (books/store-events) and the
; keystones below keep `fn-jrec-p' closed, so the two facts a journal article
; record carries about its body are stated here: it is a Store event, and a
; record that is not a configuration record is an article record.
(defthm fn-jrec-article-body-is-a-store-event
  (implies (and (fn-jrec-p j) (equal (fn-jrec-kind j) :article))
           (fn-store-event-p (fn-jrec-body j)))
  :hints (("Goal" :in-theory (enable fn-store-event-p))))

(defthm fn-jrec-non-config-is-article
  (implies (and (fn-jrec-p j) (not (equal (fn-jrec-kind j) :config)))
           (equal (fn-jrec-kind j) :article)))

; The two sequence facts `fn-jrec-p' carries, stated so the keystones below
; can keep the recognizer closed: the body's own sequence field is the
; journal sequence.
(defthm fn-jrec-article-sequence-agrees
  (implies (and (fn-jrec-p j) (equal (fn-jrec-kind j) :article))
           (equal (fn-record-sequence (fn-jrec-body j)) (fn-jrec-sequence j))))
; `fn-store-event-sequence' is withdrawn on export too, so the same agreement
; is stated over the accessor `fn-replay-loop' actually applies to the body.
(defthm fn-jrec-article-store-event-sequence-agrees
  (implies (and (fn-jrec-p j) (equal (fn-jrec-kind j) :article))
           (equal (fn-store-event-sequence (fn-jrec-body j))
                  (fn-jrec-sequence j)))
  :hints (("Goal" :in-theory (e/d (fn-store-event-sequence)
                                  (fn-record-p fn-stxe-p fn-stxk-p fn-stxa-p
                                   fn-store-retention-event-p)))))

(defthm fn-jrec-config-sequence-agrees
  (implies (and (fn-jrec-p j) (equal (fn-jrec-kind j) :config))
           (equal (fn-cfg-record-sequence (fn-jrec-body j))
                  (fn-jrec-sequence j))))

(defun fn-jrec-listp (js)
  (declare (xargs :guard t))
  (if (consp js)
      (and (fn-jrec-p (car js)) (fn-jrec-listp (cdr js)))
    (null js)))

(defun fn-jrec-article-onlyp (js)
  (declare (xargs :guard t))
  (if (consp js)
      (and (equal (fn-jrec-kind (car js)) :article)
           (fn-jrec-article-onlyp (cdr js)))
    (null js)))

(defun fn-jrec-config-onlyp (js)
  (declare (xargs :guard t))
  (if (consp js)
      (and (equal (fn-jrec-kind (car js)) :config)
           (fn-jrec-config-onlyp (cdr js)))
    (null js)))

(defun fn-jrec-sequences-from (js expected)
  (declare (xargs :guard t))
  (if (consp js)
      (and (equal (fn-jrec-sequence (car js)) expected)
           ; `(fix expected)': the same value as `(+ 1 expected)' in the
           ; logic, and the `:guard t' obligation of `+' on a non-number.
           (fn-jrec-sequences-from (cdr js) (+ 1 (fix expected))))
    (null js)))

(defun fn-jrec-bodies (js)
  (declare (xargs :guard t))
  (if (consp js)
      (cons (fn-jrec-body (car js)) (fn-jrec-bodies (cdr js)))
    nil))

; -----------------------------------------------------------------------------
; Replay over the two-kind stream.  The result is (replay-result config).

(defun fn-config-aware-result (x)
  (declare (xargs :guard t))
  (fn-cfg-ag-car x))
(defun fn-config-aware-config (x)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-ag-cdr x)))

(defthm fn-config-aware-result-of-pair
  (equal (fn-config-aware-result (list result cfg)) result))
(defthm fn-config-aware-config-of-pair
  (equal (fn-config-aware-config (list result cfg)) cfg))
(in-theory (disable (:d fn-config-aware-result) (:d fn-config-aware-config)))

(defun fn-config-aware-loop (node cfg reserved ceiling js expected)
  (declare (xargs :guard (fn-node-statep node) :verify-guards nil
                  :measure (len js)))
  (if (mbe :logic (not (fn-node-statep node)) :exec nil)
      (list (fn-replay-fault node expected :invalid-initial-node) cfg)
    (if (consp js)
        (let ((j (car js)))
          (if (not (fn-jrec-p j))
              (list (fn-replay-fault node expected :invalid-record) cfg)
            (if (not (equal (fn-jrec-sequence j) expected))
                (list (fn-replay-fault node expected :sequence) cfg)
              (if (equal (fn-jrec-kind j) :config)
                  (if (not (fn-cfg-record-acceptablep cfg (fn-jrec-body j)
                                                      reserved ceiling))
                      (list (fn-replay-fault node expected :config-refusal)
                            cfg)
                    (fn-config-aware-loop
                     node (fn-cfg-apply-record cfg (fn-jrec-body j))
                     reserved ceiling (cdr js) (1+ expected)))
                (let ((next (fn-replay-apply-record node (fn-jrec-body j))))
                  (if (mbe :logic (not (fn-node-statep next))
                           :exec (not (consp next)))
                      (list (fn-replay-fault node expected :node-refusal) cfg)
                    (fn-config-aware-loop next cfg reserved ceiling (cdr js)
                                          (1+ expected))))))))
      (if (null js)
          (list (fn-replay-ok node expected) cfg)
        (list (fn-replay-fault node expected :improper-record-list) cfg)))))

; `fn-store-event-p' is withdrawn on export (books/store-events); this
; conjecture needs it, to carry `fn-jrec-p's article branch to the used
; lemma's hypothesis.  Its three statement kind recognizers stay closed:
; opening them here unfolds the statement codec on every branch and the
; conjecture does not return (measured 2026-09-22, past 900 s at Goal'').
(verify-guards fn-config-aware-loop
  :hints (("Goal"
           :use ((:instance fn-replay-apply-record-statep-iff-consp
                            (record (fn-jrec-body (car js)))))
           :in-theory (e/d (fn-store-event-p)
                           (fn-stxe-p fn-stxk-p fn-stxa-p
                            fn-node-statep fn-replay-apply-record
                            fn-cfg-record-acceptablep)))))

(defun fn-config-aware-replay (groups capacity reserved ceiling js)
  (declare (xargs :guard t :verify-guards nil))
  (let ((node (fn-node-initial-state groups capacity)))
    (if (fn-node-statep node)
        (fn-config-aware-loop node (fn-cfg-initial) reserved ceiling js 0)
      (list (fn-replay-fault node 0 :invalid-initial-node)
            (fn-cfg-initial)))))

(verify-guards fn-config-aware-replay)

; -----------------------------------------------------------------------------
; The keystone: the two loops agree on transaction-only histories.

(local (in-theory (enable fn-replay-loop fn-replay)))

(defthm fn-config-aware-loop-is-fn-replay-loop-on-transaction-only-histories
  (implies (and (fn-jrec-listp js)
                (fn-jrec-article-onlyp js)
                (fn-node-statep node))
           (equal (fn-config-aware-result
                   (fn-config-aware-loop node cfg reserved ceiling js
                                         expected))
                  (fn-replay-loop node (fn-jrec-bodies js) expected)))
  :hints (("Goal" :induct (fn-config-aware-loop node cfg reserved ceiling js
                                                expected)
           :in-theory (e/d (fn-replay-loop)
                           (fn-node-statep fn-replay-apply-record
                            fn-jrec-p fn-record-p fn-record-sequence)))))

(defthm fn-config-aware-replay-is-fn-replay-on-transaction-only-histories
  (implies (and (fn-jrec-listp js) (fn-jrec-article-onlyp js))
           (equal (fn-config-aware-result
                   (fn-config-aware-replay groups capacity reserved ceiling
                                           js))
                  (fn-replay groups capacity (fn-jrec-bodies js))))
  :hints (("Goal"
           :in-theory (e/d (fn-replay)
                           (fn-node-statep fn-config-aware-loop
                            fn-replay-loop fn-node-initial-state
                            fn-jrec-listp fn-jrec-article-onlyp)))))

; The mirror direction: on a configuration-only history the configuration this
; loop reaches is the one `fn-config-replay' reaches.

(defthm fn-config-aware-loop-is-fn-config-replay-on-config-only-histories
  ; On a refused record the two loops report differently by design: this loop
  ; keeps the last good configuration beside the fault, `fn-config-replay-loop'
  ; returns `:fault'.  So the agreement is over histories the configuration
  ; replay accepts; the refusal tooth is in tests/acl2/config-tests.lisp.
  (implies (and (fn-jrec-listp js)
                (fn-jrec-config-onlyp js)
                (fn-node-statep node)
                (fn-jrec-sequences-from js expected)
                (not (equal (fn-config-replay-loop cfg reserved ceiling
                                                   (fn-jrec-bodies js))
                            :fault)))
           (equal (fn-config-aware-config
                   (fn-config-aware-loop node cfg reserved ceiling js
                                         expected))
                  (fn-config-replay-loop cfg reserved ceiling
                                         (fn-jrec-bodies js))))
  :hints (("Goal" :induct (fn-config-aware-loop node cfg reserved ceiling js
                                                expected)
           :in-theory (e/d (fn-config-replay-loop)
                           (fn-node-statep fn-replay-apply-record
                            fn-jrec-p fn-cfg-record-acceptablep)))))

; -----------------------------------------------------------------------------
; Export theory.  The keystones and the record lemmas stay enabled; the
; recognizers, the loop and the entry point are proof vocabulary.

(deftheory fn-jrec-vocabulary
  '((:d fn-jrec-p) (:d fn-jrec-listp) (:d fn-jrec-article-onlyp)
    (:d fn-jrec-config-onlyp) (:d fn-jrec-bodies) (:d fn-jrec-sequences-from)
    (:d fn-config-aware-loop) (:d fn-config-aware-replay)
    (:d fn-config-aware-result) (:d fn-config-aware-config)))

(in-theory (disable (:d fn-jrec-p) (:d fn-jrec-listp)
                    (:d fn-jrec-article-onlyp) (:d fn-jrec-config-onlyp)
                    (:d fn-jrec-bodies) (:d fn-jrec-sequences-from) (:d fn-config-aware-loop)
                    (:d fn-config-aware-replay)
                    (:d fn-config-aware-result) (:d fn-config-aware-config)))
