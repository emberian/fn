; Experimental fixed local operator proposals from the carried Store topic
; projection. The caller names an earlier accepted Store sequence, never
; supplies source octets, a verifier Boolean, or relay headers.
(in-package "ACL2")
(include-book "topic-history-prefix")

(defun fn-th-prefix-find-accepted-sequence (sequence accepted)
  (declare (xargs :guard t :measure (len accepted)))
  (if (consp accepted)
      (if (and (fn-stxa-p (car accepted))
               (equal sequence (fn-stxa-sequence (car accepted))))
          (car accepted)
        (fn-th-prefix-find-accepted-sequence sequence (cdr accepted)))
    nil))

(defun fn-th-local-propose-install (projection txid observed-uid entropy-id)
  (declare (xargs :guard t))
  (if (not (equal (fn-th-at 0 projection) :ok))
      (fn-stmt-error :historical-projection)
    (fn-th-local-admin-install (fn-th-at 1 projection) txid txid
                               observed-uid entropy-id
                               (fn-th-at 5 projection))))

(defun fn-th-local-propose-anchor (projection txid source-sequence
                                             observed-uid quota)
  (declare (xargs :guard t))
  (if (not (and (equal (fn-th-at 0 projection) :ok)
                (fn-record-uint32p source-sequence)))
      (fn-stmt-error :historical-projection)
    (let* ((accepted
            (fn-th-prefix-find-accepted-sequence
             source-sequence (fn-th-at 3 projection)))
           (snapshot
            (and accepted
                 (fn-stxk-find (fn-stxa-keyring-generation accepted)
                               (fn-th-at 2 projection)))))
      (if (not (and accepted snapshot))
          (fn-stmt-error :missing-historical-authorship)
        (fn-th-prepare-anchor-local
         (fn-th-at 1 projection) txid txid accepted snapshot
         observed-uid quota (fn-th-at 5 projection)
         (fn-th-at 4 projection))))))

(defun fn-th-local-propose-report (projection txid source-sequence)
  (declare (xargs :guard t))
  (if (not (and (equal (fn-th-at 0 projection) :ok)
                (fn-record-uint32p source-sequence)))
      (fn-stmt-error :historical-projection)
    (let* ((accepted
            (fn-th-prefix-find-accepted-sequence
             source-sequence (fn-th-at 3 projection)))
           (snapshot
            (and accepted
                 (fn-stxk-find (fn-stxa-keyring-generation accepted)
                               (fn-th-at 2 projection)))))
      (if (not (and accepted snapshot))
          (fn-stmt-error :missing-historical-authorship)
        (fn-th-prepare-report
         (fn-th-at 1 projection) txid txid accepted snapshot
         (fn-th-at 4 projection))))))

(defthm fn-th-local-anchor-proposal-requires-earlier-accepted-source
  (implies (fn-stmt-okp
            (fn-th-local-propose-anchor projection txid source-sequence
                                        observed-uid quota))
           (fn-th-prefix-find-accepted-sequence
            source-sequence (fn-th-at 3 projection)))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-th-local-propose-anchor)
                (fn-th-prepare-anchor-local fn-th-prepare-anchor
                 fn-th-prefix-find-accepted-sequence)))))

(defthm fn-th-local-report-proposal-requires-earlier-accepted-source
  (implies (fn-stmt-okp
            (fn-th-local-propose-report projection txid source-sequence))
           (fn-th-prefix-find-accepted-sequence
            source-sequence (fn-th-at 3 projection)))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-th-local-propose-report)
                (fn-th-prepare-report
                 fn-th-prefix-find-accepted-sequence)))))
