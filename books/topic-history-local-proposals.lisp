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

; The owner host calls this one logical dispatcher.  The operation and source
; sequence arrive through the bounded local control grammar; neither carries
; an authorship verdict or source bytes.
(defun fn-th-local-propose (operation projection txid source-sequence
                                     observed-uid entropy-id quota)
  (declare (xargs :guard t))
  (case operation
    (:install (fn-th-local-propose-install projection txid observed-uid
                                           entropy-id))
    (:anchor (fn-th-local-propose-anchor projection txid source-sequence
                                         observed-uid quota))
    (:report (fn-th-local-propose-report projection txid source-sequence))
    (otherwise (fn-stmt-error :operation))))

(defthm fn-th-local-propose-anchor-requires-earlier-accepted-source
  (implies (and (equal operation :anchor)
                (fn-stmt-okp
                 (fn-th-local-propose operation projection txid source-sequence
                                      observed-uid entropy-id quota)))
           (fn-th-prefix-find-accepted-sequence
            source-sequence (fn-th-at 3 projection)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-th-local-propose))))

(defthm fn-th-local-propose-report-requires-earlier-accepted-source
  (implies (and (equal operation :report)
                (fn-stmt-okp
                 (fn-th-local-propose operation projection txid source-sequence
                                      observed-uid entropy-id quota)))
           (fn-th-prefix-find-accepted-sequence
            source-sequence (fn-th-at 3 projection)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-th-local-propose))))

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

; The owner-called dispatcher emits the version-2 shape for a fresh anchor.
; The installed event is carried by the completed Store prefix, not supplied
; by the control command or reconstructed from the current process UID.
(defthm fn-th-local-propose-anchor-binds-install-generation
  (implies (and (equal operation :anchor)
                (fn-stmt-okp
                 (fn-th-local-propose operation projection txid
                                      source-sequence observed-uid
                                      entropy-id quota)))
           (let ((event (fn-stmt-value
                         (fn-th-local-propose operation projection txid
                                              source-sequence observed-uid
                                              entropy-id quota)))
                 (installed (fn-th-at 5 projection)))
             (and (fn-th-local-admin-eventp installed)
                  (equal (len event) 9)
                  (equal (fn-th-at 7 event) (fn-th-at 5 installed))
                  (equal (fn-th-at 8 event) (fn-th-at 3 installed)))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-th-local-propose fn-th-local-propose-anchor)
                (fn-th-prepare-anchor-local
                 fn-th-prefix-find-accepted-sequence fn-stxk-find))
           :use ((:instance fn-th-prepare-anchor-local-binds-installation
                            (sequence (fn-th-at 1 projection))
                            (generation txid)
                            (accepted
                             (fn-th-prefix-find-accepted-sequence
                              source-sequence (fn-th-at 3 projection)))
                            (snapshot
                             (and (fn-th-prefix-find-accepted-sequence
                                   source-sequence (fn-th-at 3 projection))
                                  (fn-stxk-find
                                   (fn-stxa-keyring-generation
                                    (fn-th-prefix-find-accepted-sequence
                                     source-sequence (fn-th-at 3 projection)))
                                   (fn-th-at 2 projection))))
                            (installed (fn-th-at 5 projection))
                            (anchors (fn-th-at 4 projection)))))))

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

; This is the dispatcher called by fn-owner-topic-propose. A replayed status
; can only arise after selecting the earlier exact T10 accepted source and
; its pinned keyring snapshot; it carries the retained admission, not a new
; Store event or caller-supplied report identity.
(defthm fn-th-local-propose-report-retry-is-historical
  (implies
   (and (equal operation :report)
        (equal (car (fn-th-local-propose
                     operation projection txid source-sequence
                     observed-uid entropy-id quota))
               :replayed-historical))
   (let* ((accepted
           (fn-th-prefix-find-accepted-sequence
            source-sequence (fn-th-at 3 projection)))
          (snapshot
           (and accepted
                (fn-stxk-find (fn-stxa-keyring-generation accepted)
                              (fn-th-at 2 projection))))
          (selected (fn-th-select-accepted-event accepted snapshot))
          (report (fn-th-at 0 (fn-stmt-value selected)))
          (anchor (fn-th-find-anchor (fn-th-at 1 report)
                                     (fn-th-at 4 projection)))
          (prior (fn-th-find-admission
                  (fn-stxa-authored-id accepted)
                  (fn-th-anchor-reports anchor))))
     (and accepted snapshot (fn-stmt-okp selected) prior
          (equal (fn-th-local-propose
                  operation projection txid source-sequence
                  observed-uid entropy-id quota)
                 (list :replayed-historical prior)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-th-report-retry-returns-retained-admission
                            (sequence (fn-th-at 1 projection))
                            (generation txid)
                            (accepted (fn-th-prefix-find-accepted-sequence
                                       source-sequence (fn-th-at 3 projection)))
                            (snapshot
                             (and (fn-th-prefix-find-accepted-sequence
                                   source-sequence (fn-th-at 3 projection))
                                  (fn-stxk-find
                                   (fn-stxa-keyring-generation
                                    (fn-th-prefix-find-accepted-sequence
                                     source-sequence (fn-th-at 3 projection)))
                                   (fn-th-at 2 projection))))
                            (anchors (fn-th-at 4 projection))))
           :in-theory
           (e/d (fn-th-local-propose fn-th-local-propose-report)
                (fn-th-prepare-report fn-th-select-accepted-event
                 fn-th-prefix-find-accepted-sequence fn-stxk-find
                 fn-th-find-anchor fn-th-find-admission)))))
