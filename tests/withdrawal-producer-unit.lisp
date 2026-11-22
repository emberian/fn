; Drive the existing owner control admission and APPEND request path. The
; assertions inspect published rows produced by those requests.
(in-package "ACL2")
(include-book "consumer-session-support")

(defconst *fn2-wpu-profile*
  (put-assoc-equal :groups '(("local.test" . 11) ("local.other" . 22) ("control.cancel" . 33))
                   *fn2-ccu-profile*))

(defun fn2-wpu-article (groups mid control)
  (declare (xargs :verify-guards nil))
  (fn2-cw-crlf-octets
   (append (list "From: writer@example.invalid" "Subject: withdrawal control"
                 (concatenate 'string "Newsgroups: " groups)
                 (concatenate 'string "Message-ID: " mid))
           (if control (list (concatenate 'string "Control: cancel " control)) nil)
           (list "" "body"))))

(defun fn2-wpu-values (fields fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (endp fields) nil
    (mv-let (code v) (fn2-read-value 0 (car fields) fn2-core)
      (cons (if (eq code :ok) v code) (fn2-wpu-values (cdr fields) fn2-core)))))

(defun fn2-wpu-read (schema key second-key fields fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* (((mv rc fn2-core) (fn2-read-release 0 fn2-core))
       ((unless (eq rc :ok)) (mv (list :release rc) fn2-core))
       ((mv rc fn2-core) (fn2-read-key 0 :lo 0 key fn2-core))
       ((unless (eq rc :ok)) (mv (list :key rc) fn2-core))
       ((mv rc fn2-core)
        (if second-key (fn2-read-key 0 :lo 1 second-key fn2-core) (mv :ok fn2-core)))
       ((unless (eq rc :ok)) (mv (list :second-key rc) fn2-core))
       ((mv code fn2-core) (fn2-cns-lookup-loop 32 0 schema fn2-core)))
    (mv (if (eq code :ok) (fn2-wpu-values fields fn2-core) (list :read code)) fn2-core)))

(defun fn2-wpu-run ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core)
      (b* ((target "<withdraw-target@example.invalid>")
           (fn2-core (fn2-init-executor *fn2-wpu-profile* :echo nil fn2-core))
           ((mv epoch fn2-core)
            (stobj-let ((fn2-extents (fn2-core-extents fn2-core)))
              (code fn2-extents)
              (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
           ((mv status wire store fn2-core)
            (fn2-ccu-session 0
              (list (fnc-append 81 (fn2-wpu-article "local.other" "<withdraw-seed@example.invalid>" nil))
                    (fnc-append 82 (fn2-wpu-article "local.test,local.other" target nil))
                    (fnc-append 83 (fn2-wpu-article "control.cancel" "<withdraw-cause@example.invalid>" target))
                    (fnc-control 5))
              fn2-core))
           (replies (fnc-replies '(append append append) wire))
           ((mv report-one fn2-core)
            (fn2-wpu-read *fn2-withdrawals-sid* 11 3
              (list *fn2-withdrawals-entry-field-article* *fn2-withdrawals-entry-field-number*) fn2-core))
           ((mv report-two fn2-core)
            (fn2-wpu-read *fn2-withdrawals-sid* 22 3
              (list *fn2-withdrawals-entry-field-article* *fn2-withdrawals-entry-field-number*) fn2-core))
           ((mv target-row fn2-core)
            (fn2-wpu-read *fn2-txn-article-sid* 2 nil
              (list *fn2-article-entry-field-birth* *fn2-article-entry-field-state*
                    *fn2-article-entry-field-version*) fn2-core))
           ((mv group-one fn2-core)
            (fn2-wpu-read *fn2-txn-counts-sid* 11 nil
              (list *fn2-group-counts-entry-field-count* *fn2-group-counts-entry-field-high*) fn2-core))
           ((mv group-two fn2-core)
            (fn2-wpu-read *fn2-txn-counts-sid* 22 nil
              (list *fn2-group-counts-entry-field-count* *fn2-group-counts-entry-field-high*) fn2-core)))
        (mv (list epoch status replies (consp store) (fn2-core-stop-reason fn2-core)
                  report-one report-two target-row group-one group-two)
            fn2-core))
      result)))

(assert-event
 (equal (fn2-wpu-run)
        '(:ok :quiet ((:accepted "" (1 1)) (:accepted "" (2 1)) (:accepted "" (3 1))) t 0
          (2 1) (2 2) (2 1 2) (0 1) (1 2))))
