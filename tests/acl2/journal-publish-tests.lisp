(in-package "ACL2")
(include-book "../../books/journal-publish")
(include-book "../../books/app-journal")
(include-book "must-fail-checked")
(include-book "../../books/codec-attach")

(defconst *fn-t-jpub-link-window*
  (fn-jpub-step
   (fn-jpub-step
    (fn-jpub-step (fn-jpub-initial t) '(:stage-result :ok))
    '(:file-barrier-result :ok))
   '(:link-begin)))

(assert-event (equal (fn-jpub-phase *fn-t-jpub-link-window*) :link-attempted))
(assert-event
 (equal (fn-jpub-outcome
         (fn-jpub-step *fn-t-jpub-link-window* '(:link-result :error)))
        :uncertain))
(assert-event
 (equal (fn-jpub-outcome
         (fn-jpub-step *fn-t-jpub-link-window* '(:link-result :exists)))
        :refused))

(defconst *fn-t-jpub-dir-window*
  (fn-jpub-step *fn-t-jpub-link-window* '(:link-result :ok)))
(assert-event
 (equal (fn-jpub-outcome
         (fn-jpub-step *fn-t-jpub-dir-window*
                       '(:directory-barrier-result :error)))
        :uncertain))
(assert-event
 (equal (fn-jpub-outcome
         (fn-jpub-step *fn-t-jpub-dir-window*
                       '(:directory-barrier-result :ok)))
        :durable))

; Teeth: without established authority an apparent EEXIST is never a known
; refusal, and without the directory barrier the conclusion is not durable.
(must-fail-checked
 (assert-event
  (equal (fn-jpub-outcome
          (fn-jpub-step (fn-jpub-state :link-attempted nil nil)
                        '(:link-result :exists)))
         :refused)))
(must-fail-checked
 (assert-event (equal (fn-jpub-crash-outcome *fn-t-jpub-dir-window*) :durable)))

;; The application frontier owns the filename and the admission/capacity
;; decision.  Recovery accepts only ACL2's exact next name, and a resolution
;; reservation accounts for both the intent and its maximum-sized outcome.
(defconst *fn-t-aj-empty* (fn-aj-initial :workflow (fn-ajpf-default)))
(defconst *fn-t-aj-config-op*
  (fn-aj-authorize *fn-t-aj-empty* :config 100 nil t t))
(assert-event (fn-aj-operationp *fn-t-aj-config-op*))
(assert-event
 (equal (fn-aj-operation-name *fn-t-aj-config-op*)
        "00000000000000000000.wf"))
(assert-event
 (equal (fn-aj-operation-label *fn-t-aj-config-op*) :config))
(assert-event
 (equal (fn-aj-next (fn-aj-operation-successor *fn-t-aj-config-op*)) 1))
(assert-event
 (equal (fn-aj-recover-record *fn-t-aj-empty*
                              "00000000000000000000.wf" 100 :config)
        (fn-aj-operation-successor *fn-t-aj-config-op*)))
(must-fail-checked
 (assert-event
  (not (equal (fn-aj-recover-record *fn-t-aj-empty*
                                    "00000000000000000001.wf" 100 :config)
              :fault))))
(must-fail-checked
 (assert-event
  (equal (car (fn-aj-authorize *fn-t-aj-empty* :config 100 nil nil t))
         :ok)))

;; The journal's profile (D27, lane caps).  The record count is the
;; operator's: the 4,096-record lifetime is gone, and the default admits
;; 2^20 records.
(assert-event (equal (fn-ajpf-default) '(1048576 1099511627776)))
(assert-event (equal (fn-ajpf-read :workflow nil nil) (fn-ajpf-default)))
(assert-event
 (equal (fn-ajpf-read :receipt t (fn-ajpf-octets :receipt 5 810000))
        '(5 810000)))
;; Outside the relation: under three records, under three widest frames, a
;; text that is not the format, trailing octets, an unknown domain.
(assert-event (null (fn-ajpf-octets :workflow 2 1000000)))
(assert-event (null (fn-ajpf-octets :receipt 5 809999)))
(assert-event (fn-ajpf-octets :receipt 5 810000))
(assert-event
 (null (fn-ajpf-read :workflow t
                     (append (fn-ajpf-octets :workflow 5 1000000) '(0)))))
(assert-event (null (fn-ajpf-read :mail nil nil)))
;; A receipt profile's octets are below a workflow's three receipts: the
;; reading is per domain.
(assert-event
 (null (fn-ajpf-read :receipt t (fn-ajpf-octets :workflow 5 100000))))
;; An empty journal takes any valid profile; one that holds a record is only
;; raised.
(assert-event
 (fn-ajpf-write-octets (fn-aj-initial :workflow (fn-ajpf-default)) 5 100000))
(defconst *fn-t-aj-held* (fn-aj-operation-successor *fn-t-aj-config-op*))
(assert-event
 (null (fn-ajpf-write-octets *fn-t-aj-held* 5 100000)))
(assert-event
 (equal (fn-ajpf-read :workflow t
                      (fn-ajpf-write-octets *fn-t-aj-held* 1048576 1099511627776))
        (fn-ajpf-default)))
(assert-event
 (fn-ajpf-write-octets *fn-t-aj-held* 2000000 1099511627776))
(assert-event
 (null (fn-ajpf-write-octets *fn-t-aj-held* 2000000 1099511627775)))
(assert-event (null (fn-ajpf-write-octets :fault 5 100000)))

;; Walk N records (a configuration, then intents) onto frontier S through
;; recovery, the path an open takes; answer the frontier or the refusal.
(defun fn-t-aj-walk (s n)
  (declare (xargs :measure (nfix n)))
  (if (zp n) s
    (let ((next (fn-aj-recover-record
                 s (fn-aj-record-name (fn-aj-domain s) (fn-aj-next s))
                 100 (if (fn-aj-initializedp s) :intent :config))))
      (if (keywordp next) next (fn-t-aj-walk next (1- n))))))

;; The defect (B003): 4,097 records through the default profile, and the
;; journal keeps going -- the 4,097th recovers and the next is admitted.
(defconst *fn-t-aj-4097* (fn-t-aj-walk *fn-t-aj-empty* 4097))
(assert-event (fn-aj-statep *fn-t-aj-4097*))
(assert-event (equal (fn-aj-next *fn-t-aj-4097*) 4097))
(assert-event
 (equal (fn-aj-record-name :workflow 4097) "00000000000000004097.wf"))
(assert-event
 (equal (car (fn-aj-authorize *fn-t-aj-4097* :intent 100 t t t)) :ok))

;; Teeth: under a profile of five records the sixth is refused by name at
;; recovery (never skipped), and admission refuses an intent whose
;; resolution would not fit.
(defconst *fn-t-aj-five* (fn-aj-initial :workflow '(5 1000000)))
(assert-event
 (equal (fn-aj-next (fn-t-aj-walk *fn-t-aj-five* 5)) 5))
(assert-event (equal (fn-t-aj-walk *fn-t-aj-five* 6) :beyond-profile))
(assert-event
 (equal (car (fn-aj-authorize (fn-t-aj-walk *fn-t-aj-five* 3)
                              :intent 100 t t t))
        :ok))
(must-fail-checked
 (assert-event
  (equal (car (fn-aj-authorize (fn-t-aj-walk *fn-t-aj-five* 4)
                               :intent 100 t t t))
         :ok)))
;; The same records reopened under a raised profile go on.
(assert-event
 (equal (fn-aj-next (fn-t-aj-walk (fn-aj-initial :workflow '(9 1000000)) 6))
        6))
(assert-event (equal (fn-aj-initial :workflow '(2 1000000)) :fault))

(value-triple :journal-publish-tests-passed)
