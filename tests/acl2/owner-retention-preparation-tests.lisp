; Actual configured-owner retention prepare: prepared, refused and premise tooth.
(in-package "ACL2")
(include-book "../../books/owner-retention-preparation")
(include-book "std/testing/must-fail" :dir :system)

(defconst *orpr-config*
  (fn-config-replay 0 (fn-cnode-line-ceiling)
                    (list *fn-cfg-default-record*)))
(defconst *orpr-post-config*
  (fn-inj-make-config
   t '(102 110 46 111 112 114 46 105 110 118 97 108 105 100)
   (list '(102 110 46 116 101 115 116)) 32768))
(defconst *orpr-0*
  (fn-ocfg-make
   (fn-own-configure
    (fn-own-start (fn-sn-initial '("fn.test") 10) 2)
    *orpr-post-config*)
   *orpr-config* nil nil))

(defun orpr-run (oc events)
  (if (consp events)
      (orpr-run (fn-ocfg-step oc (car events)) (cdr events))
    oc))

(defconst *orpr-reserved*
  (orpr-run *orpr-0*
            '((:store (:io :start-frontier nil))
              (:store (:io :frontier-file :ok))
              (:store (:io :frontier-replace :ok))
              (:store (:io :frontier-directory :ok)))))

(defun orpr-event (oc kind charge)
  (let* ((s (fn-own-store (fn-ocfg-owner oc)))
         (txid (fn-state-next-txid (fn-node-acceptance (fn-sn-node s)))))
    (fn-store-retention-event-make
     kind (fn-sn-identity-next s) txid txid
     (fn-record-octets-string '(111 98 108))
     (fn-record-octets-string '(115 117 98))
     (fn-record-octets-string '(101 118 105)) charge)))

(defun orpr-conclusionp (oc kind charge)
  (let* ((s (fn-own-store (fn-ocfg-owner oc)))
         (event (orpr-event oc kind charge))
         (next (fn-ocfg-step oc
                             (list :store (list :prepare-retention event))))
         (prepared (fn-own-store (fn-ocfg-owner next))))
    (and (equal prepared (fn-sn-prepare-retention s event))
         (if (equal prepared s)
             (not (equal (fn-sf-phase (fn-sn-files prepared))
                         :record-staged))
           (and (equal (fn-sf-phase (fn-sn-files prepared))
                       :record-staged)
                (equal (fn-sf-record-candidate (fn-sn-files prepared))
                       event))))))

; A related, reserved owner stages the actual ACL2-built undertaking.
(assert-event (fn-ocfg-statep *orpr-reserved*))
(assert-event
 (equal (fn-sf-phase
         (fn-sn-files (fn-own-store (fn-ocfg-owner *orpr-reserved*))))
        :reserved))
(assert-event
 (let* ((event (orpr-event *orpr-reserved* :undertake 1))
        (prepared (fn-ocfg-step
                   *orpr-reserved*
                   (list :store (list :prepare-retention event))))
        (s (fn-own-store (fn-ocfg-owner prepared))))
   (and (fn-store-retention-event-p event)
        (not (equal s (fn-own-store (fn-ocfg-owner *orpr-reserved*))))
        (orpr-conclusionp *orpr-reserved* :undertake 1)
        (equal (fn-sf-record-candidate (fn-sn-files s)) event))))

; A syntactically valid release with no undertaking is refused by the model.
(assert-event
 (let* ((event (orpr-event *orpr-reserved* :release 0))
        (next (fn-ocfg-step
               *orpr-reserved*
               (list :store (list :prepare-retention event)))))
   (and (fn-store-retention-event-p event)
        (equal (fn-own-store (fn-ocfg-owner next))
               (fn-own-store (fn-ocfg-owner *orpr-reserved*)))
        (orpr-conclusionp *orpr-reserved* :release 0))))

; The reserved-phase premise matters: on an already staged owner, refusal
; leaves :record-staged in place and the unconditional conclusion is false.
(assert-event
 (let* ((event (orpr-event *orpr-reserved* :undertake 1))
        (staged (fn-ocfg-step
                 *orpr-reserved*
                 (list :store (list :prepare-retention event)))))
   (and (not (equal
              (fn-sf-phase
               (fn-sn-files (fn-own-store (fn-ocfg-owner staged))))
              :reserved))
        (not (orpr-conclusionp staged :undertake 1)))))
(must-fail
 (assert-event
  (let* ((event (orpr-event *orpr-reserved* :undertake 1))
         (staged (fn-ocfg-step
                  *orpr-reserved*
                  (list :store (list :prepare-retention event)))))
    (orpr-conclusionp staged :undertake 1))))
