; Teeth for the current alphabet under import-of-export (PRF-205,
; fn-sxp-import-of-export-replays-the-same-history; lane closure-theorems-2,
; row X2).  store-export-tests' archive holds four store event kinds; this
; one holds every arm of fn-store-event-encode (article, retention undertake
; and release, verdict, keyring snapshot, accepted composite, consumer
; event, topic event) and configuration files whose octets are encoded
; :set-limit and :withdraw-article records -- the two configuration kinds
; the alphabet check found added last.  The keystone's antecedent is
; asserted literally, then its conclusion.
(in-package "ACL2")
(include-book "store-export-tests")
(include-book "topic-history-local-admin-tests")
(include-book "../../books/config")

; One event of each remaining kind, sequences 6 7 8 9 (after sxpt's 0 1 2 4 5),
; txids 5 6 7 8.
(defconst *cxt-verdict*
  (fn-stxe-make 6 5 1 "<cxt-6@example.invalid>" :unverified
                '(117 110 118 101 114 105 102 105 101 100) 7 '(116 101 115 116)))
(defconst *cxt-keyring* (fn-stxk-make 7 6 1 7 '(116 101 115 116) '(1 2 3 4)))
(defconst *cxt-accepted*
  (fn-stxa-make 8 7 1 0 '(112) (fn-record-string-octets "s3")
                (fn-record-encode-impl (car *sxpt-events*))
                (fn-stxe-encode *cxt-verdict*)))
(defconst *cxt-topic-source* *thla-install*)

(defun cxt-with-sequence (event sequence txid)
  ; A topic event carries its own sequence and txid at positions 1 and 2
  ; (fn-th-topic-event-items); the fixture's install is renumbered.
  (declare (xargs :guard t :verify-guards nil))
  (if (and (consp event) (consp (cdr event)) (consp (cddr event)))
      (list* (car event) sequence txid (cdddr event))
    event))

(defconst *cxt-topic* (cxt-with-sequence *cxt-topic-source* 9 8))

(defconst *cxt-events*
  (append *sxpt-events*
          (list *cxt-verdict* *cxt-keyring* *cxt-accepted* *cxt-topic*)))

; Every arm of the encoder is taken exactly once, by its recognizer.
(assert-event (fn-record-p (nth 0 *cxt-events*)))
(assert-event (and (fn-store-retention-event-p (nth 1 *cxt-events*))
                   (fn-store-retention-event-p (nth 2 *cxt-events*))))
(assert-event (and (fn-cpe-eventp (nth 3 *cxt-events*)) (fn-cpe-eventp (nth 4 *cxt-events*))))
(assert-event (fn-stxe-p *cxt-verdict*))
(assert-event (fn-stxk-p *cxt-keyring*))
(assert-event (fn-stxa-p *cxt-accepted*))
(assert-event (fn-th-topic-eventp *cxt-topic*))
(assert-event (and (consp (fn-store-event-encode *cxt-verdict*))
                   (consp (fn-store-event-encode *cxt-keyring*))
                   (consp (fn-store-event-encode *cxt-accepted*))
                   (consp (fn-store-event-encode *cxt-topic*))))

; The four new kinds decode exactly to themselves.
(assert-event
 (let ((d (fn-store-event-decode-exact (fn-store-event-encode *cxt-verdict*))))
   (and (fn-stmt-okp d) (equal (fn-stmt-value d) *cxt-verdict*))))
(assert-event
 (let ((d (fn-store-event-decode-exact (fn-store-event-encode *cxt-keyring*))))
   (and (fn-stmt-okp d) (equal (fn-stmt-value d) *cxt-keyring*))))
(assert-event
 (let ((d (fn-store-event-decode-exact (fn-store-event-encode *cxt-accepted*))))
   (and (fn-stmt-okp d) (equal (fn-stmt-value d) *cxt-accepted*))))
(assert-event
 (let ((d (fn-store-event-decode-exact (fn-store-event-encode *cxt-topic*))))
   (and (fn-stmt-okp d) (equal (fn-stmt-value d) *cxt-topic*))))

; The archive: sealed frames at sequences 0 1 2 4 5 6 7 8 9, and two
; configuration files whose octets are encoded records of the two kinds.
(make-event
 `(defconst *cxt-records*
    ',(pairlis$ '(0 1 2 4 5 6 7 8 9) (sxpt-frames *cxt-events*))))
(defconst *cxt-limit-record*
  (fn-cfg-record-make 1 9 1 (list (fn-cfg-set-limit "max-transactions" 100))
                      *fn-cfg-default-stamp*))
(defconst *cxt-withdraw-record*
  (fn-cfg-record-make 2 10 1
                      (list (fn-cfg-withdraw-article "operator" "<sxpt-0@example.invalid>"
                                                     "evidence"))
                      *fn-cfg-default-stamp*))
(make-event
 `(defconst *cxt-configs*
    ',(list (cons "config-00001" (fn-cfg-encode *cxt-limit-record*))
            (cons "config-00002" (fn-cfg-encode *cxt-withdraw-record*)))))
(make-event
 `(defconst *cxt-manifest*
    ',(fn-sxp-manifest (fn-sxp-entries *sxpt-profile* *sxpt-frontier*
                                       *cxt-configs* *cxt-records*))))

; The configuration files decode exactly (:ok record ...) to records of the
; two kinds.
(assert-event
 (let ((limit (fn-cfg-decode-exact (cdr (assoc-equal "config-00001" *cxt-configs*))))
       (withdraw (fn-cfg-decode-exact (cdr (assoc-equal "config-00002" *cxt-configs*)))))
   (and (equal (car limit) :ok) (equal (cadr limit) *cxt-limit-record*)
        (equal (car withdraw) :ok) (equal (cadr withdraw) *cxt-withdraw-record*)
        (equal (fn-cfg-delta-kind (car (fn-cfg-record-change *cxt-limit-record*))) :set-limit)
        (equal (fn-cfg-delta-kind (car (fn-cfg-record-change *cxt-withdraw-record*)))
               :withdraw-article))))

; fn-sxp-import-of-export-replays-the-same-history: the antecedent, literally.
(assert-event (fn-bs-profile-logp *fn-bs-profile-development*))
(assert-event (fn-sxp-increasingp *cxt-records*))
(assert-event (fn-sxp-config-names-increasingp *cxt-configs* nil))

; And its conclusion: the import of the export is the same history.
(assert-event
 (equal (fn-sxp-import-plan *cxt-manifest* *sxpt-profile* *sxpt-frontier*
                            *cxt-configs* *cxt-records* '(:current nil))
        (list :import *fn-bs-profile-development* *sxpt-frontier*
              *cxt-configs* *cxt-records*)))
