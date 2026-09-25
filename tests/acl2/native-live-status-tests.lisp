; Teeth for books/native-live-status: the live report is the offline report
; of the same state, and the owner's pages join to the report.  The owner
; state is owner-store-budget-tests' host-shaped one: one committed article
; (so bytes-used and the retention pin are not zero).
(in-package "ACL2")
(include-book "../../books/native-live-status")
(include-book "../../books/owner-store-budget")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defconst *nlst-groups* '("fn.letters" "fn.test"))
(defconst *nlst-config*
  (fn-config-replay 0 (fn-cnode-line-ceiling)
                    (list *fn-cfg-default-record*)))
(defconst *nlst-post-config*
  (fn-inj-make-config
   t '(102 110 46 111 112 99 46 105 110 118 97 108 105 100)
   (list (fn-nntp-string-octets "fn.letters")
         (fn-nntp-string-octets "fn.test"))
   32768))
(defconst *nlst-first*
  (fn-record-make 0 0 0 "<nlst-first@example.invalid>" '(65 66)
                  *nlst-groups* "nlst-pin-1" "nlst-subject-1"
                  "nlst-release-1" 2 841000000))
(defun nlst-run (oc events)
  (declare (xargs :guard (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
                  :verify-guards nil))
  (if (consp events)
      (nlst-run (fn-ocfg-step oc (car events)) (cdr events))
    oc))
(defconst *nlst-reserve-events*
  '((:store (:io :start-frontier nil))
    (:store (:io :frontier-file :ok))
    (:store (:io :frontier-replace :ok))
    (:store (:io :frontier-directory :ok))))
(defconst *nlst-0*
  (fn-ocfg-make
   (fn-own-configure (fn-own-start (fn-sn-initial *nlst-groups* 10) 3)
                     *nlst-post-config*)
   *nlst-config* nil nil))
(defconst *nlst-oc*
  (fn-ocfg-step
   (nlst-run (fn-opc-prepare (nlst-run *nlst-0* *nlst-reserve-events*) *nlst-first*)
             '((:store (:io :record-file :ok))
               (:store (:io :record-link :ok))
               (:store (:io :record-directory :ok))))
   '(:complete)))
(defconst *nlst-s* (fn-own-store (fn-ocfg-owner *nlst-oc*)))
(defconst *nlst-profile* (fn-bs-config-for-profile :development))
(defconst *nlst-obs* '(nil nil (:full-replay :no-checkpoint)))
; The carried sum as the owner leaves it after its first verdict: every
; committed record, counted once.
; A defconst cannot call an attached function (:DOC ignored-attachment), and
; the record octets go through the record encoder's attachment: these are
; functions, evaluated by the assertions.
(defun nlst-cache ()
  (declare (xargs :verify-guards nil))
  (cons (len (fn-sf-records (fn-sn-files *nlst-s*)))
        (fn-sbud-record-octets (fn-sf-records (fn-sn-files *nlst-s*)))))

; Reachable and not degenerate: one committed record, one article, one
; retention pin, and the cache is the one the owner keeps.
(assert-event (equal (fn-sbud-used *nlst-s*) 1))
(assert-event (posp (fn-sbud-bytes-used *nlst-s*)))
(assert-event (equal (len (fn-retain-pins (fn-nls-retention *nlst-s*))) 1))
(assert-event (fn-sbud-octets-cache-validp (nlst-cache)
                                           (fn-sf-records (fn-sn-files *nlst-s*))))
(assert-event (null (fn-ocfg-pins *nlst-oc*)))

; The keystone's instance: every kind, live equals offline.
(assert-event
 (equal (fn-nls-live-report :status *nlst-profile* *nlst-oc* (nlst-cache) *nlst-obs*)
        (fn-nls-offline-report :status *nlst-profile* *nlst-s*
                               (fn-ocfg-config *nlst-oc*) *nlst-obs*)))
(assert-event
 (equal (fn-nls-live-report :obligations *nlst-profile* *nlst-oc* (nlst-cache) *nlst-obs*)
        (fn-nls-offline-report :obligations *nlst-profile* *nlst-s*
                               (fn-ocfg-config *nlst-oc*) *nlst-obs*)))
; The words: the status report opens with the committed count and article.
(assert-event
 (equal (take 28 (fn-nls-offline-report :status *nlst-profile* *nlst-s*
                                        (fn-ocfg-config *nlst-oc*) *nlst-obs*))
        (fn-record-string-octets "transactions=1 articles=1 st")))
(assert-event
 (equal (take 29 (fn-nls-offline-report :obligations *nlst-profile* *nlst-s*
                                        (fn-ocfg-config *nlst-oc*) *nlst-obs*))
        (fn-record-string-octets "obligations=1 reserved=2
obli")))

; Without a valid carried sum the words differ: a stale sum of 5 octets too
; many is printed as bytes-used.
(defun nlst-stale ()
  (declare (xargs :verify-guards nil))
  (cons (car (nlst-cache)) (+ 5 (cdr (nlst-cache)))))
(assert-event (not (fn-sbud-octets-cache-validp
                    (nlst-stale) (fn-sf-records (fn-sn-files *nlst-s*)))))
(assert-event
 (not (equal (fn-nls-live-report :status *nlst-profile* *nlst-oc* (nlst-stale) *nlst-obs*)
             (fn-nls-offline-report :status *nlst-profile* *nlst-s*
                                    (fn-ocfg-config *nlst-oc*) *nlst-obs*))))
(must-fail
 (defthm nlst-live-is-offline-without-a-valid-sum
   (equal (fn-nls-live-report :status *nlst-profile* *nlst-oc* (nlst-stale) *nlst-obs*)
          (fn-nls-offline-report :status *nlst-profile* *nlst-s*
                                 (fn-ocfg-config *nlst-oc*) *nlst-obs*))
   :rule-classes nil))

; With a connection open the owner's pins report names it; offline has none.
(defconst *nlst-connected*
  (fn-ocfg-make (fn-ocfg-owner *nlst-oc*) (fn-ocfg-config *nlst-oc*)
                (list (cons 0 (fn-ocfg-config *nlst-oc*))) nil))
(assert-event
 (not (equal (fn-nls-live-report :pins *nlst-profile* *nlst-connected* (nlst-cache) *nlst-obs*)
             (fn-nls-offline-report :pins *nlst-profile* *nlst-s*
                                    (fn-ocfg-config *nlst-oc*) *nlst-obs*))))
(must-fail
 (defthm nlst-live-is-offline-with-a-connection
   (equal (fn-nls-live-report :pins *nlst-profile* *nlst-connected* (nlst-cache) *nlst-obs*)
          (fn-nls-offline-report :pins *nlst-profile* *nlst-s*
                                 (fn-ocfg-config *nlst-oc*) *nlst-obs*))
   :rule-classes nil))

; ---------------------------------------------------------------------------
; The exchange

(defun nlst-report ()
  (declare (xargs :verify-guards nil))
  (fn-nls-offline-report :status *nlst-profile* *nlst-s*
                         (fn-ocfg-config *nlst-oc*) *nlst-obs*))
(assert-event (equal (fn-nls-request-decode (fn-nls-request-encode :obligations 7))
                     '(:live-status :obligations 7)))
(assert-event (equal (car (fn-nls-request-decode
                           (cons 0 (cdr (fn-nls-request-encode :status 0)))))
                     :refused))
; One page: the client's fold from nothing is the report.
(assert-event
 (equal (fn-nls-client-step nil nil nil (fn-nls-reply (nlst-report) 0))
        (list :done (nlst-report))))
; Two pages: a report one octet past the chunk width.
(defconst *nlst-long*
  (make-list (1+ *fn-nls-chunk-octets*) :initial-element 65))
(assert-event
 (let ((first (fn-nls-client-step nil nil nil (fn-nls-reply *nlst-long* 0))))
   (and (equal (car first) :next)
        (equal (len (second first)) *fn-nls-chunk-octets*)
        (equal (fn-nls-client-step (second first) (third first) (fourth first)
                                   (fn-nls-reply *nlst-long* *fn-nls-chunk-octets*))
               (list :done *nlst-long*)))))

; Each hypothesis of fn-nls-client-step-of-owner-reply, dropped.
; An octet past 255 is no report: the owner refuses the page.
(assert-event (equal (fn-nls-client-step nil nil nil (fn-nls-reply '(256) 0))
                     '(:refused)))
(must-fail
 (defthm nlst-step-without-octets
   (equal (fn-nls-client-step nil nil nil (fn-nls-reply '(256) 0))
          (list :done '(256)))
   :rule-classes nil))
; A client holding what is not a prefix joins it to the owner's rest.
(assert-event (equal (fn-nls-client-step '(1) 2 (fn-frame-trailer '(2 3))
                                         (fn-nls-reply '(2 3) 1))
                     '(:done (1 3))))
(must-fail
 (defthm nlst-step-without-prefix
   (equal (fn-nls-client-step '(1) 2 (fn-frame-trailer '(2 3))
                              (fn-nls-reply '(2 3) 1))
          (list :done '(2 3)))
   :rule-classes nil))
; A client past the report is refused.
(assert-event (equal (fn-nls-client-step '(2 3 4) 2 (fn-frame-trailer '(2 3))
                                         (fn-nls-reply '(2 3) 3))
                     '(:refused)))
(must-fail
 (defthm nlst-step-without-length
   (equal (fn-nls-client-step '(2 3 4) 2 (fn-frame-trailer '(2 3))
                              (fn-nls-reply '(2 3) 3))
          (list :done '(2 3)))
   :rule-classes nil))
; A total that is not this report's restarts.
(assert-event
 (equal (fn-nls-client-step '(2) 5 (fn-frame-trailer '(2 3))
                            (fn-nls-reply '(2 3) 1))
        '(:restart)))
(must-fail
 (defthm nlst-step-without-same-report
   (equal (fn-nls-client-step '(2) 5 (fn-frame-trailer '(2 3))
                              (fn-nls-reply '(2 3) 1))
          (list :done '(2 3)))
   :rule-classes nil))
; The uint32 total: no report that long can be evaluated here, so the
; tooth is the keystone without it, under the keystone's own hints, which
; ACL2 does not prove (the reply cannot carry the total).
(must-fail
 (defthm nlst-step-without-uint32-total
   (implies (and (fn-cbor-octet-listp report)
                 (<= (len acc) (len report))
                 (equal acc (take (len acc) report))
                 (not (consp acc)))
            (equal (fn-nls-client-step acc total digest (fn-nls-reply report (len acc)))
                   (if (<= (len report) (+ (len acc) *fn-nls-chunk-octets*))
                       (list :done report)
                     (list :next (take (+ (len acc) *fn-nls-chunk-octets*) report)
                           (len report) (fn-frame-trailer report)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-nls-client-step fn-nls-page-width fn-record-uint32p)
                            (fn-nls-reply fn-nls-reply-encode fn-nls-reply-decode
                             fn-frame-trailer take nthcdr fn-cbor-encode
                             fn-record-item-encode))))))
