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
   :rule-classes nil
   ;; The keystone's own hints: the ground values go through the record
   ;; encoder's attachment, which a proof cannot evaluate; the assertion
   ;; above evaluates them and shows the two reports differ.
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-sbud-bytes-used-is-kernel-sum
                             (s *nlst-s*) (cache (nlst-cache))))
            :in-theory '(fn-nls-live-report fn-nls-offline-report)))))

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
   :rule-classes nil
   ;; The keystone's own hints: the ground values go through the record
   ;; encoder's attachment, which a proof cannot evaluate; the assertion
   ;; above evaluates them and shows the two reports differ.
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-sbud-bytes-used-is-kernel-sum
                             (s *nlst-s*) (cache (nlst-cache))))
            :in-theory '(fn-nls-live-report fn-nls-offline-report)))))

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

; ---------------------------------------------------------------------------
; The words the operator's values need (PKT-156), the checkpoint file
; (PKT-150) and the open cost (PKT-105).

(defun nlst-prefixp (x y)
  (declare (xargs :guard t))
  (cond ((atom x) t)
        ((atom y) nil)
        (t (and (equal (car x) (car y)) (nlst-prefixp (cdr x) (cdr y))))))
(defun nlst-infixp (x y)
  (declare (xargs :guard t))
  (cond ((nlst-prefixp x y) t)
        ((atom y) nil)
        (t (nlst-infixp x (cdr y)))))

; 2^40 is thirteen digits; the NNTP field renderer answers 0 for it.
(assert-event (equal (fn-nls-nat (expt 2 40))
                     (fn-record-string-octets "1099511627776")))
(assert-event (equal (fn-nntp-decimal-field (expt 2 40)) '(48)))
(assert-event (equal (fn-nls-nat 0) '(48)))
(assert-event (equal (fn-nls-nat (1- (expt 2 64)))
                     (fn-record-string-octets "18446744073709551615")))
(assert-event (equal (fn-nntp-decimal-value (fn-nls-nat (expt 2 40))) (expt 2 40)))
; fn-nls-nat-is-the-decimal-digits without its hypothesis: a value that is
; not a natural renders 0.
(assert-event (equal (fn-nls-nat -5) '(48)))
(must-fail
 (defthm nlst-nat-digits-without-natp
   (equal (fn-nntp-decimal-value (fn-nls-nat -5)) -5)
   :rule-classes nil))
; The profile's history requirement is a word.
(assert-event (equal (fn-nls-field "history-marker" "unmarked")
                     (fn-record-string-octets " history-marker=unmarked")))
(defconst *nlst-big-profile*
  (update-nth 3 (expt 2 40) (fn-bs-config-for-profile :development)))
(assert-event (equal (fn-bs-profile-max-history-octets *nlst-big-profile*)
                     (expt 2 40)))
(defun nlst-status (profile obs)
  (declare (xargs :verify-guards nil))
  (fn-nls-offline-report :status profile *nlst-s* (fn-ocfg-config *nlst-oc*) obs))
(assert-event
 (nlst-infixp (fn-record-string-octets " max-history-octets=1099511627776")
              (nlst-status *nlst-big-profile* *nlst-obs*)))
(assert-event
 (nlst-infixp (fn-record-string-octets " history-marker=")
              (nlst-status *nlst-profile* *nlst-obs*)))
(assert-event
 (not (nlst-infixp (fn-record-string-octets " history-marker=0")
                   (nlst-status *nlst-profile* *nlst-obs*))))

; The checkpoint file the host observed, and its absence.
(defconst *nlst-file-obs* '(nil nil (:checkpoint 3 2) nil (4096 1790000000)))  ; the clock is the fourth element (reclaim-host)
(assert-event
 (nlst-infixp (fn-record-string-octets "
checkpoint-file octets=4096 modified=1790000000
pins=")
              (nlst-status *nlst-profile* *nlst-file-obs*)))
(assert-event
 (nlst-infixp (fn-record-string-octets "
checkpoint-file=absent
pins=")
              (nlst-status *nlst-profile* *nlst-obs*)))
; Live equals offline with the file observed (the keystone's instance).
(assert-event
 (equal (fn-nls-live-report :status *nlst-profile* *nlst-oc* (nlst-cache) *nlst-file-obs*)
        (nlst-status *nlst-profile* *nlst-file-obs*)))

; The pessimistic open cost: every record replayed, 32 octets of list per
; octet of the history bound.
(assert-event
 (nlst-infixp (append (fn-record-string-octets "
open-cost replay-records=")
                      (fn-nls-nat (fn-bs-profile-max-transactions *nlst-big-profile*))
                      (fn-record-string-octets " list-memory-octets=35184372088832
"))
              (nlst-status *nlst-big-profile* *nlst-obs*)))
(assert-event (posp (fn-bs-profile-max-transactions *nlst-big-profile*)))

; ---------------------------------------------------------------------------
; The buffered page (PKT-145)

; fn-nls-page-of-buffer-is-reply has no hypothesis: witnesses only, a
; report, a page past the first, and a refused one.
(assert-event (equal (fn-nls-page (fn-nls-buffer (nlst-report)) 0)
                     (fn-nls-reply (nlst-report) 0)))
(assert-event (equal (fn-nls-page (fn-nls-buffer *nlst-long*) *fn-nls-chunk-octets*)
                     (fn-nls-reply *nlst-long* *fn-nls-chunk-octets*)))
(assert-event (equal (fn-nls-page (fn-nls-buffer '(256)) 0)
                     (fn-nls-reply-encode :refused 0 nil nil)))
; Two pages from one buffer join to the report.
(assert-event
 (let* ((buffer (fn-nls-buffer *nlst-long*))
        (first (fn-nls-client-step nil nil nil (fn-nls-page buffer 0))))
   (and (equal (car first) :next)
        (equal (fn-nls-client-step (second first) (third first) (fourth first)
                                   (fn-nls-page buffer *fn-nls-chunk-octets*))
               (list :done *nlst-long*)))))

; fn-nls-client-step-of-owner-page, each hypothesis dropped.
(must-fail
 (defthm nlst-page-step-without-octets
   (equal (fn-nls-client-step nil nil nil (fn-nls-page (fn-nls-buffer '(256)) 0))
          (list :done '(256)))
   :rule-classes nil))
(assert-event (equal (fn-nls-client-step '(1) 2 (fn-frame-trailer '(2 3))
                                         (fn-nls-page (fn-nls-buffer '(2 3)) 1))
                     '(:done (1 3))))
(must-fail
 (defthm nlst-page-step-without-prefix
   (equal (fn-nls-client-step '(1) 2 (fn-frame-trailer '(2 3))
                              (fn-nls-page (fn-nls-buffer '(2 3)) 1))
          (list :done '(2 3)))
   :rule-classes nil))
(must-fail
 (defthm nlst-page-step-without-length
   (equal (fn-nls-client-step '(2 3 4) 2 (fn-frame-trailer '(2 3))
                              (fn-nls-page (fn-nls-buffer '(2 3)) 3))
          (list :done '(2 3)))
   :rule-classes nil))
(assert-event
 (equal (fn-nls-client-step '(2) 5 (fn-frame-trailer '(2 3))
                            (fn-nls-page (fn-nls-buffer '(2 3)) 1))
        '(:restart)))
(must-fail
 (defthm nlst-page-step-without-same-report
   (equal (fn-nls-client-step '(2) 5 (fn-frame-trailer '(2 3))
                              (fn-nls-page (fn-nls-buffer '(2 3)) 1))
          (list :done '(2 3)))
   :rule-classes nil))
(must-fail
 (defthm nlst-page-step-without-uint32-total
   (implies (and (fn-cbor-octet-listp report)
                 (<= (len acc) (len report))
                 (equal acc (take (len acc) report))
                 (not (consp acc)))
            (equal (fn-nls-client-step acc total digest
                                       (fn-nls-page (fn-nls-buffer report) (len acc)))
                   (if (<= (len report) (+ (len acc) *fn-nls-chunk-octets*))
                       (list :done report)
                     (list :next (take (+ (len acc) *fn-nls-chunk-octets*) report)
                           (len report) (fn-frame-trailer report)))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-nls-page-of-buffer-is-reply (off (len acc))))
            :do-not-induct t
            :in-theory (e/d (fn-nls-client-step fn-nls-page-width fn-record-uint32p)
                            (fn-nls-page fn-nls-buffer fn-nls-page-of-buffer-is-reply
                             fn-nls-reply fn-nls-reply-encode fn-nls-reply-decode
                             fn-frame-trailer take nthcdr fn-cbor-encode
                             fn-record-item-encode))))))

; fn-nls-cached-buffer-of-put: a later page reads the stored buffer; a
; request from offset 0 renders anew.
(assert-event (equal (fn-nls-cached-buffer :status 1
                                           (fn-nls-cache-put :status (fn-nls-buffer '(2 3))
                                                             (list (cons :pins :other))))
                     (fn-nls-buffer '(2 3))))
(assert-event (equal (fn-nls-cached-buffer :status 0 (fn-nls-cache-put :status :b nil))
                     nil))
(must-fail
 (defthm nlst-cached-buffer-without-positive-offset
   (equal (fn-nls-cached-buffer :status 0 (fn-nls-cache-put :status :b nil)) :b)
   :rule-classes nil))

; ---------------------------------------------------------------------------
; `control list' (qual-e747dbcc A3): fn-nls-report-of-query-kind-is-query-report
; and fn-native-admin-control-report-empty-iff-no-rows.  The witness is the
; defect's shape: one durable grant (cancel over fn.mod.*) in the replayed
; configuration.  The report of the kind ACL2 names for the `control list'
; plan is the grant line; the kind the host used to name (:peers) prints
; nothing over the same configuration, which is the defect the keystone
; excludes (the unconditional equality has no hypothesis to remove).
(defun nlst-argv (words)
  (if (consp words)
      (cons (fn-record-string-octets (car words)) (nlst-argv (cdr words)))
    nil))
(defconst *nlst-p-hex*
  "1111111111111111111111111111111111111111111111111111111111111111")
(defconst *nlst-granted-config*
  (fn-cfg-make 1 (fn-cfg-apply-delta (fn-cfg-value *nlst-config*) 1 0
                                     (fn-cfg-grant-control "fn.mod.*" *nlst-p-hex*
                                                           "cancel"))))
(defconst *nlst-control-list* (fn-native-admin-plan (nlst-argv '("control" "list"))))
(assert-event (fn-native-admin-result-queryp *nlst-control-list*))
(assert-event (equal (fn-native-admin-result-report-kind *nlst-control-list*) :control))
(assert-event (consp (fn-cfg-authorities (fn-cfg-value *nlst-granted-config*))))
(assert-event
 (equal (fn-nls-report (fn-native-admin-result-report-kind *nlst-control-list*)
                       *nlst-profile* *nlst-s* 0 *nlst-granted-config* nil *nlst-obs*)
        (fn-record-string-octets
         (concatenate 'string "grant " *nlst-p-hex* " cancel fn.mod.*"
                      (coerce (list (code-char 10)) 'string)))))
(assert-event
 (equal (fn-nls-report :peers *nlst-profile* *nlst-s* 0 *nlst-granted-config*
                       nil *nlst-obs*)
        nil))
; `peer list' still names the peers.
(assert-event
 (equal (fn-native-admin-result-report-kind
         (fn-native-admin-plan (nlst-argv '("peer" "list"))))
        :peers))
; The live request carries the new kind and the owner decodes it back.
(assert-event (equal (fn-nls-code-kind (fn-nls-kind-code :control)) :control))
; Without the plan's own kind the equality fails: the host's old :peers.
(must-fail
 (defthm nlst-peers-kind-is-query-report
   (equal (fn-nls-report :peers profile s bytes cfg pins obs)
          (fn-native-admin-query-report plan (fn-cfg-value cfg)))
   :hints (("Goal" :in-theory (disable fn-native-admin-control-report
                                       fn-native-admin-peer-report)))))

; ---------------------------------------------------------------------------
; fn-nls-page-refuses-exactly-past-the-total-width (control-reply-fit,
; PRF-178).  The antecedent's past-the-width side needs a report of 2^32
; octets, which no test constructs (as PKT-254's :oversize); what is
; witnessed concretely: the refused frame the owner sends for it (the exact
; octets fn-nls-page answers there, whatever the report) is read by the
; client as the named refusal, a pre-existing unnamed refusal is not, and at
; or below the width the step is never the named refusal.
(defconst *nlst-width-refusal*
  (fn-nls-reply-encode :refused 0 nil *fn-nls-refusal-past-the-total-width*))
(assert-event (equal (fn-nls-client-step nil nil nil *nlst-width-refusal*)
                     '(:refused :report-past-the-total-width)))
(assert-event (equal (fn-nls-reply-decode *nlst-width-refusal*)
                     (list :reply :refused 0 nil
                           *fn-nls-refusal-past-the-total-width*)))
; The layout is every refused reply's: status 2, total 0, no digest.
(assert-event (equal (fn-nls-client-step nil nil nil
                                         (fn-nls-reply-encode :refused 0 nil nil))
                     '(:refused)))
; Reachable within the width (the full antecedent, the conclusion's false
; side): the owner's page of the status report is not the named refusal.
(assert-event
 (and (fn-cbor-octet-listp (nlst-report))
      (<= (len (nlst-report)) *fn-cbor-max-uint*)
      (not (equal (fn-nls-client-step nil nil nil
                                      (fn-nls-page (fn-nls-buffer (nlst-report)) 0))
                  '(:refused :report-past-the-total-width)))))
; An offset past the report within the width: the unnamed refusal, so
; both sides are false (the theorem has no offset hypothesis: every offset).
(assert-event (equal (fn-nls-client-step '(2 3 4) 2 (fn-frame-trailer '(2 3))
                                         (fn-nls-page (fn-nls-buffer '(2 3)) 3))
                     '(:refused)))
; The one hypothesis, dropped: a report that is not octets is refused
; unnamed (the buffer is :bad) at every length, so past the width the
; conclusion fails -- proved for every such report, since none is
; constructible concretely.
(assert-event (equal (fn-nls-client-step nil nil nil
                                         (fn-nls-page (fn-nls-buffer '(256)) 0))
                     '(:refused)))
(defthm nlst-width-refusal-needs-octets
  (implies (and (not (fn-cbor-octet-listp report))
                (< *fn-cbor-max-uint* (len report)))
           (not (equal (equal (fn-nls-client-step acc total digest
                                                  (fn-nls-page (fn-nls-buffer report) off))
                              '(:refused :report-past-the-total-width))
                       (< *fn-cbor-max-uint* (len report)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-nls-reply-decode-of-encode
                                   (status :refused) (total 0) (digest nil)
                                   (chunk nil)))
           :in-theory (e/d (fn-nls-page fn-nls-buffer fn-nls-client-step)
                           (fn-nls-reply-decode-of-encode fn-nls-reply-decode
                            fn-nls-reply-encode (:e fn-nls-reply-encode))))))
