; Teeth for books/consumer-owner-local-progress (PRF-116), over the actual
; local-owner subject and committed Store witnesses.
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)
(include-book "../../books/consumer-owner-local-progress")

(defun colp-reserve (s)
  (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier nil)
                                :frontier-file :ok)
                      :frontier-replace :ok)
            :frontier-directory :ok))
(defun colp-commit (s event)
  (fn-sn-finish
   (fn-sn-io
    (fn-sn-io
     (fn-sn-io (fn-sn-prepare-consumer (colp-reserve s) event)
               :record-file :ok)
     :record-link :ok)
    :record-directory :ok)))
(defconst *colp-boot*
  (colp-commit (fn-sn-initial '("fn.test") 16)
               (fn-cpe-make 0 0 0 '(:bootstrap (1) (2)))))
(defconst *colp-id* '(7))
(defconst *colp-group* '(102 110 46 116 101 115 116)) ; fn.test
(defconst *colp-register*
  (fn-col-register (fn-own-start *colp-boot* 2) 256 *colp-id* *colp-group*))
(defconst *colp-s1* (colp-commit *colp-boot* (cadr *colp-register*)))
(defconst *colp-o1* (fn-own-start *colp-s1* 2))

; --- the selector's page contract -----------------------------------------
; The literal conclusion of fn-col-poll-scan-page-contract, as a function.
(defun colp-contract (events group position frontier budget)
  (let ((scan (fn-col-poll-scan events group position frontier budget)))
    (let ((p (cadr scan)) (event (caddr scan)))
      (and (natp p)
           (<= position p)
           (<= p (max position (nfix frontier)))
           (<= p (+ position (nfix budget)))
           (if event
               (and (< position p)
                    (equal event (nth (- p (+ 1 position)) events))
                    (fn-col-matchp event group)
                    (fn-col-none-matchp (take (- p (+ 1 position)) events)
                                        group))
             (and (fn-col-none-matchp (take (- p position) events) group)
                  (implies (and (posp budget) (< position (nfix frontier)))
                           (< position p))))))))

(defconst *colp-other*
  (fn-record-make 2 2 2 "<other@fn.test>" '(67)
                  '("fn.other") "other-pin" "other-content"
                  "other-release" 1 841000000))
(defconst *colp-article*
  (fn-record-make 3 3 3 "<poll-two@fn.test>" '(66)
                  '("fn.test") "poll-two-pin" "poll-two-content"
                  "poll-two-release" 1 841000001))
(defun colp-neutral-window (sequence count)
  (if (zp count) nil
    (cons (fn-cpe-make sequence sequence sequence '(:rollover (1)))
          (colp-neutral-window (1+ sequence) (1- count)))))

; Positive, nonempty page: the non-matching article at 2 is scanned, the
; matching one at 3 is returned, the continuation is 4.
(defconst *colp-events* (list *colp-other* *colp-article*))
(assert-event (equal (fn-col-poll-scan *colp-events* *colp-group* 2 4 16)
                     (list :scan 4 *colp-article*)))
(assert-event (natp 2))
(assert-event (not (fn-col-matchp *colp-other* *colp-group*)))
(assert-event (colp-contract *colp-events* *colp-group* 2 4 16))
; Positive, empty page that progresses across sixteen nonarticle events.
(assert-event (equal (fn-col-poll-scan (colp-neutral-window 2 16)
                                       *colp-group* 2 18 16)
                     '(:scan 18 nil)))
(assert-event (colp-contract (colp-neutral-window 2 16) *colp-group* 2 18 16))
; Without (natp position): the scan still answers :scan, and its position
; is not a natural.  (The host's guard excludes this call; the logic does not.)
(assert-event (with-guard-checking :none
                (eq (car (fn-col-poll-scan nil *colp-group* -1 5 0)) :scan)))
(assert-event (not (natp -1)))
(must-fail (assert-event (with-guard-checking :none
                           (colp-contract nil *colp-group* -1 5 0))))
; Without (eq (car scan) :scan): a refused history has no continuation.
(assert-event (natp 0))
(assert-event (equal (fn-col-poll-scan nil *colp-group* 0 1 1)
                     '(:refused :history)))
(must-fail (assert-event (colp-contract nil *colp-group* 0 1 1)))

; The host-called poll over a committed Store is that selector's page.
(defconst *colp-after-article*
  (fn-sn-finish
   (fn-sn-io
    (fn-sn-io
     (fn-sn-io (fn-sn-prepare (colp-reserve *colp-s1*)
                              (fn-record-make 2 2 2 "<poll@fn.test>" '(65 66)
                                              '("fn.test") "poll-pin"
                                              "poll-content" "poll-release"
                                              2 841000000))
               :record-file :ok)
     :record-link :ok)
    :record-directory :ok)))
(defconst *colp-poll* (fn-col-poll (fn-own-start *colp-after-article* 2) *colp-id*))
(assert-event (eq (car *colp-poll*) :poll))
(assert-event (caddr *colp-poll*))
(assert-event
 (equal (fn-cp-nth 9 (fn-cp-nth 1 (fn-cp-cursor-decode (cadr *colp-poll*)))) 3))

; --- ack -------------------------------------------------------------------
(defconst *colp-state* (fn-sn-consumer *colp-s1*))
(defconst *colp-cursor*
  (fn-cp-cursor '(1) '(2) *colp-id* *fn-col-principal* *colp-group* 1 0 1 2))
(defconst *colp-same*
  (fn-cp-cursor '(1) '(2) *colp-id* *fn-col-principal* *colp-group* 1 0 1 0))
(defconst *colp-stranger*
  (fn-cp-cursor '(1) '(2) *colp-id* '(88) *colp-group* 1 0 1 2))
(defmacro colp-ack (s cursor)
  `(fn-cp-ack ,s *fn-col-principal* *fn-col-query-version*
              *fn-col-view-version* ,cursor))
(defun colp-entry (s cursor) (fn-cp-find (fn-cp-nth 3 cursor) (fn-cp-nth 5 s)))
(defun colp-write-conclusion (s cursor)
  (let ((result (colp-ack s cursor)) (entry (colp-entry s cursor)))
    (and (equal (cadr result) (list :ack cursor))
         (fn-cp-scope-matchp s *fn-col-principal* *fn-col-query-version*
                             *fn-col-view-version* cursor entry)
         (<= (nfix (fn-cp-nth 7 entry)) (fn-cp-nth 9 cursor))
         (not (equal (fn-cp-nth 9 cursor) (fn-cp-nth 7 entry)))
         (<= (fn-cp-nth 9 cursor) (nfix (fn-cp-nth 3 s))))))

; The host-called ack of this cursor is the kernel's write.
(assert-event (eq (car (fn-col-ack *colp-o1* (fn-cp-cursor-encode *colp-cursor*)))
                  :write))
; Write conjunct: witness and removal of (car result = :write).
(assert-event (eq (car (colp-ack *colp-state* *colp-cursor*)) :write))
(assert-event (colp-write-conclusion *colp-state* *colp-cursor*))
(assert-event (eq (car (colp-ack *colp-state* *colp-same*)) :no-op))
(must-fail (assert-event (colp-write-conclusion *colp-state* *colp-same*)))
; No-op conjunct: witness, then each hypothesis removed.
(defun colp-noop-conclusion (s cursor)
  (equal (colp-ack s cursor)
         (list :no-op (fn-cp-scope-cursor s (colp-entry s cursor)))))
(assert-event (fn-cp-scope-matchp *colp-state* *fn-col-principal* 1 0 *colp-same*
                                  (colp-entry *colp-state* *colp-same*)))
(assert-event (equal (fn-cp-nth 9 *colp-same*)
                     (fn-cp-nth 7 (colp-entry *colp-state* *colp-same*))))
(assert-event (colp-noop-conclusion *colp-state* *colp-same*))
(assert-event (not (fn-cp-scope-matchp *colp-state* *fn-col-principal* 1 0
                                       *colp-stranger*
                                       (colp-entry *colp-state* *colp-stranger*))))
(defconst *colp-stranger-same*
  (fn-cp-cursor '(1) '(2) *colp-id* '(88) *colp-group* 1 0 1 0))
(assert-event (equal (fn-cp-nth 9 *colp-stranger-same*)
                     (fn-cp-nth 7 (colp-entry *colp-state* *colp-stranger-same*))))
(must-fail (assert-event (colp-noop-conclusion *colp-state* *colp-stranger-same*)))
(assert-event (not (equal (fn-cp-nth 9 *colp-cursor*)
                          (fn-cp-nth 7 (colp-entry *colp-state* *colp-cursor*)))))
(must-fail (assert-event (colp-noop-conclusion *colp-state* *colp-cursor*)))

; After the committed ack, the same ack is a no-op (an uncertain ack retried).
(defun colp-after-conclusion (s cursor)
  (equal (car (colp-ack (fn-cp-apply s (list :ack cursor)) cursor)) :no-op))
(assert-event (colp-after-conclusion *colp-state* *colp-cursor*))
(assert-event (eq (car (colp-ack *colp-state* *colp-stranger*)) :refused))
(must-fail (assert-event (colp-after-conclusion *colp-state* *colp-stranger*)))

; PKT-256, CORRUPTED STATE (not reachable: a replayed scope's recorded
; position never exceeds the committed frontier, `fn-col-scope-entry'
; refuses such an entry on the served path).  The no-op conjunct of
; `fn-cp-ack-writes-only-a-forward-declaration-in-scope' without its frontier
; premise: the state after the committed ack of *colp-cursor*, with the
; frontier lowered below the recorded position.  The retained hypotheses
; hold (scope match; declared position = recorded position), the omitted one
; fails, and the conclusion fails: the kernel refuses the ack as :future.
(defconst *colp-acked* (fn-cp-apply *colp-state* (list :ack *colp-cursor*)))
(defconst *colp-corrupt* (update-nth 3 1 *colp-acked*))
(assert-event (equal (fn-cp-nth 7 (colp-entry *colp-acked* *colp-cursor*)) 2))
(assert-event (<= (fn-cp-nth 9 *colp-cursor*) (nfix (fn-cp-nth 3 *colp-acked*))))
(assert-event (fn-cp-scope-matchp *colp-corrupt* *fn-col-principal* 1 0 *colp-cursor*
                                  (colp-entry *colp-corrupt* *colp-cursor*)))
(assert-event (equal (fn-cp-nth 9 *colp-cursor*)
                     (fn-cp-nth 7 (colp-entry *colp-corrupt* *colp-cursor*))))
(assert-event (not (<= (fn-cp-nth 9 *colp-cursor*)
                       (nfix (fn-cp-nth 3 *colp-corrupt*)))))
(assert-event (equal (colp-ack *colp-corrupt* *colp-cursor*) '(:refused :future)))
(must-fail (assert-event (colp-noop-conclusion *colp-corrupt* *colp-cursor*)))

; PKT-254 (PRF-177 (c)): fn-col-poll-report-fits-or-refuses-by-name over the
; host-called report.  Reachable witness: the page above serves the article
; event's exact encoding, which the kind-6 reply carries.
(defconst *colp-report* (fn-col-poll-report (fn-own-start *colp-after-article* 2) *colp-id*))
(assert-event (eq (car *colp-poll*) :poll))
(assert-event (caddr *colp-poll*))
(assert-event (fn-ncl-poll-event-bytesp (fn-col-poll-report-octets (caddr *colp-poll*))))
(assert-event (equal *colp-report*
                     (list :poll (cadr *colp-poll*)
                           (fn-col-poll-report-octets (caddr *colp-poll*)))))
(assert-event (not (eq (fn-ncl-poll-reply-encode :accepted (cadr *colp-report*)
                                                 (caddr *colp-report*))
                       :bad)))
; The :oversize conjunct: its antecedent needs a report above
; *fn-stxa-max-octets* (4,294,966,940 octets), which no test constructs; its
; length hypothesis removed, the conclusion fails on the reachable page.
(assert-event (<= (len (fn-col-poll-report-octets (caddr *colp-poll*)))
                  *fn-stxa-max-octets*))
(must-fail (assert-event (equal *colp-report* '(:refused :oversize))))
; PKT-467 (PRF-178): fn-col-poll-report-of-an-admitted-payload-fits.
; Reachable, the full antecedent: the page's event encoding is a payload the
; development profile's publication gate admits, and the report is the page.
(assert-event
 (let ((octets (fn-col-poll-report-octets (caddr *colp-poll*))))
   (and (eq (car *colp-poll*) :poll) (caddr *colp-poll*)
        (consp octets) (fn-cbor-octet-listp octets)
        (fn-bs-publication-admissiblep *fn-bs-profile-development* 0 (len octets))
        (equal *colp-report* (list :poll (cadr *colp-poll*) octets)))))
; The page hypothesis dropped: the scope refusal is not a page.
(must-fail
 (assert-event (equal (fn-col-poll-report (fn-own-start *colp-after-article* 2) '(9))
                      (list :poll (cadr (fn-col-poll (fn-own-start *colp-after-article* 2) '(9)))
                            nil))))
; The admission hypothesis dropped: no report of 2^32 octets is
; constructible, so its failure is proved for every such page -- the
; conclusion fails whenever the encoding is past the report ceiling, which
; every valid profile's gate refuses.
(defthm colp-admitted-payload-fits-needs-the-admission
  (let ((d (fn-col-poll o consumer)))
    (implies (and (equal (car d) :poll) (caddr d)
                  (consp (fn-col-poll-report-octets (caddr d)))
                  (fn-cbor-octet-listp (fn-col-poll-report-octets (caddr d)))
                  (< *fn-stxa-max-octets* (len (fn-col-poll-report-octets (caddr d)))))
             (and (not (equal (fn-col-poll-report o consumer)
                              (list :poll (cadr d)
                                    (fn-col-poll-report-octets (caddr d)))))
                  (not (fn-bs-publication-admissiblep
                        profile committed-count
                        (len (fn-col-poll-report-octets (caddr d))))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-col-poll-report-fits-or-refuses-by-name)
                        (:instance fn-bs-profile-valid-record-fits-a-poll-reply
                                   (values profile)
                                   (octets (len (fn-col-poll-report-octets
                                                 (caddr (fn-col-poll o consumer)))))))
           :in-theory (disable fn-col-poll fn-col-poll-report fn-col-poll-report-octets
                               fn-bs-publication-admissiblep fn-cbor-octet-listp))))
; A refusal or an empty page passes through unchanged (the scope refusal).
(assert-event (equal (fn-col-poll-report (fn-own-start *colp-after-article* 2) '(9))
                     (fn-col-poll (fn-own-start *colp-after-article* 2) '(9))))
(assert-event (eq (car (fn-col-poll (fn-own-start *colp-after-article* 2) '(9)))
                  :refused))

; PKT-262 (PRF-177 (d)), INTENDED under CNS-002 and "Operations and their
; meanings": `register' sets the recorded position to zero, and the
; local-owner query is exact historical membership in the registered group,
; so a consumer registered after an article was committed polls that article
; first.  Witness: an article at sequence 1, the registration at 2, and the
; first page is the article, continuing at 2.
(defconst *colp-pre-article*
  (fn-sn-finish
   (fn-sn-io
    (fn-sn-io
     (fn-sn-io (fn-sn-prepare (colp-reserve *colp-boot*)
                              (fn-record-make 1 1 1 "<before@fn.test>" '(65)
                                              '("fn.test") "before-pin"
                                              "before-content" "before-release"
                                              1 841000000))
               :record-file :ok)
     :record-link :ok)
    :record-directory :ok)))
(defconst *colp-late-register*
  (fn-col-register (fn-own-start *colp-pre-article* 2) 256 *colp-id* *colp-group*))
(assert-event (eq (car *colp-late-register*) :write))
(defconst *colp-late* (colp-commit *colp-pre-article* (cadr *colp-late-register*)))
(defconst *colp-late-poll* (fn-col-poll (fn-own-start *colp-late* 2) *colp-id*))
(assert-event (eq (car *colp-late-poll*) :poll))
(assert-event (equal (fn-record-msgid (caddr *colp-late-poll*)) "<before@fn.test>"))
(assert-event
 (equal (fn-cp-nth 9 (fn-cp-nth 1 (fn-cp-cursor-decode (cadr *colp-late-poll*)))) 2))
