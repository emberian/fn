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
