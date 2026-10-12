; Witnesses and teeth for books/filed-history: the reclaim-aware history
; invariant FN-O1-FILES-INVP carried by every Store transition (KR1-KR7), and
; the reclaim rewrite of a record (K0).
;
; A concrete store (store-node-tests' reserved store, groups fn.letters and
; fn.test) stages and then publishes a record: the held row is interned at
; handle 0 of an arena holding the payload, so the staged row meets
; FN-O1-PREPARE-KEEPS-THE-HISTORY's hypothesis (KR5), and the record-directory
; :ok that appends it (the one step that changes the records, KR1) leaves the
; files invariant, with the row among the records and no candidate left.  The
; finish (KR2), a crash that keeps the record (KR3, the :present choice) and,
; after the crash, the recovery (KR4) are evaluated on the same store, and a
; seal of one more payload (KR7) keeps the invariant.  Two records run through
; it: a FILED one (*otf-good*, groups fn.letters, the payload names fn.test and
; fn.letters) and its RECLAIMED form *otf-z* (FN-RCLP-TOMBSTONED of it: the
; groups kept, the payload a reclaim tombstone), for which the old all-filed
; predicate FN-O1-RECORDS-FILEDP is NIL and the invariant holds throughout;
; the checked mutation drops the tombstone disjunct from the invariant and is
; then false of the satisfiable reclaimed instance.
; Removal teeth: an UNFILED non-tombstone record (*otf-bad*, groups fn.test,
; payload naming fn.letters only); a row whose handle lies outside the arena;
; a composite row whose held article is not its composite's article.
(in-package "ACL2")
(include-book "../../books/filed-history")
(include-book "store-node-tests")
(include-book "held-rows-tests")
(include-book "key-statements-tests")   ; *kst-event*: a composite for the forged-row tooth
(include-book "store-identity-traces-tests")   ; a Store that stages a composite (kind-4) row
(include-book "owner-prepare-deferred-carried-tests") ; consumer and retention events a Store stages
(include-book "../../books/topic-history-local-proposals") ; the topic install a Store stages
(include-book "../../books/crypto-attach")
(include-book "../../books/codec-attach")

(defconst *otf-crlf* (coerce '(#\Return #\Newline) 'string))
(defun otf-src (newsgroups)
  (fn-record-string-octets
   (concatenate 'string "From: a@b.example" *otf-crlf*
                "Newsgroups: " newsgroups *otf-crlf*
                "Subject: s" *otf-crlf*
                "Message-ID: <w1@b.example>" *otf-crlf*
                *otf-crlf* "body" *otf-crlf*)))
(defun otf-wire (payload groups)
  (fn-record-make 0 0 0 "<w1@b.example>" payload groups
                  "otf-pin" "otf-content" "otf-release" 2 841000000))
; filed: groups fn.letters, the payload names fn.test and fn.letters
(defconst *otf-good* (otf-wire (otf-src "fn.test,fn.letters") '("fn.letters")))
; unfiled: groups fn.test, the payload names fn.letters only
(defconst *otf-bad* (otf-wire (otf-src "fn.letters") '("fn.test")))

; the reclaimed form of the filed record: the groups kept, the payload a tombstone
(defconst *otf-z* (fn-rclp-tombstoned *otf-good*))

; The invariant with the tombstone disjunct removed (the checked mutation).
(defun otf-records-filed-only-invp (rows fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (and (fn-o1-records-filedp (fn-cat-history-articles rows fn-arena))
       (fn-rows-composites-okp rows fn-arena)
       (fn-rows-handles-inp rows fn-arena)))
(defun otf-files-filed-only-invp (files fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (and (otf-records-filed-only-invp (fn-sf-records files) fn-arena)
       (otf-records-filed-only-invp (list (fn-sf-record-candidate files)) fn-arena)))

(defun otf-scenario (w extra fn-arena)
  (declare (xargs :mode :program :stobjs fn-arena))
  (mv-let (rows fn-arena)
    (fn-hrt-events (list w) nil 0 fn-arena)
    (let* ((row (car rows))
           (s0 *sn-reserved*)
           (s1 (fn-sn-prepare s0 row))
           (f1 (fn-sn-files s1))
           (s2 (fn-sn-test-publish s1))
           (f2 (fn-sn-files s2))
           (s3 (fn-sn-finish s2))
           (c (fn-sn-crash s2 :old :present))
           (r (fn-sn-recover c)))
      (let ((items (list (fn-o1-files-invp (fn-sn-files s0) fn-arena)                ; 0 start
                  (fn-o1-rows-invp (list row) fn-arena)                          ; 1 KR5's hypothesis
                  (fn-sf-phase f1)                                             ; 2 staged
                  (equal (fn-sf-record-candidate f1) row)                      ; 3
                  (fn-o1-files-invp f1 fn-arena)                               ; 4 KR5
                  (fn-sf-phase f2)                                             ; 5 completing
                  (equal (fn-sf-records f2) (list row))                        ; 6 KR1: appended
                  (equal (fn-sf-record-candidate f2) nil)                      ; 7
                  (fn-o1-files-invp f2 fn-arena)                               ; 8 KR1
                  (equal (fn-cat-history-articles (fn-sf-records f2) fn-arena) (list w)) ; 9
                  (fn-o1-files-invp (fn-sn-files s3) fn-arena)                 ; 10 KR2
                  (equal (fn-sf-records (fn-sn-files c)) (list row))           ; 11 crash kept it
                  (fn-o1-files-invp (fn-sn-files c) fn-arena)                  ; 12 KR3
                  (fn-o1-files-invp (fn-sn-files r) fn-arena))))               ; 13 KR4
        (let ((fn-arena (fn-arena-seal-list extra fn-arena)))
          (mv (append items (list (fn-o1-files-invp f2 fn-arena)                  ; 14 KR7
                                  (otf-files-filed-only-invp f2 fn-arena)         ; 15 the mutant, same state
                                  (fn-o1-records-filedp (fn-cat-history-articles (fn-sf-records f2) fn-arena)))) ; 16 old predicate
              fn-arena))))))
(defun otf-exec (w extra)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (r fn-arena) (otf-scenario w extra fn-arena)
      r)))

(defconst *otf-g* (otf-exec *otf-good* (otf-src "fn.other")))
(defconst *otf-r* (otf-exec *otf-z* (otf-src "fn.other")))
(defconst *otf-b* (otf-exec *otf-bad* (otf-src "fn.other")))

; Satisfiable, filed record: staged, published, finished, crashed, recovered, sealed.
(assert-event (equal *otf-g* '(t t :record-staged t t :completing t t t t t t t t t t t)))
; Satisfiable, RECLAIMED record: every hypothesis and conclusion of KR1-KR5 and KR7 holds
; with a tombstoned article among the records, and the old all-filed predicate is NIL
; of the same history (the checked mutation: without the tombstone disjunct the
; conclusion is false of this satisfiable instance).
(assert-event (equal (take 14 *otf-r*) '(t t :record-staged t t :completing t t t t t t t t)))
(assert-event (nth 14 *otf-r*))                                  ; KR7 on the reclaimed history
(assert-event (and (not (nth 15 *otf-r*)) (not (nth 16 *otf-r*)))) ; mutation / old predicate: NIL
(assert-event (and (nth 15 *otf-g*) (nth 16 *otf-g*)))
; and the held article IS the tombstoned record (not a vacuous history)
(assert-event (and (fn-record-p *otf-z*)
                   (fn-rcl-tombstonep (fn-record-payload *otf-z*))
                   (equal (fn-record-groups *otf-z*) '("fn.letters"))
                   (not (fn-o1-records-filedp (list *otf-z*)))
                   (fn-o1-records-filed-or-reclaimedp (list *otf-z*))
                   (not (equal (fn-record-payload *otf-z*) (fn-record-payload *otf-good*)))))
; the removal tooth of KR5's hypothesis: the unfiled non-tombstone record is staged
; all the same, the start is invariant, and the files are NOT invariant after the prepare
(assert-event (and (nth 0 *otf-b*)
                   (not (nth 1 *otf-b*))
                   (eq (nth 2 *otf-b*) :record-staged)
                   (nth 3 *otf-b*)
                   (not (nth 4 *otf-b*))))
; ... and the append at the record directory publishes the unfiled record into the
; history, and the invariant stays lost through finish, crash, recover and seal
; (the removal teeth of KR1-KR4 and KR7: the hypothesis on the files fails, the
; conclusion fails): the history invariant is lost exactly at the prepare.
(assert-event (and (nth 6 *otf-b*) (not (nth 8 *otf-b*))
                   (not (nth 10 *otf-b*)) (not (nth 12 *otf-b*)) (not (nth 13 *otf-b*))
                   (not (nth 14 *otf-b*))))

; ---------------------------------------------------------------------------
; KR5, the four prepares that stage an event rather than an article row, on a
; Store holding the reclaimed record: the record *otf-z* (first record), a
; consumer bootstrap and a retention undertake are committed through the Store
; machine (fn-snrt-run); then a retention undertake, a consumer rollover and a
; topic install are each staged.  Each stages its event (the candidate is the
; event) and the files invariant holds before and after.  With the unfiled
; record *otf-bad* in place of *otf-z* the hypothesis on the files fails and
; so does the conclusion (the removal tooth of the files hypothesis).
; The statements carry no row hypothesis for these three: FN-O1-ROWS-INVP of
; the staged event is T of every event they stage (a retention, consumer or
; topic event is not a record, a held row or a composite; asserted below as the
; last three items), so no instance has it alone failing.
(defun otf-mixed (w fn-arena)
  (declare (xargs :mode :program :stobjs fn-arena))
  (mv-let (rows fn-arena)
    (fn-hrt-events (list w) nil 0 fn-arena)
    (let* ((wrow (car rows))
           (boot (list :consumer 1 1 1 (list :bootstrap *pdt-ida* *pdt-idb*)))
           (und (fn-store-retention-event-make :undertake 2 2 2 "pdt-id-1" "pdt-subject" "pdt-evidence" 5))
           (s1 (fn-snrt-run (fn-sn-initial *pdt-groups* 20)
                            (append *pdt-reserve* (list (list :prepare wrow)) *pdt-publish*
                                    *pdt-reserve* (list (list :prepare-consumer boot)) *pdt-publish*
                                    *pdt-reserve* (list (list :prepare-retention und)) *pdt-publish*
                                    *pdt-reserve*)))
           (roll (list :consumer 3 3 3 (list :rollover *pdt-idc*)))
           (und2 (fn-store-retention-event-make :undertake 3 3 3 "pdt-id-2" "pdt-subject" "pdt-evidence" 5))
           (p (fn-th-local-propose :install (fn-sn-topic s1)
                                   (fn-state-next-txid (fn-node-acceptance (fn-sn-node s1)))
                                   0 1000 (make-list 32 :initial-element 7) 0))
           (top (cadr p))
           (sr (fn-sn-prepare-retention s1 und2))
           (sc (fn-sn-prepare-consumer s1 roll))
           (st (fn-sn-prepare-topic s1 top)))
      (mv (list (len (fn-sf-records (fn-sn-files s1)))                              ; 0 three records
                (fn-sf-phase (fn-sn-files s1))                                      ; 1 reserved
                (fn-o1-files-invp (fn-sn-files s1) fn-arena)                        ; 2 the hypothesis
                (car p)                                                             ; 3 the topic proposal
                (list (fn-sf-phase (fn-sn-files sr))                                ; 4 retention
                      (equal (fn-sf-record-candidate (fn-sn-files sr)) und2)
                      (fn-o1-files-invp (fn-sn-files sr) fn-arena))
                (list (fn-sf-phase (fn-sn-files sc))                                ; 5 consumer
                      (equal (fn-sf-record-candidate (fn-sn-files sc)) roll)
                      (fn-o1-files-invp (fn-sn-files sc) fn-arena))
                (list (fn-sf-phase (fn-sn-files st))                                ; 6 topic
                      (equal (fn-sf-record-candidate (fn-sn-files st)) top)
                      (fn-o1-files-invp (fn-sn-files st) fn-arena))
                (fn-o1-rows-invp (list und2) fn-arena)                              ; 7 the second hypotheses
                (fn-o1-rows-invp (list roll) fn-arena)
                (fn-o1-rows-invp (list top) fn-arena))
          fn-arena))))
(defun otf-mixed-exec (w)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena (mv-let (r fn-arena) (otf-mixed w fn-arena) r)))
(defconst *otf-mz* (otf-mixed-exec *otf-z*))
(defconst *otf-mb* (otf-mixed-exec *otf-bad*))
(assert-event (equal *otf-mz* '(3 :reserved t :ok (:record-staged t t) (:record-staged t t)
                                  (:record-staged t t) t t t)))
; the files hypothesis removed: still three records, the events stage, the invariant is NIL after
(assert-event (equal *otf-mb* '(3 :reserved nil :ok (:record-staged t nil) (:record-staged t nil)
                                  (:record-staged t nil) t t t)))

; ---------------------------------------------------------------------------
; KR5 for the identity prepare, on the composite (kind-4) row of a signed
; article: the Store of store-identity-traces-tests after the keyring
; enrollment stages the composite row whose article is filed (*otf-sig-good*),
; or reclaimed (*otf-sig-z*, its tombstone); the unfiled one (*otf-sig-bad*:
; groups example, payload naming other) is the removal tooth of the row
; hypothesis (the start is invariant, the row is not, the files after are not).
(defun otf-sig-id (n) (concatenate 'string "<sig" (coerce (list (code-char (+ 48 n))) 'string) "@example.invalid>"))
(defun otf-sig-src (n newsgroups)
  (fn-record-string-octets
   (concatenate 'string "From: a@b.example" *otf-crlf* "Newsgroups: " newsgroups *otf-crlf*
                "Subject: s" *otf-crlf* "Message-ID: " (otf-sig-id n) *otf-crlf*
                *otf-crlf* "body" *otf-crlf*)))
(defun otf-sig-record (n payload)
  (fn-record-make n n n (otf-sig-id n) payload *sit-groups*
                  (concatenate 'string "signed-obligation" (coerce (list (code-char (+ 48 n))) 'string))
                  "signed-subject" "signed-release" 3 841000000))
(defun otf-sig-wire (rec)
  (fn-hsig-authorized-article-event
   (fn-record-sequence rec) (fn-record-txid rec) (fn-record-generation rec) 1 *sit-snapshot*
   (fn-record-msgid rec) (fn-record-string-octets "signed-subject")
   (fn-record-encode-impl rec) *sit-principal* *sit-keys* (fn-record-payload rec)
   *sit-signatures* *sit-ml-key* :verified :verified))
(defconst *otf-sig-good* (otf-sig-record 1 (otf-sig-src 1 "example,other")))
(defconst *otf-sig-z* (fn-rclp-tombstoned *otf-sig-good*))
(defconst *otf-sig-bad* (otf-sig-record 1 (otf-sig-src 1 "other")))
(defun otf-sig-run (rec fn-arena)
  (declare (xargs :mode :program :stobjs fn-arena))
  (mv-let (rows fn-arena)
    (fn-hrt-events (list *sit-enrollment* (otf-sig-wire rec)) nil 0 fn-arena)
    (let* ((row (cadr rows))
           (s0 (fn-sit-reserve *sit-after-enrollment*))
           (s1 (fn-sn-prepare-identity s0 row)))
      (mv (list (fn-hstxa-p row)                                       ; 0 a composite row
                (fn-o1-files-invp (fn-sn-files s0) fn-arena)           ; 1 the files hypothesis
                (fn-o1-rows-invp (list row) fn-arena)                  ; 2 the row hypothesis
                (fn-sf-phase (fn-sn-files s1))                         ; 3 staged
                (equal (fn-sf-record-candidate (fn-sn-files s1)) row)  ; 4
                (fn-o1-files-invp (fn-sn-files s1) fn-arena)           ; 5 the conclusion
                (fn-o1-records-filedp (fn-cat-history-articles (list row) fn-arena))) ; 6 the old predicate
          fn-arena))))
(defun otf-sig-exec (rec)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena (mv-let (r fn-arena) (otf-sig-run rec fn-arena) r)))
(assert-event (equal (otf-sig-exec *otf-sig-good*) '(t t t :record-staged t t t)))
(assert-event (equal (otf-sig-exec *otf-sig-z*) '(t t t :record-staged t t nil)))
(assert-event (equal (otf-sig-exec *otf-sig-bad*) '(t t nil :record-staged t nil nil)))

; ---------------------------------------------------------------------------
; D2's conjuncts, each removed alone (the rows of a prepare cannot reach all
; three: the identity gate refuses a composite whose held article is not its
; composite's, so a forged one stays unstaged).  The rows: an unfiled record
; (records conjunct), a composite row whose held article is another record
; (composites conjunct), a held row whose handle lies outside the arena with
; no groups (handles conjunct).
(defconst *otf-nog* (otf-wire (otf-src "fn.letters") nil))
(defun otf-conjuncts (fn-arena)
  (declare (xargs :mode :program :stobjs fn-arena))
  (mv-let (rows fn-arena)
    (fn-intern-events (list *kst-event* *otf-good* *otf-bad*) nil 0 fn-arena)
    (let* ((genuine (car rows))
           (forged (fn-hstxa-make (fn-hstxa-stxa genuine) (cadr rows)))
           (unfiled (caddr rows))
           (oob (fn-held-plain *otf-nog* 99)))
      (mv (list (list (fn-o1-rows-invp (list genuine) fn-arena)            ; 0 the genuine composite: invariant
                      (fn-o1-rows-invp (list (cadr rows)) fn-arena))
                (list (fn-o1-rows-invp (list unfiled) fn-arena)             ; 1 records conjunct alone
                      (fn-o1-records-filed-or-reclaimedp (fn-cat-history-articles (list unfiled) fn-arena))
                      (fn-rows-composites-okp (list unfiled) fn-arena)
                      (fn-rows-handles-inp (list unfiled) fn-arena))
                (list (fn-o1-rows-invp (list forged) fn-arena)              ; 2 composites conjunct alone
                      (fn-o1-records-filed-or-reclaimedp (fn-cat-history-articles (list forged) fn-arena))
                      (fn-rows-composites-okp (list forged) fn-arena)
                      (fn-rows-handles-inp (list forged) fn-arena))
                (list (fn-o1-rows-invp (list oob) fn-arena)                 ; 3 handles conjunct alone
                      (fn-o1-records-filed-or-reclaimedp (fn-cat-history-articles (list oob) fn-arena))
                      (fn-rows-composites-okp (list oob) fn-arena)
                      (fn-rows-handles-inp (list oob) fn-arena)))
          fn-arena))))
(defun otf-conjuncts-exec ()
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena (mv-let (r fn-arena) (otf-conjuncts fn-arena) r)))
(assert-event (equal (otf-conjuncts-exec)
                     '((t t) (nil nil t t) (nil t nil t) (nil t t nil))))

; ---------------------------------------------------------------------------
; KR6: the initial Store's files are invariant, over an empty arena and over
; one holding the payloads of the scenario above.  The statement has no
; hypothesis, so there is nothing to remove; the instance has no records, the
; candidate is the empty row.
(defun otf-initial (fn-arena)
  (declare (xargs :mode :program :stobjs fn-arena))
  (let ((a (fn-o1-files-invp (fn-sn-files (fn-sn-initial *pdt-groups* 20)) fn-arena)))
    (mv-let (rows fn-arena)
      (fn-hrt-events (list *otf-z*) nil 0 fn-arena)
      (declare (ignore rows))
      (mv (list a (fn-o1-files-invp (fn-sn-files (fn-sn-initial *pdt-groups* 20)) fn-arena)
                (fn-arena-count fn-arena))
          fn-arena))))
(defun otf-initial-exec ()
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena (mv-let (r fn-arena) (otf-initial fn-arena) r)))
(assert-event (equal (otf-initial-exec) '(t t 1)))

; ---------------------------------------------------------------------------
; K0: the reclaim rewrite of a record is reclaimed (its payload a tombstone),
; whatever its groups and whatever its payload.  The instances below satisfy
; FN-RCL-PAYLOAD-PROFILEP; the unfiled record's rewrite too; and a payload that
; does not satisfy it ('(300)) is rewritten to a tombstone all the same, which
; is why the statement carries no profile hypothesis.  The mutation (the
; tombstone disjunct removed) is false of the filed record's rewrite.
(assert-event (and (fn-rcl-payload-profilep (fn-record-payload *otf-good*))
                   (fn-o1-records-filed-or-reclaimedp (list (fn-rclp-tombstoned *otf-good*)))
                   (fn-o1-records-filed-or-reclaimedp (list (fn-rclp-tombstoned *otf-bad*)))
                   (not (fn-o1-records-filedp (list (fn-rclp-tombstoned *otf-good*))))
                   (not (fn-o1-records-filedp (list (fn-rclp-tombstoned *otf-bad*))))))
(assert-event (with-guard-checking :none
                (and (not (fn-rcl-payload-profilep '(300)))
                     (fn-o1-records-filed-or-reclaimedp
                      (list (fn-rclp-tombstoned (otf-wire '(300) '("fn.test"))))))))
