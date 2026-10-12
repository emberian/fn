; Witnesses and teeth for books/filed-lifecycle: the reclaim-aware history
; invariant FN-O1-FILES-INVP through the owner's lifecycle beyond the Store
; transitions (those are books/filed-history's, witnessed in
; filed-history-tests).  Every keystone has an instance with a RECLAIMED
; article (a tombstoned record, FN-RCLP-TOMBSTONED) among the history for
; which every hypothesis holds, the conclusion holds, and the old all-filed
; predicate FN-O1-RECORDS-FILEDP is NIL; the checked mutation (the conclusion
; with the tombstone disjunct dropped, OTF-FILES-FILED-ONLY-INVP) is false of
; it.  The teeth: an unfiled non-tombstone record (*otf-bad*, or the swapped
; record *p4-swap* that recovery accepts), a handle the release names, a
; composite whose stxa article is not its held article.
;
; Hypotheses the first statement draft carried, dropped because no instance
; has one failing alone with a false conclusion (the instances below are the
; evidence: each asserts the conclusion with the hypothesis failing):
;   K3: the interned row is not :bad; the prepare of :bad stages nothing.
;   K4: the rebuilt owner is not :fault; the swap over a fault is an empty Store.
;   K5a: the full replay is not :bad and the open is not :fault; a failed open
;        has no Store, and the empty Store is invariant.
;   K5b: the open is not :fault: likewise.
; K5b keeps (true-listp ws) and the intern of the whole journal not :bad, which
; the cited equality with the full recover needs.  The stobj recognizers
; (fn-arena-p) are true of every live arena; fn-sf-record-valuesp (K7) has no
; runtime removal witness: a catalog loaded from a non-record row is not a live
; fn-cat.
(in-package "ACL2")
(include-book "../../books/filed-lifecycle")
(include-book "filed-history-tests")   ; *otf-good*, *otf-z*, *otf-bad*, the signed composites, the mixed Store
(include-book "filed-catalog-tests")   ; *p3-w0*, *p5-z1*, *p4-swap*, p4-open, p5-served-run
(include-book "arena-lift")
(include-book "must-fail-checked")

; --------------------------------------------------------------------------
; Fixtures: Stores holding a committed record, reserved again.
(defun fl-wire-n (n msgid payload groups)
  (fn-record-make n n n msgid payload groups (concatenate 'string "fl-pin-" msgid) "otf-content" "otf-release" 2 841000000))
; a Store with W0 as its one record (arena: W0 at handle 0)
(defun fl-one-store (w0 fn-arena)
  (declare (xargs :mode :program :stobjs fn-arena))
  (mv-let (rows fn-arena)
    (fn-hrt-events (list w0) nil 0 fn-arena)
    (mv (fn-sit-reserve (fn-sn-finish (fn-sn-test-publish (fn-sn-prepare *sn-reserved* (car rows))))) fn-arena)))
(defconst *fl-w1* (fl-wire-n 1 "<w2@b.example>" (otf-src "fn.test,fn.letters") '("fn.letters")))
(defconst *fl-z1* (fn-rclp-tombstoned *fl-w1*))
(defconst *fl-u1* (fl-wire-n 1 "<w2@b.example>" (otf-src "fn.letters") '("fn.test")))   ; unfiled

; --------------------------------------------------------------------------
; K2 FN-O1-RELEASE-KEEPS-THE-HISTORY.  The Store publishes W; the arena holds
; its payload at handle 0 and another at handle 1; the release forgets HANDLE.
; Items: the files hypothesis, the disjointness hypothesis, the conclusion,
; the mutant conclusion, the emptied payload.
(defun fl-k2 (w handle fn-arena)
  (declare (xargs :mode :program :stobjs fn-arena))
  (mv-let (rows fn-arena)
    (fn-hrt-events (list w) nil 0 fn-arena)
    (let* ((row (car rows))
           (fn-arena (fn-arena-seal-list (otf-src "fn.other") fn-arena))
           (files (fn-sn-files (fn-sn-test-publish (fn-sn-prepare *sn-reserved* row))))
           (rel (list (cons 7 (fn-arf-tag (list handle)))))
           (disj (fn-arf-disjointp (fn-arf-pend-handles rel)
                                   (fn-arf-rows-handles (cons (fn-sf-record-candidate files) (fn-sf-records files)))))
           (before (fn-o1-files-invp files fn-arena))
           (fn-arena (fn-arf-apply-released rel fn-arena))
           (after (fn-o1-files-invp files fn-arena))
           (mut (otf-files-filed-only-invp files fn-arena)))
      (mv (list before disj after mut (fn-arena-payload handle fn-arena)) fn-arena))))
(defun fl-k2-exec (w h)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena (mv-let (r fn-arena) (fl-k2 w h fn-arena) r)))
(assert-event (equal (fl-k2-exec *otf-good* 1) '(t t t t nil)))
(assert-event (equal (fl-k2-exec *otf-z* 1) '(t t t nil nil)))        ; reclaimed record: invariant, mutant false
; the disjointness removed: the release names the row's handle (the row reads no bytes after)
(assert-event (equal (fl-k2-exec *otf-good* 0) '(t nil nil nil nil)))
(assert-event (equal (fl-k2-exec *otf-z* 0) '(t nil nil nil nil)))
; the files hypothesis removed: the unfiled record
(assert-event (equal (fl-k2-exec *otf-bad* 1) '(nil t nil nil nil)))

; --------------------------------------------------------------------------
; K3 FN-O1-INTERN-THEN-STAGE-KEEPS-THE-HISTORY, over the files of a Store
; holding a committed record W0: the wire event W is interned at the arena's
; count (after another payload sealed), then staged by fn-sf-prepare-record
; (or not staged: FILES2 = FILES).  Items: the files hypothesis, the article
; hypothesis, row not :bad, the arena count before and after, the phase, the
; conclusion, the mutant.
(defun fl-k3 (w0 w kind fn-arena)
  (declare (xargs :mode :program :stobjs fn-arena))
  (mv-let (s fn-arena) (fl-one-store w0 fn-arena)
    (let* ((files0 (fn-sn-files s))
           (fn-arena (fn-arena-seal-list (otf-src "fn.other") fn-arena))
           (hyp-files (fn-o1-files-invp files0 fn-arena))
           (art (fn-o1-records-filed-or-reclaimedp (list (fn-bpr-event-article w))))
           (before (fn-arena-count fn-arena)))
      (mv-let (row fn-arena)
        (fn-intern-event w nil 0 fn-arena)
        (let ((files2 (if (equal kind :same) files0
                        (fn-sf-prepare-record files0 row (fn-sn-groups s) (fn-sn-capacity s)))))
          (mv (list hyp-files art (not (equal row :bad)) before (fn-arena-count fn-arena)
                    (fn-sf-phase files2)
                    (fn-o1-files-invp files2 fn-arena)
                    (otf-files-filed-only-invp files2 fn-arena))
              fn-arena))))))
(defun fl-k3-exec (w0 w kind)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena (mv-let (r fn-arena) (fl-k3 w0 w kind fn-arena) r)))
; the Store already holds the reclaimed *otf-z*; a filed or a reclaimed record is staged
(assert-event (equal (fl-k3-exec *otf-z* *fl-w1* :stage) '(t t t 2 3 :record-staged t nil)))
(assert-event (equal (fl-k3-exec *otf-z* *fl-z1* :stage) '(t t t 2 3 :record-staged t nil)))
(assert-event (equal (fl-k3-exec *otf-z* *fl-z1* :same) '(t t t 2 3 :reserved t nil)))
; the article hypothesis removed: the unfiled record is interned and staged
(assert-event (equal (fl-k3-exec *otf-z* *fl-u1* :stage) '(t nil t 2 3 :record-staged nil nil)))
; the files hypothesis removed: the Store already holds the unfiled *otf-bad*
(assert-event (equal (fl-k3-exec *otf-bad* *fl-w1* :stage) '(nil t t 2 3 :record-staged nil nil)))
; (not (equal row :bad)) removed: the intern refuses the event and the prepare stages nothing
(assert-event (equal (fl-k3-exec *otf-z* 5 :stage) '(t t nil 2 2 :reserved t nil)))

; K3a FN-O1-PREPARE-INTERNED-KEEPS-THE-HISTORY: the article entry the host calls.
(defun fl-k3a (w0 w fn-arena)
  (declare (xargs :mode :program :stobjs fn-arena))
  (mv-let (s fn-arena) (fl-one-store w0 fn-arena)
    (let ((hyp-files (fn-o1-files-invp (fn-sn-files s) fn-arena))
          (art (fn-o1-records-filed-or-reclaimedp (list w))))
      (mv-let (s2 fn-arena)
        (fn-store-prepare-interned s w fn-arena)
        (mv (list hyp-files art (fn-sf-phase (fn-sn-files s2))
                  (fn-o1-files-invp (fn-sn-files s2) fn-arena)
                  (otf-files-filed-only-invp (fn-sn-files s2) fn-arena))
            fn-arena)))))
(defun fl-k3a-exec (w0 w)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena (mv-let (r fn-arena) (fl-k3a w0 w fn-arena) r)))
(assert-event (equal (fl-k3a-exec *otf-z* *fl-w1*) '(t t :record-staged t nil)))
(assert-event (equal (fl-k3a-exec *otf-z* *fl-z1*) '(t t :record-staged t nil)))
(assert-event (equal (fl-k3a-exec *otf-z* *fl-u1*) '(t nil :record-staged nil nil)))     ; article hypothesis
(assert-event (equal (fl-k3a-exec *otf-bad* *fl-w1*) '(nil t :record-staged nil nil)))   ; files hypothesis

; K3b FN-O1-PREPARE-IDENTITY-INTERNED-KEEPS-THE-HISTORY: the composite entry.
; The Store holds the enrollment and the composite of REC0; the composite of
; REC1 is interned under the Store's keyring and staged.
(defun fl-k3b (rec0 rec1 fn-arena)
  (declare (xargs :mode :program :stobjs fn-arena))
  (mv-let (rows fn-arena)
    (fn-hrt-events (list *sit-enrollment* (otf-sig-wire rec0)) nil 0 fn-arena)
    (let* ((s (fn-sit-reserve (fn-sit-commit-identity *sit-after-enrollment* (cadr rows))))
           (w (otf-sig-wire rec1))
           (hyp-files (fn-o1-files-invp (fn-sn-files s) fn-arena))
           (art (fn-o1-records-filed-or-reclaimedp (list (fn-bpr-event-article w)))))
      (mv-let (row fn-arena)
        (fn-intern-event w (fn-sn-keyring s) (fn-sn-keyring-generation s) fn-arena)
        (let ((s2 (fn-sn-prepare-identity s row)))
          (mv (list (fn-sn-statep s) (len (fn-sf-records (fn-sn-files s))) hyp-files art (fn-hstxa-p row)
                    (fn-sf-phase (fn-sn-files s2))
                    (fn-o1-files-invp (fn-sn-files s2) fn-arena)
                    (otf-files-filed-only-invp (fn-sn-files s2) fn-arena))
              fn-arena))))))
(defun fl-k3b-exec (r0 r1)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena (mv-let (r fn-arena) (fl-k3b r0 r1 fn-arena) r)))
(defconst *fl-sg1* (otf-sig-record 1 (otf-sig-src 1 "example,other")))
(defconst *fl-sz1* (fn-rclp-tombstoned *fl-sg1*))
(defconst *fl-sb1* (otf-sig-record 1 (otf-sig-src 1 "other")))
(defconst *fl-sg2* (otf-sig-record 2 (otf-sig-src 2 "example,other")))
(defconst *fl-sz2* (fn-rclp-tombstoned *fl-sg2*))
(defconst *fl-sb2* (otf-sig-record 2 (otf-sig-src 2 "other")))
(assert-event (equal (fl-k3b-exec *fl-sz1* *fl-sg2*) '(t 2 t t t :record-staged t nil)))
(assert-event (equal (fl-k3b-exec *fl-sz1* *fl-sz2*) '(t 2 t t t :record-staged t nil)))
(assert-event (equal (fl-k3b-exec *fl-sz1* *fl-sb2*) '(t 2 t nil t :record-staged nil nil)))  ; article hypothesis
(assert-event (equal (fl-k3b-exec *fl-sb1* *fl-sg2*) '(t 2 nil t t :record-staged nil nil)))  ; files hypothesis

; --------------------------------------------------------------------------
; K4 FN-O1-RECLAIM-SWAP-KEEPS-THE-HISTORY, on the owner recovered over the
; interned rows of a wire history WS: the pass rewrites its rows under RULE
; (:released-by-all-holders rewrites every unheld article to a tombstone,
; :keep-forever rewrites none), interns them at the arena's count, rebuilds
; with MC connections and swaps.  Items: the owner opened, the rows
; hypothesis, rows changed by the rewrite, rebuilt not :fault, the swapped
; Store's record count, the conclusion, the mutant, the old predicate.
(defun fl-k4 (ws rule mc fn-arena)
  (declare (xargs :mode :program :stobjs fn-arena))
  (let* ((oc (p4-open ws))
         (live (fn-ocfg-owner oc))
         (fn-arena (fn-arena-clear fn-arena))
         (fn-arena (fn-arn-seal-many (p4-payloads ws) fn-arena))
         (rows (fn-sf-records (fn-sn-files (fn-own-store live))))
         (ctx (fn-rclp-ctx rule 0 (fn-own-store live)))
         (hyp (fn-o1-rows-invp rows fn-arena))
         (rw (fn-orc-rewrite-rows rows ctx fn-arena)))
    (mv-let (rows2 fn-arena)
      (fn-orcp-intern-rows rw (fn-stxk-initial-context 0) fn-arena)
      (let* ((rebuilt (cadr (fn-orcp-rebuild rows2 *p4-configs* 8 mc)))
             (swapped (fn-orcp-swapped-owner live (fn-ocfg-owner rebuilt)))
             (files (fn-sn-files (fn-own-store swapped))))
        (mv (list (not (equal oc :fault)) hyp (not (equal rows rw)) (not (equal rebuilt :fault))
                  (len (fn-sf-records files))
                  (fn-o1-files-invp files fn-arena)
                  (otf-files-filed-only-invp files fn-arena)
                  (fn-o1-records-filedp (fn-cat-history-articles (fn-sf-records files) fn-arena)))
            fn-arena)))))
(defun fl-k4-exec (ws rule mc)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena (mv-let (r fn-arena) (fl-k4 ws rule mc fn-arena) r)))
; satisfiable: two filed articles are reclaimed by the swap; the old predicate is false after it
(assert-event (equal (fl-k4-exec *p3-h* '(:released-by-all-holders) 4) '(t t t t 2 t nil nil)))
; the pass that rewrites nothing is the identity swap
(assert-event (equal (fl-k4-exec *p3-h* '(:keep-forever) 4) '(t t nil t 2 t t t)))
; the rows hypothesis removed (the unfiled record recovery accepts, rewritten by nothing)
(assert-event (equal (fl-k4-exec (list *p3-w0* *p4-swap*) '(:keep-forever) 4) '(t nil nil t 2 nil nil nil)))
; (not (equal rebuilt :fault)) removed: the swap over a fault is an empty Store, invariant
(assert-event (equal (fl-k4-exec *p3-h* '(:released-by-all-holders) -1) '(t t t nil 0 t t t)))

; --------------------------------------------------------------------------
; K5a FN-O1-REOPEN-KEEPS-THE-HISTORY: the full replay of the decoded journal WS.
; Items: car fr not :bad, oc not :fault, the premise, the record count, the
; conclusion, the mutant, the old premise.
(defun fl-k5a (ws)
  (declare (xargs :mode :program))
  (let* ((fr (fn-scka-full-recover *p4-configs* ws))
         (oc (fn-ock-recover-extended (car fr) *p4-configs* 8 4)))
    (with-local-stobj fn-arena
      (mv-let (r fn-arena)
        (let* ((fn-arena (fn-arena-clear fn-arena))
               (fn-arena (fn-arn-seal-many (cadr fr) fn-arena))
               (files (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
          (mv (list (not (equal (car fr) :bad)) (not (equal oc :fault))
                    (fn-o1-records-filed-or-reclaimedp (fn-bpr-article-records ws))
                    (len (fn-sf-records files))
                    (fn-o1-files-invp files fn-arena)
                    (otf-files-filed-only-invp files fn-arena)
                    (fn-o1-records-filedp (fn-bpr-article-records ws)))
              fn-arena))
        r))))
(assert-event (equal (fl-k5a *p3-h*) '(t t t 2 t t t)))
(assert-event (equal (fl-k5a *p5-hz*) '(t t t 2 t nil nil)))              ; reclaimed record: the old premise is false
(assert-event (equal (fl-k5a (list *p3-w0* *p4-swap*)) '(t t nil 2 nil nil nil)))   ; premise removed
; a failed open (an unfiled record the replay refuses; a non-record): no owner, and the
; empty Store the conclusion then reads is invariant
(assert-event (equal (take 2 (fl-k5a *p3-hbad*)) '(nil nil)))
(assert-event (equal (take 2 (fl-k5a (list 5))) '(nil nil)))

; K5b FN-O1-CHECKPOINT-REOPEN-KEEPS-THE-HISTORY: the capture of the prefix WS,
; its arena, the suffix VS interned on top.  Items: (true-listp ws), the whole
; journal interns, oc not :fault, the premise, the record count, the
; conclusion, the mutant, the old premise.
(defun fl-k5b (ws vs fn-arena)
  (declare (xargs :mode :program :stobjs fn-arena))
  (let* ((c (fn-sco-capture *p4-configs* (fn-scka-intern-at ws (fn-stxk-initial-context 0) 0)))
         (fn-arena (fn-arena-clear fn-arena))
         (fn-arena (fn-arn-seal-many (fn-scka-payloads ws) fn-arena)))
    (mv-let (ext fn-arena)
      (fn-scka-recover-rows c *p4-configs* vs fn-arena)
      (let ((oc (fn-ock-recover-extended ext *p4-configs* 8 4))
            (whole-ok (not (equal (fn-scka-intern-at (append ws vs) (fn-stxk-initial-context 0) 0) :bad))))
        (if (equal oc :fault)
            (mv (list (true-listp ws) whole-ok nil) fn-arena)
          (let ((files (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
            (mv (list (true-listp ws) whole-ok t
                      (fn-o1-records-filed-or-reclaimedp (fn-bpr-article-records (append ws vs)))
                      (len (fn-sf-records files))
                      (fn-o1-files-invp files fn-arena)
                      (otf-files-filed-only-invp files fn-arena)
                      (fn-o1-records-filedp (fn-bpr-article-records (append ws vs))))
                fn-arena)))))))
(defun fl-k5b-exec (ws vs)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena (mv-let (r fn-arena) (fl-k5b ws vs fn-arena) r)))
(assert-event (equal (fl-k5b-exec (list *p3-w0*) (list *p5-z1*)) '(t t t t 2 t nil nil)))       ; reclaimed in the suffix
(assert-event (equal (fl-k5b-exec (list *p3-w0* *p5-z1*) nil) '(t t t t 2 t nil nil)))          ; reclaimed in the prefix
(assert-event (equal (fl-k5b-exec nil *p5-hz*) '(t t t t 2 t nil nil)))                         ; empty prefix
(assert-event (equal (fl-k5b-exec (list *p3-w0*) (list *p4-swap*)) '(t t t nil 2 nil nil nil))) ; premise removed
; the whole-journal intern hypothesis removed: *p5-z1* is sequence 1 at position 0, the
; whole journal does not intern; the Store opened over the empty capture is invariant
(assert-event (equal (fl-k5b-exec (list *p5-z1*) nil) '(t nil t t 0 t t nil)))
; oc :fault: the suffix is not a record (the whole journal does not intern either)
(assert-event (equal (fl-k5b-exec (list *p3-w0*) (list 5)) '(t nil nil)))

; K5c FN-O1-JOURNAL-OF-THE-HISTORY: what a live history writes (the rows'
; wire events) has filed-or-reclaimed articles.  Items: the rows hypothesis,
; the conclusion, the journal's article count, the old predicate.
(defun fl-k5c (wires fn-arena)
  (declare (xargs :mode :program :stobjs fn-arena))
  (mv-let (rows fn-arena)
    (fn-intern-events wires nil 0 fn-arena)
    (let ((journal (fn-bpr-article-records (fn-rows-wire-of rows fn-arena))))
      (mv (list (fn-o1-rows-invp rows fn-arena)
                (fn-o1-records-filed-or-reclaimedp journal)
                (len journal)
                (fn-o1-records-filedp journal))
          fn-arena))))
(defun fl-k5c-exec (wires)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena (mv-let (r fn-arena) (fl-k5c wires fn-arena) r)))
; a composite row whose stxa carries one article and whose held row is another
(defun fl-k5c-forged (stxa-wire held-wire fn-arena)
  (declare (xargs :mode :program :stobjs fn-arena))
  (mv-let (rows fn-arena)
    (fn-intern-events (list stxa-wire held-wire) nil 0 fn-arena)
    (let* ((forged (fn-hstxa-make (fn-hstxa-stxa (car rows)) (cadr rows)))
           (rs (list forged))
           (journal (fn-bpr-article-records (fn-rows-wire-of rs fn-arena))))
      (mv (list (fn-o1-rows-invp rs fn-arena)
                (fn-o1-records-filed-or-reclaimedp (fn-cat-history-articles rs fn-arena))   ; the records conjunct holds
                (fn-rows-composites-okp rs fn-arena)                                        ; the composites conjunct fails
                (fn-o1-records-filed-or-reclaimedp journal)                                 ; the conclusion fails
                (len journal))
          fn-arena))))
(defun fl-k5c-forged-exec (a b)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena (mv-let (r fn-arena) (fl-k5c-forged a b fn-arena) r)))
(assert-event (equal (fl-k5c-exec (list *p3-w0* *p5-z1*)) '(t t 2 nil)))                              ; reclaimed record
(assert-event (equal (fl-k5c-exec (list *sit-enrollment* (otf-sig-wire *fl-sz1*))) '(t t 2 nil)))    ; reclaimed composite article
(assert-event (equal (fl-k5c-exec (list *p3-w0* *p3-bad*)) '(nil nil 2 nil)))                         ; rows hypothesis removed
(assert-event (equal (fl-k5c-exec (list *sit-enrollment* (otf-sig-wire *fl-sb1*))) '(nil nil 2 nil))) ; unfiled composite article
; the composites conjunct alone: the held article is filed, the stxa's is not
(assert-event (equal (fl-k5c-forged-exec (otf-sig-wire *fl-sb1*) *otf-good*) '(nil t nil nil 1)))

; --------------------------------------------------------------------------
; K6 FN-O1-LOAD-MAKES-THE-CATALOG-POSITIONAL and K7 FN-O1-INSTALLED-CATALOG-
; ROWS-ARE-RECLAIMED-OR-WITHIN-HEADER: the catalog the install loads
; (fn-sca-load-held-rows) over the rows of the owner recovered from WS, at row
; I.  Items: fn-sf-record-valuesp of the rows, the rows hypothesis, the
; catalog's count, positional (K6, no hypothesis), the row's article a
; tombstone, within its header (the mutated conclusion), the conclusion.
(defun fl-k7 (ws i fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((own (fn-ocfg-owner (p4-open ws)))
         (rows (fn-sf-records (fn-sn-files (fn-own-store own))))
         (view (fn-own-view own))
         (fn-arena (fn-arena-clear fn-arena))
         (fn-arena (fn-arn-seal-many (p4-payloads ws) fn-arena))
         (valuesp (fn-sf-record-valuesp rows))
         (invp (fn-o1-rows-invp rows fn-arena))
         (fn-cat (fn-cat-clear fn-cat))
         (fn-cat (fn-sca-load-held-rows rows (fn-midx-build (fn-state-articles (fn-own-view-archive view))) fn-arena fn-cat))
         (article (fn-cat-row-article i fn-arena fn-cat))
         (tomb (fn-nntp-article-tombstonep article fn-arena))
         (within (fn-o1-article-within-headerp article (fn-nntp-article-bytes article fn-arena))))
    (mv (list valuesp invp (fn-cat-count fn-cat) (fn-o1-cat-positionalp fn-cat)
              (if tomb t nil) (if within t nil) (if (or tomb within) t nil))
        fn-arena fn-cat)))
(defun fl-k7-exec (ws i)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (r fn-arena)
      (with-local-stobj fn-cat
        (mv-let (r fn-arena fn-cat) (fl-k7 ws i fn-arena fn-cat) (mv r fn-arena)))
      r)))
(assert-event (equal (fl-k7-exec *p5-hz* 0) '(t t 2 t nil t t)))        ; the filed row
(assert-event (equal (fl-k7-exec *p5-hz* 1) '(t t 2 t t nil t)))        ; the reclaimed row: a tombstone, not within its header
(assert-event (equal (fl-k7-exec *p3-h* 1) '(t t 2 t nil t t)))
; the rows hypothesis removed: the swapped record recovery accepts
(assert-event (equal (fl-k7-exec (list *p3-w0* *p4-swap*) 1) '(t nil 2 t nil nil nil)))
; K6 has no hypothesis (positional in every instance above); fn-sf-record-valuesp has no
; runtime removal witness: a catalog loaded from a non-record row is not a live fn-cat.
