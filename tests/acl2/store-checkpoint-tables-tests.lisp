; fn: teeth for books/store-checkpoint-tables.lisp, store-checkpoint-tables-
; reader.lisp and owner-checkpoint-pipeline.lisp (lane checkpoint-pipeline,
; 2026-09-26; PRF-199, PRF-200; D33, D34).
;
; The ground history is owner-checkpoint-open-tests' image (two retention
; events, two configuration records), captured, written as the schema-3
; tables through the pipeline at batch size 1 and segment size 64 (many
; steps, many segments), loaded back by the buffer reader and compared to
; the capture.  A stored article's payload dedupe is exercised on a
; hand-made R-shaped value against a hand-made event index (the ground
; history holds no article: a signed composite needs keys; the native
; module tests.test_native_checkpoint_auto posts real articles).  The
; refusal at the budget boundary both sides, a row referencing a P row
; past the count, the space deferral below the estimate, and a must-fail
; per keystone hypothesis.  (Attachments evaluate in assert-event: the seal
; is fn-sha256's.)

(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)
(include-book "../../books/owner-checkpoint-pipeline")
(include-book "../../books/store-checkpoint-tables-reader")

; Every executable function the host reaches is guard-verified.
(assert-event
 (and (eq (symbol-class 'fn-sct-payload-of (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sct-run (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sct-program (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sct-decode-rows (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sct-decode-programs (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sct-run-decode (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sct-decode-file (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sct-capture-of-tables (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sctr-run (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sctr-decode-programs (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sctr-run-decode (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ockp-len-acc (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ockp-estimate (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ockp-decide (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sct-renc (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ockp-encode-batch (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ockp-cut-frames (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ockp-setup (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ock-capture-budget (w state)) :common-lisp-compliant)))

(defconst *sctt-events*
  (list (fn-store-retention-event-make :undertake 0 0 0
                                        "forward-sct" "subject" "evidence" 10)
        (fn-store-retention-event-make :release 1 1 1
                                        "forward-sct" "subject" "evidence" 0)))
(defconst *sctt-configs*
  (list *fn-cfg-default-record*
        (fn-cfg-record-make 1 7 2 (list (fn-cfg-set-capacity 1))
                            *fn-cfg-default-stamp*)))
(defconst *sctt-capture* (fn-sco-capture *sctt-configs* *sctt-events*))
(defconst *sctt-tables* (fn-sct-tables-of-capture *sctt-capture* 9 "rev-test"))
(defconst *sctt-index* (fn-sco-event-index *sctt-capture*))
(defconst *sctt-progs* (fn-sct-table-programs *sctt-tables* *sctt-index*))
(defconst *sctt-seg* 64)
(defconst *sctt-s* (len *sctt-events*))
; Free space the host would have observed: ample (an unobserved figure,
; nil, is a deferral by name: the space case below).
(defconst *sctt-free* 1000000000)

; The tables mean the capture, and the list-level file round trip.
(assert-event
 (and (fn-sct-tables-treep *sctt-tables*)
      (fn-ockp-tables-encodablep *sctt-tables*)
      (equal (fn-sct-capture-of-tables *sctt-tables*) *sctt-capture*)
      (equal (fn-sct-decode-programs *sctt-progs*) (list :ok *sctt-tables*))
      (equal (fn-sct-decode-file (fn-sct-file-segments *sctt-progs* *sctt-seg* *sctt-s*))
             (list :ok *sctt-tables*))
      ; more than one segment in the file
      (< 4 (len (fn-sct-file-segments *sctt-progs* *sctt-seg* *sctt-s*)))
      ; the estimate is the file's length
      (equal (fn-ockp-estimate *sctt-tables* *sctt-index* *sctt-seg*)
             (len (fn-sct-file-octets *sctt-progs* *sctt-seg* *sctt-s*)))))

; -----------------------------------------------------------------------------
; The pipeline: the loop at batch size B over a live buffer, the octets it
; wrote read back through the host's plan shape (each segment its own frame
; over a fresh buffer) by fn-sct-load.

(defun sctt-frames-of (octets header-octets trailer-octets acc fuel fn-octets)
  ; The host's read: split OCTETS into frames (HEADER A B TRAILER) by each
  ; header's LENGTH, appending each chunk into the buffer (FUEL bounds the
  ; recursion: one frame per unit).
  (declare (xargs :stobjs fn-octets :guard t :verify-guards nil
                  :measure (nfix fuel)))
  (if (or (zp fuel) (not (consp octets)))
      (mv (if (consp octets) :torn (revappend acc nil)) fn-octets)
    (let* ((header (take header-octets octets))
           (h (fn-scc-parse-header header)))
      (if (or (not h) (< (len octets) (+ header-octets (nth 2 h) trailer-octets)))
          (mv :torn fn-octets)
        (let* ((chunk (take (nth 2 h) (nthcdr header-octets octets)))
               (trailer (take trailer-octets (nthcdr (+ header-octets (nth 2 h)) octets)))
               (rest (nthcdr (+ header-octets (nth 2 h) trailer-octets) octets))
               (a (fn-octets-len fn-octets))
               (fn-octets (fn-octets-append-list chunk fn-octets)))
          (sctt-frames-of rest header-octets trailer-octets
                          (cons (list header a (+ a (len chunk)) trailer) acc)
                          (1- fuel) fn-octets))))))

(defun sctt-run (b budget free)
  ; (VERDICT-OF-SETUP OCTETS STEPS LOADED)
  (declare (xargs :guard (and (natp b) (natp budget)) :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (result fn-octets)
      (let* ((setup (fn-ockp-setup *sctt-capture* 9 "rev-test" *sctt-seg* budget free))
             (verdict (car setup)))
        (if (not (and (consp verdict) (eq (car verdict) :plan)))
            (mv (list verdict nil 0 nil) fn-octets)
          (mv-let (v octets fn-octets)
            (fn-ockp-run setup (fn-ockp-initial-state (cadr setup)) b *sctt-seg* *sctt-s*
                         100000 100000000 1000 fn-octets)
            (let ((fn-octets (fn-octets-clear fn-octets)))
              (mv-let (plan fn-octets)
                (sctt-frames-of octets *fn-scc-segment-header-octets*
                                *fn-frame-trailer-octets* nil 100000 fn-octets)
                (mv (list verdict octets v (if (eq plan :torn) :torn (fn-sct-load plan fn-octets)))
                    fn-octets))))))
      result)))

; The file's octets: the seal is an attachment, which evaluates in
; assert-event and defun bodies, never in defconst.
(defun sctt-file ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-sct-file-octets *sctt-progs* *sctt-seg* *sctt-s*))

; KEYSTONE witness (PRF-199): at batch size 1 and 3 and 1000 the pipeline's
; octets are the file the tables book specifies, byte for byte; the host's
; plan of them loads to the tables; the tables mean the capture.
(assert-event
 (let ((r (sctt-run 1 (len (sctt-file)) *sctt-free*)))
   (and (equal (car r) (list :plan (len (sctt-file))))
        (equal (cadr r) (sctt-file))
        (eq (caddr r) :ok)
        (equal (cadddr r) (list :ok *sctt-tables*))
        (equal (fn-sct-capture-of-tables (cadr (cadddr r))) *sctt-capture*))))
(assert-event
 (and (equal (cadr (sctt-run 3 (len (sctt-file)) *sctt-free*)) (sctt-file))
      (equal (cadr (sctt-run 1000 (len (sctt-file)) *sctt-free*)) (sctt-file))))

; The refusal at the budget boundary, both sides (PRF-200): one octet
; below the file's length is deferred by name with both numbers and NOTHING
; is written; at the length, a plan.  The space deferral: free space whose
; figure less the reserve is below the estimate.
(assert-event
 (let* ((n (len (sctt-file)))
        (below (sctt-run 1 (1- n) *sctt-free*))
        (unobserved (sctt-run 1 (+ n 1000) nil))
        (space (sctt-run 1 (+ n 1000) (+ n (fn-smr-reserve-octets) -1)))
        (enough (sctt-run 1 (+ n 1000) (+ n (fn-smr-reserve-octets)))))
   (and (equal (car below) (list :deferred :exceeds-budget n (1- n)))
        (equal (cadr below) nil)
        (equal (car space) (list :deferred :exceeds-space n (1- n)))
        (equal (cadr space) nil)
        (equal (car enough) (list :plan n))
        (equal (cadr enough) (sctt-file))
        ; an unobserved free-space figure defers by name, budget 0
        (equal (car unobserved) (list :deferred :exceeds-space n 0))
        (fn-ock-publication-blockedp (car below) (1- n) nil)
        (not (fn-ock-publication-blockedp (car below) n nil))
        (fn-ock-publication-blockedp (car space) (+ n 1000) (1- n))
        (fn-ock-publication-blockedp (car space) (+ n 1000) nil)
        (not (fn-ock-publication-blockedp (car space) (+ n 1000) n)))))

; -----------------------------------------------------------------------------
; The reference dedupe on a stored article's payload: a hand-made event
; index holding one article-shaped record at sequence 0 whose payload is
; PAYLOAD, and an R-shaped value holding a stored article (MSGID PAYLOAD
; ...) under that Message-ID: the payload leaf is written as `ref 0' (three
; octets), never literally, and decodes to the same list against the P
; table built from the record's payload.

(defconst *sctt-payload* (list 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20))
; An article record's shape: sequence, txid, generation, Message-ID at 3,
; payload at 4 (fn-record-make's order, books/records-shape).
(defconst *sctt-record* (list 0 5 1 "<a@x>" *sctt-payload* '("g") nil nil nil 0 0))
(defconst *sctt-mindex* (fn-cei-put 0 *sctt-record* nil))
(defconst *sctt-r* (list "node" (list (list "<a@x>" *sctt-payload* '("g") nil t 0)) 7))

(assert-event
 (and (equal (fn-sct-payload-of *sctt-record*) *sctt-payload*)
      (equal (fn-sct-ref-get 0 *sctt-mindex*) *sctt-payload*)
      (equal (fn-cei-trie-records "<a@x>" (fn-cei-msgid-trie *sctt-mindex*))
             (list *sctt-record*))
      (let* ((prog (fn-sct-program *sctt-r* nil (fn-cei-msgid-trie *sctt-mindex*) 1 *sctt-mindex*))
             (literal (fn-scc-program *sctt-r*))
             (ptable (fn-cei-build (list *sctt-payload*))))
        (and (< (len prog) (len literal))
             (equal (- (len literal) (len prog)) (- (+ 1 2 (len *sctt-payload*)) 3))
             (equal (fn-sct-run prog nil ptable) (list *sctt-r*))
             (equal (fn-sct-decode-rows prog ptable) (list :ok (list *sctt-r*)))
             ; a reference to a P row past the count is refused by name
             (equal (fn-sct-decode-rows prog (fn-cei-build nil)) (list :refused :ref))))))

; A row referencing p = count: the program `ref 1' against a one-row P
; table; and p = 0 against it restores the row.
(assert-event
 (let ((ptable (fn-cei-build (list *sctt-payload*))))
   (and (equal (fn-sct-decode-rows (cons *fn-sct-op-ref* (fn-scc-nat-octets 1)) ptable)
               (list :refused :ref))
        (equal (fn-sct-decode-rows (cons *fn-sct-op-ref* (fn-scc-nat-octets 0)) ptable)
               (list :ok (list *sctt-payload*))))))

; The schema refusal: a header of this magic under schema 2 is refused by
; name by the reader's admission, and the open's select names it.
(assert-event
 (let* ((h3 (fn-scc-header 0 1 5 0))
        (h2 (append (take 4 h3) (list 2) (nthcdr 5 h3))))
   (and (equal (car (fn-sccr-admit-segment h3 0 1000 100000)) :ok)
        (equal (fn-sccr-admit-segment h2 0 1000 100000) (list :refused :schema))
        (equal (fn-sco-select-named :schema 0 5 10) (list :full-replay :checkpoint-schema))
        (equal (fn-sco-select-named :ok 3 5 10) (list :checkpoint 3)))))

; -----------------------------------------------------------------------------
; Per hypothesis (each must-fail closes the codec in its hint).

; fn-sct-decode-file-of-file-is-the-capture, its width hypothesis: a value
; whose S is 2^64 wraps the header field, so the read sequence differs.
(assert-event
 (let* ((big (expt 2 64))
        (segs (fn-sct-run-segments (fn-sct-rows-program (list (fn-sct-f-row big 9 "r")) 0 nil nil big nil)
                                   64 big)))
   (not (equal (nth 3 (fn-scc-parse-header (car segs))) big))))
(must-fail
 (defthm sctt-r-decode-file-without-width
   (let* ((c (fn-sco-capture configs records))
          (tables (fn-sct-tables-of-capture c frontier revision))
          (progs (fn-sct-table-programs tables (fn-sco-event-index c))))
     (implies (and (fn-sct-tables-treep tables)
                   (<= (len records) (1+ *fn-cbor-max-uint*)))
              (equal (fn-sct-decode-file (fn-sct-file-segments progs seg (len records)))
                     (list :ok tables))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-sct-decode-file fn-sct-file-segments fn-sct-table-programs
                                fn-sct-tables-of-capture fn-sco-capture
                                fn-sct-decode-file-of-file-is-the-capture
                                fn-sct-decode-file-of-file-segments)))))

; fn-sct-run-of-program, its agreement hypothesis: a decoder table that
; disagrees restores a different list.
(assert-event
 (let* ((prog (fn-sct-program *sctt-payload* 0 nil 1 *sctt-mindex*))
        (other (fn-cei-build (list (list 9 9 9)))))
   (and (equal (car prog) *fn-sct-op-ref*)
        (not (fn-sct-agreep *sctt-mindex* other 1))
        (equal (fn-sct-run prog nil other) (list (list 9 9 9)))
        (not (equal (fn-sct-run prog nil other) (list *sctt-payload*))))))
(must-fail
 (defthm sctt-r-run-of-program-without-agreement
   (implies (fn-scc-treep x)
            (equal (fn-sct-run (append (fn-sct-program x cand mtrie n te) rest) stack td)
                   (fn-sct-run rest (cons x stack) td)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-sct-run fn-sct-program fn-sct-run-of-program)))))

; fn-ockp-decide-defers-by-the-estimate, its (natp budget) hypothesis: a
; non-natural budget defers nothing by the budget.
(assert-event
 (and (not (natp nil))
      (equal (car (fn-ockp-decide 5 nil 1000000)) :plan)))
(must-fail
 (defthm sctt-r-decide-without-natp-budget
   (implies (natp estimate)
            (iff (equal (car (fn-ockp-decide estimate budget free)) :deferred)
                 (or (< budget estimate)
                     (not (natp (fn-ockp-space free)))
                     (< (fn-ockp-space free) estimate))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-ockp-decide-defers-by-the-estimate)))))

; fn-ockp-estimate-is-len-file-octets, its encodability hypothesis: a table
; whose row the codec refuses (a leaf of 2^2040 octets is not constructible;
; a natural of 2^2040 is) has a file of :unencodable frames, length 0.
(assert-event
 (let* ((c (fn-sco-capture *sctt-configs* (list (expt 2 2040))))
        (tables (fn-sct-tables-of-capture c 9 "r")))
   (and (not (fn-ockp-tables-encodablep tables))
        (equal (car (fn-ockp-setup c 9 "r" 64 1000000 nil)) :unencodable))))
(must-fail
 (defthm sctt-r-estimate-without-encodable
   (equal (len (fn-sct-file-octets (fn-sct-table-programs tables index) seg s))
          (fn-ockp-estimate tables index seg))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-sct-file-octets fn-sct-table-programs fn-ockp-estimate
                                fn-ockp-estimate-is-len-file-octets)))))
