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
(include-book "must-fail-checked")
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
      (eq (symbol-class 'fn-ock-capture-budget (w state)) :common-lisp-compliant)
      ; the host's per-step entry, its step, and the reader's load (checkpoint-pipeline-4)
      (eq (symbol-class 'fn-ockp-batch (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ockp-step (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ockp-statep (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ockp-initial-state (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ockp-donep (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ockp-segment-octets (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sct-load (w state)) :common-lisp-compliant)))

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
(defconst *sctt-tables* (fn-sct-tables-of-capture *sctt-capture* 9 "rev-test" nil))
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

(defun sctt-run (b bytes budget free)
  ; (VERDICT-OF-SETUP OCTETS STEPS LOADED); B rows and BYTES octets per step
  (declare (xargs :guard (and (natp b) (natp budget)) :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (result fn-octets)
      (let* ((setup (fn-ockp-setup *sctt-capture* 9 "rev-test" nil *sctt-seg* budget free))
             (verdict (car setup)))
        (if (not (and (consp verdict) (eq (car verdict) :plan)))
            (mv (list verdict nil 0 nil) fn-octets)
          (mv-let (v octets fn-octets)
            (fn-ockp-run setup (fn-ockp-initial-state (cadr setup) fn-octets) b bytes *sctt-seg*
                         *sctt-s* 100000 100000000 1000 fn-octets)
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
; plan of them loads to the tables; the tables mean the capture.  The octet
; bound per step: unbounded (1000000), one octet (every step ends after its
; first row) and the segment size.
(assert-event
 (let ((r (sctt-run 1 1000000 (len (sctt-file)) *sctt-free*)))
   (and (equal (car r) (list :plan (len (sctt-file))))
        (equal (cadr r) (sctt-file))
        (eq (caddr r) :ok)
        (equal (cadddr r) (list :ok *sctt-tables*))
        (equal (fn-sct-capture-of-tables (cadr (cadddr r))) *sctt-capture*))))
(assert-event
 (and (equal (cadr (sctt-run 3 1000000 (len (sctt-file)) *sctt-free*)) (sctt-file))
      (equal (cadr (sctt-run 1000 1000000 (len (sctt-file)) *sctt-free*)) (sctt-file))
      (equal (cadr (sctt-run 1000 1 (len (sctt-file)) *sctt-free*)) (sctt-file))
      (equal (cadr (sctt-run 1000 *sctt-seg* (len (sctt-file)) *sctt-free*)) (sctt-file))))

; The refusal at the budget boundary, both sides (PRF-200): one octet
; below the file's length is deferred by name with both numbers and NOTHING
; is written; at the length, a plan.  The space deferral: free space whose
; figure less the reserve is below the estimate.
(assert-event
 (let* ((n (len (sctt-file)))
        (below (sctt-run 1 1000000 (1- n) *sctt-free*))
        (unobserved (sctt-run 1 1000000 (+ n 1000) nil))
        (space (sctt-run 1 1000000 (+ n 1000) (+ n (fn-smr-reserve-octets) -1)))
        (enough (sctt-run 1 1000000 (+ n 1000) (+ n (fn-smr-reserve-octets)))))
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
; The sequence half of the index by fn-cei-put; the Message-ID half built
; directly (fn-cei-msgid-add indexes only a record the full recognizer
; admits, which a hand-made shape is not): what the capture's index holds
; for a real article.
(defconst *sctt-mindex* (fn-cei-put 0 *sctt-record* nil))
(defconst *sctt-mtrie* (fn-midx-put-chars (coerce "<a@x>" 'list) (list *sctt-record*) nil))
(defconst *sctt-r* (list "node" (list (list "<a@x>" *sctt-payload* '("g") nil t 0)) 7))

(assert-event
 (and (equal (fn-sct-payload-of *sctt-record*) *sctt-payload*)
      (equal (fn-sct-ref-get 0 *sctt-mindex*) *sctt-payload*)
      (equal (fn-cei-trie-records "<a@x>" *sctt-mtrie*) (list *sctt-record*))
      (equal (fn-sct-candidate (list "<a@x>" *sctt-payload*) *sctt-mtrie* 1 *sctt-mindex*) 0)
      (let* ((prog (fn-sct-program *sctt-r* nil *sctt-mtrie* 1 *sctt-mindex*))
             (literal (fn-scc-program *sctt-r*))
             (ptable (fn-cei-build (list *sctt-payload*))))
        (and (< (len prog) (len literal))
             ; the literal leaf: op, a length of one digit (count byte and
             ; digit), the 20 octets; the reference: op and nat 0 (one
             ; count byte, no digit)
             (equal (- (len literal) (len prog)) (- (+ 1 2 (len *sctt-payload*)) 2))
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
; The writer's segment size (checkpoint-pipeline-5): the development
; profile's R (32,768) stays the segment under a 4 MiB step; the scale-1m
; profile's R (17,138,486) gives a 1 MiB segment; a bound of 0 gives 1.
(assert-event
 (and (equal (fn-ockp-segment-octets 32768 4194304) 32768)
      (equal (fn-ockp-segment-octets 17138486 4194304) 1048576)
      (equal (fn-ockp-segment-octets 0 4194304) 1)
      (equal (fn-ockp-segment-octets 17138486 0) 1)
      (equal (fn-ockp-segment-octets "r" 4194304) 1)))

; -----------------------------------------------------------------------------
; The invariants carried between steps (checkpoint-pipeline-5, PKT-583 (a)).
; The host's entry checks fn-ockp-statep (O(1)) per step and nothing else;
; the rows' encodability is established once by the setup and preserved by
; every step.  A witness from the ground capture: the initial state is
; encodable and well shaped, the first step answers :ok, its state is both
; again; a state holding a row the codec refuses (a natural of 2^2040) makes
; the step answer :unencodable with nothing written.

(defun sctt-step (setup pst)
  ; (VERDICT FRAMES STATE' STATEP' ENCODABLE') over a fresh buffer
  (declare (xargs :guard t :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (result fn-octets)
      (mv-let (verdict frames pst2 fn-octets)
        (fn-ockp-step setup pst 1000 1000000 *sctt-seg* *sctt-s* 100000 100000000 fn-octets)
        (mv (list verdict frames pst2 (fn-ockp-statep pst2 fn-octets) (fn-ockp-state-encodablep pst2))
            fn-octets))
      result)))

(defconst *sctt-setup* (fn-ockp-setup *sctt-capture* 9 "rev-test" nil *sctt-seg* 100000000 *sctt-free*))

(defun sctt-initial (tables)
  ; (STATE STATEP) of the pipeline's start over a fresh buffer
  (declare (xargs :guard t :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (r fn-octets)
      (mv (list (fn-ockp-initial-state tables fn-octets)
                (fn-ockp-statep (fn-ockp-initial-state tables fn-octets) fn-octets))
          fn-octets)
      r)))

(defun sctt-run-from (setup pst)
  ; (VERDICT OCTETS) of the loop from a given state over a fresh buffer
  (declare (xargs :guard t :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (r fn-octets)
      (mv-let (v octets fn-octets)
        (fn-ockp-run setup pst 1000 1000000 *sctt-seg* *sctt-s* 100000 100000000 10 fn-octets)
        (mv (list v octets) fn-octets))
      r)))
(defconst *sctt-bad-capture* (fn-sco-capture *sctt-configs* (list (expt 2 2040))))
(defconst *sctt-bad-tables* (fn-sct-tables-of-capture *sctt-bad-capture* 9 "r" nil))
; A hand-made setup over the unencodable tables (fn-ockp-setup refuses them,
; so the step is never reached this way in the composition: the witness
; for the hypothesis that says so).
(defconst *sctt-bad-setup*
  (list (list :plan 0) *sctt-bad-tables* (list 1 1 1 1) nil (fn-sco-event-index *sctt-bad-capture*)
        1 0))

(assert-event
 (and (equal (car *sctt-setup*) (list :plan (len (sctt-file))))
      (fn-ockp-tables-encodablep (cadr *sctt-setup*))
      (let* ((init (sctt-initial (cadr *sctt-setup*)))
             (pst (car init))
             (r (sctt-step *sctt-setup* pst)))
        (and (cadr init)
             (fn-ockp-state-encodablep pst)
             (eq (car r) :ok) (consp (cadr r))
             (nth 3 r) (nth 4 r)))
      ; a row the codec refuses: :unencodable, nothing written
      (let ((r (sctt-step *sctt-setup* (list 1 (list (expt 2 2040)) 0 0 *fn-scc-genesis* 0 0))))
        (and (eq (car r) :unencodable) (null (cadr r))))
      ; the run from such a state answers :unencodable
      (equal (sctt-run-from *sctt-setup* (list 1 (list (expt 2 2040)) 0 0 *fn-scc-genesis* 0 0))
             (list :unencodable nil))
      ; unencodable tables behind an encodable state: the run's end hands the
      ; step the E table the codec refuses, so the next state is not encodable
      (not (fn-ockp-tables-encodablep *sctt-bad-tables*))
      (let ((r (sctt-step *sctt-bad-setup* (list 1 nil 0 0 *fn-scc-genesis* 0 0))))
        (and (eq (car r) :ok) (not (nth 4 r))))))

; A state that is not well shaped (K a string; one row per step so the run
; continues and K is carried) leaves the next state not well shaped.  A ground theorem, not an evaluation: the
; call is outside the step's guard (fn-ockp-statep), so a proof evaluates it
; by the logic where an evaluation refuses (as sctt-decide-without-natp-
; estimate-witness).
(defthm sctt-step-without-shape-witness
  (let ((r (fn-ockp-step *sctt-setup* (list "a" (list nil nil) 0 0 *fn-scc-genesis* 0 0)
                         1 1000000 *sctt-seg* *sctt-s* 100000 100000000 nil)))
    (and (not (fn-ockp-statep (list "a" (list nil nil) 0 0 *fn-scc-genesis* 0 0) nil))
         (equal (car r) :ok)
         (not (fn-ockp-statep (mv-nth 2 r) (mv-nth 3 r)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ockp-step fn-ockp-statep))))

; fn-ockp-step-preserves-encodable without its state hypothesis (the
; :unencodable witness above), and without its tables hypothesis (the
; unencodable tables behind an encodable state).
(must-fail-checked
 (defthm sctt-r-step-preserves-encodable-without-state
   (implies (fn-ockp-tables-encodablep (fn-sco-at 1 setup))
            (let ((r (fn-ockp-step setup pst b bytes seg s segment-bound file-bound fn-octets)))
              (and (not (equal (car r) :unencodable))
                   (fn-ockp-state-encodablep (mv-nth 2 r)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-ockp-step fn-ockp-step-preserves-encodable)))))
(must-fail-checked
 (defthm sctt-r-step-preserves-encodable-without-tables
   (implies (fn-ockp-state-encodablep pst)
            (fn-ockp-state-encodablep
             (mv-nth 2 (fn-ockp-step setup pst b bytes seg s segment-bound file-bound fn-octets))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-ockp-step fn-ockp-step-preserves-encodable)))))

; fn-ockp-step-preserves-statep without its shape hypothesis (the string K
; above).
(must-fail-checked
 (defthm sctt-r-step-preserves-statep-without-shape
   (fn-ockp-statep (mv-nth 2 (fn-ockp-step setup pst b bytes seg s segment-bound file-bound
                                           fn-octets))
                   (mv-nth 3 (fn-ockp-step setup pst b bytes seg s segment-bound file-bound
                                           fn-octets)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-ockp-step fn-ockp-step-preserves-statep)))))

; fn-ockp-run-of-encodable-never-refuses-a-row without its state hypothesis
; (the run above answers :unencodable).
(must-fail-checked
 (defthm sctt-r-run-never-refuses-without-state
   (implies (fn-ockp-tables-encodablep (fn-sco-at 1 setup))
            (not (equal (car (fn-ockp-run setup pst b bytes seg s segment-bound file-bound fuel
                                          fn-octets))
                        :unencodable)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-ockp-run fn-ockp-run-of-encodable-never-refuses-a-row
                                fn-ockp-setup-not-unencodable-never-refuses-a-row)))))

; -----------------------------------------------------------------------------
; Per hypothesis (each must-fail closes the codec in its hint).

; fn-sct-decode-file-of-file-is-the-capture, its width hypothesis: a value
; whose S is 2^64 wraps the header field, so the read sequence differs.
(assert-event
 (let* ((big (expt 2 64))
        (segs (fn-sct-run-segments (fn-sct-rows-program (list (fn-sct-f-row big 9 "r" nil)) 0 nil nil big nil)
                                   64 big)))
   (not (equal (nth 3 (fn-scc-parse-header (car segs))) big))))
(must-fail-checked
 (defthm sctt-r-decode-file-without-width
   (let* ((c (fn-sco-capture configs records))
          (tables (fn-sct-tables-of-capture c frontier revision log))
          (progs (fn-sct-table-programs tables (fn-sco-event-index c))))
     (implies (and (fn-sct-tables-treep tables)
                   (fn-sct-log-positionp log)
                   (<= (len records) (1+ *fn-cbor-max-uint*)))
              (equal (fn-sct-decode-file (fn-sct-file-segments progs seg (len records)))
                     (list :ok tables))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-sct-decode-file fn-sct-file-segments fn-sct-table-programs
                                fn-sct-tables-of-capture fn-sco-capture
                                fn-sct-decode-file-of-file-is-the-capture
                                fn-sct-decode-file-of-file-segments)))))

; The F row's log position (lane log-recovery): a reachable witness of
; fn-sct-decode-file-of-file-is-the-capture with a position (segment 3, a
; 32-octet genesis): every hypothesis holds and the file reads back the tables,
; the position included.
(defconst *sctt-log* (list 3 (make-list 32 :initial-element 7)))
(defconst *sctt-log-tables* (fn-sct-tables-of-capture *sctt-capture* 9 "rev-test" *sctt-log*))
(defconst *sctt-log-progs* (fn-sct-table-programs *sctt-log-tables* *sctt-index*))
(assert-event
 (and (fn-sct-tables-treep *sctt-log-tables*)
      (fn-sct-log-positionp *sctt-log*)
      (<= (len *sctt-events*) (1+ *fn-cbor-max-uint*))
      (fn-sct-programs-widthp *sctt-log-progs*)
      (equal (fn-sct-decode-file (fn-sct-file-segments *sctt-log-progs* *sctt-seg* *sctt-s*))
             (list :ok *sctt-log-tables*))
      (equal (fn-sct-tables-log *sctt-log-tables*) *sctt-log*)
      (equal (fn-sct-capture-of-tables *sctt-log-tables*) *sctt-capture*)))
; Its log-position hypothesis: a position of segment 0 is written and the
; read refuses the F row by name; the other hypotheses hold.
(defconst *sctt-bad-log* (list 0 (make-list 32 :initial-element 7)))
(defconst *sctt-bad-log-tables* (fn-sct-tables-of-capture *sctt-capture* 9 "rev-test" *sctt-bad-log*))
(defconst *sctt-bad-log-progs* (fn-sct-table-programs *sctt-bad-log-tables* *sctt-index*))
(assert-event
 (and (fn-sct-tables-treep *sctt-bad-log-tables*)
      (not (fn-sct-log-positionp *sctt-bad-log*))
      (fn-sct-programs-widthp *sctt-bad-log-progs*)
      (equal (fn-sct-decode-file (fn-sct-file-segments *sctt-bad-log-progs* *sctt-seg* *sctt-s*))
             (list :refused :f-row))))
(must-fail-checked
 (defthm sctt-r-decode-file-without-log-position
   (let* ((c (fn-sco-capture configs records))
          (tables (fn-sct-tables-of-capture c frontier revision log))
          (progs (fn-sct-table-programs tables (fn-sco-event-index c))))
     (implies (and (fn-sct-tables-treep tables)
                   (<= (len records) (1+ *fn-cbor-max-uint*))
                   (fn-sct-programs-widthp progs))
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
(must-fail-checked
 (defthm sctt-r-run-of-program-without-agreement
   (implies (fn-scc-treep x)
            (equal (fn-sct-run (append (fn-sct-program x cand mtrie n te) rest) stack td)
                   (fn-sct-run rest (cons x stack) td)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-sct-run fn-sct-program fn-sct-run-of-program)))))

; fn-ockp-decide-defers-by-the-estimate, its natp hypothesis on the
; estimate (checkpoint-pipeline-4; the one on the budget was removed after
; the weakened theorem was proved): a rational estimate above a budget of 0
; is deferred by name, yet the recorded deferral does not block a later
; budget of 0, where the conclusion says it does (`fn-ock-publication-
; blockedp' compares naturals).  The retained hypotheses: none.
; A ground theorem, not an assert-event: the call is outside the decision's
; guard, and a proof evaluates it by the logic where an evaluation refuses.
(defthm sctt-decide-without-natp-estimate-witness
  (let ((verdict (fn-ockp-decide 1/2 0 nil)))
    (and (not (natp 1/2))
         (equal verdict (list :deferred :exceeds-budget 1/2 0))
         (not (iff (fn-ock-publication-blockedp verdict 0 0) (< (nfix 0) 1/2)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ockp-decide fn-ock-publication-blockedp fn-ockp-space))))
(must-fail-checked
 (defthm sctt-r-decide-without-natp-estimate
   (let ((verdict (fn-ockp-decide estimate budget free)))
     (implies (< budget estimate)
              (iff (fn-ock-publication-blockedp verdict later-budget later-space)
                   (< (nfix later-budget) estimate))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-ockp-decide fn-ock-publication-blockedp)
                            (fn-ockp-decide-defers-by-the-estimate))))))

; fn-ockp-estimate-is-len-file-octets, its encodability hypothesis: a table
; whose row the codec refuses (a leaf of 2^2040 octets is not constructible;
; a natural of 2^2040 is) has a file of :unencodable frames, length 0.
(assert-event
 (let* ((c (fn-sco-capture *sctt-configs* (list (expt 2 2040))))
        (tables (fn-sct-tables-of-capture c 9 "r" nil)))
   (and (not (fn-ockp-tables-encodablep tables))
        (equal (car (fn-ockp-setup c 9 "r" nil 64 1000000 nil)) :unencodable))))
(must-fail-checked
 (defthm sctt-r-estimate-without-encodable
   (equal (len (fn-sct-file-octets (fn-sct-table-programs tables index) seg s))
          (fn-ockp-estimate tables index seg))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-sct-file-octets fn-sct-table-programs fn-ockp-estimate
                                fn-ockp-estimate-is-len-file-octets)))))

; keystone-audit 2026-09-27: books/owner-checkpoint-pipeline.lisp
; fn-ockp-run-writes-the-file and fn-ockp-setup-not-unencodable-never-refuses-
; a-row with the restated LOG argument non-nil (the witnesses above pass nil):
; the pipeline over the capture with the log position *sctt-log* writes the
; file of the tables that carry it, byte for byte, at batch 1 and 1000.
(defun sctt-run-log (log b)
  ; (SETUP-VERDICT RUN-VERDICT OCTETS ENCODABLEP)
  (declare (xargs :guard (natp b) :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (result fn-octets)
      (let* ((setup (fn-ockp-setup *sctt-capture* 9 "rev-test" log *sctt-seg* 100000000 *sctt-free*))
             (tables (fn-sct-tables-of-capture *sctt-capture* 9 "rev-test" log)))
        (mv-let (v octets fn-octets)
          (fn-ockp-run setup (fn-ockp-initial-state tables fn-octets) b 1000000 *sctt-seg*
                       *sctt-s* 100000 100000000 1000 fn-octets)
          (mv (list (car setup) v octets (fn-ockp-tables-encodablep tables)) fn-octets)))
      result)))
(defun sctt-log-file ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-sct-file-octets *sctt-log-progs* *sctt-seg* *sctt-s*))
(assert-event
 (let ((r1 (sctt-run-log *sctt-log* 1))
       (r1000 (sctt-run-log *sctt-log* 1000)))
   (and (nth 3 r1) (not (equal (car r1) :unencodable))
        (eq (nth 1 r1) :ok)
        (equal (nth 2 r1) (sctt-log-file))
        (equal (nth 2 r1000) (sctt-log-file))
        ; non-degenerate: the log position is in the file (it differs from
        ; the file without one)
        (not (equal (sctt-log-file) (sctt-file))))))
