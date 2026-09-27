; fn: teeth for books/history-columns.lisp (lane history-columns, 2026-09-27).
;
; What this book is evidence FOR.  The abstraction obligations of the
; history stobj (`fn-hist-append{correspondence}' and the others, checked by
; `defabsstobj') say every export's executable step on the columns equals
; the list operation whenever the correspondence and the guard hold; the
; keystone `fn-hist-load-is-the-history' says the open's load answers the
; history; and the three bridges say the store node's event index answers
; what the stobj answers under the index's correspondence.  The exec path
; runs on a live local stobj (the COLUMNS, not the logical list): a mixed
; history of held articles, a duplicate Message-ID, an accepted-statement
; composite, a malformed :hstxa-headed event, and non-article events, loaded
; under two salts; every answer is compared with the list's.  Each bridge
; gets a ground positive witness asserting its complete antecedent and
; conclusion and, per hypothesis, a witness where the retained hypotheses
; hold, the omitted one fails and the conclusion fails.

(in-package "ACL2")
(include-book "../../books/history-columns")
(include-book "must-fail-checked")

; -----------------------------------------------------------------------------
; The host runs compiled code: every exec function is guard-verified.

(assert-event
 (and (eq (symbol-class 'fn-hist$c-append (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-hist$c-at (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-hist$c-msgid-records (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-hist$c-clear (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-hist-load (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-hist-fnv (w state)) :common-lisp-compliant)))

; -----------------------------------------------------------------------------
; A ground history.

(defun hct-held (seq msgid octets)
  (fn-held-make seq (+ 1 seq) 0 msgid seq '("fn.test") "o" "s" "e" 1 5
                (fn-hf-make octets 14 2 nil nil)
                (fn-hc-make (fn-stx-make-verdict :unverified nil 0) nil 0)
                nil nil))

(defconst *hct-a* (hct-held 0 "<a@x>" 100))
(defconst *hct-b* (hct-held 1 "<b@x>" 200))
(defconst *hct-a2* (hct-held 3 "<a@x>" 300))       ; a second row under <a@x>
(defconst *hct-retention*
  (fn-store-retention-event-make :undertake 2 2 2 "forward" "fwd-subject"
                                 "fwd-evidence" 2))
; An accepted-statement composite whose article is <c@x>.
(defconst *hct-c-wire*
  (fn-record-make 4 4 4 "<c@x>" '(67) '("fn.test") "a4" "s4" "e4" 2 841000004))
(defconst *hct-c-verdict*
  (fn-stxe-make 4 4 4 "<c@x>" :unverified *fn-stx-token-signature* 0 '(112)))
(defconst *hct-stxa*
  (fn-stxa-make 4 4 4 0 '(112) (fn-record-string-octets "s4")
                (fn-record-encode-impl *hct-c-wire*)
                (fn-stxe-encode *hct-c-verdict*)))
(defconst *hct-c* (hct-held 4 "<c@x>" 50))
(defconst *hct-composite* (fn-hstxa-make *hct-stxa* *hct-c*))
; A malformed event headed :hstxa: keyed by shape under <b@x>, never an article.
(defconst *hct-fake* (list :hstxa :not-a-composite (hct-held 5 "<b@x>" 7)))

(defconst *hct-events*
  (list *hct-a* *hct-b* *hct-retention* *hct-a2* *hct-composite* *hct-fake*))

(assert-event (and (fn-held-p *hct-a*) (fn-held-p *hct-b*) (fn-held-p *hct-a2*)
                   (fn-held-p *hct-c*) (fn-hstxa-p *hct-composite*)
                   (not (fn-hstxa-p *hct-fake*))
                   (not (fn-held-p (fn-cei-event-article *hct-fake*)))
                   (equal (fn-hist-key-msgid *hct-fake*) "<b@x>")))

(defconst *hct-msgids* '("<a@x>" "<b@x>" "<c@x>" "<none@x>" ""))

; -----------------------------------------------------------------------------
; The exec path on a live stobj: load, then every answer.

(defun hct-ats (i n fn-hist)
  (declare (xargs :stobjs fn-hist
                  :guard (and (natp i) (natp n) (<= n (fn-hist-count fn-hist)))
                  :measure (nfix (- (nfix n) (nfix i)))))
  (if (and (natp i) (natp n) (< i n))
      (cons (fn-hist-at i fn-hist) (hct-ats (1+ i) n fn-hist))
    nil))

(defun hct-lookups (msgids fn-hist)
  (declare (xargs :stobjs fn-hist :guard (string-listp msgids)))
  (if (consp msgids)
      (cons (fn-hist-msgid-records (car msgids) fn-hist)
            (hct-lookups (cdr msgids) fn-hist))
    nil))

(defun hct-append-all (events fn-hist$c)
  (declare (xargs :stobjs fn-hist$c :guard (true-listp events)))
  (if (consp events)
      (let ((fn-hist$c (fn-hist$c-append (car events) fn-hist$c)))
        (hct-append-all (cdr events) fn-hist$c))
    fn-hist$c))

(defun hct-spec-lookups (msgids events)
  (declare (xargs :guard (string-listp msgids)))
  (if (consp msgids)
      (cons (fn-cei-article-records-for (car msgids) events)
            (hct-spec-lookups (cdr msgids) events))
    nil))

; Load under SALT, answer (count ats lookups), then append one more event
; and answer again: the append path after the open.
(defun hct-run (events extra salt msgids)
  (declare (xargs :guard (and (true-listp events) (unsigned-byte-p 32 salt)
                              (string-listp msgids))))
  (with-local-stobj fn-hist
    (mv-let (answers fn-hist)
      (let* ((fn-hist (fn-hist-load events salt fn-hist))
             (n (fn-hist-count fn-hist))
             (before (list n (hct-ats 0 n fn-hist) (hct-lookups msgids fn-hist)))
             (fn-hist (fn-hist-append extra fn-hist))
             (m (fn-hist-count fn-hist))
             (after (list m (hct-ats 0 m fn-hist) (hct-lookups msgids fn-hist))))
        (mv (list before after) fn-hist))
      answers)))

(defun hct-spec (events extra msgids)
  (declare (xargs :guard (and (true-listp events) (string-listp msgids))))
  (let ((events2 (append events (list extra))))
    (list (list (len events) events (hct-spec-lookups msgids events))
          (list (len events2) events2 (hct-spec-lookups msgids events2)))))

(defconst *hct-extra* (hct-held 6 "<b@x>" 11))

; The columns answer the list, under two salts.
(assert-event (equal (hct-run *hct-events* *hct-extra* 0 *hct-msgids*)
                     (hct-spec *hct-events* *hct-extra* *hct-msgids*)))
(assert-event (equal (hct-run *hct-events* *hct-extra* 3735928559 *hct-msgids*)
                     (hct-spec *hct-events* *hct-extra* *hct-msgids*)))

; What the answers are (not vacuous): <a@x> has two rows in history order,
; <b@x> the plain row only (the :hstxa-headed malformed event is keyed and
; refused), then two after the append, <c@x> the composite's article.
(assert-event
 (equal (hct-spec-lookups *hct-msgids* *hct-events*)
        (list (list *hct-a* *hct-a2*) (list *hct-b*) (list *hct-c*) nil nil)))
(assert-event
 (equal (nth 2 (nth 1 (hct-run *hct-events* *hct-extra* 0 *hct-msgids*)))
        (list (list *hct-a* *hct-a2*) (list *hct-b* *hct-extra*) (list *hct-c*)
              nil nil)))

; Growth past the first 16 rows (the column doubles): 40 events.
(defun hct-many (i n)
  (declare (xargs :measure (nfix (- (nfix n) (nfix i)))))
  (if (and (natp i) (natp n) (< i n))
      (cons (hct-held i (if (evenp i) "<even@x>" "<odd@x>") i) (hct-many (1+ i) n))
    nil))
(defconst *hct-40* (hct-many 0 40))
(assert-event (equal (hct-run *hct-40* *hct-extra* 7 '("<even@x>" "<odd@x>" "<b@x>"))
                     (hct-spec *hct-40* *hct-extra* '("<even@x>" "<odd@x>" "<b@x>"))))

; -----------------------------------------------------------------------------
; A hash collision costs a longer bucket, never a wrong answer: two
; Message-IDs with the same salted hash (found by search at salt 0), both
; in the history; each lookup answers only its own rows.

; The pair was found by a birthday search (a 32-bit hash; the first
; collision among "<N@c>" names at salt 0 is at N = 1,022,040).
(defconst *hct-collision* (list "<170999@c>" "<1022040@c>"))
(assert-event (equal (fn-hist-hash (first *hct-collision*) 0)
                     (fn-hist-hash (second *hct-collision*) 0)))
(assert-event (not (equal (first *hct-collision*) (second *hct-collision*))))
(defconst *hct-coll-events*
  (list (hct-held 0 (first *hct-collision*) 1) (hct-held 1 (second *hct-collision*) 2)))
(assert-event (equal (hct-run *hct-coll-events* *hct-extra* 0 *hct-collision*)
                     (hct-spec *hct-coll-events* *hct-extra* *hct-collision*)))
(assert-event (equal (fn-cei-article-records-for (first *hct-collision*) *hct-coll-events*)
                     (list (first *hct-coll-events*))))

; -----------------------------------------------------------------------------
; KEYSTONE fn-hist-load-is-the-history: (true-listp events) -> load = events.
; Positive: the antecedent and conclusion on the ground history.
(defthm hct-load-witness
  (and (true-listp *hct-events*)
       (equal (fn-hist-load *hct-events* 9 nil) *hct-events*))
  :rule-classes nil)
; Removal of (true-listp events): an improper list loads its proper prefix.
(defthm hct-load-improper-witness
  (and (not (true-listp (cons *hct-a* :tail)))
       (not (equal (fn-hist-load (cons *hct-a* :tail) 9 nil)
                   (cons *hct-a* :tail))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-hist-load))))
(must-fail-checked
 (defthm hct-false-load-without-true-listp
   (equal (fn-hist-load events salt fn-hist) events)))

; -----------------------------------------------------------------------------
; The bridges over the store node's index.

(defconst *hct-index* (fn-cei-build *hct-events*))

; fn-hist-count-serves-cei-count: positive, then removal of the
; correspondence (a corrupted index with a second put counts one more).
(defthm hct-bridge-w1 (and (fn-cei-correspondencep *hct-index* *hct-events*)
                   (equal (fn-cei-count *hct-index*) (fn-hist-count *hct-events*))
                   (equal (fn-hist-count *hct-events*) 6))
  :rule-classes nil)
(defconst *hct-corrupt* (fn-cei-put 1 *hct-a2* *hct-index*))
(defthm hct-bridge-w2 (and (not (fn-cei-correspondencep *hct-corrupt* *hct-events*))
                   (not (equal (fn-cei-count *hct-corrupt*)
                               (fn-hist-count *hct-events*))))
  :rule-classes nil)
(must-fail-checked
 (defthm hct-false-count-without-correspondence
   (equal (fn-cei-count *hct-corrupt*) (fn-hist-count *hct-events*))))

; fn-hist-at-serves-cei-get: positive at every sequence of the history.
(defthm hct-bridge-w3
 (and (fn-cei-correspondencep *hct-index* *hct-events*)
      (true-listp *hct-events*)
      (<= (len *hct-events*) (1+ *fn-cbor-max-uint*))
      (equal (fn-cei-get 0 *hct-index*) (fn-hist-at 0 *hct-events*))
      (equal (fn-cei-get 3 *hct-index*) (fn-hist-at 3 *hct-events*))
      (equal (fn-cei-get 4 *hct-index*) *hct-composite*)
      (equal (fn-cei-get 5 *hct-index*) (fn-hist-at 5 *hct-events*)))
  :rule-classes nil)
; Removal of the correspondence: the corrupted index answers another event.
(defthm hct-bridge-w4 (and (natp 1) (not (fn-cei-correspondencep *hct-corrupt* *hct-events*))
                   (not (equal (fn-cei-get 1 *hct-corrupt*)
                               (fn-hist-at 1 *hct-events*))))
  :rule-classes nil)
; Removal of (natp seq): a non-natural reads position 0 of the list and
; nothing from the index.
(defthm hct-bridge-w5 (and (fn-cei-correspondencep *hct-index* *hct-events*)
                   (not (natp :x))
                   (not (equal (fn-cei-get :x *hct-index*)
                               (fn-hist-at :x *hct-events*))))
  :rule-classes nil)
(must-fail-checked
 (defthm hct-false-at-without-natp
   (implies (fn-cei-correspondencep index fn-hist)
            (equal (fn-cei-get seq index) (fn-hist-at seq fn-hist)))))
; Removal of the length bound (symbolic: a history longer than 2^32 is not
; constructible here): at sequence 2^32 the index answers nil for every
; history, while the list answers its event there.
(defthm hct-at-past-the-bound-is-nil-in-the-index
  (equal (fn-cei-get (expt 2 32) index) nil)
  :hints (("Goal" :in-theory (enable fn-cei-get fn-cp-uintp))))

; fn-hist-msgid-records-serve-cei: positive at every Message-ID above.
(defthm hct-bridge-w6
 (and (fn-cei-correspondencep *hct-index* *hct-events*)
      (equal (fn-cei-msgid-records "<a@x>" *hct-index*)
             (fn-hist-msgid-records "<a@x>" *hct-events*))
      (equal (fn-cei-msgid-records "<b@x>" *hct-index*)
             (fn-hist-msgid-records "<b@x>" *hct-events*))
      (equal (fn-cei-msgid-records "<c@x>" *hct-index*)
             (list *hct-c*))
      (equal (fn-cei-msgid-records "<none@x>" *hct-index*) nil))
  :rule-classes nil)
; Removal of the correspondence: an index built over a shorter history.
(defconst *hct-short* (fn-cei-build (take 3 *hct-events*)))
(defthm hct-bridge-w7 (and (not (fn-cei-correspondencep *hct-short* *hct-events*))
                   (stringp "<a@x>")
                   (not (equal (fn-cei-msgid-records "<a@x>" *hct-short*)
                               (fn-hist-msgid-records "<a@x>" *hct-events*))))
  :rule-classes nil)
(must-fail-checked
 (defthm hct-false-msgid-without-correspondence
   (equal (fn-cei-msgid-records "<a@x>" *hct-short*)
          (fn-hist-msgid-records "<a@x>" *hct-events*))))

; -----------------------------------------------------------------------------
; CORRUPTED-STATE witness (labelled): the foundation's columns with the
; bucket for <a@x> dropping its second row answer differently from the
; list, so the correspondence is what the exports' answers rest on.  Built
; on a live local foundation object (the same append the export runs).
(defun hct-corrupt-lookup (events drop)
  (declare (xargs :guard (true-listp events)))
  (with-local-stobj fn-hist$c
    (mv-let (answer fn-hist$c)
      (let* ((fn-hist$c (fn-hist$c-clear 0 fn-hist$c))
             (fn-hist$c (hct-append-all events fn-hist$c))
             (fn-hist$c (if drop
                            (fn-hist$c-mids-put (fn-hist-hash "<a@x>" 0) '(0) fn-hist$c)
                          fn-hist$c)))
        (mv (fn-hist$c-msgid-records "<a@x>" fn-hist$c) fn-hist$c))
      answer)))
(assert-event (equal (hct-corrupt-lookup *hct-events* nil)
                     (fn-cei-article-records-for "<a@x>" *hct-events*)))
(assert-event (equal (hct-corrupt-lookup *hct-events* t) (list *hct-a*)))
(assert-event (not (equal (hct-corrupt-lookup *hct-events* t)
                          (fn-cei-article-records-for "<a@x>" *hct-events*))))
