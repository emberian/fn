; Witnesses for books/native-live-pages.lisp (lane obligations-paged).
;
; REACHABLE: retention ledgers built as the ledger is (fn-retain-make-state,
; obligations newest first): a short one (5 obligations, 7-octet pages, many
; pages) and a long one (2,500 obligations, a report past one
; `*fn-nls-chunk-octets*' page, read at the served width).  The owner's
; answers and the client's steps are composed as the host composes them
; (fn-nlp-run), each keystone's antecedent is checked and its conclusion.
; HYPOTHESIS-REMOVAL: each hypothesis of fn-nlp-pages-reach-the-report and of
; fn-nlp-answer-keeps-other-versions dropped in turn, the others checked,
; the conclusion failing; the only hypothesis of the join keystones (the run
; reached :done) dropped with too little fuel.
(in-package "ACL2")
(include-book "../../books/native-live-pages")

; ---------------------------------------------------------------------------
; Fixtures

(defun nlpt-obligations (n acc)
  (declare (xargs :verify-guards nil))
  (if (zp n)
      acc
    (nlpt-obligations
     (- n 1)
     (cons (fn-retain-make-obligation
            (concatenate 'string "id-" (coerce (explode-atom n 10) 'string))
            (concatenate 'string "<m" (coerce (explode-atom n 10) 'string)
                         "@obligations.example>")
            (if (evenp n) :forward :archive) nil (+ 1 (mod n 5)))
           acc))))

(defun nlpt-sum (pins)
  (declare (xargs :verify-guards nil))
  (if (consp pins) (+ (fn-retain-obligation-charge (car pins)) (nlpt-sum (cdr pins))) 0))

(defun nlpt-ret (n)
  (declare (xargs :verify-guards nil))
  (let ((pins (nlpt-obligations n nil)))
    (fn-retain-make-state 1000000 (nlpt-sum pins) pins nil)))

(defconst *nlpt-short* (nlpt-ret 5))
(defconst *nlpt-long* (nlpt-ret 2500))
(defconst *nlpt-other* (nlpt-ret 3))

; The short report is a few hundred octets, the long one past one page.
(assert-event (< 7 (len (fn-nlp-report *nlpt-short*))))
(assert-event (< *fn-nls-chunk-octets* (len (fn-nlp-report *nlpt-long*))))
(assert-event (equal (fn-record-octets-string
                      (take 26 (fn-nlp-report *nlpt-short*)))
                     "obligations=5 reserved=15
"))

; ---------------------------------------------------------------------------
; The frames round trip

(assert-event (equal (fn-nlp-request-decode (fn-nlp-request-encode :obligations 0 0))
                     '(:page :obligations 0 0)))
(assert-event (equal (fn-nlp-request-decode
                      (fn-nlp-request-encode :obligations 4294967295 4294967295))
                     '(:page :obligations 4294967295 4294967295)))
(assert-event (equal (fn-nlp-request-encode :status 0 0) :bad))
(assert-event (equal (fn-nlp-request-encode :obligations 4294967296 0) :bad))
(assert-event (equal (fn-nlp-reply-decode
                      (fn-nlp-reply-encode :version-gone 0 0 nil nil))
                     '(:page-reply :version-gone 0 0 nil nil)))
(assert-event (equal (fn-nlp-reply-decode
                      (fn-nlp-reply-encode :accepted 9 3 t '(65 10)))
                     '(:page-reply :accepted 9 3 t (65 10))))
; A whole-report request (FNLS kind 1) is not a page request.
(assert-event (equal (car (fn-nlp-request-decode (fn-nls-request-encode :obligations 0)))
                     :refused))

; ---------------------------------------------------------------------------
; KEYSTONE fn-nlp-pages-join-to-the-report (REACHABLE, whatever the cache)

(defun nlpt-run-short ()
  (declare (xargs :verify-guards nil))
  (fn-nlp-run 1000 nil *nlpt-short* 7 0 0))
(assert-event (equal (car (nlpt-run-short)) :done))
(assert-event (equal (cadr (nlpt-run-short)) (fn-nlp-report *nlpt-short*)))
; Many pages: every page but the last is exactly 7 octets.
(assert-event (< 20 (ceiling (len (fn-nlp-report *nlpt-short*)) 7)))
; From an owner that already holds other cursors and a last version.
(defconst *nlpt-busy-cache*
  (list 41 (list 40 3 '(65 66) nil) (list 39 0 nil (fn-retain-pins *nlpt-other*))))
(assert-event (equal (fn-nlp-run 1000 *nlpt-busy-cache* *nlpt-short* 7 0 0)
                     (list :done (fn-nlp-report *nlpt-short*))))
; At the served width, past one page.
(defun nlpt-run-long ()
  (declare (xargs :verify-guards nil))
 
  (fn-nlp-run 1000 nil *nlpt-long* *fn-nls-chunk-octets* 0 0))
(assert-event (equal (car (nlpt-run-long)) :done))
(assert-event (equal (cadr (nlpt-run-long)) (fn-nlp-report *nlpt-long*)))
; The first answer: version 1, page 0, not the last page, one full page.
(defun nlpt-first ()
  (declare (xargs :verify-guards nil))
 
  (fn-nlp-answer (fn-nlp-request-encode :obligations 0 0) nil *nlpt-long*
                 *fn-nls-chunk-octets*))
(assert-event (let ((d (fn-nlp-reply-decode (car (nlpt-first)))))
                (and (equal (nth 1 d) :accepted) (equal (nth 2 d) 1)
                     (equal (nth 3 d) 0) (not (nth 4 d))
                     (equal (len (nth 5 d)) *fn-nls-chunk-octets*)
                     (equal (nth 5 d) (take *fn-nls-chunk-octets*
                                            (fn-nlp-report *nlpt-long*))))))
; The owner keeps one cursor, at page 1 of version 1; a finished report
; keeps none.
(assert-event (equal (len (fn-nlp-cache-entries (cadr (nlpt-first)))) 1))
(assert-event (equal (fn-nlp-entry-stream 1 1 (cadr (nlpt-first)))
                     (nthcdr *fn-nls-chunk-octets* (fn-nlp-report *nlpt-long*))))
; HYPOTHESIS-REMOVAL (the run reached :done): two requests of a many-page
; report end in (:fuel), and what they carry is not the report.
(assert-event (equal (fn-nlp-run 2 nil *nlpt-short* 7 0 0) '(:fuel)))
(assert-event (not (equal (cadr (fn-nlp-run 2 nil *nlpt-short* 7 0 0))
                          (fn-nlp-report *nlpt-short*))))

; fn-nlp-run-joins-the-entry (REACHABLE): from a named version's cursor, the
; rest.
(assert-event (equal (fn-nlp-run 1000 (cadr (nlpt-first)) *nlpt-other*
                                 *fn-nls-chunk-octets* 1 1)
                     (list :done (nthcdr *fn-nls-chunk-octets*
                                         (fn-nlp-report *nlpt-long*)))))

; ---------------------------------------------------------------------------
; KEYSTONE fn-nlp-pages-reach-the-report

(defun nlpt-reach-hyps (w fuel ret)
  (declare (xargs :verify-guards nil))
  (list (posp w) (<= w *fn-nls-chunk-octets*) (posp fuel)
        (<= (len (fn-nlp-report ret)) (* w fuel))))

(defun nlpt-reaches (w fuel ret)
  (declare (xargs :verify-guards nil))
  (equal (fn-nlp-run fuel nil ret w 0 0) (list :done (fn-nlp-report ret))))

; REACHABLE: the exact fuel, ceiling(L / W).
(defconst *nlpt-exact-fuel* (ceiling (len (fn-nlp-report *nlpt-short*)) 7))
(assert-event (equal (nlpt-reach-hyps 7 *nlpt-exact-fuel* *nlpt-short*) '(t t t t)))
(assert-event (nlpt-reaches 7 *nlpt-exact-fuel* *nlpt-short*))
(assert-event (equal (nlpt-reach-hyps *fn-nls-chunk-octets* 2 *nlpt-long*) '(t t t t)))
(assert-event (nlpt-reaches *fn-nls-chunk-octets* 2 *nlpt-long*))
; (posp w) removed: w = 1/2, the other three hold, no page moves.
(assert-event (equal (nlpt-reach-hyps 1/2 100000 *nlpt-short*) '(nil t t t)))
(assert-event (not (nlpt-reaches 1/2 100000 *nlpt-short*)))
; (<= w chunk) removed: a first page wider than the frame is refused.
(assert-event (equal (nlpt-reach-hyps (* 2 *fn-nls-chunk-octets*) 1 *nlpt-long*)
                     '(t nil t t)))
(assert-event (not (nlpt-reaches (* 2 *fn-nls-chunk-octets*) 1 *nlpt-long*)))
(assert-event (equal (fn-nlp-run 1 nil *nlpt-long* (* 2 *fn-nls-chunk-octets*) 0 0)
                     '(:refused)))
; (posp fuel) removed: fuel 1/2 runs no request.
(assert-event (equal (nlpt-reach-hyps *fn-nls-chunk-octets* 1/2 *nlpt-short*)
                     '(t t nil t)))
; (fuel 1/2 is outside zp's guard: evaluated without guard checking.)
(assert-event (not (with-guard-checking :none
                     (nlpt-reaches *fn-nls-chunk-octets* 1/2 *nlpt-short*))))
; (<= L (* w fuel)) removed: one request short.
(assert-event (equal (nlpt-reach-hyps 7 (- *nlpt-exact-fuel* 1) *nlpt-short*)
                     '(t t t nil)))
(assert-event (not (nlpt-reaches 7 (- *nlpt-exact-fuel* 1) *nlpt-short*)))

; ---------------------------------------------------------------------------
; KEYSTONE fn-nlp-answer-keeps-other-versions

; Client A starts version 1 (short report, 7-octet pages), client B starts
; version 2 of another report and reads a page: A's cursor is where it was.
(defun nlpt-a ()
  (declare (xargs :verify-guards nil))
  (fn-nlp-answer (fn-nlp-request-encode :obligations 0 0) nil
                                  *nlpt-short* 7))
(defun nlpt-ab ()
  (declare (xargs :verify-guards nil))
  (fn-nlp-answer (fn-nlp-request-encode :obligations 0 0)
                                   (cadr (nlpt-a)) *nlpt-other* 7))
(defun nlpt-abb ()
  (declare (xargs :verify-guards nil))
  (fn-nlp-answer (fn-nlp-request-encode :obligations 2 1)
                                    (cadr (nlpt-ab)) *nlpt-other* 7))

(defun nlpt-keep-hyps (req cache v)
  (declare (xargs :verify-guards nil))
  (list (not (equal (nth 2 (fn-nlp-request-decode req)) v))
        (not (equal (fn-nlp-next-version (fn-nlp-cache-last cache)) v))))

(defun nlpt-kept (req cache ret w v page)
  ; the conclusion: V's rest unchanged or dropped
  (declare (xargs :verify-guards nil))
  (let ((after (fn-nlp-entry-stream v page (cadr (fn-nlp-answer req cache ret w)))))
    (or (equal after (fn-nlp-entry-stream v page cache))
        (equal after :none))))

(assert-event (equal (nlpt-keep-hyps (fn-nlp-request-encode :obligations 2 1)
                                     (cadr (nlpt-ab)) 1)
                     '(t t)))
(assert-event (nlpt-kept (fn-nlp-request-encode :obligations 2 1) (cadr (nlpt-ab))
                         *nlpt-other* 7 1 1))
; REACHABLE, kept (not dropped): A's rest after B's page is A's rest before.
(assert-event (equal (fn-nlp-entry-stream 1 1 (cadr (nlpt-abb)))
                     (nthcdr 7 (fn-nlp-report *nlpt-short*))))
; A reads on to the end, from B's cache: the short report.
(assert-event (let ((r (fn-nlp-run 1000 (cadr (nlpt-abb)) *nlpt-other* 7 1 1)))
                (equal (append (take 7 (fn-nlp-report *nlpt-short*)) (cadr r))
                       (fn-nlp-report *nlpt-short*))))
; REACHABLE, dropped: four more starts evict version 1; A reads version-gone
; by name and its client restarts.
(defun nlpt-starts (n cache)
  (declare (xargs :verify-guards nil))
  (if (zp n)
      cache
    (nlpt-starts (- n 1)
                 (cadr (fn-nlp-answer (fn-nlp-request-encode :obligations 0 0)
                                      cache *nlpt-other* 7)))))
(defun nlpt-evicted ()
  (declare (xargs :verify-guards nil))
  (nlpt-starts 4 (cadr (nlpt-a))))
(assert-event (equal (fn-nlp-entry-stream 1 1 (nlpt-evicted)) :none))
(assert-event (equal (fn-nlp-client-step
                      1 1 (car (fn-nlp-answer (fn-nlp-request-encode :obligations 1 1)
                                              (nlpt-evicted) *nlpt-other* 7)))
                     '(:restart)))
; HYPOTHESIS-REMOVAL (the request names V): A's own request moves A's cursor:
; the rest at page 1 is gone (the cursor stands at page 2), not kept.
(assert-event (equal (nlpt-keep-hyps (fn-nlp-request-encode :obligations 1 1)
                                     (cadr (nlpt-a)) 1)
                     '(nil t)))
(assert-event (not (nlpt-kept (fn-nlp-request-encode :obligations 1 1) (cadr (nlpt-a))
                              *nlpt-other* 7 1 2)))
; HYPOTHESIS-REMOVAL (the start issues V): an owner whose last version is
; V - 1 and which holds V (the counter wrapped) replaces V's cursor with
; another report's.
(defconst *nlpt-wrap-cache* (list 0 (list 1 1 '(65 66 67) nil)))
(assert-event (equal (nlpt-keep-hyps (fn-nlp-request-encode :obligations 0 0)
                                     *nlpt-wrap-cache* 1)
                     '(t nil)))
(assert-event (not (nlpt-kept (fn-nlp-request-encode :obligations 0 0) *nlpt-wrap-cache*
                              *nlpt-other* 7 1 1)))

; ---------------------------------------------------------------------------
; KEYSTONE fn-nlp-offline-pages-join-to-the-report

(assert-event (equal (fn-nlp-offline-run 1000 (fn-nlp-offline-start *nlpt-long*)
                                         *fn-nls-chunk-octets*)
                     (list :done (fn-nlp-report *nlpt-long*))))
(assert-event (equal (fn-nlp-offline-run 1000 (fn-nlp-offline-start *nlpt-short*) 7)
                     (list :done (fn-nlp-report *nlpt-short*))))
; HYPOTHESIS-REMOVAL (the run reached :done): one step of a two-page report.
(assert-event (equal (fn-nlp-offline-run 1 (fn-nlp-offline-start *nlpt-long*)
                                         *fn-nls-chunk-octets*)
                     '(:fuel)))
(assert-event (not (equal (cadr (fn-nlp-offline-run 1 (fn-nlp-offline-start *nlpt-long*)
                                                    *fn-nls-chunk-octets*))
                          (fn-nlp-report *nlpt-long*))))

; ---------------------------------------------------------------------------
; The whole-report exchange refuses the paged kind by name (the owner never
; renders it whole): the refusal word, and fn-nlp-pagedp.
(assert-event (fn-nlp-pagedp :obligations))
(assert-event (not (fn-nlp-pagedp :status)))
(assert-event (equal (fn-record-octets-string *fn-nlp-refusal-paged*) "report-is-paged"))
