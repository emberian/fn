; Witnesses for books/owner-article-slots.lisp (lane zero-copy-commit).
;
; The host's call, fn-oas-read-span, on live stobjs over owner-reader-read-
; tests' owner (*lgt-finished*: a configured owner, connection 0 a reader),
; with its posting bit on as owner-time-model-tests' *t2r-open* (a
; connection opened under a posting configuration), at the admitted gate
; value *t2-s1*.
(in-package "ACL2")
(include-book "../../books/owner-article-slots")
(include-book "../../books/heap-figure")
(include-book "owner-time-model-tests")

(defun oast-read-in (oc views id octs s slots rows payloads fn-octets fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-octets fn-arena fn-cat)))
  (let* ((fn-octets (fn-octets-from-list octs fn-octets))
         (fn-arena (fn-arena-clear fn-arena))
         (fn-arena (fn-arn-seal-many payloads fn-arena))
         (fn-cat (fn-sca-load-held-rows rows (fn-own-view-index (fn-own-view (fn-ocfg-owner oc)))
                                        fn-arena fn-cat)))
    (mv (fn-oas-read-span oc views id 0 (len octs) nil s slots fn-octets fn-arena fn-cat)
        fn-octets fn-arena fn-cat)))

(defun oast-read (oc views id octs s slots)
  (declare (xargs :mode :program))
  (with-local-stobj fn-octets
    (mv-let (result fn-octets)
      (with-local-stobj fn-arena
        (mv-let (result fn-octets fn-arena)
          (with-local-stobj fn-cat
            (mv-let (result fn-octets fn-arena fn-cat)
              (oast-read-in oc views id octs s slots (orrt-records *lgt-finished*)
                            *g12b-payloads* fn-octets fn-arena fn-cat)
              (mv result fn-octets fn-arena)))
          (mv result fn-octets)))
      result)))

; The keystone's two antecedents and its conclusion, as a list.
(defun oast-keystone (oc result id slots)
  (declare (xargs :mode :program))
  (let ((oc1 (fn-own-tls-result-owner result)))
    (list (not (fn-oas-articlep oc id))
          (fn-oas-articlep oc1 id)
          (<= (fn-oas-held oc1) (nfix slots)))))

(defconst *oast-open* *t2r-open*)

; REACHABLE POSITIVE WITNESS (fn-oas-read-span-admits-within-the-slots): one
; slot, nothing in flight; the POST is offered (340), the connection enters
; article mode and the owner then holds one article: both antecedents and
; the conclusion.  The read is the read before this book
; (fn-oas-read-span-when-held-unfolds: not over).
(defconst *oast-admit* (oast-read *oast-open* *orrt-views* 0 *t2r-post* *t2-s1* 1))
(assert-event (equal (fn-oas-held *oast-open*) 0))
(assert-event (equal (oast-keystone *oast-open* *oast-admit* 0 1) '(t t t)))
(assert-event (equal (fn-oas-held (fn-own-tls-result-owner *oast-admit*)) 1))
(assert-event
 (let ((effects (fn-own-tls-result-effects *oast-admit*)))
   (and (fn-post-offeredp effects)
        (equal (t2r-effect-text (car effects))
               (concatenate 'string "340 send article to be posted" *t2r-crlf*)))))
(assert-event (equal *oast-admit*
                     (t2r-host-read *oast-open* *orrt-views* 0 *t2r-post* *t2-s1*)))

; CONSTRUCTED STATE (a submission queued, as a connection whose article has
; arrived leaves it while the commit is pending): one slot and one held.  The
; read before this book offers the POST anyway, and the owner would then hold
; two articles in one slot -- the MUTATION the book removes, the old host
; call violating the conclusion.  The host's call now answers 440 with this
; book's reason at the command, consumes the command, leaves the connection
; in command mode with its posting bit back on, and holds one.
(defconst *oast-queued*
  (fn-ocfg-with-owner *oast-open*
                      (fn-own-enqueue (fn-ocfg-owner *oast-open*) '(:queued-witness))))
(assert-event (equal (fn-oas-held *oast-queued*) 1))
(defconst *oast-old* (t2r-host-read *oast-queued* *orrt-views* 0 *t2r-post* *t2-s1*))
(assert-event (equal (oast-keystone *oast-queued* *oast-old* 0 1) '(t t nil)))
(defconst *oast-refused* (oast-read *oast-queued* *orrt-views* 0 *t2r-post* *t2-s1* 1))
(assert-event
 (let ((effects (fn-own-tls-result-effects *oast-refused*))
       (oc1 (fn-own-tls-result-owner *oast-refused*)))
   (and (equal effects (list (fn-nntp-reply-effect *fn-oas-post-line*)))
        (equal (t2r-effect-text (car effects))
               (concatenate 'string "440 posting not permitted now; the articles in flight fill the memory, try again later" *t2r-crlf*))
        (not (fn-post-offeredp effects))
        (not (fn-served-closingp effects))
        (equal (fn-own-tls-result-consumed *oast-refused*) (len *t2r-post*))
        (not (fn-oas-articlep oc1 0))
        (fn-otm-conn-allow oc1 0)
        (equal (fn-oas-held oc1) 1))))
; The antecedent fails (no entry into article mode), so the keystone says
; nothing here; the refusal is the book's, not the served machine's.
(assert-event (equal (oast-keystone *oast-queued* *oast-refused* 0 1) '(t nil t)))

; HYPOTHESIS REMOVAL (the first antecedent, "not in article mode before"): a
; connection already in article mode continues whatever the slots -- its
; body is admitted in the slot it took at the 340.  Reached: the admitted
; POST's owner, a body line read with zero slots.  The second antecedent
; holds, the first fails, and so does the conclusion: the keystone cannot
; drop it.
(defconst *oast-mid* (fn-own-tls-result-owner *oast-admit*))
(defconst *oast-body* (append (fn-nntp-string-octets "Subject: x") '(13 10)))
(defconst *oast-continue* (oast-read *oast-mid* *orrt-views* 0 *oast-body* *t2-s1* 0))
(assert-event (equal (oast-keystone *oast-mid* *oast-continue* 0 0) '(nil t nil)))
(assert-event (null (fn-own-tls-result-effects *oast-continue*)))

; KEYSTONE fn-oas-read-span-never-blocks-an-admitted-article.  Reachable
; witness: the same read (connection 0 mid-article, zero slots, one held):
; the hypothesis holds and the host's call is the read before this book.
(assert-event (fn-oas-articlep *oast-mid* 0))
(assert-event (equal *oast-continue*
                     (t2r-host-read *oast-mid* *orrt-views* 0 *oast-body* *t2-s1*)))
; Hypothesis removal: connection 0 NOT in article mode (the queued state
; above, one slot): the host's call is not the read before this book (it
; refused the POST that read offered).
(assert-event (not (fn-oas-articlep *oast-queued* 0)))
(assert-event (not (equal *oast-refused* *oast-old*)))

; The slots the figure holds, at the small preset: 32 slots (the most) of
; 1,589,248 octets (an article of A = 32 KiB, its header bound of 16 KiB and
; a line, as lists, twice for the collector), under the 64 MiB budget
; (fn-heap-article-slots-are-held at k = 32; at k = 33 it fails).
(assert-event (equal (fn-heap-article-slots *fn-heap-small-profile*) 32))
(assert-event (equal (fn-heap-article-reserve-octets *fn-heap-small-profile*) 1589248))
(assert-event (equal (fn-heap-articles-octets *fn-heap-small-profile*) 50855936))
(assert-event (<= (* 32 (fn-heap-article-reserve-octets *fn-heap-small-profile*))
                  (fn-heap-articles-octets *fn-heap-small-profile*)))
(assert-event (not (<= (* 33 (fn-heap-article-reserve-octets *fn-heap-small-profile*))
                       (fn-heap-articles-octets *fn-heap-small-profile*))))
; A profile whose reserve is past the budget holds one slot (the node always
; takes a POST): A = 4 MiB, the native case's (tests/test_native_article_slots.py).
(defconst *oast-a4*
  (fn-bs-profile-resolve (list :development
                               (list (cons *fn-bs-pf-max-transactions* 1024)
                                     (cons *fn-bs-pf-max-history-octets* (* 64 1048576))
                                     (cons *fn-bs-pf-max-record-octets* 4199563)
                                     (cons *fn-bs-pf-max-article-octets* 4194304)
                                     (cons *fn-bs-pf-max-groups-per-article* 16)))
                         nil))
(assert-event (fn-bs-profile-admittedp *oast-a4*))
(assert-event (equal (fn-heap-article-slots *oast-a4*) 1))
; The native deadlock case's profile (A = 600,000): three slots.
(defconst *oast-a600k*
  (fn-bs-profile-resolve (list :development
                               (list (cons *fn-bs-pf-max-transactions* 1024)
                                     (cons *fn-bs-pf-max-history-octets* (* 64 1048576))
                                     (cons *fn-bs-pf-max-record-octets* 4199563)
                                     (cons *fn-bs-pf-max-article-octets* 600000)
                                     (cons *fn-bs-pf-max-groups-per-article* 16)))
                         nil))
(assert-event (fn-bs-profile-admittedp *oast-a600k*))
(assert-event (equal (fn-heap-article-slots *oast-a600k*) 3))
