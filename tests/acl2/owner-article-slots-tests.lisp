; Witnesses for books/owner-article-slots.lisp (lane zero-copy-commit) and
; books/owner-article-held.lisp (lane admission-gap).
;
; The host's call, fn-oas-read-span, on live stobjs over owner-reader-read-
; tests' owner (*lgt-finished*: a configured owner, connection 0 a reader),
; with its posting bit on as owner-time-model-tests' *t2r-open* (a
; connection opened under a posting configuration), at the admitted gate
; value *t2-s1*.
(in-package "ACL2")
(include-book "../../books/owner-article-held")
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
; both hypotheses hold (admitted; the read leaves it in article mode with
; the queue as it was) and the host's call is the read before this book.
(assert-event (fn-oas-articlep *oast-mid* 0))
(assert-event (fn-oas-articlep (fn-own-tls-result-owner *oast-continue*) 0))
(assert-event (equal (len (fn-own-queue (fn-ocfg-owner (fn-own-tls-result-owner *oast-continue*))))
                     (len (fn-own-queue (fn-ocfg-owner *oast-mid*)))))
(assert-event (equal *oast-continue*
                     (t2r-host-read *oast-mid* *orrt-views* 0 *oast-body* *t2-s1*)))
; Hypothesis removal (the first, "admitted"): connection 0 NOT in article
; mode (the queued state above, one slot): the host's call is not the read
; before this book (it refused the POST that read offered), and it is not
; that read closed either (fn-oah-admitted-read-keeps-what-it-completed's
; hypothesis removal).
(assert-event (not (fn-oas-articlep *oast-queued* 0)))
(assert-event (not (equal *oast-refused* *oast-old*)))
(assert-event (not (equal *oast-refused* (fn-oas-close-result *oast-old* 0))))

; -----------------------------------------------------------------------------
; Lane admission-gap: a read that enters article mode AND completes the
; article (books/owner-article-held.lisp).
;
; CONSTRUCTED STATE: the queued state with connection 0 opened under a
; posting configuration for fn.test (an owner configured with it opens its
; connections so, fn-own-open) and the owner's clock a usable observation
; (fn-own-observe sets it), so a POST is taken as a submission.
(defun oahx-with-cfg-obs (oc id cfg obs)
  (declare (xargs :mode :program))
  (let* ((o (fn-ocfg-owner oc))
         (c (fn-own-find-conn id (fn-own-conns o))))
    (fn-ocfg-with-owner oc (update-nth 7 obs
                                       (fn-own-set-conns o (fn-own-replace-conn
                                                            (update-nth 7 obs (update-nth 6 cfg c))
                                                            (fn-own-conns o)))))))
(defconst *oahx-obs* (fn-clock-observation 2000000 1600000010000 500 t))
(defconst *oahx-cfg*
  (fn-inj-make-config t (fn-nntp-string-octets "fn.example.invalid")
                      (list (fn-nntp-string-octets "fn.test")) 32768))
(defconst *oahx-queued* (oahx-with-cfg-obs *oast-queued* 0 *oahx-cfg* *oahx-obs*))
(assert-event (equal (fn-oas-held *oahx-queued*) 1))
(defconst *oahx-article*
  (append (fn-nntp-string-octets "From: a@example.invalid") '(13 10)
          (fn-nntp-string-octets "Newsgroups: fn.test") '(13 10)
          (fn-nntp-string-octets "Subject: one read") '(13 10)
          (fn-nntp-string-octets "Message-ID: <one-read@example.invalid>") '(13 10)
          '(13 10)
          (fn-nntp-string-octets "body") '(13 10)
          (fn-nntp-string-octets ".") '(13 10)))

; A PEER connection on that owner (RFC 4644 streaming): opened by
; fn-ocfg-open-peer under a configuration naming peer "p", the owner's own
; configuration then restored (the pins do not change at a peer's open).
(defconst *oahx-peer-record*
  (fn-cfg-peer-make "p" "peer.example" '(:nntp "127.0.0.1" 1119)
                    '("fn.*" 32768 16) nil '(:source-address "127.0.0.1")))
(defconst *oahx-peer-cfg*
  (fn-config-replay 0 510
                    (list (fn-cfg-record-make
                           0 0 1
                           (append *fn-cfg-default-change*
                                   (list (fn-cfg-set-peer-delta *oahx-peer-record*)))
                           *fn-cfg-default-stamp*))))
(defun oahx-with-peer (oc)
  (declare (xargs :mode :program))
  (fn-ocfg-with-owner
   oc (fn-ocfg-owner (cdr (fn-ocfg-open-peer (fn-ocfg-make (fn-ocfg-owner oc) *oahx-peer-cfg*
                                                           (fn-ocfg-pins oc) (fn-ocfg-staged oc))
                                             "p" nil)))))
(defconst *oahx-peer* (fn-own-next-id (fn-ocfg-owner *oahx-queued*)))
(defconst *oahx-peered* (oahx-with-peer *oahx-queued*))
(assert-event (equal *oahx-peer* 2))
(assert-event (fn-own-find-conn *oahx-peer* (fn-own-conns (fn-ocfg-owner *oahx-peered*))))
(assert-event (equal (fn-oas-held *oahx-peered*) 1))

; TAKETHIS <id> and its whole article in ONE read (RFC 4644 section 2.5:
; the peer does not wait for a reply before the article).
(defconst *oahx-takethis*
  (append (fn-nntp-string-octets "TAKETHIS <one-read@example.invalid>") '(13 10)
          (fn-nntp-string-octets "Path: peer.example!not-for-mail") '(13 10)
          *oahx-article*))

; The invariant keystone's antecedent and conclusion, and whether the read
; left connection ID in article mode, as a list.
(defun oahx-invariant (oc result id slots)
  (declare (xargs :mode :program))
  (let ((oc1 (fn-own-tls-result-owner result)))
    (list (<= (fn-oas-held oc) (nfix slots))
          (<= (fn-oas-held oc1) (nfix slots))
          (fn-oas-articlep oc1 id))))

; MUTATION WITNESS (fn-oah-read-span-keeps-held-within-the-slots), the
; TAKETHIS in one read: one slot, one held.  The read before this lane's
; admission (the host's call before PRF-377's fix, fn-otm-read-span, which
; the old fn-oas-read-span returned for every read that did not leave the
; connection newly mid-article) takes the whole transfer -- the submission
; queued, the connection back in command mode -- and the owner then holds
; TWO articles in one slot: the antecedent holds and the conclusion fails.
(defconst *oahx-t-old* (t2r-host-read *oahx-peered* *orrt-views* *oahx-peer* *oahx-takethis* *t2-s1*))
(assert-event (equal (oahx-invariant *oahx-peered* *oahx-t-old* *oahx-peer* 1) '(t nil nil)))
(assert-event (equal (fn-oas-held (fn-own-tls-result-owner *oahx-t-old*)) 2))
(assert-event (equal (fn-own-tls-result-consumed *oahx-t-old*) (len *oahx-takethis*)))
(assert-event (fn-served-submission (fn-own-tls-result-effects *oahx-t-old*)))
; The host's call refuses the WHOLE read (tier c: the posting-off read takes
; the TAKETHIS too, and ends in command mode): 400 with the memory reason and
; close, the span consumed, nothing queued, the peer's wire closed; the owner
; holds one.
(defconst *oahx-t-new* (oast-read *oahx-peered* *orrt-views* *oahx-peer* *oahx-takethis* *t2-s1* 1))
(assert-event (equal (oahx-invariant *oahx-peered* *oahx-t-new* *oahx-peer* 1) '(t t nil)))
(assert-event
 (let ((oc1 (fn-own-tls-result-owner *oahx-t-new*)))
   (and (equal (fn-own-tls-result-effects *oahx-t-new*)
               (list (fn-nntp-reply-effect *fn-oas-busy-line*) (fn-nntp-close-effect)))
        (equal (t2r-effect-text (car (fn-own-tls-result-effects *oahx-t-new*)))
               (concatenate 'string "400 the articles in flight fill the memory; try again later"
                            *t2r-crlf*))
        (equal (fn-own-tls-result-consumed *oahx-t-new*) (len *oahx-takethis*))
        (equal (fn-own-queue (fn-ocfg-owner oc1)) (fn-own-queue (fn-ocfg-owner *oahx-peered*)))
        (equal (fn-wire-state-mode
                (fn-own-conn-wire (fn-own-find-conn *oahx-peer* (fn-own-conns (fn-ocfg-owner oc1)))))
               :closed)
        (equal (fn-oas-held oc1) 1))))
(assert-event (equal *oahx-t-new*
                     (fn-oas-whole-refusal *oahx-peered* *oahx-peer* 0 (len *oahx-takethis*))))
; The same read with two slots is taken as before (not over).
(assert-event (equal (oast-read *oahx-peered* *orrt-views* *oahx-peer* *oahx-takethis* *t2-s1* 2)
                     *oahx-t-old*))

; The POST that a client pipelines with its article (RFC 3977 section 6.3.1
; says to wait for 340; a client may not): the same gap, the same
; MUTATION.  The host's call is tier (a): 440 with the memory reason at the
; POST, the article's lines then answered as the commands they now are;
; nothing queued, the posting bit back on, one held.
(defconst *oahx-post-one-read* (append *t2r-post* *oahx-article*))
(defconst *oahx-p-old* (t2r-host-read *oahx-queued* *orrt-views* 0 *oahx-post-one-read* *t2-s1*))
(assert-event (equal (oahx-invariant *oahx-queued* *oahx-p-old* 0 1) '(t nil nil)))
(defconst *oahx-p-new* (oast-read *oahx-queued* *orrt-views* 0 *oahx-post-one-read* *t2-s1* 1))
(assert-event (equal (oahx-invariant *oahx-queued* *oahx-p-new* 0 1) '(t t nil)))
(assert-event
 (let ((oc1 (fn-own-tls-result-owner *oahx-p-new*)))
   (and (equal (car (fn-own-tls-result-effects *oahx-p-new*))
               (fn-nntp-reply-effect *fn-oas-post-line*))
        (not (fn-served-submission (fn-own-tls-result-effects *oahx-p-new*)))
        (fn-otm-conn-allow oc1 0)
        (equal (fn-oas-held oc1) 1))))

; REACHABLE POSITIVE WITNESS of the invariant: the admitted POST above (no
; slot held, one slot): held 0 <= 1 before, 1 <= 1 after.
(assert-event (equal (oahx-invariant *oast-open* *oast-admit* 0 1) '(t t t)))
; HYPOTHESIS REMOVAL: the owner already past the slots (one held, zero
; slots) -- a body line of the admitted article leaves it past them.
(assert-event (equal (oahx-invariant *oast-mid* *oast-continue* 0 0) '(nil nil t)))

; KEYSTONE fn-oah-read-span-leaves-the-others-article-mode.  Connection 0
; mid-article (its POST admitted in two slots), then the peer's TAKETHIS in
; one read, taken (three slots) and refused whole (two): either way
; connection 0's record, and so its article mode, is as it was.
(defconst *oahx-admit2* (oast-read *oahx-queued* *orrt-views* 0 *t2r-post* *t2-s1* 2))
(defconst *oahx-mid2* (oahx-with-peer (fn-own-tls-result-owner *oahx-admit2*)))
(assert-event (and (fn-oas-articlep *oahx-mid2* 0) (equal (fn-oas-held *oahx-mid2*) 2)))
(defconst *oahx-t-taken* (oast-read *oahx-mid2* *orrt-views* *oahx-peer* *oahx-takethis* *t2-s1* 3))
(defconst *oahx-t-refused* (oast-read *oahx-mid2* *orrt-views* *oahx-peer* *oahx-takethis* *t2-s1* 2))
(defun oahx-frame (oc result id id2)
  (declare (xargs :mode :program))
  (let ((oc1 (fn-own-tls-result-owner result)))
    (list (not (equal id2 id))
          (equal (fn-own-find-conn id2 (fn-own-conns (fn-ocfg-owner oc1)))
                 (fn-own-find-conn id2 (fn-own-conns (fn-ocfg-owner oc))))
          (equal (fn-oas-articlep oc1 id2) (fn-oas-articlep oc id2)))))
(assert-event (equal (oahx-frame *oahx-mid2* *oahx-t-taken* *oahx-peer* 0) '(t t t)))
(assert-event (equal (fn-oas-held (fn-own-tls-result-owner *oahx-t-taken*)) 3))
(assert-event (equal (oahx-frame *oahx-mid2* *oahx-t-refused* *oahx-peer* 0) '(t t t)))
(assert-event (equal (fn-oas-held (fn-own-tls-result-owner *oahx-t-refused*)) 2))
(assert-event (fn-oas-articlep (fn-own-tls-result-owner *oahx-t-refused*) 0))
; HYPOTHESIS REMOVAL (id2 = id): the read's own connection -- the admitted
; POST's -- changes its record and enters article mode.
(assert-event (equal (oahx-frame *oast-open* *oast-admit* 0 0) '(nil nil nil)))

; fn-oah-admitted-read-keeps-what-it-completed and never-blocks, the read
; that COMPLETES the admitted article: connection 0 mid-article, its article
; and the next POST in one read, zero slots.  The read stops after the
; submission (PKT-600: the served fold yields after one), connection 0 back
; in command mode with the article queued, and the host's call is that read
; exactly.  This is why the never-blocks keystone's second hypothesis has no
; reachable removal witness: a read that queues a submission leaves its
; connection in command mode.
(defconst *oahx-mid* (fn-own-tls-result-owner *oahx-admit2*))
(defconst *oahx-finish-then-post* (append *oahx-article* *t2r-post*))
(defconst *oahx-fp-old* (t2r-host-read *oahx-mid* *orrt-views* 0 *oahx-finish-then-post* *t2-s1*))
(assert-event (fn-oas-articlep *oahx-mid* 0))
(assert-event (equal (fn-own-tls-result-consumed *oahx-fp-old*) (len *oahx-article*)))
(assert-event (not (fn-oas-articlep (fn-own-tls-result-owner *oahx-fp-old*) 0)))
(assert-event (equal (len (fn-own-queue (fn-ocfg-owner (fn-own-tls-result-owner *oahx-fp-old*))))
                     (+ 1 (len (fn-own-queue (fn-ocfg-owner *oahx-mid*))))))
(assert-event (equal (oast-read *oahx-mid* *orrt-views* 0 *oahx-finish-then-post* *t2-s1* 0)
                     *oahx-fp-old*))

;; ONE SUBMISSION IN FLIGHT COUNTS ONE (fn-oas-inflight-count; lane
;; admission-gap follow-up, found by lane credits).  The in-flight field is
;; nil or ONE submission record (books/owner.lisp), and the count before
;; this fix was its LENGTH: a six-field record with a login held six slots.
;; CONSTRUCTED STATE: the opened owner with such a record in flight (as
;; fn-own-take-submission leaves it).  It holds one; a POST with two slots
;; is admitted (340) and the owner then holds two.  MUTATION: the old count
;; reads seven there, past the two slots, and the old admission refused the
;; POST that the slots allow.
(defconst *oahi-sub*
  (fn-own-sub-make-author 1 1 nil '(:decision-witness) '(108) '(97)))
(defconst *oahi-inflight*
  (fn-ocfg-with-owner *oast-open* (update-nth 11 *oahi-sub* (fn-ocfg-owner *oast-open*))))
(assert-event (equal (fn-own-inflight (fn-ocfg-owner *oahi-inflight*)) *oahi-sub*))
(assert-event (equal (len *oahi-sub*) 6))
(assert-event (equal (fn-oas-held *oahi-inflight*) 1))
(defun oahi-old-held (oc)
  (declare (xargs :mode :program))
  (let ((o (fn-ocfg-owner oc)))
    (+ (fn-oas-article-conns (fn-own-conns o)) (len (fn-own-queue o))
       (len (fn-own-inflight o)))))
(defconst *oahi-admit* (oast-read *oahi-inflight* *orrt-views* 0 *t2r-post* *t2-s1* 2))
(assert-event (equal (oast-keystone *oahi-inflight* *oahi-admit* 0 2) '(t t t)))
(assert-event (fn-post-offeredp (fn-own-tls-result-effects *oahi-admit*)))
(assert-event (equal (fn-oas-held (fn-own-tls-result-owner *oahi-admit*)) 2))
(assert-event (equal (oahi-old-held (fn-own-tls-result-owner *oahi-admit*)) 7))

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

; -----------------------------------------------------------------------------
; THE DISK'S REASON BEFORE THE MEMORY'S (lane credits-stall, 2026-09-28;
; fn-oas-refusal-line).  The refused POST's tier (a), fn-oas-posting-off-read,
; on the posting connection: at the admitted gate value it says the memory's
; 440; at the STALLED value (*t2-stalled*: a barrier past H) the disk's --
; the very line fn-otm-read-span gives a POST while the disk sheds -- and
; not the memory's.  MUTATION: the substitution before this lane (the
; memory's line whatever the disk) gives the memory's 440 at the stalled
; value, the wrong reason for a disk outcome.
(defun oast-off-in (oc views id octs s rows payloads fn-octets fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-octets fn-arena fn-cat)))
  (let* ((fn-octets (fn-octets-from-list octs fn-octets))
         (fn-arena (fn-arena-clear fn-arena))
         (fn-arena (fn-arn-seal-many payloads fn-arena))
         (fn-cat (fn-sca-load-held-rows rows (fn-own-view-index (fn-own-view (fn-ocfg-owner oc)))
                                        fn-arena fn-cat)))
    (mv (fn-oas-posting-off-read oc views id 0 (len octs) nil s fn-octets fn-arena fn-cat)
        fn-octets fn-arena fn-cat)))

(defun oast-off (oc views id octs s)
  (declare (xargs :mode :program))
  (with-local-stobj fn-octets
    (mv-let (result fn-octets)
      (with-local-stobj fn-arena
        (mv-let (result fn-octets fn-arena)
          (with-local-stobj fn-cat
            (mv-let (result fn-octets fn-arena fn-cat)
              (oast-off-in oc views id octs s (orrt-records *lgt-finished*)
                           *g12b-payloads* fn-octets fn-arena fn-cat)
              (mv result fn-octets fn-arena)))
          (mv result fn-octets)))
      result)))

(defconst *oast-memory-440* (fn-nntp-reply-effect *fn-oas-post-line*))
(assert-event (equal (fn-otm-admit-post *t2-s1*) :admit))
(assert-event (equal (fn-otm-admit-post *t2-stalled*) :shed))
(assert-event (equal (fn-own-tls-result-effects (oast-off *oast-open* *orrt-views* 0 *t2r-post* *t2-s1*))
                     (list *oast-memory-440*)))
(defconst *oast-stalled-off* (oast-off *oast-open* *orrt-views* 0 *t2r-post* *t2-stalled*))
(defconst *oast-disk-440* (fn-nntp-reply-effect (fn-otm-post-command-reply *t2-stalled*)))
(assert-event (equal (fn-own-tls-result-effects *oast-stalled-off*) (list *oast-disk-440*)))
(assert-event (not (member-equal *oast-memory-440* (fn-own-tls-result-effects *oast-stalled-off*))))
; It is the time model's own answer to a POST while the disk sheds.
(assert-event (equal (fn-own-tls-result-effects
                      (t2r-host-read *oast-open* *orrt-views* 0 *t2r-post* *t2-stalled*))
                     (list *oast-disk-440*)))
; The mutation (the memory's line whatever the disk).
(assert-event (equal (fn-oas-post-effects-onto
                      (fn-own-tls-result-effects
                       (t2r-host-read (fn-otm-owner-with-allow *oast-open* 0 nil) *orrt-views* 0
                                      *t2r-post* *t2-stalled*))
                      *fn-oas-post-line* nil)
                     (list *oast-memory-440*)))

; THE IN-FLIGHT COUNT the default profile holds, by the article limit
; (tests/test_native_slow_disk.py's init): A = 64 KiB, 25 articles in flight;
; A = 1 MiB, one (a credit is the article's worst case as octet lists, 32
; octets an octet, until chunked-body (B6) holds the body in packed chunks).
(defun oast-default-at (a)
  (declare (xargs :mode :program))
  (fn-bs-profile-resolve (list :default (list (cons *fn-bs-pf-max-article-octets* a))) nil))
(assert-event (equal (fn-heap-article-reserve-octets (oast-default-at 65536)) 2637824))
(assert-event (equal (fn-heap-article-slots (oast-default-at 65536)) 25))
(assert-event (equal (fn-heap-article-reserve-octets (oast-default-at 1048576)) 34095104))
(assert-event (equal (fn-heap-article-slots (oast-default-at 1048576)) 1))
