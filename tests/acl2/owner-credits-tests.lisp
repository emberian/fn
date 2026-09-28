; Witnesses for books/owner-credits.lisp (lane credits, B5).
;
; The host's call, fn-mca-read-span, on live stobjs over owner-article-slots-
; tests' owner (*oast-open*: connection 0 a reader with its posting bit on)
; at the admitted gate value *t2-s1*, and the commit's credit steps over
; ledgers of the host's shape.
(in-package "ACL2")
(include-book "../../books/owner-credits")
(include-book "../../books/codec-attach")
(include-book "owner-article-slots-tests")

(defun mcat-read-in (credits oc views id octs s slots reserve rows payloads fn-octets fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-octets fn-arena fn-cat)))
  (let* ((fn-octets (fn-octets-from-list octs fn-octets))
         (fn-arena (fn-arena-clear fn-arena))
         (fn-arena (fn-arn-seal-many payloads fn-arena))
         (fn-cat (fn-sca-load-held-rows rows (fn-own-view-index (fn-own-view (fn-ocfg-owner oc)))
                                        fn-arena fn-cat)))
    (mv (fn-mca-read-span credits oc views id 0 (len octs) nil s slots reserve fn-octets fn-arena fn-cat)
        fn-octets fn-arena fn-cat)))

(defun mcat-read (credits oc views id octs s slots reserve)
  (declare (xargs :mode :program))
  (with-local-stobj fn-octets
    (mv-let (result fn-octets)
      (with-local-stobj fn-arena
        (mv-let (result fn-octets fn-arena)
          (with-local-stobj fn-cat
            (mv-let (result fn-octets fn-arena fn-cat)
              (mcat-read-in credits oc views id octs s slots reserve
                            (orrt-records *lgt-finished*) *g12b-payloads*
                            fn-octets fn-arena fn-cat)
              (mv result fn-octets fn-arena)))
          (mv result fn-octets)))
      result)))

; One article's reserve at the small preset (fn-heap-article-reserve-octets).
(defconst *mcat-r* 1589248)
; A ledger with ROOM octets free: 100 MiB of base, nothing else held.
(defun mcat-ledger (room ops)
  (declare (xargs :mode :program))
  (fn-mcr-make (+ (* 100 1048576) room (fn-mcr-ops-credit ops)) (* 100 1048576) 0 0 0 0 ops))

; KEYSTONE fn-mca-read-span-keeps-funded and fn-mca-read-span-covers-the-
; connection.  REACHABLE POSITIVE WITNESS: room for one reserve, connection 0
; holding nothing (covering its need of 0); the POST is offered (340), the
; read is the read before this book (fn-mca-read-span-within-the-credit-
; unfolds), and connection 0 then holds exactly one reserve, the ledger
; funded with no room left.
(defconst *mcat-l1* (mcat-ledger *mcat-r* nil))
(defconst *mcat-admit* (mcat-read *mcat-l1* *oast-open* *orrt-views* 0 *t2r-post* *t2-s1* 32 *mcat-r*))
(assert-event (fn-mcr-fundedp *mcat-l1*))
(assert-event (<= (fn-mca-need *oast-open* 0 *mcat-r*) (fn-mca-held *mcat-l1* 0)))
(assert-event (equal (car *mcat-admit*) (oast-read *oast-open* *orrt-views* 0 *t2r-post* *t2-s1* 32)))
(assert-event (fn-post-offeredp (fn-own-tls-result-effects (car *mcat-admit*))))
(assert-event (fn-mcr-fundedp (cdr *mcat-admit*)))
(assert-event (equal (fn-mca-held (cdr *mcat-admit*) 0)
                     (fn-mca-need (fn-own-tls-result-owner (car *mcat-admit*)) 0 *mcat-r*)))
(assert-event (equal (fn-mca-held (cdr *mcat-admit*) 0) *mcat-r*))
(assert-event (equal (fn-mcr-total (cdr *mcat-admit*)) (fn-mcr-budget (cdr *mcat-admit*))))

; THE CREDIT REFUSES BY NAME where the slots would not.  Thirty-two slots,
; nothing in flight, but the ledger has one octet less than a reserve free:
; fn-oas-read-span offers the POST (the MUTATION: taken, the connection would
; need a reserve the ledger cannot fund -- over-committed), and the host's
; call answers the memory 440 at the command, holds nothing and leaves the
; ledger as it was.
(defconst *mcat-l0* (mcat-ledger (1- *mcat-r*) nil))
(defconst *mcat-oas* (oast-read *oast-open* *orrt-views* 0 *t2r-post* *t2-s1* 32))
(assert-event (fn-post-offeredp (fn-own-tls-result-effects *mcat-oas*)))
(assert-event (equal (fn-mcr-resize *mcat-l0* (fn-mca-conn-key 0)
                                    (fn-mca-need (fn-own-tls-result-owner *mcat-oas*) 0 *mcat-r*))
                     '(:refused :memory-budget-exhausted)))
(assert-event (< (fn-mcr-budget *mcat-l0*) (+ (fn-mcr-total *mcat-l0*) *mcat-r*)))
(defconst *mcat-refused* (mcat-read *mcat-l0* *oast-open* *orrt-views* 0 *t2r-post* *t2-s1* 32 *mcat-r*))
(assert-event
 (let ((effects (fn-own-tls-result-effects (car *mcat-refused*))))
   (and (equal effects (list (fn-nntp-reply-effect *fn-oas-post-line*)))
        (not (fn-post-offeredp effects))
        (not (fn-oas-articlep (fn-own-tls-result-owner (car *mcat-refused*)) 0)))))
(assert-event (fn-mcr-fundedp (cdr *mcat-refused*)))
(assert-event (equal (fn-mca-held (cdr *mcat-refused*) 0) 0))
(assert-event (equal (fn-mcr-total (cdr *mcat-refused*)) (fn-mcr-total *mcat-l0*)))

; HYPOTHESIS REMOVAL for fn-mca-read-span-keeps-funded: from an UNFUNDED
; ledger (total past the budget) the admitted read leaves it unfunded.
(defconst *mcat-over* (fn-mcr-make 10 20 0 0 0 0 nil))
(assert-event (not (fn-mcr-fundedp *mcat-over*)))
(assert-event (not (fn-mcr-fundedp
                    (cdr (mcat-read *mcat-over* *oast-open* *orrt-views* 0 *t2r-post* *t2-s1* 32 0)))))

; RESERVE TO FINISH (fn-mca-read-span-never-blocks-what-is-held).  Reachable:
; the admitted POST's owner, connection 0 mid-article holding its reserve,
; NO room left: a body line reads exactly as fn-oas-read-span, and the
; credit is unchanged.
(defconst *mcat-mid* (fn-own-tls-result-owner (car *mcat-admit*)))
(defconst *mcat-cont* (mcat-read (cdr *mcat-admit*) *mcat-mid* *orrt-views* 0 *oast-body* *t2-s1* 32 *mcat-r*))
(assert-event (<= (fn-mca-need (fn-own-tls-result-owner *mcat-cont* ) 0 *mcat-r*)
                  (fn-mca-held (cdr *mcat-admit*) 0)))
(assert-event (equal (car *mcat-cont*) (oast-read *mcat-mid* *orrt-views* 0 *oast-body* *t2-s1* 32)))
(assert-event (equal (cdr *mcat-cont*) (cdr *mcat-admit*)))
; Hypothesis removal: the same body line from a ledger where connection 0
; holds nothing and there is no room: the need (one reserve) is past what it
; holds, and the read is NOT the read before this book -- the connection
; mid-article is closed 400 by the refused read.
(defconst *mcat-cont0* (mcat-read *mcat-l0* *mcat-mid* *orrt-views* 0 *oast-body* *t2-s1* 32 *mcat-r*))
(assert-event (not (<= (fn-mca-need (fn-own-tls-result-owner
                                     (oast-read *mcat-mid* *orrt-views* 0 *oast-body* *t2-s1* 32))
                                    0 *mcat-r*)
                       (fn-mca-held *mcat-l0* 0))))
(assert-event (not (equal (car *mcat-cont0*)
                          (oast-read *mcat-mid* *orrt-views* 0 *oast-body* *t2-s1* 32))))
(assert-event (fn-served-closingp (fn-own-tls-result-effects (car *mcat-cont0*))))

; HYPOTHESIS REMOVAL for fn-mca-read-span-covers-the-connection: connection 0
; with a queued submission (need one reserve) that its credit does NOT cover
; (it holds nothing) and no room: whatever the host's call answers, the
; credit left is not the need (the ledger is kept, not over-committed).
(defconst *mcat-queued* *oast-queued*)
(assert-event (equal (fn-mca-need *mcat-queued* 0 *mcat-r*) 0))
(defconst *mcat-queued0*
  (fn-ocfg-with-owner *oast-open*
                      (fn-own-enqueue (fn-ocfg-owner *oast-open*)
                                      (fn-own-sub-make 0 0 nil :witness))))
(assert-event (equal (fn-mca-need *mcat-queued0* 0 *mcat-r*) *mcat-r*))
(assert-event (not (<= (fn-mca-need *mcat-queued0* 0 *mcat-r*) (fn-mca-held *mcat-l0* 0))))
(defconst *mcat-uncovered* (mcat-read *mcat-l0* *mcat-queued0* *orrt-views* 0 *t2r-post* *t2-s1* 32 *mcat-r*))
(assert-event (not (equal (fn-mca-held (cdr *mcat-uncovered*) 0)
                          (fn-mca-need (fn-own-tls-result-owner (car *mcat-uncovered*)) 0 *mcat-r*))))
(assert-event (fn-mcr-fundedp (cdr *mcat-uncovered*)))

; The shut read (the tier past the refused read: a peer's article completed
; within one read, IHAVE or TAKETHIS, whose refused read still queues it):
; 400 and close, every octet consumed, the connection out of article mode,
; nothing else of the owner changed.  (A served-state witness of that tier
; needs an owner with a peer connection; open, see the lane record.)
(defconst *mcat-shut* (fn-mca-shut-read *mcat-mid* 0 0 7))
(assert-event (equal (fn-own-tls-result-effects *mcat-shut*)
                     (list (fn-nntp-reply-effect *fn-oas-busy-line*) (fn-nntp-close-effect))))
(assert-event (equal (fn-own-tls-result-consumed *mcat-shut*) 7))
(assert-event (not (fn-oas-articlep (fn-own-tls-result-owner *mcat-shut*) 0)))
(assert-event (<= (fn-mca-need (fn-own-tls-result-owner *mcat-shut*) 0 *mcat-r*)
                  (fn-mca-need *mcat-mid* 0 *mcat-r*)))

; THE COMMIT'S STEPS.  Connection 0 holds one reserve (its queued POST); the
; take moves it to :open, the seal to :sealed; the client then times out and
; is closed: KEYSTONE fn-mca-close-keeps-what-the-commit-owns -- the batch
; in flight keeps its reserve, so the ledger still has no room for another
; article while the barrier runs (the case the slots missed: the owner's
; queue, its in-flight field and connection 0 all empty).  Only COMPLETE
; frees it.
(defconst *mcat-c0* (mcat-ledger 0 (list (cons (fn-mca-conn-key 0) (cons 0 *mcat-r*)))))
(assert-event (fn-mcr-fundedp *mcat-c0*))
(defconst *mcat-c1* (fn-mca-take *mcat-c0* 0 *mcat-r*))
(assert-event (equal (fn-mca-held *mcat-c1* 0) 0))
(assert-event (equal (fn-mcr-credit-of *fn-mca-open* (fn-mcr-ops *mcat-c1*)) *mcat-r*))
(assert-event (equal (fn-mcr-total *mcat-c1*) (fn-mcr-total *mcat-c0*)))
(defconst *mcat-c2* (fn-mca-seal *mcat-c1*))
(assert-event (equal (fn-mcr-credit-of *fn-mca-open* (fn-mcr-ops *mcat-c2*)) 0))
(assert-event (equal (fn-mcr-credit-of *fn-mca-sealed* (fn-mcr-ops *mcat-c2*)) *mcat-r*))
(defconst *mcat-c3* (fn-mca-close *mcat-c2* 0))
(assert-event (equal (fn-mcr-credit-of *fn-mca-sealed* (fn-mcr-ops *mcat-c3*)) *mcat-r*))
(assert-event (fn-mcr-fundedp *mcat-c3*))
; While the batch is in flight a new POST is refused by name ...
(assert-event (equal (car (fn-mcr-resize *mcat-c3* (fn-mca-conn-key 1) *mcat-r*))
                     :refused))
; ... and a close that released the batch's credit too (the MUTATION: credit
; freed on the client's timeout) would have admitted it.
(defconst *mcat-mutant*
  (cadr (fn-mcr-resize (fn-mca-close *mcat-c2* 0) *fn-mca-sealed* 0)))
(assert-event (equal (car (fn-mcr-resize *mcat-mutant* (fn-mca-conn-key 1) *mcat-r*)) :ok))
; COMPLETE releases it; then the POST fits.
(defconst *mcat-c4* (fn-mca-batch-done *mcat-c3*))
(assert-event (equal (fn-mcr-credit-of *fn-mca-sealed* (fn-mcr-ops *mcat-c4*)) 0))
(assert-event (fn-mcr-fundedp *mcat-c4*))
(assert-event (equal (car (fn-mcr-resize *mcat-c4* (fn-mca-conn-key 1) *mcat-r*)) :ok))
; A shed POST (taken, nothing stored) gives its reserve back from :open.
(assert-event (equal (fn-mcr-credit-of *fn-mca-open* (fn-mcr-ops (fn-mca-untake *mcat-c1* *mcat-r*))) 0))
; The stop releases both.
(assert-event (equal (fn-mcr-ops-credit (fn-mcr-ops (fn-mca-stop (fn-mca-take *mcat-c2* 0 *mcat-r*)))) 0))
; The control channel's submission (no connection key) moves nothing.
(assert-event (equal (fn-mca-take *mcat-c0* :control *mcat-r*) *mcat-c0*))

; KEYSTONE fn-mca-initial-funds-exactly-the-articles on the production core
; (heap-figure-tests' *hft-prod-core*): at the small preset the pool is
; 50,855,936 octets, 32 reserves and not 33; under A = 4 MiB exactly one
; (the native case, tests/test_native_article_slots.py).
(defconst *mcat-core* '(200411640 . 114644864))
(defconst *mcat-small* (fn-mca-initial *fn-heap-small-profile* *mcat-core* nil))
(assert-event (fn-mcr-fundedp *mcat-small*))
(assert-event (equal (fn-mcr-budget *mcat-small*)
                     (fn-heap-figure-octets *fn-heap-small-profile* *mcat-core* nil)))
(assert-event (equal (- (fn-mcr-budget *mcat-small*) (fn-mcr-total *mcat-small*)) 50855936))
(assert-event (equal (fn-mcr-completion *mcat-small*) (fn-mca-open-octets *fn-heap-small-profile*)))
(defun mcat-admit-n (l n r)
  (declare (xargs :mode :program))
  (if (zp n) l
    (let ((d (fn-mcr-resize l (fn-mca-conn-key n) r)))
      (if (equal (car d) :ok) (mcat-admit-n (cadr d) (1- n) r) :refused))))
(assert-event (fn-mcr-fundedp (mcat-admit-n *mcat-small* 32 *mcat-r*)))
(assert-event (equal (mcat-admit-n *mcat-small* 33 *mcat-r*) :refused))
(defconst *mcat-a4* (fn-mca-initial *oast-a4* *mcat-core* nil))
(defconst *mcat-a4-r* (fn-heap-article-reserve-octets *oast-a4*))
(assert-event (fn-mcr-fundedp (mcat-admit-n *mcat-a4* 1 *mcat-a4-r*)))
(assert-event (equal (mcat-admit-n *mcat-a4* 2 *mcat-a4-r*) :refused))
