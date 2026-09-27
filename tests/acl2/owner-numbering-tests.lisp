; Teeth for books/owner-numbering.lisp (v0 P3, PRF-002).
;
; For each keystone: a reachable witness at which every hypothesis and the
; conclusion hold, then per hypothesis a value at which the other hypotheses
; hold and that one fails, asserted first, then the false conclusion, then a
; must-fail on the conclusion.  The fixture is the served POST scenario of
; tests/acl2/owner-tests.lisp as tests/acl2/owner-served-invariants-tests.lisp
; configures it (*osi-q*: reader 3 pinned at version 2, connection 4's
; injected article queued).

(in-package "ACL2")
(include-book "owner-served-invariants-tests")
(include-book "../../books/owner-numbering")
(include-book "std/testing/must-fail" :dir :system)

(defun onb-archive (oc)
  (fn-own-view-archive (fn-own-view (fn-ocfg-owner oc))))

(defun onb-watermark-conclusion (oc events sub-id word group fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (<= (fn-next-number group (fn-state-nexts (onb-archive oc)))
      (fn-next-number group (fn-state-nexts
                             (onb-archive (osi-after-post oc events sub-id word fn-arena))))))

; The served conclusion: the visible holder after is the one before or none.
(defun onb-holder-conclusion (oc events sub-id word group number fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let ((after (fn-own-number-holder
                group number (fn-state-articles (onb-archive (osi-after-post oc events sub-id word fn-arena))))))
    (or (null after)
        (equal after
               (fn-own-number-holder group number (fn-state-articles (onb-archive oc)))))))

(defun onb-raw (oc)
  (fn-own-view-raw (fn-own-view (fn-ocfg-owner oc))))

; The raw conclusion (fn-own-raw-local-number-is-never-reassigned).
(defun onb-raw-holder-conclusion (oc events sub-id word group number fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (equal (fn-own-number-holder group number (onb-raw (osi-after-post oc events sub-id word fn-arena)))
         (fn-own-number-holder group number (onb-raw oc))))

; -----------------------------------------------------------------------------
; Witness: two POSTs in fn.letters across a completion.  Connection 4's
; queued article is taken, staged, completed; then a second transaction for
; <four@example> is begun by connection 3 and completed; then connection 4's
; outcome is the 240.  Every event is a writer event.
(defconst *onb-events*
  (append *osi-post-events* '((:begin 3)) (own-post-events (own-record 3 3 "<four@example>"))))
(include-book "arena-lift")
;; The payloads the arena holds at handles 0, 1, ...: none (no byte is read here).
(defconst *sr-arena* nil)
(bpr-lift fn-ocfg-run 2)
(bpr-lift onb-holder-conclusion 6)
(bpr-lift onb-raw-holder-conclusion 6)
(bpr-lift onb-watermark-conclusion 5)
(bpr-lift osi-after-post 4)
(defconst *onb-after* (in-arena-osi-after-post *sr-arena* *osi-q* *onb-events* 4 :durable))
(defconst *onb-injected-id*
  "<00000001600000010000.00000000000002000000.fn@fn.example.invalid>")

(assert-event (fn-own-relation (fn-ocfg-owner *osi-q*)))
(assert-event (fn-ocfg-writer-eventsp *onb-events*))
(assert-event (equal (fn-own-take 4 (fn-served-reply-octets
                                     (car (fn-own-outcome
                                           (fn-ocfg-owner (in-arena-fn-ocfg-run *sr-arena* *osi-q* *onb-events*))
                                           4 :durable))))
                     (fn-nntp-string-octets "240 ")))
; The watermark of fn.letters rises from 3 to 5; fn.test stays at 1.
(assert-event (equal (fn-state-nexts (onb-archive *osi-q*))
                     '(("fn.letters" . 3) ("fn.test" . 1))))
(assert-event (equal (fn-state-nexts (onb-archive *onb-after*))
                     '(("fn.letters" . 5) ("fn.test" . 1))))
(assert-event (in-arena-onb-watermark-conclusion *sr-arena* *osi-q* *onb-events* 4 :durable "fn.letters"))
(assert-event (in-arena-onb-watermark-conclusion *sr-arena* *osi-q* *onb-events* 4 :durable "fn.test"))
; Numbers 1 and 2 keep their Message-IDs; 3 and 4 are the two new articles.
(assert-event (equal (fn-own-number-holder "fn.letters" 1 (fn-state-articles (onb-archive *osi-q*)))
                     "<one@example>"))
(assert-event (in-arena-onb-holder-conclusion *sr-arena* *osi-q* *onb-events* 4 :durable "fn.letters" 1))
(assert-event (equal (fn-own-number-holder "fn.letters" 2 (fn-state-articles (onb-archive *osi-q*)))
                     "<two@example>"))
(assert-event (in-arena-onb-holder-conclusion *sr-arena* *osi-q* *onb-events* 4 :durable "fn.letters" 2))
; The same on the raw list, which in this fixture (no cancel) is the visible one.
(assert-event (equal (fn-own-number-holder "fn.letters" 1 (onb-raw *osi-q*)) "<one@example>"))
(assert-event (in-arena-onb-raw-holder-conclusion *sr-arena* *osi-q* *onb-events* 4 :durable "fn.letters" 1))
(assert-event (in-arena-onb-raw-holder-conclusion *sr-arena* *osi-q* *onb-events* 4 :durable "fn.letters" 2))
; The served conclusion holds here by its equality arm, not by the null one.
(assert-event (equal (fn-own-number-holder
                      "fn.letters" 1 (fn-state-articles (onb-archive *onb-after*)))
                     "<one@example>"))
(assert-event (equal (fn-own-number-holder "fn.letters" 3 (fn-state-articles (onb-archive *onb-after*)))
                     *onb-injected-id*))
(assert-event (equal (fn-own-number-holder "fn.letters" 4 (fn-state-articles (onb-archive *onb-after*)))
                     "<four@example>"))

; A reader's numbers, through the served read.  Reader 3 is still pinned at
; version 2 after the post (its record is unchanged: P3); BY SPECIFICATION
; (NNT-042, 2026-09-27) its GROUP acquires the fresh view and sees 1 to 4 --
; before NNT-042 it answered 211 2 1 2 as before the post.  Advanced first
; (fn-ocfg-advance, the pin write the host performs) it sees the same, and
; STAT names the new articles by the numbers above.
(defun onb-reply (oc id octets fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (fn-served-reply-octets (fn-own-tls-result-effects (fn-ocfg-read-tls-prefix oc id octets fn-arena))))
(bpr-lift onb-reply 3)
(defconst *onb-stat-octets*
  (append *own-group-octets*
          (fn-nntp-string-octets "STAT 3") '(13 10)
          (fn-nntp-string-octets "STAT 4") '(13 10)))
(assert-event (equal (fn-own-conn-version
                      (fn-own-find-conn 3 (fn-own-conns (fn-ocfg-owner *onb-after*))))
                     2))
(assert-event (equal (in-arena-onb-reply *sr-arena* *onb-after* 3 *own-group-octets*)
                     (append (fn-nntp-string-octets "211 4 1 4 fn.letters") '(13 10))))
(assert-event (equal (in-arena-onb-reply *sr-arena* (fn-ocfg-advance *onb-after* 3) 3 *onb-stat-octets*)
                     (append (fn-nntp-string-octets "211 4 1 4 fn.letters") '(13 10)
                             (fn-nntp-string-octets "223 3 ") (fn-nntp-string-octets *onb-injected-id*)
                             (fn-nntp-string-octets " retrieved") '(13 10)
                             (fn-nntp-string-octets "223 4 <four@example> retrieved") '(13 10))))

; -----------------------------------------------------------------------------
; Hypothesis (fn-own-relation), both keystones.  The store node's archive
; wound back to empty (initial watermarks, no articles, no bindings) while
; the committed view still shows fn.letters 1 and 2: the node is a valid
; node state, but it is not the replay of the durable records, so the owner
; relation fails.  Connection 4's POST then allocates fn.letters 1 again,
; the store completes, the owner answers 240, and the refreshed view gives
; number 1 to the injected article with the watermark at 2, below 3.
(defun onb-wind-back (oc)
  (let* ((o (fn-ocfg-owner oc))
         (s (fn-own-store o))
         (node (fn-sn-node s))
         (a (fn-node-acceptance node))
         (a2 (fn-make-state (fn-state-groups a) (fn-initial-nexts (fn-state-groups a))
                            nil (fn-state-next-txid a) nil nil))
         (node2 (fn-node-make-state a2 (fn-node-retention node) nil nil)))
    (fn-ocfg-with-owner
     oc
     (fn-own-make (fn-sn-update s (fn-sn-files s) node2) (fn-own-view o) (fn-own-conns o)
                  (fn-own-next-id o) (fn-own-max-conns o) (fn-own-pending o)
                  (fn-own-ledger-field o) (fn-own-clock o) (fn-own-facts o) (fn-own-config o)
                  (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o) (fn-own-node-secret o) (fn-own-refused o)))))
(defconst *onb-wound* (onb-wind-back *osi-q*))
(assert-event (fn-node-statep (fn-sn-node (fn-own-store (fn-ocfg-owner *onb-wound*)))))
(assert-event (not (fn-own-relation (fn-ocfg-owner *onb-wound*))))
(assert-event (fn-ocfg-writer-eventsp *osi-post-events*))
(assert-event (equal (fn-own-take 4 (fn-served-reply-octets
                                     (car (fn-own-outcome
                                           (fn-ocfg-owner (in-arena-fn-ocfg-run *sr-arena* *onb-wound* *osi-post-events*))
                                           4 :durable))))
                     (fn-nntp-string-octets "240 ")))
(assert-event (equal (fn-state-nexts (onb-archive (in-arena-osi-after-post *sr-arena* *onb-wound* *osi-post-events* 4 :durable)))
                     '(("fn.letters" . 2) ("fn.test" . 1))))
(assert-event (not (in-arena-onb-watermark-conclusion *sr-arena* *onb-wound* *osi-post-events* 4 :durable "fn.letters")))
(must-fail (assert-event
            (in-arena-onb-watermark-conclusion *sr-arena* *onb-wound* *osi-post-events* 4 :durable "fn.letters")))
(assert-event (equal (fn-own-number-holder "fn.letters" 1 (fn-state-articles (onb-archive *onb-wound*)))
                     "<one@example>"))
(assert-event (not (in-arena-onb-holder-conclusion *sr-arena* *onb-wound* *osi-post-events* 4 :durable "fn.letters" 1)))
(must-fail (assert-event
            (in-arena-onb-holder-conclusion *sr-arena* *onb-wound* *osi-post-events* 4 :durable "fn.letters" 1)))
(assert-event (equal (fn-own-number-holder "fn.letters" 1 (onb-raw *onb-wound*)) "<one@example>"))
(assert-event (not (in-arena-onb-raw-holder-conclusion *sr-arena* *onb-wound* *osi-post-events* 4 :durable "fn.letters" 1)))
(must-fail (assert-event
            (in-arena-onb-raw-holder-conclusion *sr-arena* *onb-wound* *osi-post-events* 4 :durable "fn.letters" 1)))

; Hypothesis (the number is held before), both holder keystones.
; fn.letters 3 names nothing before the witness events and the injected
; article after.  A number is fixed once it is given, not before.
(assert-event (null (fn-own-number-holder "fn.letters" 3 (fn-state-articles (onb-archive *osi-q*)))))
(assert-event (not (in-arena-onb-holder-conclusion *sr-arena* *osi-q* *onb-events* 4 :durable "fn.letters" 3)))
(must-fail (assert-event (in-arena-onb-holder-conclusion *sr-arena* *osi-q* *onb-events* 4 :durable "fn.letters" 3)))
(assert-event (null (fn-own-number-holder "fn.letters" 3 (onb-raw *osi-q*))))
(assert-event (not (in-arena-onb-raw-holder-conclusion *sr-arena* *osi-q* *onb-events* 4 :durable "fn.letters" 3)))
(must-fail (assert-event (in-arena-onb-raw-holder-conclusion *sr-arena* *osi-q* *onb-events* 4 :durable "fn.letters" 3)))

; Hypothesis (fn-ocfg-writer-eventsp events): NO TOOTH.  No violating value
; was found.  Every other arm of fn-ocfg-step leaves the committed view
; alone or, for (:reopen ...), refreshes it from a crash image that extends
; the durable records (fn-own-step-records-prefix holds for every event),
; so the hypothesis looks redundant; that is not proved here.  It is the
; statement's scope: the writer events the host runs for a POST.
