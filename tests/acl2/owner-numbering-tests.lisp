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

(defun onb-watermark-conclusion (oc events sub-id word group)
  (<= (fn-next-number group (fn-state-nexts (onb-archive oc)))
      (fn-next-number group (fn-state-nexts
                             (onb-archive (osi-after-post oc events sub-id word))))))

(defun onb-holder-conclusion (oc events sub-id word group number)
  (equal (fn-own-number-holder
          group number (fn-state-articles (onb-archive (osi-after-post oc events sub-id word))))
         (fn-own-number-holder group number (fn-state-articles (onb-archive oc)))))

; -----------------------------------------------------------------------------
; Witness: two POSTs in fn.letters across a completion.  Connection 4's
; queued article is taken, staged, completed; then a second transaction for
; <four@example> is begun by connection 3 and completed; then connection 4's
; outcome is the 240.  Every event is a writer event.
(defconst *onb-events*
  (append *osi-post-events* '((:begin 3)) (own-post-events (own-record 3 3 "<four@example>"))))
(defconst *onb-after* (osi-after-post *osi-q* *onb-events* 4 :durable))
(defconst *onb-injected-id*
  "<00000001600000010000.00000000000002000000.fn@fn.example.invalid>")

(assert-event (fn-own-relation (fn-ocfg-owner *osi-q*)))
(assert-event (fn-ocfg-writer-eventsp *onb-events*))
(assert-event (equal (fn-own-take 4 (fn-served-reply-octets
                                     (car (fn-own-outcome
                                           (fn-ocfg-owner (fn-ocfg-run *osi-q* *onb-events*))
                                           4 :durable))))
                     (fn-nntp-string-octets "240 ")))
; The watermark of fn.letters rises from 3 to 5; fn.test stays at 1.
(assert-event (equal (fn-state-nexts (onb-archive *osi-q*))
                     '(("fn.letters" . 3) ("fn.test" . 1))))
(assert-event (equal (fn-state-nexts (onb-archive *onb-after*))
                     '(("fn.letters" . 5) ("fn.test" . 1))))
(assert-event (onb-watermark-conclusion *osi-q* *onb-events* 4 :durable "fn.letters"))
(assert-event (onb-watermark-conclusion *osi-q* *onb-events* 4 :durable "fn.test"))
; Numbers 1 and 2 keep their Message-IDs; 3 and 4 are the two new articles.
(assert-event (equal (fn-own-number-holder "fn.letters" 1 (fn-state-articles (onb-archive *osi-q*)))
                     "<one@example>"))
(assert-event (onb-holder-conclusion *osi-q* *onb-events* 4 :durable "fn.letters" 1))
(assert-event (equal (fn-own-number-holder "fn.letters" 2 (fn-state-articles (onb-archive *osi-q*)))
                     "<two@example>"))
(assert-event (onb-holder-conclusion *osi-q* *onb-events* 4 :durable "fn.letters" 2))
(assert-event (equal (fn-own-number-holder "fn.letters" 3 (fn-state-articles (onb-archive *onb-after*)))
                     *onb-injected-id*))
(assert-event (equal (fn-own-number-holder "fn.letters" 4 (fn-state-articles (onb-archive *onb-after*)))
                     "<four@example>"))

; A reader's numbers, through the served read.  Reader 3, still pinned at
; version 2, answers GROUP as before; advanced (fn-ocfg-advance, the pin
; write the host performs), it sees 1 to 4 and STAT names the new articles
; by the numbers above.
(defun onb-reply (oc id octets)
  (fn-served-reply-octets (fn-own-tls-result-effects (fn-ocfg-read-tls-prefix oc id octets))))
(defconst *onb-stat-octets*
  (append *own-group-octets*
          (fn-nntp-string-octets "STAT 3") '(13 10)
          (fn-nntp-string-octets "STAT 4") '(13 10)))
(assert-event (equal (onb-reply *onb-after* 3 *own-group-octets*)
                     (append (fn-nntp-string-octets "211 2 1 2 fn.letters") '(13 10))))
(assert-event (equal (onb-reply (fn-ocfg-advance *onb-after* 3) 3 *onb-stat-octets*)
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
                  (fn-own-ledger o) (fn-own-clock o) (fn-own-facts o) (fn-own-config o)
                  (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o)))))
(defconst *onb-wound* (onb-wind-back *osi-q*))
(assert-event (fn-node-statep (fn-sn-node (fn-own-store (fn-ocfg-owner *onb-wound*)))))
(assert-event (not (fn-own-relation (fn-ocfg-owner *onb-wound*))))
(assert-event (fn-ocfg-writer-eventsp *osi-post-events*))
(assert-event (equal (fn-own-take 4 (fn-served-reply-octets
                                     (car (fn-own-outcome
                                           (fn-ocfg-owner (fn-ocfg-run *onb-wound* *osi-post-events*))
                                           4 :durable))))
                     (fn-nntp-string-octets "240 ")))
(assert-event (equal (fn-state-nexts (onb-archive (osi-after-post *onb-wound* *osi-post-events* 4 :durable)))
                     '(("fn.letters" . 2) ("fn.test" . 1))))
(assert-event (not (onb-watermark-conclusion *onb-wound* *osi-post-events* 4 :durable "fn.letters")))
(must-fail (assert-event
            (onb-watermark-conclusion *onb-wound* *osi-post-events* 4 :durable "fn.letters")))
(assert-event (equal (fn-own-number-holder "fn.letters" 1 (fn-state-articles (onb-archive *onb-wound*)))
                     "<one@example>"))
(assert-event (not (onb-holder-conclusion *onb-wound* *osi-post-events* 4 :durable "fn.letters" 1)))
(must-fail (assert-event
            (onb-holder-conclusion *onb-wound* *osi-post-events* 4 :durable "fn.letters" 1)))

; Hypothesis (the number is held before), fn-own-served-local-number-is-never-reassigned.
; fn.letters 3 names nothing before the witness events and the injected
; article after.  A number is fixed once it is given, not before.
(assert-event (null (fn-own-number-holder "fn.letters" 3 (fn-state-articles (onb-archive *osi-q*)))))
(assert-event (not (onb-holder-conclusion *osi-q* *onb-events* 4 :durable "fn.letters" 3)))
(must-fail (assert-event (onb-holder-conclusion *osi-q* *onb-events* 4 :durable "fn.letters" 3)))

; Hypothesis (fn-ocfg-writer-eventsp events): NO TOOTH.  No violating value
; was found.  Every other arm of fn-ocfg-step leaves the committed view
; alone or, for (:reopen ...), refreshes it from a crash image that extends
; the durable records (fn-own-step-records-prefix holds for every event),
; so the hypothesis looks redundant; that is not proved here.  It is the
; statement's scope: the writer events the host runs for a POST.
