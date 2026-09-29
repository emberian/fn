; Teeth for books/native-health (PRF-112): the health verdict's nine states,
; its exit code and the owner's report.  The owner state is
; native-live-status-tests' host-shaped one: one committed article, one
; retention pin, the development profile.
(in-package "ACL2")
(include-book "../../books/native-health")
(include-book "../../books/owner-store-budget")
(include-book "../../books/codec-attach")
(include-book "must-fail-checked")
(include-book "held-rows-tests")
;; PRF-335: the owner-level witness below reuses owner-tests' control
;; submission with one outbound peer of max-queue 1.
(include-book "owner-tests")

(defconst *nht-groups* '("fn.letters" "fn.test"))
(defconst *nht-config*
  (fn-config-replay 0 (fn-cnode-line-ceiling)
                    (list *fn-cfg-default-record*)))
(defconst *nht-post-config*
  (fn-inj-make-config
   t '(102 110 46 111 112 99 46 105 110 118 97 108 105 100)
   (list (fn-nntp-string-octets "fn.letters")
         (fn-nntp-string-octets "fn.test"))
   32768))
(defconst *nht-first-wire*
  (fn-record-make 0 0 0 "<nht-first@example.invalid>" '(65 66)
                  *nht-groups* "nht-pin-1" "nht-subject-1"
                  "nht-release-1" 2 841000000))
; The store retains held rows (records-flip): each record reaches the
; store as the row the entry interns (store-intern fn-intern-row-at,
; keyring nil at generation 0), its handle its place in the run's arena.
(defconst *nht-first* (fn-hrt-row-at *nht-first-wire* 0))
(defun nht-run (oc events fn-arena)
  (declare (xargs :stobjs fn-arena :guard (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
                  :verify-guards nil))
  (if (consp events)
      (nht-run (fn-ocfg-step oc (car events) fn-arena) (cdr events) fn-arena)
    oc))
(defconst *nht-reserve-events*
  '((:store (:io :start-frontier nil))
    (:store (:io :frontier-file :ok))
    (:store (:io :frontier-replace :ok))
    (:store (:io :frontier-directory :ok))))
(defconst *nht-0*
  (fn-ocfg-make
   (fn-own-configure (fn-own-start (fn-sn-initial *nht-groups* 10) 3)
                     *nht-post-config*)
   *nht-config* nil nil))
(include-book "arena-lift")
;; The payloads the arena holds at handles 0, 1, ...: none (no byte is read here).
(defconst *sr-arena* nil)
(bpr-lift fn-ocfg-step 2)
(bpr-lift nht-run 2)
(bpr-lift fn-nls-live-report 5)
(defconst *nht-oc*
  (in-arena-fn-ocfg-step *sr-arena* (in-arena-nht-run *sr-arena* (fn-opc-prepare (in-arena-nht-run *sr-arena* *nht-0* *nht-reserve-events*) *nht-first*) '((:store (:io :record-file :ok))
               (:store (:io :record-link :ok))
               (:store (:io :record-directory :ok)))) '(:complete)))
(defconst *nht-s* (fn-own-store (fn-ocfg-owner *nht-oc*)))
(defconst *nht-profile* (fn-bs-config-for-profile :development))
(defconst *nht-obs* '(nil nil (:full-replay :no-checkpoint)))
; The carried sum as the owner leaves it after its first verdict: every
; committed record, counted once.

(defun nht-cache ()
  (declare (xargs :verify-guards nil))
  (cons (len (fn-sf-records (fn-sn-files *nht-s*)))
        (fn-sbud-record-octets (fn-sf-records (fn-sn-files *nht-s*)))))
(defun nht-stale ()
  (declare (xargs :verify-guards nil))
  (cons (car (nht-cache)) (+ 5 (cdr (nht-cache)))))
(defconst *nht-cfg* (fn-ocfg-config *nht-oc*))
(defconst *nht-scale* (fn-bs-config-for-profile :scale))

;; PRF-335: the feeds carry real limits (a peer record's max-queue 1024); a
;; feed with no limits has no room at all and is saturated.
(defconst *nht-limits* (fn-feed-limits 1024 1000 3 t))

; ---------------------------------------------------------------------------
; A feed table: peer "down" has a queued article and no connection
; (unavailable); peer "gave-up" dropped one at its retry bound (stranded).
(defconst *nht-feeds*
  (list (fn-own-feed-entry "down" nil
                           (fn-feed-make '(100 111 119 110) *nht-limits*
                                         (list (fn-feed-entry '(60 97 62) :queued 1 0))
                                         nil 0 nil 0))
        (fn-own-feed-entry "gave-up" nil
                           (fn-feed-make '(103) *nht-limits*
                                         (list (fn-feed-entry '(60 98 62) '(:dropped :retry-bound) 3 0))
                                         nil 0 7 0))))
(defconst *nht-idle-feeds*
  (list (fn-own-feed-entry "up" nil
                           (fn-feed-make '(117 112) *nht-limits*
                                         ;; PRF-335: its one article was
                                         ;; delivered and retired.
                                         nil
                                         nil 0 7 0))))

(defun nht-store (profile)
  (declare (xargs :verify-guards nil))
  (fn-nh-store-inputs profile *nht-s* (fn-sbud-bytes-used *nht-s*) *nht-cfg*))

(defun nht-states (v)
  (declare (xargs :verify-guards nil))
  (if (consp v) (cons (car (car v)) (nht-states (cdr v))) nil))

; ---------------------------------------------------------------------------
; fn-nh-verdict-states, instances.  The development store: unqualified held;
; pressure at 10 % (1 of 10 transactions used would be 90 % free) clear; no
; forwarding obligation, so no route and no debt; offline feeds unobserved.
(assert-event (fn-nh-unqualifiedp *nht-profile*))
(assert-event (not (fn-nh-unqualifiedp *nht-scale*)))
(assert-event
 (equal (nht-states (fn-nh-verdict nil (nht-store *nht-profile*) 10 :unobserved :unobserved :unobserved))
        '(:clear :clear :held :clear :clear :unobserved :unobserved :clear :unobserved :unobserved)))
; At min 100 every figure with a positive bound is under pressure.
(assert-event
 (equal (nht-states (fn-nh-verdict nil (nht-store *nht-scale*) 100 *nht-idle-feeds* '(:clear) nil))
        '(:clear :clear :clear :held :clear :clear :clear :clear :clear :clear)))
; The owner's feed table: stranded and unavailable held, each its own line.
(assert-event
 (equal (nht-states (fn-nh-verdict nil (nht-store *nht-scale*) 0 *nht-feeds* '(:clear) nil))
        '(:clear :clear :clear :clear :clear :held :held :clear :clear :clear)))
(assert-event (equal (fn-nh-stranded-peers *nht-feeds*) '("gave-up")))
(assert-event (equal (fn-nh-unavailable-peers *nht-feeds*) '("down")))
(assert-event (null (fn-nh-unavailable-peers *nht-idle-feeds*)))
;; PKT-711: fn-nh-deferring-peer-is-held.  Peer "full" has a connection
;; open and one article it deferred (a full Store answered 436): held.
(defconst *nht-full-feeds*
  (list (fn-own-feed-entry "full" nil
                           (fn-feed-make '(102) *nht-limits*
                                         (list (fn-feed-entry '(60 102 62) :queued 2 0))
                                         nil 0 7 0))))
(assert-event (fn-nh-feed-deferredp (fn-own-feed-entry-feed (car *nht-full-feeds*))))
(assert-event (equal (car (fn-nh-nth 6 (fn-nh-verdict nil (nht-store *nht-scale*) 0
                                                      *nht-full-feeds* '(:clear) nil)))
                     :held))
(assert-event (equal (fn-nh-unavailable-peers *nht-full-feeds*) '("full")))
;; Without deferredp: the idle feed's article was delivered, and it is clear.
(assert-event (not (fn-nh-feed-deferredp (fn-own-feed-entry-feed (car *nht-idle-feeds*)))))
(assert-event (equal (car (fn-nh-nth 6 (fn-nh-verdict nil (nht-store *nht-scale*) 0
                                                      *nht-idle-feeds* '(:clear) nil)))
                     :clear))
(must-fail-checked
 (defthm nht-deferring-without-deferred
   (implies (member-equal e feeds)
            (equal (car (fn-nh-nth 6 (fn-nh-verdict fence store min feeds disk ckpt))) :held))
   :hints (("Goal" :do-not-induct t :in-theory (disable fn-nh-verdict)))))
;; Without the member: a deferring feed outside the table holds nothing.
(assert-event (equal (car (fn-nh-nth 6 (fn-nh-verdict nil (nht-store *nht-scale*) 0 nil '(:clear) nil)))
                     :clear))
(must-fail-checked
 (defthm nht-deferring-without-member
   (implies (fn-nh-feed-deferredp (fn-own-feed-entry-feed e))
            (equal (car (fn-nh-nth 6 (fn-nh-verdict fence store min feeds disk ckpt))) :held))
   :hints (("Goal" :do-not-induct t :in-theory (disable fn-nh-verdict)))))
;; PRF-335: fn-nh-saturated-peer-is-held and fn-nh-feed-queue-refusal-is-held.
;; Peer "sat" has room for one entry, holds one undelivered article and a
;; connection open (so neither pending-without-connection nor deferred):
;; saturated alone holds unavailable-peer.
(defconst *nht-sat-feeds*
  (list (fn-own-feed-entry "sat" nil
                           (fn-feed-make '(115) (fn-feed-limits 1 1000 3 t)
                                         (list (fn-feed-entry '(60 115 62) :queued 0 0))
                                         nil 0 7 1))))
(defconst *nht-sat-feed* (fn-own-feed-entry-feed (car *nht-sat-feeds*)))
(assert-event (fn-feedp *nht-sat-feed*))
(assert-event (fn-nh-feed-saturatedp *nht-sat-feed*))
(assert-event (not (fn-nh-feed-deferredp *nht-sat-feed*)))
(assert-event (natp (fn-feed-conn *nht-sat-feed*)))
(assert-event (member-equal (car *nht-sat-feeds*) *nht-sat-feeds*))
(assert-event (equal (car (fn-nh-nth 6 (fn-nh-verdict nil (nht-store *nht-scale*) 0
                                                      *nht-sat-feeds* '(:clear) nil)))
                     :held))
(assert-event (equal (fn-nh-saturated-total *nht-sat-feeds*) 1))
;; The table-level refusal: a new Message-ID has no room at "sat".
(assert-event (fn-nh-names-have-entriesp '("sat") *nht-sat-feeds*))
(assert-event (not (fn-own-feed-target-capacityp '("sat") *nht-sat-feeds* '(60 110 62))))
;; Without saturation: the idle feed is a member, unsaturated, and clear.
(assert-event (not (fn-nh-feed-saturatedp (fn-own-feed-entry-feed (car *nht-idle-feeds*)))))
(assert-event (member-equal (car *nht-idle-feeds*) *nht-idle-feeds*))
;; Without the member: the saturated feed outside the (empty) table holds nothing.
(assert-event (equal (car (fn-nh-nth 6 (fn-nh-verdict nil (nht-store *nht-scale*) 0 nil '(:clear) nil)))
                     :clear))
;; Without fn-nh-names-have-entriesp: a target the table does not hold has no
;; room either, and the idle table is clear.
(assert-event (not (fn-nh-names-have-entriesp '("ghost") *nht-idle-feeds*)))
(assert-event (not (fn-own-feed-target-capacityp '("ghost") *nht-idle-feeds* '(60 110 62))))
;; Without the refusal: the idle peer has room, and it is clear.
(assert-event (fn-nh-names-have-entriesp '("up") *nht-idle-feeds*))
(assert-event (fn-own-feed-target-capacityp '("up") *nht-idle-feeds* '(60 110 62)))
(assert-event (equal (car (fn-nh-nth 6 (fn-nh-verdict nil (nht-store *nht-scale*) 0
                                                      *nht-idle-feeds* '(:clear) nil)))
                     :clear))

; Forwarding obligations: two :forward pins are debt; with no BP route in the
; configuration (this one has none) that is also no route.
(defconst *nht-pins*
  (list (fn-retain-make-obligation "w1" "s1" :forward nil 3)
        (fn-retain-make-obligation "a1" "s2" :archive nil 2)
        (fn-retain-make-obligation "w2" "s3" :forward nil 4)))
(assert-event (equal (fn-nh-forward-count *nht-pins*) 2))
(assert-event (equal (fn-nh-forward-charge *nht-pins*) 7))
(assert-event (null (fn-bprt-table *nht-cfg*)))
(assert-event (equal (fn-nh-forward-count (fn-nh-forward-pins *nht-s*)) 0))
; Exhaustion is the codec ceiling, not the profile's budget.
(assert-event (fn-nh-exhaustedp (list 4294967295 4294967295 0 1 0 1)))
(assert-event (not (fn-nh-exhaustedp (list 4294967294 4294967295 0 1 0 1))))
(assert-event (not (fn-nh-space-pressedp (list 4294967295 4294967295 0 1 0 1) 10)))
(assert-event (fn-nh-space-pressedp (list 4294967294 4294967295 0 1 0 1) 10))

; ---------------------------------------------------------------------------
; The exit code and the report's first line.

(defun nht-dev-report ()
  (declare (xargs :verify-guards nil))
  (fn-nh-offline-report *nht-profile* *nht-s* *nht-cfg* 10))
(assert-event (equal (fn-nh-report-exit (nht-dev-report)) 22))
(assert-event
 (equal (take 40 (nht-dev-report))
        (fn-record-string-octets "health exit=22 state=unqualified-profile")))
(assert-event (equal (fn-nh-report-exit (fn-nh-fenced-report :store-held)) 20))
(assert-event (equal (fn-nh-code-state 20) :fenced))
(assert-event
 (equal (fn-nh-report-exit
         (fn-nh-render (fn-nh-verdict nil (nht-store *nht-scale*) 0 *nht-feeds* '(:clear) nil)))
        25))
(assert-event
 (equal (fn-nh-report-exit
         (fn-nh-render (fn-nh-verdict nil (nht-store *nht-scale*) 0 *nht-idle-feeds* '(:clear) nil)))
        0))
(assert-event
 (equal (fn-nh-report-exit
         (fn-nh-render (fn-nh-verdict nil (nht-store *nht-scale*) 0 :unobserved :unobserved :unobserved)))
        19))

; fn-nh-report-exit-of-render without (<= (len v) 9): 81 outcomes, the last
; held, code 100, printed as two digits "00" and read back as 0.
(defconst *nht-long* (append (make-list 80 :initial-element '(:clear)) '((:held))))
(assert-event (equal (fn-nh-exit-code *nht-long*) 100))
(assert-event (equal (fn-nh-report-exit (fn-nh-render *nht-long*)) 0))
(must-fail-checked
 (defthm nht-report-exit-of-any-render
   (equal (fn-nh-report-exit (fn-nh-render v)) (fn-nh-exit-code v))
   :rule-classes nil))

; ---------------------------------------------------------------------------
; fn-nh-first-held-monotone, each hypothesis.
(defconst *nht-v* '((:clear) (:clear) (:held) (:clear)))
(defconst *nht-w* '((:clear) (:held) (:held) (:clear)))
(assert-event (fn-nh-held-covers *nht-v* *nht-w*))
(assert-event (equal (fn-nh-first-held-index *nht-v* 0) 2))
(assert-event (equal (fn-nh-first-held-index *nht-w* 0) 1))
; Without covers: W holds nothing V holds.
(assert-event (not (fn-nh-held-covers *nht-v* '((:clear) (:clear) (:clear) (:clear)))))
(assert-event (null (fn-nh-first-held-index '((:clear) (:clear) (:clear) (:clear)) 0)))
(must-fail-checked
 (defthm nht-monotone-without-covers
   (implies (and (natp i) (fn-nh-first-held-index v i))
            (fn-nh-first-held-index w i))
   :rule-classes nil))
; Without a held state in V: both hold nothing.
(assert-event (fn-nh-held-covers '((:clear)) '((:clear))))
(must-fail-checked
 (defthm nht-monotone-without-held
   (implies (and (fn-nh-held-covers v w) (natp i))
            (fn-nh-first-held-index w i))
   :rule-classes nil))

; ---------------------------------------------------------------------------
; fn-nh-pressedp-monotone, each hypothesis.
(assert-event (fn-nh-pressedp 95 100 10))
(assert-event (fn-nh-pressedp 96 100 20))
(assert-event (not (fn-nh-pressedp 50 100 10)))  ; less use: clear
(assert-event (not (fn-nh-pressedp 95 100 1)))   ; lower threshold: clear
(assert-event (not (fn-nh-pressedp 0 100 0)))    ; no premise: clear
(must-fail-checked
 (defthm nht-pressure-without-more-use
   (implies (and (fn-nh-pressedp used bound min) (<= (nfix min) (nfix min2)))
            (fn-nh-pressedp used2 bound min2))
   :rule-classes nil))
(must-fail-checked
 (defthm nht-pressure-without-higher-threshold
   (implies (and (fn-nh-pressedp used bound min) (<= (nfix used) (nfix used2)))
            (fn-nh-pressedp used2 bound min2))
   :rule-classes nil))
(must-fail-checked
 (defthm nht-pressure-without-pressure
   (implies (and (<= (nfix used) (nfix used2)) (<= (nfix min) (nfix min2)))
            (fn-nh-pressedp used2 bound min2))
   :rule-classes nil))

; ---------------------------------------------------------------------------
; fn-nh-live-report-is-the-store-report: the instance, and a stale sum.
(assert-event (fn-sbud-octets-cache-validp (nht-cache)
                                           (fn-sf-records (fn-sn-files *nht-s*))))
(assert-event
 (equal (fn-nh-live-report *nht-profile* *nht-oc* (nht-cache) 10 '(:clear) nil)
        (fn-nh-render (fn-nh-verdict nil (nht-store *nht-profile*) 10
                                     (fn-own-feeds (fn-ocfg-owner *nht-oc*)) '(:clear) nil))))
; A stale sum of 5 octets too many changes the history-octets figure the
; held pressure line prints (min 100: every figure with a bound is pressed).
(assert-event (not (fn-sbud-octets-cache-validp
                    (nht-stale) (fn-sf-records (fn-sn-files *nht-s*)))))
(assert-event
 (not (equal (fn-nh-live-report *nht-profile* *nht-oc* (nht-stale) 100 '(:clear) nil)
             (fn-nh-render (fn-nh-verdict nil (nht-store *nht-profile*) 100
                                          (fn-own-feeds (fn-ocfg-owner *nht-oc*)) '(:clear) nil)))))
(must-fail-checked
 (defthm nht-live-is-store-report-without-a-valid-sum
   (equal (fn-nh-live-report *nht-profile* *nht-oc* (nht-stale) 100 '(:clear) nil)
          (fn-nh-render (fn-nh-verdict nil (nht-store *nht-profile*) 100
                                       (fn-own-feeds (fn-ocfg-owner *nht-oc*)) '(:clear) nil)))
   :rule-classes nil
   ;; The keystone's own hints; the assertion above evaluates both sides.
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-sbud-bytes-used-is-kernel-sum
                             (s *nht-s*) (cache (nht-stale))))
            :in-theory '(fn-nh-live-report nht-store)))))

; ---------------------------------------------------------------------------
; fn-nh-fence-of-route: an answered owner is never fenced by its route; the
; hypothesis matters (an uncertain route is fenced whatever the lock says).
(assert-event (equal (fn-nh-fence-of :offline :free nil t) nil))
(assert-event (equal (fn-nh-fence-of :offline :held nil nil) :store-held))
(assert-event (equal (fn-nh-fence-of :offline :unknown nil t) :store-held))
(assert-event (equal (fn-nh-fence-of :offline :free t t) :clone-fence))
(assert-event (equal (fn-nh-fence-of :uncertain :free nil t) :owner-unanswering))
(must-fail-checked
 (defthm nht-fence-without-route
   (equal (fn-nh-fence-of route lock clone listener)
          (cond (clone :clone-fence)
                ((and (equal lock :held) listener) :starting)
                ((member-equal lock '(:held :unknown)) :store-held)
                (t nil)))
   :rule-classes nil))

; ---------------------------------------------------------------------------
; fn-nh-fence-of-starting-iff (PKT-283).  Positive: a held lock where an owner
; would listen, nothing answering and no clone fence: :starting, and the
; report's first line says so with the fenced code.
(assert-event (equal (fn-nh-fence-of :offline :held nil t) :starting))
(assert-event (fn-nh-fence-reasonp :starting))
(defconst *nht-starting* (fn-nh-fenced-report :starting))
(assert-event (equal (fn-nh-report-exit *nht-starting*) 20))
(assert-event
 (equal (take (len (fn-record-string-octets "health exit=20 state=fenced reason=starting"))
              *nht-starting*)
        (fn-record-string-octets "health exit=20 state=fenced reason=starting")))
; The free and absent arms: never fenced.
(assert-event (null (fn-nh-fence-of :offline :absent nil t)))
; Without no-clone: a clone fence wins over a held lock.
(assert-event (equal (fn-nh-fence-of :offline :held t t) :clone-fence))
(must-fail-checked
 (defthm nht-starting-without-no-clone
   (implies (not (equal route :uncertain))
            (iff (equal (fn-nh-fence-of route lock clone listener) :starting)
                 (and (equal lock :held) listener)))
   :rule-classes nil))
; Without a route that missed the owner: an uncertain route is unanswering.
(assert-event (equal (fn-nh-fence-of :uncertain :held nil t) :owner-unanswering))
(must-fail-checked
 (defthm nht-starting-without-route
   (implies (not clone)
            (iff (equal (fn-nh-fence-of route lock clone listener) :starting)
                 (and (equal lock :held) listener)))
   :rule-classes nil))
; The conclusion fails for a held lock with no listener to expect.
(assert-event (not (equal (fn-nh-fence-of :offline :held nil nil) :starting)))

; ---------------------------------------------------------------------------
; fn-nh-starting-clears-on-listening (PKT-454).  Positive, the whole antecedent
; of the iff: no clone fence, the lock held, a listener expected, the socket
; node present and the connect failing before submission (route :offline):
; fenced :starting.  The same lock, fence and listener with the owner
; answering: its octets, no fence.
(assert-event (equal (fn-nls-route t :before-submission) :offline))
(assert-event (equal (fn-nh-health-step t :before-submission :held nil t)
                     '(:fenced :starting)))
(assert-event (equal (fn-nh-health-step nil :none :held nil t) '(:fenced :starting)))
(assert-event (equal (fn-nh-health-step t '(:done (104 101)) :held nil t)
                     '(:answered (104 101))))
; Each conjunct of the iff's right side, failed alone, loses :starting.
(assert-event (equal (fn-nh-health-step t :before-submission :held t t) '(:fenced :clone-fence)))
; A free lock where an owner would listen is not :starting: the node is not
; running (friend-path-2).
(assert-event (equal (fn-nh-health-step t :before-submission :free nil t) '(:not-running)))
(assert-event (equal (fn-nh-health-step t :before-submission :held nil nil) '(:fenced :store-held)))
(assert-event (equal (fn-nh-health-step t :after-submission :held nil t) '(:fenced :owner-unanswering)))
(assert-event (equal (fn-nh-health-step t :refused :held nil t) '(:refused)))
; The second conjunct's hypothesis: with no socket node a (:done ...) outcome
; is not an answer (the host never produces one; ACL2 does not trust it).
(assert-event (equal (fn-nh-health-step nil '(:done (104 101)) :held nil t)
                     '(:fenced :starting)))
(must-fail-checked
 (defthm nht-clears-without-socket-present
   (equal (fn-nh-health-step sp (list :done octets) lock clone listener)
          (list :answered octets))
   :hints (("Goal" :in-theory (enable fn-nh-health-step fn-nh-answeredp
                                      fn-nh-fence-of fn-nls-route)))
   :rule-classes nil))
; The iff without its route conjunct fails (an uncertain route is unanswering).
(must-fail-checked
 (defthm nht-starting-step-without-route
   (iff (equal (fn-nh-health-step sp outcome lock clone listener) '(:fenced :starting))
        (and (not clone) (equal lock :held) listener))
   :hints (("Goal" :in-theory (enable fn-nh-health-step fn-nh-answeredp
                                      fn-nh-fence-of fn-nls-route)))
   :rule-classes nil))

; ---------------------------------------------------------------------------
; fn-nh-exit-code-is-zero-or-past-the-outcome-codes (PKT-329): no hypothesis;
; the witnesses: a held verdict (a nonzero code that is no outcome code), an
; all-clear one (0, the code of :accepted), one unobserved (19).
(defconst *nht-held-3* '((:clear) (:clear) (:clear) (:held) (:clear) (:clear) (:clear) (:clear)))
(assert-event (equal (fn-nh-exit-code *nht-held-3*) 23))
(assert-event (not (fn-outcome-codep 23)))
(assert-event (equal (fn-nh-exit-code (make-list 8 :initial-element '(:clear))) 0))
(assert-event (fn-outcome-codep 0))
(assert-event (equal (fn-nh-exit-code '((:clear) (:unobserved))) 19))
(assert-event (not (fn-outcome-codep 19)))
; The conclusion's teeth: the seven outcome codes are 0..7 less 2, so a
; scale starting below 8 would overlap (the keystone reads the table).
(assert-event (fn-outcome-codep 7))
(assert-event (equal (fn-outcome-code :accepted) 0))
; fn-nh-exit-code-cases without (<= (len v) 9): *nht-long* above has code 100.
(must-fail-checked
 (defthm nht-exit-code-cases-without-len
   (member-equal (fn-nh-exit-code v) '(0 19 20 21 22 23 24 25 26 27 28))
   :rule-classes nil))

; PKT-220 (PRF-185) fn-nls-obligations-figures-are-the-retention-figures: a
; reachable owner with one retention pin and a reserved charge of 2; the
; offline verb's figures and the live report's first line agree.
(assert-event (equal (fn-rtf-pin-count *nht-s*) 1))
(assert-event (equal (fn-rtf-reserved *nht-s*) 2))
(assert-event
 (equal (take 25 (in-arena-fn-nls-live-report *sr-arena* :obligations *nht-profile* *nht-oc* (nht-cache) *nht-obs*))
        (fn-record-string-octets "obligations=1 reserved=2
")))

; ---------------------------------------------------------------------------
; PKT-508 (PRF-187): the log-sink line after the nine states.
(defconst *nht-sink* (list 40 1 2 3 6))
(assert-event (fn-log-sink-okp *nht-sink* (fn-log-sink-pending-bound)))
(assert-event
 (equal (fn-nh-log-sink-line *nht-sink*)
        (fn-record-string-octets "log-sink pending=1 dropped=2 written=3
")))
; fn-nh-report-exit-of-render-and-more, the reachable witness: a held
; unavailable-peer (exit 26) followed by the log-sink line.
(defconst *nht-v26* '((:clear) (:clear) (:clear) (:clear) (:clear) (:clear) (:held) (:clear)))
(assert-event (equal (fn-nh-exit-code *nht-v26*) 26))
(assert-event (true-listp (fn-nh-log-sink-line *nht-sink*)))
(assert-event
 (equal (fn-nh-report-exit (append (fn-nh-render *nht-v26*) (fn-nh-log-sink-line *nht-sink*)))
        26))
; Without (<= (len v) 9): *nht-long* reads 0 however it is followed.
(assert-event
 (equal (fn-nh-report-exit (append (fn-nh-render *nht-long*) (fn-nh-log-sink-line *nht-sink*)))
        0))
(must-fail-checked
 (defthm nht-render-and-more-without-length
   (implies (and (equal v *nht-long*) (equal more (fn-nh-log-sink-line *nht-sink*))
                 (true-listp more))
            (equal (fn-nh-report-exit (append (fn-nh-render v) more)) (fn-nh-exit-code v)))
   :rule-classes nil))
; Without (true-listp more): an improper tail makes the page malformed.
(assert-event (equal (fn-nh-report-exit (append (fn-nh-render *nht-v26*) 7)) :malformed))
(must-fail-checked
 (defthm nht-render-and-more-without-true-list
   (implies (and (equal v *nht-v26*) (equal more 7) (<= (len v) 9))
            (equal (fn-nh-report-exit (append (fn-nh-render v) more)) (fn-nh-exit-code v)))
   :rule-classes nil))

; ---------------------------------------------------------------------------
; friend-path-2: the node that is not running.
;
; fn-nh-not-running-exactly-when-nothing-runs.  Positive, the whole right side:
; no clone fence, a listener expected, the lock free (and absent), the route
; :offline (no socket node, or a stale one refusing the connect): not running.
(assert-event (equal (fn-nls-route nil :none) :offline))
(assert-event (equal (fn-nh-health-step nil :none :free nil t) '(:not-running)))
(assert-event (equal (fn-nh-health-step nil :none :absent nil t) '(:not-running)))
(assert-event (equal (fn-nh-health-step t :before-submission :free nil t) '(:not-running)))
; Each conjunct failed alone loses it: a clone fence, no listener expected, the
; lock held or unreadable, a route that is not :offline, an owner answering.
(assert-event (equal (fn-nh-health-step nil :none :free t t) '(:fenced :clone-fence)))
(assert-event (equal (fn-nh-health-step nil :none :free nil nil) '(:offline)))
(assert-event (equal (fn-nh-health-step nil :none :held nil t) '(:fenced :starting)))
(assert-event (equal (fn-nh-health-step nil :none :unknown nil t) '(:fenced :store-held)))
(assert-event (equal (fn-nh-health-step t :after-submission :free nil t)
                     '(:fenced :owner-unanswering)))
(assert-event (equal (fn-nh-health-step t '(:done (104 101)) :free nil t)
                     '(:answered (104 101))))
; The iff without its lock conjunct fails (a held lock is starting, not down).
(must-fail-checked
 (defthm nht-not-running-without-lock
   (iff (equal (fn-nh-health-step sp outcome lock clone listener) '(:not-running))
        (and (not clone) listener (equal (fn-nls-route sp outcome) :offline)))
   :hints (("Goal" :in-theory (enable fn-nh-health-step fn-nh-answeredp
                                      fn-nh-fence-of fn-nls-route)))
   :rule-classes nil))

; fn-nh-not-running-report-exit: the report over the witness store opens
; `health exit=18 state=not-running', says why, and its exit is 18.
(defconst *nht-stop-reason*
  (fn-record-string-octets "owner core/store fault; process stopped: feed connection/reply authorized an empty command"))
(defconst *nht-log*
  (append (fn-record-string-octets "accepted reader connection=1") (list 10)
          (fn-nh-run-started-line) (list 10)
          (fn-record-string-octets "LISTENING 119") (list 10)
          (fn-nh-run-stopped-line 4 *nht-stop-reason*) (list 10)))
(defconst *nht-last* (fn-nh-last-run *nht-log*))
(defconst *nht-down*
  (fn-nh-not-running-report *nht-profile* *nht-s* *nht-cfg* 10 *nht-last*))
(assert-event (equal (fn-nh-report-exit *nht-down*) 18))
(defconst *nht-down-head*
  (fn-record-string-octets
   "health exit=18 state=not-running (no process holds the store and nothing answers on its control socket: the node is not running)"))
(assert-event (equal (take (len *nht-down-head*) *nht-down*) *nht-down-head*))
(assert-event
 (equal *nht-last*
        (cons :stopped
              (fn-record-string-octets
               "exit=04 reason=owner core/store fault; process stopped: feed connection/reply authorized an empty command"))))
(assert-event
 (equal (fn-nh-last-run-words *nht-last*)
        (append (fn-record-string-octets
                 "last-stop exit=04 reason=owner core/store fault; process stopped: feed connection/reply authorized an empty command")
                (list 10))))
; The last run line wins: a start after the stop is a run with no stop line
; (killed); a log with no run line is unrecorded; a line that only contains
; the words is not one.
(assert-event (equal (fn-nh-last-run (append *nht-log* (fn-nh-run-started-line) (list 10)))
                     '(:started)))
; `run opened ms=N' (the start's measured length, host/native/owner.lisp) is
; a line of its own that renders the count; the scan passes it over, so a
; run whose last line is it is still :started (killed, not stopped).
(assert-event (equal (fn-nh-run-opened-line 2140)
                     (fn-record-string-octets "run opened ms=2140")))
(assert-event (equal (fn-nh-last-run (append *nht-log* (fn-nh-run-started-line) (list 10)
                                             (fn-nh-run-opened-line 2140) (list 10)))
                     '(:started)))
(assert-event (equal (fn-nh-last-run (fn-record-string-octets "LISTENING 119\n")) nil))
(assert-event (equal (fn-nh-last-run nil) nil))
(assert-event (equal (fn-nh-last-run (fn-record-string-octets "x run stopped exit=04\n")) nil))
; A stop line cut short at the tail's end (no final LF) is still read.
(assert-event (equal (car (fn-nh-last-run (fn-nh-run-stopped-line 0 nil))) :stopped))
; A reason is one clean line: a newline and a control octet become spaces,
; a non-ASCII octet a `?', and it is bounded.
(assert-event (equal (fn-nh-run-stopped-line 4 (list 97 10 98 7 200))
                     (fn-record-string-octets "run stopped exit=04 reason=a b ?")))
(assert-event (equal (len (fn-nh-run-stopped-line 4 (make-list 5000 :initial-element 97)))
                     (+ 12 7 8 *fn-nh-reason-max-octets*)))
; status's first lines when nothing runs.
(assert-event (equal (take 11 (fn-nh-not-running-lines *nht-last*))
                     (fn-record-string-octets "not-running")))

;; PRF-335: fn-nh-feed-queue-full-intent-is-held, over the owner.  owner-tests'
;; control submission targets peer "out" (max-queue 1); with its feed holding
;; another undelivered article the intent is :capacity, POST answers the
;; named feed-queue-full, and health holds unavailable-peer.
(defconst *nht-own-full*
  (fn-own-with-feeds *own-control-fed-taken*
                     (fn-own-feed-put "out" *own-out-peer-record* *own-full-feed*
                                      (fn-own-feeds *own-control-fed-taken*))))
(assert-event (fn-own-feed-tablep (fn-own-feeds *nht-own-full*)))
(assert-event (equal (fn-own-submission-intent-result
                      *nht-own-full* *own-control-evidence* 1 3)
                     :capacity))
(assert-event (equal (fn-own-intent-refusal-word :capacity) :feed-queue-full))
(assert-event (equal (fn-post-store-refusal-line (fn-own-intent-refusal-word :capacity))
                     "441 posting failed; a peer's outbound feed queue is full, nothing was stored (feed-queue-full); the peer is behind, and the node's operator sees which one in health"))
(assert-event (equal (car (fn-nh-nth 6 (fn-nh-verdict nil (nht-store *nht-scale*) 0
                                                      (fn-own-feeds *nht-own-full*) '(:clear) nil)))
                     :held))
;; Without the :capacity intent: the same owner before the other article,
;; intent :ready, and its feed table is clear.
(assert-event (fn-own-feed-tablep (fn-own-feeds *own-control-fed-taken*)))
(assert-event (equal (fn-own-submission-intent-result
                      *own-control-fed-taken* *own-control-evidence* 1 3)
                     :ready))
(assert-event (equal (car (fn-nh-nth 6 (fn-nh-verdict nil (nht-store *nht-scale*) 0
                                                      (fn-own-feeds *own-control-fed-taken*) '(:clear) nil)))
                     :clear))
;; Any other non-ready intent keeps the bare refusal.
(assert-event (equal (fn-own-intent-refusal-word :refused) :refused))
(assert-event (equal (fn-own-intent-refusal-word :absent) :refused))

; ---------------------------------------------------------------------------
; PRF-358 (PKT-879): the ninth state, the disk.  KEYSTONE
; fn-nh-held-disk-is-never-healthy.  Reached: the scale store with idle feeds
; (every other state clear) and the owner's disk outcome held (a stalled
; barrier, as books/owner-time-model.lisp fn-otm-health-disk renders it):
; exit 28, the line names the mode.
(defconst *nht-disk-held*
  (cons :held (fn-record-string-octets " mode=stalled pending-ms=61557 stall-ms=30000 members=uncertain posts=try-later")))
(assert-event
 (equal (nht-states (fn-nh-verdict nil (nht-store *nht-scale*) 0 *nht-idle-feeds* *nht-disk-held* nil))
        '(:clear :clear :clear :clear :clear :clear :clear :clear :held :clear)))
(assert-event
 (equal (fn-nh-report-exit
         (fn-nh-render (fn-nh-verdict nil (nht-store *nht-scale*) 0 *nht-idle-feeds* *nht-disk-held* nil)))
        28))
(assert-event (equal (fn-nh-code-state 28) :disk))
(assert-event
 (equal (take 25 (fn-nh-render (fn-nh-verdict nil (nht-store *nht-scale*) 0 *nht-idle-feeds*
                                              *nht-disk-held* nil)))
        (fn-record-string-octets "health exit=28 state=disk")))
; With an earlier state held (unavailable-peer), the code is that state's,
; still never 0: the ninth state does not mask the others.
(assert-event
 (equal (fn-nh-exit-code (fn-nh-verdict nil (nht-store *nht-scale*) 0 *nht-full-feeds* *nht-disk-held* nil))
        26))
; Tooth (the held hypothesis): the same node with the disk clear is healthy.
(assert-event
 (equal (fn-nh-exit-code (fn-nh-verdict nil (nht-store *nht-scale*) 0 *nht-idle-feeds* '(:clear) nil))
        0))
(must-fail-checked
 (defthm nht-disk-never-healthy-without-held
   (implies (consp disk)
            (<= 20 (fn-nh-exit-code (fn-nh-verdict fence store min feeds disk ckpt))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t :in-theory (disable fn-nh-verdict fn-nh-exit-code)))))
; Offline the disk is unobserved (19 with nothing held), never clear.
(assert-event
 (equal (car (fn-nh-nth 8 (fn-nh-verdict nil (nht-store *nht-scale*) 0 :unobserved :unobserved :unobserved)))
        :unobserved))

; fn-nh-deferred-checkpoint-is-never-healthy (PKT-542).  Reached: the scale
; store with idle feeds and a clear disk (the first nine states clear) and
; the owner's deferred publication as books/owner-checkpoint-pipeline.lisp
; fn-ockp-decide answers it: the antecedent holds, the tenth state is held,
; exit 29, and the line names the reason and the two figures.
(defconst *nht-ckpt-deferred* '(:deferred :exceeds-budget 70000 65536))
(assert-event (fn-nh-checkpoint-deferredp *nht-ckpt-deferred*))
(assert-event
 (equal (nht-states (fn-nh-verdict nil (nht-store *nht-scale*) 0 *nht-idle-feeds* '(:clear)
                                   *nht-ckpt-deferred*))
        '(:clear :clear :clear :clear :clear :clear :clear :clear :clear :held)))
(assert-event
 (let ((v (fn-nh-verdict nil (nht-store *nht-scale*) 0 *nht-idle-feeds* '(:clear) *nht-ckpt-deferred*)))
   (and (equal (fn-nh-exit-code v) 29)
        (<= 20 (fn-nh-exit-code v))
        (not (fn-nh-first-held-index (take 9 v) 0))
        (equal (fn-nh-report-exit (fn-nh-render v)) 29)
        (equal (cdr (fn-nh-nth 9 v))
               (fn-record-string-octets " reason=exceeds-budget estimate=70000 budget=65536")))))
(assert-event (equal (fn-nh-code-state 29) :checkpoint-deferred))
; The host-called path: the owner's observation carries the deferral as its
; sixth element (host/native-live-status-host.lisp appends
; fn-owner-sco-deferred to fnn-store-observation's five), which
; fn-nh-answer-report and its column twin hand to fn-nh-live-report.
(assert-event
 (equal (fn-nls-obs-checkpoint-deferred (list nil nil nil nil nil *nht-ckpt-deferred*))
        *nht-ckpt-deferred*))
(assert-event
 (equal (fn-nh-report-exit
         (fn-nh-live-report *nht-profile* *nht-oc* (nht-cache) 0 '(:clear) *nht-ckpt-deferred*))
        (fn-nh-exit-code (fn-nh-verdict nil (nht-store *nht-profile*) 0
                                        (fn-own-feeds (fn-ocfg-owner *nht-oc*)) '(:clear)
                                        *nht-ckpt-deferred*))))
; With an earlier state held (the disk), the code is that state's: the
; tenth state does not mask the others, and the conclusion's iff is false.
(assert-event
 (let ((v (fn-nh-verdict nil (nht-store *nht-scale*) 0 *nht-idle-feeds* *nht-disk-held* *nht-ckpt-deferred*)))
   (and (equal (fn-nh-exit-code v) 28)
        (fn-nh-first-held-index (take 9 v) 0))))
; Tooth (the deferred hypothesis): nothing deferred (nil, as the observation
; carries it) is healthy, and the conclusion fails.
(assert-event (not (fn-nh-checkpoint-deferredp nil)))
(assert-event
 (equal (fn-nh-exit-code (fn-nh-verdict nil (nht-store *nht-scale*) 0 *nht-idle-feeds* '(:clear) nil))
        0))
(must-fail-checked
 (defthm nht-checkpoint-never-healthy-without-deferred
   (implies (consp ckpt)
            (<= 20 (fn-nh-exit-code (fn-nh-verdict fence store min feeds disk ckpt))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t :in-theory (disable fn-nh-verdict fn-nh-exit-code)))))
; Offline the publisher is unobserved, never clear.
(assert-event
 (equal (car (fn-nh-nth 9 (fn-nh-verdict nil (nht-store *nht-scale*) 0 :unobserved :unobserved :unobserved)))
        :unobserved))
