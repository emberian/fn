; Teeth for books/native-health (PRF-112): the health verdict's eight states,
; its exit code and the owner's report.  The owner state is
; native-live-status-tests' host-shaped one: one committed article, one
; retention pin, the development profile.
(in-package "ACL2")
(include-book "../../books/native-health")
(include-book "../../books/owner-store-budget")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

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
(defconst *nht-first*
  (fn-record-make 0 0 0 "<nht-first@example.invalid>" '(65 66)
                  *nht-groups* "nht-pin-1" "nht-subject-1"
                  "nht-release-1" 2 841000000))
(defun nht-run (oc events)
  (declare (xargs :guard (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
                  :verify-guards nil))
  (if (consp events)
      (nht-run (fn-ocfg-step oc (car events)) (cdr events))
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
(defconst *nht-oc*
  (fn-ocfg-step
   (nht-run (fn-opc-prepare (nht-run *nht-0* *nht-reserve-events*) *nht-first*)
             '((:store (:io :record-file :ok))
               (:store (:io :record-link :ok))
               (:store (:io :record-directory :ok))))
   '(:complete)))
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

; ---------------------------------------------------------------------------
; A feed table: peer "down" has a queued article and no connection
; (unavailable); peer "gave-up" dropped one at its retry bound (stranded).
(defconst *nht-feeds*
  (list (fn-own-feed-entry "down" nil
                           (fn-feed-make '(100 111 119 110) nil
                                         (list (fn-feed-entry '(60 97 62) :queued 1 0))
                                         nil 0 nil 0))
        (fn-own-feed-entry "gave-up" nil
                           (fn-feed-make '(103) nil
                                         (list (fn-feed-entry '(60 98 62) '(:dropped :retry-bound) 3 0))
                                         nil 0 7 0))))
(defconst *nht-idle-feeds*
  (list (fn-own-feed-entry "up" nil
                           (fn-feed-make '(117 112) nil
                                         (list (fn-feed-entry '(60 99 62) :done 1 0))
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
 (equal (nht-states (fn-nh-verdict nil (nht-store *nht-profile*) 10 :unobserved))
        '(:clear :clear :held :clear :clear :unobserved :unobserved :clear)))
; At min 100 every figure with a positive bound is under pressure.
(assert-event
 (equal (nht-states (fn-nh-verdict nil (nht-store *nht-scale*) 100 *nht-idle-feeds*))
        '(:clear :clear :clear :held :clear :clear :clear :clear)))
; The owner's feed table: stranded and unavailable held, each its own line.
(assert-event
 (equal (nht-states (fn-nh-verdict nil (nht-store *nht-scale*) 0 *nht-feeds*))
        '(:clear :clear :clear :clear :clear :held :held :clear)))
(assert-event (equal (fn-nh-stranded-peers *nht-feeds*) '("gave-up")))
(assert-event (equal (fn-nh-unavailable-peers *nht-feeds*) '("down")))
(assert-event (null (fn-nh-unavailable-peers *nht-idle-feeds*)))
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
         (fn-nh-render (fn-nh-verdict nil (nht-store *nht-scale*) 0 *nht-feeds*)))
        25))
(assert-event
 (equal (fn-nh-report-exit
         (fn-nh-render (fn-nh-verdict nil (nht-store *nht-scale*) 0 *nht-idle-feeds*)))
        0))
(assert-event
 (equal (fn-nh-report-exit
         (fn-nh-render (fn-nh-verdict nil (nht-store *nht-scale*) 0 :unobserved)))
        19))

; fn-nh-report-exit-of-render without (<= (len v) 8): 81 outcomes, the last
; held, code 100, printed as two digits "00" and read back as 0.
(defconst *nht-long* (append (make-list 80 :initial-element '(:clear)) '((:held))))
(assert-event (equal (fn-nh-exit-code *nht-long*) 100))
(assert-event (equal (fn-nh-report-exit (fn-nh-render *nht-long*)) 0))
(must-fail
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
(must-fail
 (defthm nht-monotone-without-covers
   (implies (and (natp i) (fn-nh-first-held-index v i))
            (fn-nh-first-held-index w i))
   :rule-classes nil))
; Without a held state in V: both hold nothing.
(assert-event (fn-nh-held-covers '((:clear)) '((:clear))))
(must-fail
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
(must-fail
 (defthm nht-pressure-without-more-use
   (implies (and (fn-nh-pressedp used bound min) (<= (nfix min) (nfix min2)))
            (fn-nh-pressedp used2 bound min2))
   :rule-classes nil))
(must-fail
 (defthm nht-pressure-without-higher-threshold
   (implies (and (fn-nh-pressedp used bound min) (<= (nfix used) (nfix used2)))
            (fn-nh-pressedp used2 bound min2))
   :rule-classes nil))
(must-fail
 (defthm nht-pressure-without-pressure
   (implies (and (<= (nfix used) (nfix used2)) (<= (nfix min) (nfix min2)))
            (fn-nh-pressedp used2 bound min2))
   :rule-classes nil))

; ---------------------------------------------------------------------------
; fn-nh-live-report-is-the-store-report: the instance, and a stale sum.
(assert-event (fn-sbud-octets-cache-validp (nht-cache)
                                           (fn-sf-records (fn-sn-files *nht-s*))))
(assert-event
 (equal (fn-nh-live-report *nht-profile* *nht-oc* (nht-cache) 10)
        (fn-nh-render (fn-nh-verdict nil (nht-store *nht-profile*) 10
                                     (fn-own-feeds (fn-ocfg-owner *nht-oc*))))))
; A stale sum of 5 octets too many changes the history-octets figure the
; held pressure line prints (min 100: every figure with a bound is pressed).
(assert-event (not (fn-sbud-octets-cache-validp
                    (nht-stale) (fn-sf-records (fn-sn-files *nht-s*)))))
(assert-event
 (not (equal (fn-nh-live-report *nht-profile* *nht-oc* (nht-stale) 100)
             (fn-nh-render (fn-nh-verdict nil (nht-store *nht-profile*) 100
                                          (fn-own-feeds (fn-ocfg-owner *nht-oc*)))))))
(must-fail
 (defthm nht-live-is-store-report-without-a-valid-sum
   (equal (fn-nh-live-report *nht-profile* *nht-oc* (nht-stale) 100)
          (fn-nh-render (fn-nh-verdict nil (nht-store *nht-profile*) 100
                                       (fn-own-feeds (fn-ocfg-owner *nht-oc*)))))
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
(must-fail
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
(must-fail
 (defthm nht-starting-without-no-clone
   (implies (not (equal route :uncertain))
            (iff (equal (fn-nh-fence-of route lock clone listener) :starting)
                 (and (equal lock :held) listener)))
   :rule-classes nil))
; Without a route that missed the owner: an uncertain route is unanswering.
(assert-event (equal (fn-nh-fence-of :uncertain :held nil t) :owner-unanswering))
(must-fail
 (defthm nht-starting-without-route
   (implies (not clone)
            (iff (equal (fn-nh-fence-of route lock clone listener) :starting)
                 (and (equal lock :held) listener)))
   :rule-classes nil))
; The conclusion fails for a held lock with no listener to expect.
(assert-event (not (equal (fn-nh-fence-of :offline :held nil nil) :starting)))

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
; fn-nh-exit-code-cases without (<= (len v) 8): *nht-long* above has code 100.
(must-fail
 (defthm nht-exit-code-cases-without-len
   (member-equal (fn-nh-exit-code v) '(0 19 20 21 22 23 24 25 26 27))
   :rule-classes nil))
