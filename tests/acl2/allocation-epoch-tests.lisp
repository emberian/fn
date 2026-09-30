(in-package "ACL2")
; Hypothesis-removal witnesses intentionally evaluate the total logical functions
; outside their executable guards. Production functions remain guard-verified.
(set-guard-checking nil)
; Synthetic internal producer fixtures establish no runtime installation.
(defconst *aec-assoc* '(:allocation-epoch-association :runtime :profile :pool 10 1000))
(defconst *aec-i* (list :allocation-epoch-installation *aec-assoc* 1000 800 2 20 20 20 50 10 20 7))
; Positive: complete antecedent and conclusion of enter preservation.
(assert-event
 (and (fn-aec-statep *aec-i* :active 3 100 20 0 nil)
  (mv-let (w m a n) (fn-aec-enter *aec-i* :active 3 100 20 0 nil nil)
   (and (equal (list w m a n) '(:prepaid :active 30 1))
        (fn-aec-statep *aec-i* m 3 100 a n nil) (<= 20 a)))))
; Hypothesis removal, statep omitted: corrupt epoch is not repaired by entry.
(assert-event
 (and (not (fn-aec-statep *aec-i* :active 1001 100 20 0 nil))
  (mv-let (w m a n) (fn-aec-enter *aec-i* :active 1001 100 20 0 nil nil)
   (declare (ignore w))
   (not (and (fn-aec-statep *aec-i* m 1001 100 a n nil) (<= 20 a))))))
; Positive body and headroom refusal keep cumulative allocation.
(assert-event
 (and (fn-aec-statep *aec-i* :active 3 100 30 1 nil)
      (not (eq :active :uninstalled))
  (mv-let (w m a) (fn-aec-body *aec-i* :active 3 100 30 1 nil 40 nil)
   (and (equal (list w m a) '(:prepaid :active 70))
        (fn-aec-statep *aec-i* m 3 100 a 1 nil) (<= 30 a)))))
(assert-event (equal (mv-list 3 (fn-aec-body *aec-i* :active 3 100 30 1 nil 240 nil))
                     '(:yield :draining 30)))
; Body hypothesis removal: uninstalled state satisfies statep, but cannot
; establish installed recovery. No allocation occurs in this invalid route.
(assert-event
 (and (fn-aec-statep nil :uninstalled 0 0 0 0 nil)
      (not (not (eq :uninstalled :uninstalled)))
  (mv-let (w m a) (fn-aec-body nil :uninstalled 0 0 0 0 nil 1 nil)
   (declare (ignore w))
   (not (and (fn-aec-statep nil m 0 0 a 0 nil) (<= 0 a))))))
(assert-event
 (and (not (fn-aec-statep *aec-i* :active 1001 100 30 1 nil))
      (not (eq :active :uninstalled))
  (mv-let (w m a) (fn-aec-body *aec-i* :active 1001 100 30 1 nil 1 nil)
   (declare (ignore w))
   (not (and (fn-aec-statep *aec-i* m 1001 100 a 1 nil) (<= 30 a))))))
; Once-only producer settlement positive and both hypothesis removals.
(assert-event
 (and (fn-aec-statep *aec-i* :draining 3 100 70 1 nil) (posp 1)
  (mv-let (w m a n) (fn-aec-leave-owned :draining 70 1)
   (and (eq w :left) (equal a 70) (equal n (- 1 1))
        (fn-aec-statep *aec-i* m 3 100 a n nil)))))
(assert-event
 (and (fn-aec-statep *aec-i* :draining 3 100 70 0 nil) (not (posp 0))
  (mv-let (w m a n) (fn-aec-leave-owned :draining 70 0)
   (not (and (eq w :left) (equal a 70) (equal n (- 0 1))
             (fn-aec-statep *aec-i* m 3 100 a n nil))))))
(assert-event
 (and (not (fn-aec-statep *aec-i* :draining 1001 100 70 1 nil)) (posp 1)
  (mv-let (w m a n) (fn-aec-leave-owned :draining 70 1)
   (not (and (eq w :left) (equal a 70) (equal n (- 1 1))
             (fn-aec-statep *aec-i* m 1001 100 a n nil))))))
; Collector cannot start with a worker present; valid prepayment and issuance.
(assert-event (equal (mv-list 3 (fn-aec-collect-prepay *aec-i* :draining 3 100 70 1 nil))
                     '(:not-quiescent :draining 70)))
(assert-event (equal (mv-list 3 (fn-aec-collect-prepay *aec-i* :draining 3 100 70 0 nil))
                     '(:issue-collection-nonce :collecting 90)))
(assert-event (equal (mv-list 3 (fn-aec-collect-issued :collecting 0 nil 42 1000))
                     '(:collect :collecting 42)))
; Reset positive asserts the complete preservation conclusion, including
; nonzero qualified suffix and new epoch. Automatic GC is not a reset input.
(assert-event
 (and (fn-aec-statep *aec-i* :collecting 3 100 90 0 42)
  (mv-let (w m e l a g)
   (fn-aec-collect-complete *aec-i* :collecting 3 100 90 0 42 *aec-assoc* 3 42 :completed 80)
   (and (member-eq w '(:resume :resource-unavailable))
        (equal (list w m e l a g) '(:resume :active 4 80 7 nil))
        (fn-aec-statep *aec-i* m e l a 0 g)
        (equal e (+ 1 3)) (equal l 80) (equal a (fn-aec-at 11 *aec-i*))))))
; Hypothesis removal: malformed immutable association can pass scalar
; completion tests internally but is never an installed state.
(defconst *aec-bad-i* '(:allocation-epoch-installation nil 1000 800 2 20 20 20 50 10 20 7))
(assert-event
 (and (not (fn-aec-statep *aec-bad-i* :collecting 3 100 90 0 42))
  (mv-let (w m e l a g)
   (fn-aec-collect-complete *aec-bad-i* :collecting 3 100 90 0 42 nil 3 42 :completed 80)
   (and (member-eq w '(:resume :resource-unavailable))
        (not (and (fn-aec-statep *aec-bad-i* m e l a 0 g)
                  (equal e (+ 1 3)) (equal l 80) (equal a (fn-aec-at 11 *aec-bad-i*))))))))
; Mutation/raw-uncertainty cases retain all accounting and identity.
(assert-event (equal (mv-list 6 (fn-aec-collect-complete *aec-i* :collecting 3 100 90 0 42 *aec-assoc* 3 41 :completed 80))
                     '(:recovery-required :recovery 3 100 90 42)))
(assert-event (equal (mv-list 6 (fn-aec-collect-complete *aec-i* :collecting 3 100 90 0 42 *aec-assoc* 3 42 :uncertain 80))
                     '(:recovery-required :recovery 3 100 90 42)))
(assert-event (equal (mv-list 6 (fn-aec-collect-complete *aec-i* :collecting 3 100 90 0 42 *aec-assoc* 3 42 :deferred 80))
                     '(:recovery-required :recovery 3 100 90 42)))
(assert-event (equal (mv-list 6 (fn-aec-collect-complete *aec-i* :collecting 3 100 90 0 42 *aec-assoc* 3 42 :completed 1001))
                     '(:recovery-required :recovery 3 100 90 42)))
(assert-event (equal (mv-list 6 (fn-aec-collect-complete *aec-i* :collecting 3 100 90 0 42 *aec-assoc* 3 42 :completed 320))
                     '(:resource-unavailable :draining 4 320 7 42)))
(assert-event (equal (mv-list 3 (fn-aec-collect-prepay *aec-i* :draining 4 320 7 0 42))
                     '(:not-quiescent :draining 7)))
(assert-event (and (fn-aec-statep *aec-i* :collecting 3 100 90 0 42)
                   (not (eq :collecting :uninstalled))
                   (fn-aec-statep *aec-i* (fn-aec-uncertain) 3 100 90 0 42)))
; Immediate-domain and reserved-headroom boundaries.
(assert-event (equal (mv-list 2 (fn-aed-add 999 1 1000)) '(:fits 1000)))
(assert-event (equal (mv-list 2 (fn-aed-add 1000 1 1000)) '(:unavailable 1000)))
(assert-event (equal (mv-list 4 (fn-aec-enter *aec-i* :active 3 100 220 0 nil nil))
                     '(:yield :draining 220 0)))
(assert-event (equal (mv-list 4 (fn-aec-enter *aec-i* :active 3 100 220 0 nil t))
                     '(:prepaid :active 230 1)))

(set-guard-checking t)

; Complete positive and state-invariant hypothesis-removal footprint teeth.
(assert-event
 (and (fn-aec-statep *aec-i* :active 3 100 20 0 nil)
      (<= (+ (* (fn-aec-at 4 *aec-i*) (+ 100 20))
             (fn-aec-at 5 *aec-i*) (fn-aec-at 6 *aec-i*) (fn-aec-at 7 *aec-i*))
          (fn-aec-at 3 *aec-i*))))
(assert-event
 (and (not (fn-aec-statep *aec-i* :active 3 100 500 0 nil))
      (not (<= (+ (* (fn-aec-at 4 *aec-i*) (+ 100 500))
                  (fn-aec-at 5 *aec-i*) (fn-aec-at 6 *aec-i*) (fn-aec-at 7 *aec-i*))
               (fn-aec-at 3 *aec-i*)))))
