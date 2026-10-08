(in-package "ACL2")
(include-book "../../books/owner-publication-composition")
(include-book "../../books/defkeystone")

(defteeth fn-opub-capture-serial-increases
  :claim (() (< (nfix (fn-opub-get :serial r)) (mv-nth 0 (fn-opub-capture r count))))
  :subject fn-opub-capture
  :witness ((r '(nil nil nil nil nil nil nil nil 7 nil)) (count 64))
  :breaks ()
  :mutations ((same-serial (:conclusion
                 (equal (mv-nth 0 (fn-opub-capture r count)) (nfix (fn-opub-get :serial r))))
               ((r '(nil nil nil nil nil nil nil nil 7 nil)) (count 64))
               :fault "retrying a count reuses the earlier capture serial")))

(defteeth fn-opub-capture-establishes-holder
  :claim (((admissible (and (natp count)
                           (or (not (fn-opub-get :pass r))
                               (equal (fn-opub-get :pass r) :dry-run)))))
          (let ((next (mv-nth 1 (fn-opub-capture r count))))
            (fn-opl-holdsp count (mv-nth 0 (fn-opub-capture r count))
                          (fn-opub-get :pass next) (fn-opub-get :inflight next)
                          (fn-opub-get :serial next))))
  :subject fn-opub-capture
  :witness ((r '(nil nil nil nil nil nil nil nil 7 nil)) (count 64))
  :breaks ((admissible ((r '(nil nil nil nil nil nil nil nil 7 :reclaim)) (count 64))))
  :mutations ((old-serial (:conclusion
                (let ((next (mv-nth 1 (fn-opub-capture r count))))
                  (fn-opl-holdsp count (fn-opub-get :serial r)
                                (fn-opub-get :pass next) (fn-opub-get :inflight next)
                                (fn-opub-get :serial next))))
               ((r '(nil nil nil nil nil nil nil nil 7 nil)) (count 64))
               :fault "capture publishes the old serial")))

(defteeth fn-opub-done-does-not-release-another-holder
  :claim (((other (or (and (fn-opub-get :pass r)
                          (not (equal (fn-opub-get :pass r) :dry-run)))
                     (not (equal (fn-opub-get :inflight r) (fn-sco-sequence next))))))
          (equal (fn-opub-get :inflight (mv-nth 1 (fn-opub-done r next payloads durablep verdict)))
                 (fn-opub-get :inflight r)))
  :subject fn-opub-done
  :witness ((r '(nil nil nil nil nil 64 nil nil 7 nil)) (next nil)
            (payloads 0) (durablep t) (verdict nil))
  :breaks ((other ((r '(nil nil nil nil nil 0 nil nil 7 nil)) (next nil)
                   (payloads 0) (durablep t) (verdict nil))))
  :mutations ((clear-foreign-slot (:conclusion
                (equal (fn-opub-get :inflight (mv-nth 1 (fn-opub-done r next payloads durablep verdict))) nil))
               ((r '(nil nil nil nil nil 64 nil nil 7 nil)) (next nil)
                (payloads 0) (durablep t) (verdict nil))
               :fault "completion clears another capture's slot")))

(defteeth fn-opub-abandoned-stale-fields-unchanged
  :claim (((stale (not (fn-opl-holdsp count serial (fn-opub-get :pass r)
                                    (fn-opub-get :inflight r) (fn-opub-get :serial r)))))
          (and (equal (mv-nth 0 (fn-opub-abandoned r count serial outcome now)) :stale)
               (equal (fn-opub-get field (mv-nth 1 (fn-opub-abandoned r count serial outcome now)))
                      (fn-opub-get field r))))
  :subject fn-opub-abandoned
  :witness ((r '(64 nil nil nil nil 64 nil nil 8 nil)) (count 64) (serial 7)
            (outcome '(:io-refusal)) (now 1000) (field :inflight))
  :breaks ((stale ((r '(64 nil nil nil nil 64 nil nil 8 nil)) (count 64) (serial 8)
                   (outcome '(:io-refusal)) (now 1000) (field :inflight))))
  :mutations ((release-newer (:conclusion
                (equal (fn-opub-get field (mv-nth 1 (fn-opub-abandoned r count serial outcome now))) nil))
               ((r '(64 nil nil nil nil 64 nil nil 8 nil)) (count 64) (serial 7)
                (outcome '(:io-refusal)) (now 1000) (field :inflight))
               :fault "late abandonment releases a retry at the same count")))

(defteeth fn-opub-install-preserves-serial
  :claim (() (equal (fn-opub-get :serial (fn-opub-install r base)) (fn-opub-get :serial r)))
  :subject fn-opub-install
  :witness ((r '(64 old 2 deferred 60 64 t t 7 :reclaim)) (base 'recovered))
  :breaks ()
  :mutations ((reset-serial (:conclusion
                (equal (fn-opub-get :serial (fn-opub-install r base)) nil))
               ((r '(64 old 2 deferred 60 64 t t 7 :reclaim)) (base 'recovered))
               :fault "install resets a serial the old installer preserved")))

(assert-event (equal (fn-opub-install '(64 old 2 deferred 60 64 t t 7 :reclaim) 'recovered)
                     '(nil recovered nil nil nil nil nil nil 7 nil)))
(assert-event (equal (fn-opub-reclaim-install '(64 old 2 deferred 60 64 t t 7 :reclaim) 'rebuilt 80)
                     '(80 rebuilt nil nil 80 nil t t 7 nil)))
(defteeth fn-opub-due-composition-by-definition
  :claim (() (let ((word (fn-ock-requested-next
        (fn-opub-get :durable r) count suffix
        (fn-opl-attempted (fn-opub-get :deferred r) (fn-opub-get :attempted r) count now)
        (fn-opub-get :inflight r)
        (fn-opl-blockedp (fn-opub-get :deferred r) budget space count now)
        (fn-opub-get :requested r))))
    (and (equal (mv-nth 0 (fn-opub-due r profile count suffix budget space now)) (if profile (if (equal word :coalesce) :inflight word) :idle))
         (equal (fn-opub-observe (mv-nth 1 (fn-opub-due r profile count suffix budget space now)))
                (if (not profile) (fn-opub-observe r)
          (cond ((equal word :coalesce) (list (fn-opub-get :attempted r) (fn-opub-get :base r) (fn-opub-get :base-payloads r) (fn-opub-get :deferred r) (fn-opub-get :durable r) (fn-opub-get :inflight r) t (fn-opub-get :requested r) (fn-opub-get :serial r) (fn-opub-get :pass r)))
                ((equal word :inflight) (fn-opub-observe r))
                ((equal word :due) (list (fn-opub-get :attempted r) (fn-opub-get :base r) (fn-opub-get :base-payloads r) (fn-opub-get :deferred r) (fn-opub-get :durable r) (fn-opub-get :inflight r) nil (fn-opub-get :requested r) (fn-opub-get :serial r) (fn-opub-get :pass r)))
                (t (list (fn-opub-get :attempted r) (fn-opub-get :base r) (fn-opub-get :base-payloads r) (fn-opub-get :deferred r) (fn-opub-get :durable r) (fn-opub-get :inflight r) nil nil (fn-opub-get :serial r) (fn-opub-get :pass r)))))))))
  :subject fn-opub-due
  :witness ((r '(64 base 5 nil 32 64 nil nil 8 nil)) (profile t) (count 128) (suffix 128) (budget 1000) (space 1000) (now 2000))
  :breaks ()
  :mutations ((duplicate-capture (:conclusion
                (equal (mv-nth 0 (fn-opub-due r profile count suffix budget space now)) :due))
               ((r '(64 base 5 nil 32 64 nil nil 8 nil)) (profile t) (count 128) (suffix 128) (budget 1000) (space 1000) (now 2000))
               :fault "a decision starts a second publication while one holds the slot")))

(defteeth fn-opub-request-composition-by-definition
  :claim (() (let ((word (fn-ock-request-word
        (fn-opub-get :durable r) count
        (fn-opl-attempted (fn-opub-get :deferred r) (fn-opub-get :attempted r) count now)
        (fn-opub-get :inflight r)
        (fn-opl-blockedp (fn-opub-get :deferred r) budget space count now))))
    (and (equal (mv-nth 0 (fn-opub-request r profile count budget space now)) (if profile word :nothing-to-compact))
         (equal (fn-opub-observe (mv-nth 1 (fn-opub-request r profile count budget space now)))
                (if profile (list (fn-opub-get :attempted r) (fn-opub-get :base r) (fn-opub-get :base-payloads r) (fn-opub-get :deferred r) (fn-opub-get :durable r) (fn-opub-get :inflight r) (fn-opub-get :pending r) (and (member-eq word '(:requested :coalesced)) t) (fn-opub-get :serial r) (fn-opub-get :pass r)) (fn-opub-observe r))))))
  :subject fn-opub-request
  :witness ((r '(64 base 5 nil 32 64 nil nil 8 nil)) (profile t) (count 128) (budget 1000) (space 1000) (now 2000))
  :breaks ()
  :mutations ((duplicate-capture (:conclusion
                (equal (mv-nth 0 (fn-opub-request r profile count budget space now)) :requested))
               ((r '(64 base 5 nil 32 64 nil nil 8 nil)) (profile t) (count 128) (budget 1000) (space 1000) (now 2000))
               :fault "a decision starts a second publication while one holds the slot")))

(defteeth-check (fn-opub-capture-serial-increases fn-opub-capture-establishes-holder
                 fn-opub-done-does-not-release-another-holder
                 fn-opub-abandoned-stale-fields-unchanged fn-opub-install-preserves-serial
                 fn-opub-due-composition-by-definition fn-opub-request-composition-by-definition))
