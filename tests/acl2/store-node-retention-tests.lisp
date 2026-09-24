; Teeth for books/store-node-retention: the P9 keystones over the functions
; the host calls.  Every state below is built from `fn-sn-initial' by the
; I/O, prepare and finish transitions the host drives
; (host/store-node-host.lisp), so each witness is reachable.  Each must-fail
; is a ground instance of a keystone's conclusion at a reachable state where
; the dropped hypothesis is false, so ACL2 refuses it by evaluation.
(in-package "ACL2")
(include-book "../../books/store-node-retention")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defun snrt-reserve (s)
  (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier nil)
                                 :frontier-file :ok)
                       :frontier-replace :ok)
            :frontier-directory :ok))
(defun snrt-publish (s)
  (fn-sn-io (fn-sn-io (fn-sn-io s :record-file :ok)
                       :record-link :ok)
            :record-directory :ok))
(defun snrt-pins (s) (fn-retain-pins (fn-node-retention (fn-sn-node s))))
(defun snrt-articles (s) (fn-state-articles (fn-node-acceptance (fn-sn-node s))))

; One accepted article (charge 2) in a capacity-10 store: 8 units of room.
(defconst *snrt-groups* '("fn.letters" "fn.test"))
(defun snrt-article (sequence id charge)
  (fn-record-make sequence sequence sequence
                  (if (equal id "snrt-pin-1") "<snrt-first@example.invalid>"
                    "<snrt-second@example.invalid>")
                  '(65 66) '("fn.test") id "snrt-subject" "snrt-release"
                  charge 841000000))
(defconst *snrt-first* (snrt-article 0 "snrt-pin-1" 2))
(defconst *snrt-ready-one*
  (fn-sn-finish (snrt-publish (fn-spc-prepare
                               (snrt-reserve (fn-sn-initial *snrt-groups* 10))
                               *snrt-first*))))
(defconst *snrt-reserved* (snrt-reserve *snrt-ready-one*))
(defconst *snrt-first-article* (car (snrt-articles *snrt-ready-one*)))
(defconst *snrt-archive-pin* (car (snrt-pins *snrt-ready-one*)))
(assert-event (fn-snt-relation *snrt-reserved*))
(assert-event (equal (fn-sf-phase (fn-sn-files *snrt-reserved*)) :reserved))
(assert-event (equal (fn-retain-reserved (fn-node-retention (fn-sn-node *snrt-reserved*))) 2))
(assert-event (equal (fn-retain-capacity (fn-node-retention (fn-sn-node *snrt-reserved*))) 10))
(assert-event (equal (fn-retain-obligation-kind *snrt-archive-pin*) :archive))

; -----------------------------------------------------------------------------
; fn-spc-prepare-refuses-unaffordable-obligation (and fn-sn-prepare-...)
;
; Charge 9: 2 + 9 = 11 > 10.  The host-called prepare returns the exact
; input, which store-node-host.lisp:475 answers as :refused.
(defconst *snrt-unaffordable* (snrt-article 1 "snrt-pin-2" 9))
(defconst *snrt-affordable* (snrt-article 1 "snrt-pin-2" 8))
(assert-event (fn-record-p *snrt-unaffordable*))
(assert-event (> (+ 2 (fn-record-charge *snrt-unaffordable*)) 10))
(assert-event (equal (fn-spc-prepare *snrt-reserved* *snrt-unaffordable*) *snrt-reserved*))
(assert-event (equal (fn-sn-prepare *snrt-reserved* *snrt-unaffordable*) *snrt-reserved*))
; The capacity hypothesis dropped: charge 8 fits exactly (2 + 8 = 10), the
; same record otherwise, and prepare stages it.
(assert-event (equal (fn-sf-phase (fn-sn-files (fn-spc-prepare *snrt-reserved* *snrt-affordable*)))
                     :record-staged))
(must-fail
 (defthm snrt-spc-prepare-refusal-without-capacity-hypothesis
   (equal (fn-spc-prepare *snrt-reserved* *snrt-affordable*) *snrt-reserved*)
   :rule-classes nil))
(must-fail
 (defthm snrt-sn-prepare-refusal-without-capacity-hypothesis
   (equal (fn-sn-prepare *snrt-reserved* *snrt-affordable*) *snrt-reserved*)
   :rule-classes nil))

; fn-node-prepare-refuses-unaffordable-obligation, on the node the host's
; prepare hands it (fn-sn-prepare-node's advanced node).
(defconst *snrt-node* (fn-replay-advance-txid (fn-sn-node *snrt-reserved*) 1))
(defun snrt-node-prepare (charge)
  (fn-node-prepare *snrt-node* 1 "<snrt-second@example.invalid>" '(65 66)
                   '("fn.test") "snrt-pin-2" "snrt-subject" "snrt-release"
                   charge 841000000))
(assert-event (fn-node-statep *snrt-node*))
(assert-event (equal (snrt-node-prepare 9) *snrt-node*))
(assert-event (consp (fn-node-stage (snrt-node-prepare 8))))
(must-fail
 (defthm snrt-node-prepare-refusal-without-capacity-hypothesis
   (equal (snrt-node-prepare 8) *snrt-node*)
   :rule-classes nil))

; fn-node-prepare-refuses-whatever-retain-admit-refuses: its one hypothesis
; is fn-retain-admit's no-op.  At charge 9 admit refuses and so does prepare;
; at charge 8 admit admits, and the conclusion fails.
(defun snrt-admit (charge)
  (fn-retain-admit (fn-node-retention *snrt-node*) "snrt-pin-2" "snrt-subject"
                   :archive "snrt-release" charge))
(assert-event (equal (snrt-admit 9) (fn-node-retention *snrt-node*)))
(assert-event (not (equal (snrt-admit 8) (fn-node-retention *snrt-node*))))
(must-fail
 (defthm snrt-prepare-refusal-without-admit-refusal
   (equal (snrt-node-prepare 8) *snrt-node*)
   :rule-classes nil))
; A refusal for a reason other than capacity (a reused obligation id) is also
; an admit no-op, and prepare refuses it: the equation is not only the
; capacity case.
(assert-event (equal (fn-retain-admit (fn-node-retention *snrt-node*) "snrt-pin-1"
                                      "snrt-subject" :archive "snrt-release" 1)
                     (fn-node-retention *snrt-node*)))
(assert-event (equal (fn-node-prepare *snrt-node* 1 "<snrt-second@example.invalid>"
                                      '(65 66) '("fn.test") "snrt-pin-1"
                                      "snrt-subject" "snrt-release" 1 841000000)
                     *snrt-node*))

; fn-retain-admit-is-a-no-op-exactly-when-inadmissible has no hypothesis;
; both sides of the iff occur at the witness.
(assert-event (not (fn-retain-admissiblep (fn-node-retention *snrt-node*) "snrt-pin-2"
                                          "snrt-subject" :archive "snrt-release" 9)))
(assert-event (fn-retain-admissiblep (fn-node-retention *snrt-node*) "snrt-pin-2"
                                     "snrt-subject" :archive "snrt-release" 8))

; -----------------------------------------------------------------------------
; fn-sn-finish-keeps-accepted-articles and
; fn-sn-finish-releases-an-obligation-only-by-its-matching-release
;
; Three finish arms from the one-article store: the article arm (a second
; article), the retention undertaking arm, and the retention release arm.
; The identity, consumer and topic arms are covered by the theorems but have
; no witness here.

; Article arm.
(defconst *snrt-second* (snrt-article 1 "snrt-pin-2" 1))
(defconst *snrt-completing-article*
  (snrt-publish (fn-spc-prepare *snrt-reserved* *snrt-second*)))
(defconst *snrt-ready-two* (fn-sn-finish *snrt-completing-article*))
(assert-event (fn-sn-completion-enabledp *snrt-completing-article*))
(assert-event (equal (len (snrt-articles *snrt-ready-two*)) 2))
(assert-event (member-equal *snrt-first-article* (snrt-articles *snrt-ready-two*)))
(assert-event (member-equal *snrt-archive-pin* (snrt-pins *snrt-ready-two*)))

; Undertaking arm: a :forward obligation is added; the article and its
; archive pin stay.
(defconst *snrt-undertake*
  (fn-store-retention-event-make :undertake 1 1 1 "snrt-forward" "snrt-object"
                                 "snrt-receipt" 1))
(defconst *snrt-completing-undertake*
  (snrt-publish (fn-sn-prepare-retention *snrt-reserved* *snrt-undertake*)))
(defconst *snrt-undertaken* (fn-sn-finish *snrt-completing-undertake*))
(defconst *snrt-forward-pin* (car (snrt-pins *snrt-undertaken*)))
(assert-event (fn-sn-completion-enabledp *snrt-completing-undertake*))
(assert-event (equal (fn-sn-completion-record *snrt-completing-undertake*) *snrt-undertake*))
(assert-event (equal (fn-retain-obligation-kind *snrt-forward-pin*) :forward))
(assert-event (equal (len (snrt-pins *snrt-undertaken*)) 2))
(assert-event (member-equal *snrt-first-article* (snrt-articles *snrt-undertaken*)))
(assert-event (member-equal *snrt-archive-pin* (snrt-pins *snrt-undertaken*)))

; Release arm: the matching release removes the :forward obligation and
; nothing else; the article and its archive pin stay.
(defconst *snrt-release*
  (fn-store-retention-event-make :release 2 2 2 "snrt-forward" "snrt-object"
                                 "snrt-receipt" 0))
(defconst *snrt-completing-release*
  (snrt-publish (fn-sn-prepare-retention (snrt-reserve *snrt-undertaken*)
                                         *snrt-release*)))
(defconst *snrt-released* (fn-sn-finish *snrt-completing-release*))
(assert-event (fn-sn-completion-enabledp *snrt-completing-release*))
(assert-event (not (member-equal *snrt-forward-pin* (snrt-pins *snrt-released*))))
(assert-event (equal (snrt-pins *snrt-released*) (list *snrt-archive-pin*)))
(assert-event (member-equal *snrt-first-article* (snrt-articles *snrt-released*)))
; The removal is the theorem's case: a release record matching the pin.
(assert-event
 (fn-retain-matching-releasep *snrt-forward-pin* "snrt-forward" "snrt-object"
                              :forward "snrt-receipt"))
; A release with the wrong evidence never reaches completion: the Store
; refuses to stage it, so no finish arm sees it.
(defconst *snrt-wrong-release*
  (fn-store-retention-event-make :release 2 2 2 "snrt-forward" "snrt-object"
                                 "not-the-receipt" 0))
(assert-event (equal (fn-sn-prepare-retention (snrt-reserve *snrt-undertaken*)
                                              *snrt-wrong-release*)
                     (snrt-reserve *snrt-undertaken*)))
; An archive obligation cannot be released by a retention event: a release
; naming the article's own pin id is refused at staging.
(defconst *snrt-archive-release*
  (fn-store-retention-event-make :release 2 2 2 "snrt-pin-1" "snrt-subject"
                                 "snrt-release" 0))
(assert-event (equal (fn-sn-prepare-retention (snrt-reserve *snrt-undertaken*)
                                              *snrt-archive-release*)
                     (snrt-reserve *snrt-undertaken*)))

; Teeth for fn-sn-finish-keeps-accepted-articles (one hypothesis): an article
; that was not accepted before is not accepted after.
(must-fail
 (defthm snrt-keep-without-membership
   (member-equal '(:never-accepted) (snrt-articles *snrt-released*))
   :rule-classes nil))

; Teeth for the release keystone, one per hypothesis.
; (1) Drop "the pin was held before": a pin never held is absent after an
;     undertaking, which is no release.
(must-fail
 (defthm snrt-release-without-held-pin
   (let ((record (fn-sn-completion-record *snrt-completing-undertake*)))
     (and (fn-store-retention-event-p record)
          (not (equal (fn-store-event-kind record) :undertake))))
   :rule-classes nil))
(assert-event (not (member-equal '(:never-held) (snrt-pins *snrt-completing-undertake*))))
(assert-event (not (member-equal '(:never-held) (snrt-pins *snrt-undertaken*))))
; (2) Drop "the pin is gone after": the archive pin was held across the
;     release arm, and the release does not match it.
(assert-event (member-equal *snrt-archive-pin* (snrt-pins *snrt-completing-release*)))
(assert-event (member-equal *snrt-archive-pin* (snrt-pins *snrt-released*)))
(must-fail
 (defthm snrt-release-without-removal
   (fn-retain-matching-releasep *snrt-archive-pin* "snrt-forward" "snrt-object"
                                :forward "snrt-receipt")
   :rule-classes nil))

; Teeth for fn-sn-finish-keeps-every-archive-obligation: drop the :archive
; kind and the :forward pin is released by the release arm.
(assert-event (member-equal *snrt-forward-pin* (snrt-pins *snrt-completing-release*)))
(must-fail
 (defthm snrt-archive-keep-without-archive-kind
   (member-equal *snrt-forward-pin* (snrt-pins *snrt-released*))
   :rule-classes nil))
