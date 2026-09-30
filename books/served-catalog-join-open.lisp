; served-catalog-join-open.lisp -- the row relation at the opens (lane
; sca-join-2, 2026-09-27; E of PRF-302).
;
; The node the replay folds (books/config-physical-replay.lisp fn-cpr-loop,
; the one-record step fn-replay-apply-record) and the catalog the host loads
; from the same rows (books/served-catalog-owner.lisp fn-sca-load-held-row)
; keep fn-scj-acc-rowsp (books/served-catalog-join-number.lisp) event for
; event: an article or composite row is prepared and installed by the node
; and committed (visible or hidden) by the load; a configuration record
; grows the domain at watermark 1; every other event keeps the acceptance's
; articles, watermarks and domain and is skipped by the load.

(in-package "ACL2")

(include-book "served-catalog-join-number")

(local (in-theory (disable fn-nntp-article-idp-is-consp fn-scat-article-idp-is-msgid-idp
                           fn-scat-msgid-idp fn-nntp-index-msgid-okp-stringp
                           fn-nntp-index-msgid-okp fn-cp-id-length-bound)))

; -----------------------------------------------------------------------------
; The node's side of one replayed record.

(defthm fn-scj-acc-rowsp-of-same-fields
  (implies (and (equal (fn-state-articles a) (fn-state-articles b))
                (equal (fn-state-nexts a) (fn-state-nexts b))
                (equal (fn-state-groups a) (fn-state-groups b)))
           (equal (fn-scj-acc-rowsp a c) (fn-scj-acc-rowsp b c)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-scj-acc-rowsp))))

(defthm fn-scj-advance-txid-keeps-fields
  (let ((a (fn-node-acceptance (fn-replay-advance-txid node x))))
    (implies (consp (fn-replay-advance-txid node x))
             (and (equal (fn-state-articles a) (fn-state-articles (fn-node-acceptance node)))
                  (equal (fn-state-nexts a) (fn-state-nexts (fn-node-acceptance node)))
                  (equal (fn-state-groups a) (fn-state-groups (fn-node-acceptance node))))))
  :hints (("Goal" :in-theory (enable fn-replay-advance-txid))))

(defthm fn-scj-node-prepare-staged
  (implies (and (null (fn-node-stage s))
                (consp (fn-node-stage (fn-node-prepare s generation msgid payload groups
                                                       obligation-id subject evidence charge stamp binding))))
           (and (equal (fn-node-acceptance (fn-node-prepare s generation msgid payload groups
                                                            obligation-id subject evidence charge stamp binding))
                       (fn-accept-prepare (fn-node-acceptance s) generation msgid payload groups stamp))
                (not (equal (fn-accept-prepare (fn-node-acceptance s) generation msgid payload groups stamp)
                            (fn-node-acceptance s)))))
  :hints (("Goal" :in-theory (e/d (fn-node-prepare) (fn-accept-prepare fn-retain-admissiblep fn-retain-admit)))))

(defthm fn-scj-node-complete-durable-installs
  (implies (fn-node-pending-matchesp s txid generation)
           (equal (fn-node-acceptance (fn-node-complete s txid generation :durable))
                  (fn-install-pending (fn-node-acceptance s))))
  :hints (("Goal" :in-theory (e/d (fn-node-complete fn-node-pending-matchesp fn-accept-complete fn-node-statep)
                                  (fn-install-pending)))))

(defthm fn-scj-advance-txid-unstaged
  (implies (null (fn-node-stage node))
           (null (fn-node-stage (fn-replay-advance-txid node x))))
  :hints (("Goal" :in-theory (enable fn-replay-advance-txid))))

(local (defthm fn-scj-cat-rowp-not-tagged-composite
  (implies (fn-cat-rowp x) (not (equal (car x) :hstxa)))
  :hints (("Goal" :in-theory (enable fn-cat-rowp fn-held-shapep fn-held-internals fn-record-internals
                                     fn-record-uint64p)))))

(local (defthm fn-scj-hstxa-is-composite-shape
  (implies (fn-hstxa-p x)
           (and (fn-sca-composite-shapep x) (not (fn-cat-rowp x))))
  :hints (("Goal" :in-theory (enable fn-sca-composite-shapep fn-hstxa-p fn-hstxa-held)))))

(local (defthm fn-scj-not-composite-shape-unless-tagged
  (implies (not (equal (car x) :hstxa)) (not (fn-sca-composite-shapep x)))
  :hints (("Goal" :in-theory (enable fn-sca-composite-shapep)))))

(defthm fn-scj-node-with-retention-keeps-acceptance
  (equal (fn-node-acceptance (fn-replay-node-with-retention node retention))
         (fn-node-acceptance node))
  :hints (("Goal" :in-theory (enable fn-replay-node-with-retention))))

(local (defthm fn-scj-row-is-no-other-event
   (implies (fn-cat-rowp x)
            (and (not (fn-store-retention-event-p x))
                 (not (fn-stxe-p x)) (not (fn-stxk-p x))
                 (not (fn-cpe-eventp x)) (not (fn-th-topic-eventp x))))
   :hints (("Goal" :in-theory (enable fn-cat-rowp fn-store-retention-event-p
                                      fn-stxe-p fn-stxe-shapep fn-stxk-p fn-stxk-shapep
                                      fn-cpe-eventp fn-held-shapep
                                      fn-th-topic-eventp fn-th-local-admin-eventp)))))

(local (defthm fn-scj-other-events-are-not-tagged-composite
   (implies (or (fn-store-retention-event-p x) (fn-stxe-p x) (fn-stxk-p x)
                (fn-cpe-eventp x) (fn-th-topic-eventp x))
            (not (equal (car x) :hstxa)))
   :hints (("Goal" :in-theory (enable fn-store-retention-event-p fn-stxe-p fn-stxe-shapep fn-stxe-sequence
                                      fn-record-uint32p fn-stxk-p fn-stxk-shapep fn-stxk-sequence
                                      fn-cpe-eventp fn-th-topic-eventp fn-th-local-admin-eventp)))))

(defthm fn-scj-advance-txid-keeps-fields-always
  (let ((a (fn-node-acceptance (fn-replay-advance-txid node x))))
    (and (equal (fn-state-articles a) (fn-state-articles (fn-node-acceptance node)))
         (equal (fn-state-nexts a) (fn-state-nexts (fn-node-acceptance node)))
         (equal (fn-state-groups a) (fn-state-groups (fn-node-acceptance node)))))
  :hints (("Goal" :in-theory (enable fn-replay-advance-txid))))

; The article arm: advance, prepare, install.
(defthm fn-scj-article-arm-keeps-acc-rowsp
  (let* ((adv (fn-replay-advance-txid node x))
         (prepared (fn-node-prepare adv (fn-record-generation h) (fn-record-msgid h)
                                    (fn-record-payload h) (fn-record-groups h)
                                    oid subj ev charge (fn-record-stamp h) (fn-held-binding h))))
    (implies (and (null (fn-node-stage node))
                  (fn-node-pending-matchesp prepared txid gen)
                  (fn-scj-acc-rowsp (fn-node-acceptance node) c))
             (and (fn-scj-acc-rowsp (fn-node-acceptance (fn-node-complete prepared txid gen :durable))
                                    (fn-cat-commit h c))
                  (fn-scj-acc-rowsp (fn-node-acceptance (fn-node-complete prepared txid gen :durable))
                                    (fn-cat-commit (fn-held-with-withdrawn h w) c)))))
  :hints (("Goal" :in-theory (e/d (fn-node-pending-matchesp)
                                  (fn-node-prepare fn-node-complete fn-replay-advance-txid
                                   fn-accept-prepare fn-install-pending fn-scj-acc-rowsp
                                   fn-cat-commit-is-append fn-held-with-withdrawn))
           :use ((:instance fn-scj-advance-txid-unstaged)
                 (:instance fn-scj-node-prepare-staged
                            (s (fn-replay-advance-txid node x))
                            (generation (fn-record-generation h)) (msgid (fn-record-msgid h))
                            (payload (fn-record-payload h)) (groups (fn-record-groups h))
                            (obligation-id oid) (subject subj) (evidence ev) (stamp (fn-record-stamp h)) (binding (fn-held-binding h)))
                 (:instance fn-scj-acc-rowsp-of-same-fields
                            (a (fn-node-acceptance (fn-replay-advance-txid node x)))
                            (b (fn-node-acceptance node)))
                 (:instance fn-scj-acc-rowsp-of-install
                            (s (fn-node-acceptance (fn-replay-advance-txid node x)))
                            (generation (fn-record-generation h)))
                 (:instance fn-scj-acc-rowsp-of-install-withdrawn
                            (s (fn-node-acceptance (fn-replay-advance-txid node x)))
                            (generation (fn-record-generation h)))))))

(defun-nx fn-scj-acc-rowsp-fields (arts nexts groups c)
  (and (equal arts (fn-scj-rows-arts c))
       (fn-scj-nexts-matchp groups nexts c)
       (fn-scj-rows-keys-inp c groups)))

(defthmd fn-scj-acc-rowsp-is-fields
  (equal (fn-scj-acc-rowsp a c)
         (fn-scj-acc-rowsp-fields (fn-state-articles a) (fn-state-nexts a) (fn-state-groups a) c))
  :hints (("Goal" :in-theory (enable fn-scj-acc-rowsp fn-scj-acc-rowsp-fields))))

; KEYSTONE (one replayed record).  The node step and the load step keep
; the row relation, under any view index.
(defthm fn-scj-acc-rowsp-of-replay-record
  (implies (and (consp (fn-replay-apply-record node e))
                (fn-scj-acc-rowsp (fn-node-acceptance node) c))
           (fn-scj-acc-rowsp (fn-node-acceptance (fn-replay-apply-record node e))
                             (fn-sca-load-held-row e idx c)))
  :hints (("Goal" :in-theory (e/d (fn-replay-apply-record fn-replay-apply-retention-event
                                   fn-replay-complete-retention fn-replay-apply-identity-neutral
                                   fn-replay-composite-held fn-sca-load-held-row fn-scj-acc-rowsp-is-fields)
                                  (fn-node-prepare fn-node-complete fn-replay-advance-txid
                                   fn-node-pending-matchesp fn-scj-acc-rowsp fn-scj-rows-arts fn-cat-commit-is-append
                                   fn-held-with-withdrawn fn-replay-node-with-retention fn-scj-article-arm-keeps-acc-rowsp
                                   fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-cpe-eventp
                                   fn-th-topic-eventp fn-hstxa-p fn-held-p fn-cat-rowp
                                   fn-sca-composite-shapep fn-retain-admissiblep fn-retain-admit
                                   fn-retain-release fn-retain-find-id fn-retain-matching-releasep))
           :use ((:instance fn-scj-article-arm-keeps-acc-rowsp
                            (x (fn-store-event-txid e)) (h (fn-hstxa-held e))
                            (oid (fn-record-obligation-id (fn-hstxa-held e))) (subj (fn-record-content-subject (fn-hstxa-held e)))
                            (ev (fn-record-release-evidence (fn-hstxa-held e))) (charge (fn-record-charge (fn-hstxa-held e)))
                            (txid (fn-record-txid (fn-hstxa-held e))) (gen (fn-record-generation (fn-hstxa-held e)))
                            (w (cons (len c) 0)))
                 (:instance fn-scj-article-arm-keeps-acc-rowsp
                            (x (fn-store-event-txid e)) (h e)
                            (oid (fn-record-obligation-id e)) (subj (fn-record-content-subject e))
                            (ev (fn-record-release-evidence e)) (charge (fn-record-charge e))
                            (txid (fn-record-txid e)) (gen (fn-record-generation e))
                            (w (cons (len c) 0)))
                 (:instance fn-scj-acc-rowsp-of-same-fields
                            (a (fn-node-acceptance
                                (fn-replay-advance-txid
                                 (fn-replay-advance-txid node (fn-store-event-txid e))
                                 (+ 1 (fn-store-event-txid e)))))
                            (b (fn-node-acceptance node)))
                 (:instance fn-scj-acc-rowsp-of-same-fields
                            (a (fn-node-acceptance (fn-replay-advance-txid node (fn-store-event-txid e))))
                            (b (fn-node-acceptance node)))))))

;; -----------------------------------------------------------------------------
; A configuration record.

(defthm fn-scj-next-of-extend-nexts
  (implies (member-equal name names)
           (equal (fn-next-number name (fn-cnode-extend-nexts names nexts))
                  (let ((n (fn-next-number name nexts)))
                    (if (posp n) n 1))))
  :hints (("Goal" :induct (fn-cnode-extend-nexts names nexts)
           :in-theory (enable fn-cnode-extend-nexts fn-next-number))))

(defthm fn-scj-next-absent
  (implies (and (fn-nexts-for-p groups nexts) (not (member-equal g groups)))
           (equal (fn-next-number g nexts) 0))
  :hints (("Goal" :in-theory (enable fn-nexts-for-p fn-next-number))))

(defthm fn-scj-keys-inp-absent
  (implies (and (fn-scj-keys-inp numbers old) (not (member-equal g old)))
           (not (fn-cat-assoc g numbers))))

(defthm fn-scj-group-high-absent
  (implies (and (fn-scj-rows-keys-inp c old) (not (member-equal g old)))
           (equal (fn-cat-group-high g c) 0))
  :hints (("Goal" :in-theory (enable fn-held-number-in))))

(defthm fn-scj-keys-inp-monotone
  (implies (and (fn-scj-keys-inp numbers a) (fn-subsetp a b))
           (fn-scj-keys-inp numbers b))
  :hints (("Goal" :in-theory (enable fn-subsetp))))

(defthm fn-scj-rows-keys-inp-monotone
  (implies (and (fn-scj-rows-keys-inp c a) (fn-subsetp a b))
           (fn-scj-rows-keys-inp c b)))

(defthm fn-scj-extend-next-matches
  (implies (and (fn-scj-nexts-matchp old nexts c)
                (fn-nexts-for-p old nexts)
                (fn-scj-rows-keys-inp c old)
                (member-equal g names2))
           (equal (fn-next-number g (fn-cnode-extend-nexts names2 nexts))
                  (+ 1 (fn-cat-group-high g c))))
  :hints (("Goal" :cases ((member-equal g old))
           :in-theory (disable fn-cnode-extend-nexts))))

(defthm fn-scj-nexts-matchp-of-extend
  (implies (and (fn-scj-nexts-matchp old nexts c)
                (fn-nexts-for-p old nexts)
                (fn-scj-rows-keys-inp c old)
                (fn-subsetp names names2))
           (fn-scj-nexts-matchp names (fn-cnode-extend-nexts names2 nexts) c))
  :hints (("Goal" :induct (fn-subsetp names names2)
           :in-theory (e/d (fn-subsetp) (fn-cnode-extend-nexts)))))

(defthm fn-scj-subsetp-self
  (fn-subsetp x x)
  :hints (("Goal" :in-theory (enable fn-subsetp))))

(defthm fn-scj-node-statep-nexts-for
  (implies (fn-node-statep node)
           (fn-nexts-for-p (fn-state-groups (fn-node-acceptance node))
                           (fn-state-nexts (fn-node-acceptance node))))
  :hints (("Goal" :in-theory (enable fn-node-statep fn-statep))))

(defthm fn-scj-cnode-statep-facts
  (implies (fn-cnode-statep cn)
           (and (fn-node-statep (fn-cnode-node cn))
                (equal (fn-state-groups (fn-node-acceptance (fn-cnode-node cn)))
                       (fn-cnode-domain-of (fn-cnode-config cn)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-cnode-statep fn-cnode-domain))))

; A configuration record grows the domain at watermark 1 and keeps the
; articles and every existing watermark.
(defthm fn-scj-acc-rowsp-of-apply-config
  (implies (and (fn-cnode-statep cn)
                (fn-scj-acc-rowsp (fn-node-acceptance (fn-cnode-node cn)) c))
           (fn-scj-acc-rowsp (fn-node-acceptance (fn-cnode-node (fn-cnode-apply-config cn record ceiling)))
                             c))
  :hints (("Goal" :in-theory (e/d (fn-scj-acc-rowsp-is-fields)
                                  (fn-cnode-apply-config fn-cnode-extend-nexts fn-cnode-statep
                                   fn-scj-rows-arts fn-node-statep))
           :cases ((fn-cnode-record-acceptablep cn record ceiling)))
          ("Subgoal 2" :use ((:instance fn-cnode-inadmissible-config-changes-nothing)))
          ("Subgoal 1" :in-theory (e/d (fn-scj-acc-rowsp-is-fields fn-cnode-apply-config fn-cnode-domain)
                                       (fn-cnode-extend-nexts fn-scj-rows-arts fn-node-statep
                                        fn-cnode-record-acceptablep))
           :use ((:instance fn-cnode-apply-config-keeps-watermarks-and-articles)
                 (:instance fn-scj-node-statep-nexts-for (node (fn-cnode-node cn)))
                 (:instance fn-scj-cnode-statep-facts)
                 (:instance fn-scj-nexts-matchp-of-extend
                            (old (fn-state-groups (fn-node-acceptance (fn-cnode-node cn))))
                            (nexts (fn-state-nexts (fn-node-acceptance (fn-cnode-node cn))))
                            (names (fn-cnode-domain-of (fn-cfg-apply-record (fn-cnode-config cn) record)))
                            (names2 (fn-cnode-domain-of (fn-cfg-apply-record (fn-cnode-config cn) record))))))))

;; -----------------------------------------------------------------------------
; The fold.

(local (defun-nx fn-scj-loop-ind (cn configs events config-sequence event-sequence idx c)
  (declare (xargs :measure (+ (len configs) (len events)) :verify-guards nil))
  (if (not (fn-cnode-statep cn))
      c
    (if (fn-cpr-config-firstp configs events)
        (let* ((record (car configs))
               (txid (fn-cfg-record-txid record))
               (node (fn-cnode-node cn)))
          (cond ((not (fn-cfg-recordp record)) c)
                ((not (equal (fn-cfg-record-sequence record) config-sequence)) c)
                ((not (fn-replay-advance-okp node txid)) c)
                (t (let ((at (fn-cnode-make (fn-replay-advance-txid node txid) (fn-cnode-config cn))))
                     (if (not (fn-cnode-statep at))
                         c
                       (if (not (fn-cnode-record-acceptablep at record (fn-cnode-line-ceiling)))
                           c
                         (fn-scj-loop-ind (fn-cnode-apply-config at record (fn-cnode-line-ceiling))
                                          (cdr configs) events
                                          (+ 1 (nfix config-sequence)) event-sequence idx c)))))))
      (if (consp events)
          (let ((event (car events)))
            (cond ((not (fn-store-event-p event)) c)
                  ((not (equal (fn-store-event-sequence event) event-sequence)) c)
                  (t (let ((next (fn-cpr-apply-event cn event)))
                       (if (not (fn-cnode-statep next))
                           c
                         (fn-scj-loop-ind next configs (cdr events) config-sequence
                                          (+ 1 (nfix event-sequence)) idx
                                          (fn-sca-load-held-row event idx c)))))))
        c)))))

(defthm fn-scj-acc-rowsp-of-config-step
  (let ((at (fn-cnode-make (fn-replay-advance-txid (fn-cnode-node cn) txid) (fn-cnode-config cn))))
    (implies (and (fn-cnode-statep at)
                  (fn-scj-acc-rowsp (fn-node-acceptance (fn-cnode-node cn)) c))
             (fn-scj-acc-rowsp (fn-node-acceptance (fn-cnode-node (fn-cnode-apply-config at record ceiling)))
                               c)))
  :hints (("Goal" :in-theory (disable fn-scj-acc-rowsp fn-cnode-apply-config fn-cnode-statep
                                      fn-replay-advance-txid)
           :use ((:instance fn-scj-acc-rowsp-of-apply-config
                            (cn (fn-cnode-make (fn-replay-advance-txid (fn-cnode-node cn) txid)
                                               (fn-cnode-config cn))))
                 (:instance fn-scj-acc-rowsp-of-same-fields
                            (a (fn-node-acceptance (fn-replay-advance-txid (fn-cnode-node cn) txid)))
                            (b (fn-node-acceptance (fn-cnode-node cn))))))))

(defthm fn-scj-acc-rowsp-of-config-step-2
  (let ((at (fn-cnode-make (fn-replay-advance-txid (fn-cnode-node cn) txid) (fn-cnode-config cn))))
    (implies (fn-scj-acc-rowsp (fn-node-acceptance (fn-cnode-node cn)) c)
             (fn-scj-acc-rowsp (fn-node-acceptance (fn-cnode-node (fn-cnode-apply-config at record ceiling)))
                               c)))
  :hints (("Goal" :in-theory (disable fn-scj-acc-rowsp fn-cnode-apply-config fn-cnode-statep
                                      fn-replay-advance-txid)
           :use ((:instance fn-scj-acc-rowsp-of-same-fields
                            (a (fn-node-acceptance (fn-replay-advance-txid (fn-cnode-node cn) txid)))
                            (b (fn-node-acceptance (fn-cnode-node cn)))))
           :cases ((fn-cnode-statep (fn-cnode-make (fn-replay-advance-txid (fn-cnode-node cn) txid)
                                                   (fn-cnode-config cn)))))
          ("Subgoal 2" :expand ((:free (x) (fn-cnode-apply-config x record ceiling))))
          ("Subgoal 1" :use ((:instance fn-scj-acc-rowsp-of-apply-config
                            (cn (fn-cnode-make (fn-replay-advance-txid (fn-cnode-node cn) txid)
                                               (fn-cnode-config cn))))))))
(defthm fn-scj-acc-rowsp-of-cpr-loop
  (implies (and (equal (fn-replay-result-kind (fn-cpr-loop cn configs events cs es)) :ok)
                (fn-scj-acc-rowsp (fn-node-acceptance (fn-cnode-node cn)) c))
           (fn-scj-acc-rowsp (fn-node-acceptance
                              (fn-cnode-node (fn-replay-result-node (fn-cpr-loop cn configs events cs es))))
                             (fn-sca-load-held-rows-from events idx c)))
  :hints (("Goal" :induct (fn-scj-loop-ind cn configs events cs es idx c)
           :expand ((:free (cs es) (fn-cpr-loop cn configs events cs es)))
           :in-theory (e/d (fn-cpr-apply-event)
                           (fn-cpr-loop fn-cnode-statep fn-cnode-apply-config fn-cnode-record-acceptablep
                            fn-replay-apply-record fn-sca-load-held-row fn-scj-acc-rowsp
                            fn-store-event-p fn-cfg-recordp fn-replay-advance-txid
                            fn-cpr-event-servedp fn-node-statep fn-replay-advance-okp)))))

(local (defthm fn-scj-next-of-initial-member
  (implies (member-equal g groups)
           (equal (fn-next-number g (fn-initial-nexts groups)) 1))
  :hints (("Goal" :in-theory (enable fn-next-number fn-initial-nexts)))))

(defthm fn-scj-nexts-matchp-of-initial
  (implies (fn-subsetp names groups)
           (fn-scj-nexts-matchp names (fn-initial-nexts groups) nil))
  :hints (("Goal" :in-theory (enable fn-subsetp))))

(defthm fn-scj-acc-rowsp-of-initial
  (fn-scj-acc-rowsp (fn-node-acceptance (fn-cnode-node (fn-cnode-initial cfg))) nil)
  :hints (("Goal" :in-theory (enable fn-scj-acc-rowsp fn-cnode-initial fn-node-initial-state
                                     fn-initial-state))))

(defthm fn-scj-acc-rowsp-of-cpr-replay
  (implies (equal (fn-replay-result-kind (fn-cpr-replay configs events)) :ok)
           (fn-scj-acc-rowsp (fn-node-acceptance (fn-cnode-node (fn-replay-result-node (fn-cpr-replay configs events))))
                             (fn-sca-load-held-rows-from events idx nil)))
  :hints (("Goal" :in-theory (e/d (fn-cpr-replay) (fn-cpr-loop fn-scj-acc-rowsp fn-cnode-initial (:e fn-cnode-initial) (:e fn-cfg-initial)))
           :use ((:instance fn-scj-acc-rowsp-of-cpr-loop (cn (fn-cnode-initial (fn-cfg-initial)))
                            (cs 0) (es 0) (c nil))
                 (:instance fn-scj-acc-rowsp-of-initial (cfg (fn-cfg-initial)))))))

(defthm fn-scj-acc-rowsp-of-cst-replay-node
  (implies (consp (fn-cst-replay-node configs events frontier))
           (fn-scj-acc-rowsp (fn-node-acceptance (fn-cst-replay-node configs events frontier))
                             (fn-sca-load-held-rows-from events idx nil)))
  :hints (("Goal" :in-theory (e/d (fn-cst-replay-node) (fn-cpr-replay fn-scj-acc-rowsp fn-replay-advance-txid))
           :use ((:instance fn-scj-acc-rowsp-of-same-fields
                            (a (fn-node-acceptance (fn-replay-advance-txid
                                                    (fn-cnode-node (fn-replay-result-node (fn-cpr-replay configs events)))
                                                    frontier)))
                            (b (fn-node-acceptance (fn-cnode-node (fn-replay-result-node (fn-cpr-replay configs events)))))
                            (c (fn-sca-load-held-rows-from events idx nil)))
                 (:instance fn-scj-acc-rowsp-of-cpr-replay)))))

;; -----------------------------------------------------------------------------
; E at the host entries, and the row equation.

(defthm fn-scj-load-held-rows-is-from-empty
  (equal (fn-sca-load-held-rows rows idx fn-arena fn-cat)
         (fn-sca-load-held-rows-from rows idx nil))
  :hints (("Goal" :in-theory (enable fn-sca-load-held-rows fn-cat-clear create-fn-cat))))

; KEYSTONE (E, the row relation at every entry).  The catalog the host
; loads (fn-sca-load-held-rows, under any view index) from the rows of an
; owner in the live relation at an idle store is related to that store's
; acceptance.  Every entry establishes that owner: recover and checkpoint
; open (fn-sca-ocl-relation-at-recover), the full open
; (fn-sca-ocl-relation-at-full-open), and a reclaimed store re-entering
; through either.
(defthm fn-scj-acc-rowsp-at-idle-related-owner
  (let ((st (fn-own-store (fn-ocfg-owner oc))))
    (implies (and (fn-ocl-relation oc)
                  (fn-own-store-idlep st))
             (fn-scj-acc-rowsp (fn-node-acceptance (fn-sn-node st))
                               (fn-sca-load-held-rows (fn-sf-records (fn-sn-files st))
                                                      view-index fn-arena fn-cat))))
  :hints (("Goal" :in-theory (e/d (fn-ocl-relation fn-cst-relation fn-own-store-idlep fn-cst-recoverablep)
                                  (fn-scj-acc-rowsp fn-cst-replay-node fn-sca-load-held-rows-from
                                   fn-sn-statep fn-sn-observed-historyp fn-cst-final-configurationp))
           :use ((:instance fn-scj-acc-rowsp-of-cst-replay-node
                            (configs (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc))))
                            (events (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
                            (frontier (fn-sf-frontier (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
                            (idx view-index))))))

; KEYSTONE (the row equation, PRF-302's open hypothesis).  When the
; acceptance that installed the article is related to the catalog that
; committed its row, the committed row read as an article is the article
; the acceptance installed: fn-scj-joinp-of-article-finish's hypothesis
; (fn-cat-row-article at the count of the commit = A) with A the head of
; the acceptance's articles, the article the refresh adds.
(defthm fn-scj-row-equation-of-acc-rowsp
  (implies (fn-scj-acc-rowsp acc2 (fn-cat-commit held c))
           (equal (fn-cat-row-article (len c) fn-arena (fn-cat-commit held c))
                  (car (fn-state-articles acc2))))
  :hints (("Goal" :in-theory (e/d (fn-scj-acc-rowsp fn-cat-assign fn-scj-row-art) (fn-cat-commit-is-append fn-scj-rows-arts)))))
