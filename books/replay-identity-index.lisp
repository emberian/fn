; fn: the open's replay answers its identity questions from tries it builds as
; it advances, and its history recognizer reads each record's kind once
; (PRF-242).
;
; Measured before this book (lane open-by-index's hbox sb-sprof of the
; 40,001-event fixture t40k-2k-cp5, quoted in
; planning/evidence/replay-identity-2026-09-27.md): a full replay spent
; 51.7 percent of its samples in fn-retain-known-id-scanp and 23.0 percent in
; fn-acceptedp.  Each replayed article asks two identity questions of the node
; the replay has built so far, and both were a walk of a list that grows with
; the history:
;
;   - fn-accept-prepare (books/acceptance.lisp): has an article with this
;     Message-ID been accepted?  fn-acceptedp over the committed articles.
;   - fn-node-prepare (books/node.lisp) and fn-retain-admit
;     (books/retention.lisp): is this obligation id known to the ledger?
;     fn-retain-known-id-scanp over the pins and the releases, asked twice.
;
; So a full replay was quadratic in the history.  Here the fold carries IX, a
; pair of tries beside the configured node:
;
;   (car IX)  the Message-ID trie of the node's articles: EQUAL to
;             fn-midx-build of them (books/msgid-index.lisp);
;   (cdr IX)  a trie of obligation ids: for every string id, it holds the id
;             exactly when the ledger knows it (fn-rii-known-okp).
;
; fn-rii-okp is the pair of facts.  It holds of the initial node's empty tries
; and of fn-rii-ix-of (the tries built from any node, once, when a checkpoint
; resumes over a nonempty suffix), and fn-rii-ix-next keeps it across every
; step of the fold: it observes the node before and after the step and
;
;   - refreshes the Message-ID trie (one path copy when the step accepted an
;     article, fn-midx-refresh-preserves-correspondence);
;   - leaves the id trie when the ledger is unchanged or the step was a
;     release (a release moves a known id from the pins to the releases,
;     fn-rii-release-step-keeps-known), adds one id when the step consed one
;     pin, and otherwise rebuilds it from the ledger (always correct; no step
;     of the composed fold reaches it, and none is claimed).
;
; KEYSTONES (the host calls the left-hand sides):
;
;   fn-rii-sco-extend-is-sco-extend       (fn-rii-sco-extend c configs suffix)
;                                          = (fn-sco-extend c configs suffix)
;   fn-rii-classified-open-is-classified-open
;                                          (fn-rii-classified-open e configs frontier)
;                                          = (fn-sopc-classified-open e configs frontier)
;
; both with no hypothesis, so every theorem about the open
; (fn-sn-recover-from-checkpoint-equals-full-recover,
; fn-sco-store-open-of-extended-capture and the owner's
; fn-owner-recover-from-checkpoint-equals-full-recover) is about the host's
; calls: host/store-node-host.lisp fn-store-sn-recover,
; fn-store-sn-recover-from-checkpoint and fn-store-sn-open-extended;
; host/owner-host.lisp fn-owner-recover and fn-owner-recover-from-checkpoint.
;
; The second keystone is the history recognizer's: fn-sf-record-listp asked
; fn-store-event-p, -sequence, -txid (three times) and -generation of every
; record, and each of those dispatchers re-runs the record recognizers from
; fn-record-p, which walks the payload.  fn-event-fields reads the four
; answers in one dispatch (books/store-event-fields.lisp,
; fn-event-fields-of-rows-is-the-dispatchers), and the
; recognizer, the file kernel's and the Store's whole-state recognizers and
; the open's finalization are twins over it, each EQUAL to its reference.

(in-package "ACL2")
(include-book "store-open-pre-c1")
(include-book "store-event-fields")
(include-book "msgid-index-concrete")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; 1. A trie of ids: the Message-ID trie's nodes, the value t at each id.

(defun fn-rii-id-put (id trie)
  (declare (xargs :guard t))
  (if (stringp id) (fn-mxc-put id 0 t trie) trie))

(defun fn-rii-id-hasp (id trie)
  (declare (xargs :guard t))
  (if (stringp id) (if (fn-mxc-get id 0 trie) t nil) nil))

; The walk by index from 0 is the walk of the character list (the local
; lemmas of books/msgid-index-concrete.lisp at I = 0).
(local
 (defthm fn-rii-shift-less
   (implies (and (integerp i) (integerp n))
            (equal (< (+ -1 i) n) (< i (+ 1 n))))
   :hints (("Goal" :cases ((< i (+ 1 n)))))))

(local
 (defthm fn-rii-consp-of-nthcdr
   (implies (natp i) (equal (consp (nthcdr i l)) (< i (len l))))
   :hints (("Goal" :induct (nthcdr i l) :in-theory (enable nthcdr len)))))

(local
 (defthm fn-rii-car-of-nthcdr
   (equal (car (nthcdr i l)) (nth i l))
   :hints (("Goal" :induct (nthcdr i l) :in-theory (enable nthcdr nth)))))

(local
 (defthm fn-rii-cdr-of-nthcdr
   (implies (natp i) (equal (cdr (nthcdr i l)) (nthcdr (+ 1 i) l)))
   :hints (("Goal" :induct (nthcdr i l) :in-theory (enable nthcdr)))))

(local
 (defthm fn-rii-char-is-nth
   (equal (char s i) (nth i (coerce s 'list)))
   :hints (("Goal" :in-theory (enable char)))))

(local
 (defthm fn-rii-len-coerce-is-length
   (implies (stringp s) (equal (len (coerce s 'list)) (length s)))))

(local (in-theory (disable nth nthcdr)))

(local
 (defthm fn-rii-get-is-get-chars-of-nthcdr
   (implies (natp i)
            (equal (fn-mxc-get msgid i trie)
                   (fn-midx-get-chars (nthcdr i (coerce msgid 'list)) trie)))
   :hints (("Goal" :induct (fn-mxc-get msgid i trie)
            :in-theory (enable fn-mxc-get)
            :expand ((fn-midx-get-chars (nthcdr i (coerce msgid 'list)) trie))))))

(local
 (defthm fn-rii-put-is-put-chars-of-nthcdr
   (implies (natp i)
            (equal (fn-mxc-put msgid i value trie)
                   (fn-midx-put-chars (nthcdr i (coerce msgid 'list)) value trie)))
   :hints (("Goal" :induct (fn-mxc-put msgid i value trie)
            :in-theory (enable fn-mxc-put)
            :expand ((fn-midx-put-chars (nthcdr i (coerce msgid 'list))
                                        value trie))))))

(local (in-theory (disable fn-rii-len-coerce-is-length)))

(local
 (defthm fn-rii-nthcdr-zero
   (equal (nthcdr 0 l) l)
   :hints (("Goal" :in-theory (enable nthcdr)))))

(defthm fn-rii-id-hasp-of-put
  (implies (stringp id)
           (equal (fn-rii-id-hasp id (fn-rii-id-put new trie))
                  (or (equal id new) (fn-rii-id-hasp id trie))))
  :hints (("Goal" :in-theory (enable fn-rii-id-hasp fn-rii-id-put))))

(defthm fn-rii-id-hasp-of-nil
  (not (fn-rii-id-hasp id nil))
  :hints (("Goal" :in-theory (enable fn-rii-id-hasp))))

(in-theory (disable fn-rii-id-put fn-rii-id-hasp))

; -----------------------------------------------------------------------------
; 2. What the ledger knows, and the id trie's relation to it.

; fn-retain-pin-id-scanp and fn-retain-release-id-scanp with guard t (the
; relation below is a guard, so its body must be guard-verified at t).
(defun fn-rii-pin-hasp (id pins)
  (declare (xargs :guard t))
  (if (consp pins)
      (or (equal id (fn-retain-obligation-id (car pins)))
          (fn-rii-pin-hasp id (cdr pins)))
    nil))

(defun fn-rii-release-hasp (id releases)
  (declare (xargs :guard t))
  (if (consp releases)
      (or (equal id (fn-retain-release-id (car releases)))
          (fn-rii-release-hasp id (cdr releases)))
    nil))

(defun fn-rii-knownp (id retention)
  (declare (xargs :guard t))
  (if (or (fn-rii-pin-hasp id (fn-retain-pins retention))
          (fn-rii-release-hasp id (fn-retain-releases retention)))
      t
    nil))

(local
 (defthm fn-rii-pin-hasp-is-member
   (iff (fn-rii-pin-hasp id pins)
        (member-equal id (fn-retain-obligation-ids pins)))))

(local
 (defthm fn-rii-release-hasp-is-member
   (iff (fn-rii-release-hasp id releases)
        (member-equal id (fn-retain-release-ids releases)))))

(defthm fn-rii-knownp-is-known-idp
  (iff (fn-rii-knownp id retention)
       (fn-retain-known-idp id (fn-retain-pins retention)
                            (fn-retain-releases retention)))
  :hints (("Goal" :in-theory (enable fn-retain-known-idp))))

; The id trie answers exactly the ledger's known ids, for every string.
(defun-sk fn-rii-known-okp (ktrie retention)
  (declare (xargs :guard t :verify-guards t))
  (forall id (implies (stringp id)
                      (equal (fn-rii-id-hasp id ktrie)
                             (fn-rii-knownp id retention)))))

(in-theory (disable fn-rii-knownp fn-rii-known-okp))

; -----------------------------------------------------------------------------
; 3. The identity questions answered from the tries.

; fn-retain-admissiblep with the known-id test answered by KTRIE.
(defun fn-rii-admissiblep (s id subject kind evidence charge ktrie)
  (declare (xargs :guard (fn-retain-statep s)
                  :guard-hints (("Goal" :in-theory (enable fn-retain-statep)))))
  (and (mbe :logic (fn-retain-statep s) :exec t)
       (stringp id)
       (stringp subject)
       (fn-retain-kindp kind)
       (fn-provp evidence)
       (posp charge)
       (not (fn-rii-id-hasp id ktrie))
       (<= (+ (fn-retain-reserved s) charge)
           (fn-retain-capacity s))))

(defthm fn-rii-admissiblep-is-admissiblep
  (implies (fn-rii-known-okp ktrie s)
           (equal (fn-rii-admissiblep s id subject kind evidence charge ktrie)
                  (fn-retain-admissiblep s id subject kind evidence charge)))
  :hints (("Goal" :in-theory (e/d (fn-retain-admissiblep)
                                  (fn-rii-known-okp fn-rii-known-okp-necc
                                   fn-retain-statep))
           :use ((:instance fn-rii-known-okp-necc (retention s))
                 (:instance fn-rii-knownp-is-known-idp (retention s))))))

; The admitted ledger, in the branch where admissibility has just held:
; fn-retain-admit's body there, without deciding it a second time.
(defun fn-rii-admitted (s id subject kind evidence charge)
  (declare (xargs :guard (and (fn-retain-statep s) (posp charge))
                  :guard-hints (("Goal" :in-theory (enable fn-retain-statep)))))
  (fn-retain-make-state
   (fn-retain-capacity s)
   (+ (fn-retain-reserved s) charge)
   (cons (fn-retain-make-obligation id subject kind evidence charge)
         (fn-retain-pins s))
   (fn-retain-releases s)))

(defthm fn-rii-admitted-is-admit
  (implies (fn-retain-admissiblep s id subject kind evidence charge)
           (equal (fn-rii-admitted s id subject kind evidence charge)
                  (fn-retain-admit s id subject kind evidence charge)))
  :hints (("Goal" :in-theory (enable fn-retain-admit fn-retain-admissiblep
                                     fn-retain-statep))))

(local
 (defthm fn-rii-find-article-iff-acceptedp
   (implies (stringp msgid)
            (iff (fn-find-article msgid articles)
                 (fn-acceptedp msgid articles)))
   :hints (("Goal" :in-theory (enable fn-find-article fn-acceptedp
                                      fn-article-msgid)))))

(local
 (defthm fn-rii-nonempty-string-has-key-chars
   (implies (stringp msgid)
            (equal (consp (fn-midx-key-chars msgid)) (< 0 (length msgid))))
   :hints (("Goal" :in-theory (enable fn-midx-key-chars length)
            :expand ((len (coerce msgid 'list)))))))

; fn-acceptedp through the Message-ID trie; the empty string takes the scan
; (the trie's root slot also holds non-string identifiers).
(defun fn-rii-acceptedp (msgid articles mtrie)
  (declare (xargs :guard t))
  (if (and (stringp msgid) (< 0 (length msgid)))
      (if (fn-mxc-lookup msgid mtrie) t nil)
    (fn-acceptedp msgid articles)))

(defthm fn-rii-acceptedp-is-acceptedp
  (implies (equal mtrie (fn-midx-build articles))
           (iff (fn-rii-acceptedp msgid articles mtrie)
                (fn-acceptedp msgid articles)))
  :hints (("Goal" :in-theory (e/d (fn-rii-acceptedp
                                   fn-midx-concrete-lookup-is-lookup)
                                  (fn-midx-lookup fn-midx-build fn-find-article
                                   fn-acceptedp fn-mxc-lookup fn-midx-key-chars))
           :use ((:instance fn-midx-lookup-of-build-is-find-article-for-nonempty)))))

(in-theory (disable fn-rii-acceptedp))

; fn-accept-prepare with the duplicate test through MTRIE.
(defun fn-rii-accept-prepare (s generation msgid payload groups stamp mtrie)
  (declare (xargs :guard (fn-statep s) :verify-guards nil))
  (if (mbe :logic (not (fn-statep s)) :exec nil)
      s
    (if (or (equal (fn-state-fenced s) t)
            (consp (fn-state-pending s))
            (not (natp generation))
            (not (stringp msgid))
            (not (natp payload))
            (not (fn-record-stampp stamp))
            (not (fn-selection-validp groups (fn-state-groups s)))
            (fn-rii-acceptedp msgid (fn-state-articles s) mtrie))
        s
      (fn-make-state
       (fn-state-groups s)
       (fn-state-nexts s)
       (fn-state-articles s)
       (1+ (fn-state-next-txid s))
       (fn-make-pending
        (fn-state-next-txid s)
        generation
        msgid
        payload
        groups
        (fn-allocate-memberships groups (fn-state-nexts s))
        t
        stamp)
       nil))))

(verify-guards fn-rii-accept-prepare
  :hints (("Goal" :in-theory (enable fn-statep))))

(defthm fn-rii-accept-prepare-is-accept-prepare
  (implies (equal mtrie (fn-midx-build (fn-state-articles s)))
           (equal (fn-rii-accept-prepare s generation msgid payload groups
                                         stamp mtrie)
                  (fn-accept-prepare s generation msgid payload groups stamp)))
  :hints (("Goal" :in-theory (e/d (fn-rii-accept-prepare fn-accept-prepare)
                                  (fn-statep fn-make-state fn-make-pending
                                   fn-selection-validp fn-midx-build
                                   fn-acceptedp)))))

(in-theory (disable fn-rii-accept-prepare))

; The relation between IX and a node.
(defun fn-rii-okp (ix node)
  (declare (xargs :guard t))
  (and (consp ix)
       (equal (car ix)
              (fn-midx-build (fn-state-articles (fn-node-acceptance node))))
       (fn-rii-known-okp (cdr ix) (fn-node-retention node))))

; fn-node-prepare with both identity questions answered from IX, and the
; admitted ledger built where admissibility has just held.
(defun fn-rii-node-prepare (s generation msgid payload groups
                              obligation-id subject evidence charge stamp ix)
  (declare (xargs :guard (and (fn-node-statep s) (fn-rii-okp ix s))
                  :verify-guards nil))
  (if (mbe :logic (not (fn-node-statep s)) :exec nil)
      s
    (let ((retention (fn-node-retention s)))
      (if (not (fn-rii-admissiblep retention obligation-id subject :archive
                                   evidence charge (cdr ix)))
          s
        (let ((next-acceptance
               (fn-rii-accept-prepare (fn-node-acceptance s)
                                      generation msgid payload groups stamp
                                      (car ix))))
          (if (equal next-acceptance (fn-node-acceptance s))
              s
            (fn-node-make-state
             next-acceptance
             retention
             (fn-node-make-stage
              msgid generation obligation-id subject evidence charge
              (fn-rii-admitted retention obligation-id subject :archive
                               evidence charge))
             (fn-node-bindings s))))))))

(defthm fn-rii-node-prepare-is-node-prepare
  (implies (fn-rii-okp ix s)
           (equal (fn-rii-node-prepare s generation msgid payload groups
                                       obligation-id subject evidence charge
                                       stamp ix)
                  (fn-node-prepare s generation msgid payload groups
                                   obligation-id subject evidence charge
                                   stamp)))
  :hints (("Goal" :in-theory (e/d (fn-rii-node-prepare fn-node-prepare)
                                  (fn-node-statep fn-retain-admissiblep
                                   fn-rii-admissiblep fn-retain-admit
                                   fn-rii-admitted fn-accept-prepare
                                   fn-midx-build fn-rii-known-okp
                                   fn-node-make-state fn-node-make-stage)))))

(verify-guards fn-rii-node-prepare
  :hints (("Goal" :in-theory (e/d (fn-node-statep fn-retain-admissiblep)
                                  (fn-rii-known-okp)))))

(in-theory (disable fn-rii-node-prepare))

; -----------------------------------------------------------------------------
; 4. One replayed record, through the tries.

(defthm fn-rii-okp-of-advance
  (equal (fn-rii-okp ix (fn-replay-advance-txid node txid))
         (fn-rii-okp ix node))
  :hints (("Goal" :in-theory (disable fn-rii-known-okp))))

; fn-replay-apply-retention-event with the undertaking's admission answered
; from the id trie.
(defun fn-rii-apply-retention-event (node event ix)
  (declare (xargs :guard (and (fn-node-statep node)
                              (fn-store-retention-event-p event)
                              (fn-rii-okp ix node))
                  :verify-guards nil))
  (let* ((advanced (fn-replay-advance-txid node (fn-store-event-txid event)))
         (retention (fn-node-retention advanced))
         (id (fn-store-event-obligation-id event))
         (subject (fn-store-event-subject event))
         (evidence (fn-store-event-evidence event)))
    (if (or (not (fn-node-statep advanced))
            (not (equal (fn-state-next-txid (fn-node-acceptance advanced))
                        (fn-store-event-txid event)))
            (not (null (fn-node-stage advanced)))
            (member-equal id (fn-node-binding-ids (fn-node-bindings advanced))))
        nil
      (if (equal (fn-store-event-kind event) :undertake)
          (if (not (fn-rii-admissiblep retention id subject :forward evidence
                                       (fn-store-event-charge event)
                                       (cdr ix)))
              nil
            (fn-replay-complete-retention
             advanced (fn-rii-admitted retention id subject :forward evidence
                                       (fn-store-event-charge event))
             event))
        (let ((pin (fn-retain-find-id id (fn-retain-pins retention))))
          (if (not (fn-retain-matching-releasep pin id subject :forward evidence))
              nil
            (fn-replay-complete-retention
             advanced (fn-retain-release retention id subject :forward evidence)
             event)))))))

(defthm fn-rii-apply-retention-event-is-apply-retention-event
  (implies (fn-rii-okp ix node)
           (equal (fn-rii-apply-retention-event node event ix)
                  (fn-replay-apply-retention-event node event)))
  :hints (("Goal" :in-theory (e/d (fn-rii-apply-retention-event
                                   fn-replay-apply-retention-event)
                                  (fn-node-statep fn-retain-admissiblep
                                   fn-rii-admissiblep fn-retain-admit
                                   fn-rii-admitted fn-rii-known-okp
                                   fn-replay-complete-retention
                                   fn-retain-release fn-replay-advance-txid)))))

; fn-replay-apply-record with the article's prepare through the tries.
(defun fn-rii-apply-record (node record ix)
  (declare (xargs :guard (and (fn-node-statep node) (true-listp record)
                              (fn-rii-okp ix node))
                  :verify-guards nil))
  (if (fn-store-retention-event-p record)
      (fn-rii-apply-retention-event node record ix)
    (if (or (fn-stxe-p record) (fn-stxk-p record) (fn-cpe-eventp record)
            (fn-th-topic-eventp record))
        (if (and (or (fn-cpe-eventp record) (fn-th-topic-eventp record))
                 (not (null (fn-node-stage node))))
            nil
          (fn-replay-apply-identity-neutral node record))
      (if (not (null (fn-node-stage node)))
          nil
        (let* ((article (if (fn-hstxa-p record)
                            (fn-replay-composite-held record)
                          record))
               (advanced (fn-replay-advance-txid node (fn-store-event-txid record))))
          (if (not (equal (fn-state-next-txid (fn-node-acceptance advanced))
                          (fn-store-event-txid record)))
              nil
            (if (not (fn-held-p article)) nil
              (let ((prepared
                     (fn-rii-node-prepare advanced
                                          (fn-record-generation article)
                                          (fn-record-msgid article)
                                          (fn-record-payload article)
                                          (fn-record-groups article)
                                          (fn-record-obligation-id article)
                                          (fn-record-content-subject article)
                                          (fn-record-release-evidence article)
                                          (fn-record-charge article)
                                          (fn-record-stamp article)
                                          ix)))
                (if (not (fn-node-pending-matchesp
                          prepared
                          (fn-record-txid article)
                          (fn-record-generation article)))
                    nil
                  (fn-node-complete prepared
                                    (fn-record-txid article)
                                    (fn-record-generation article)
                                    :durable))))))))))

(defthm fn-rii-apply-record-is-apply-record
  (implies (fn-rii-okp ix node)
           (equal (fn-rii-apply-record node record ix)
                  (fn-replay-apply-record node record)))
  :hints (("Goal" :in-theory (e/d (fn-rii-apply-record fn-replay-apply-record)
                                  (fn-node-statep fn-node-prepare
                                   fn-rii-okp fn-replay-advance-txid
                                   fn-replay-apply-retention-event
                                   fn-rii-apply-retention-event
                                   fn-node-pending-matchesp fn-node-complete
                                   fn-replay-apply-identity-neutral
                                   fn-replay-composite-held
                                   fn-store-event-p fn-held-p fn-stxe-p
                                   fn-stxk-p fn-hstxa-p fn-store-retention-event-p
                                   fn-cpe-eventp fn-th-topic-eventp)))))

(defthm fn-rii-admissiblep-has-charge-and-state
  (implies (fn-retain-admissiblep s id subject kind evidence charge)
           (and (posp charge) (fn-retain-statep s)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-retain-admissiblep))))

(verify-guards fn-rii-apply-retention-event
  :hints (("Goal"
           :use ((:instance fn-nrt-node-admit-preserves-statep
                            (node (fn-replay-advance-txid
                                   node (fn-store-event-txid event)))
                            (id (fn-store-event-obligation-id event))
                            (subject (fn-store-event-subject event))
                            (kind :forward)
                            (evidence (fn-store-event-evidence event))
                            (charge (fn-store-event-charge event)))
                 (:instance fn-nrt-node-release-preserves-statep
                            (node (fn-replay-advance-txid
                                   node (fn-store-event-txid event)))
                            (id (fn-store-event-obligation-id event))
                            (subject (fn-store-event-subject event))
                            (kind :forward)
                            (evidence (fn-store-event-evidence event)))
                 (:instance fn-nrt-node-statep-retention
                            (node (fn-replay-advance-txid
                                   node (fn-store-event-txid event))))
                 (:instance fn-replay-retain-pins-typed
                            (retention
                             (fn-node-retention
                              (fn-replay-advance-txid
                               node (fn-store-event-txid event))))))
           :in-theory (e/d (fn-replay-node-with-retention
                            fn-nrt-node-with-retention)
                           (fn-rii-known-okp)))))

(verify-guards fn-rii-apply-record
  :hints (("Goal" :in-theory (disable fn-rii-known-okp))))

(in-theory (disable fn-rii-apply-retention-event fn-rii-apply-record))

; -----------------------------------------------------------------------------
; 5. The tries after one step.

; The id trie of a ledger, built once: every pin's id over every release's.
(defun fn-rii-kbuild-releases (releases)
  (declare (xargs :guard t))
  (if (consp releases)
      (fn-rii-id-put (fn-retain-release-id (car releases))
                     (fn-rii-kbuild-releases (cdr releases)))
    nil))

(defun fn-rii-kbuild-pins (pins base)
  (declare (xargs :guard t))
  (if (consp pins)
      (fn-rii-id-put (fn-retain-obligation-id (car pins))
                     (fn-rii-kbuild-pins (cdr pins) base))
    base))

(defun fn-rii-kbuild (retention)
  (declare (xargs :guard t))
  (fn-rii-kbuild-pins (fn-retain-pins retention)
                      (fn-rii-kbuild-releases (fn-retain-releases retention))))

(local
 (defthm fn-rii-id-hasp-of-kbuild-releases
   (implies (stringp x)
            (iff (fn-rii-id-hasp x (fn-rii-kbuild-releases releases))
                 (fn-rii-release-hasp x releases)))))

(local
 (defthm fn-rii-id-hasp-of-kbuild-pins
   (implies (stringp x)
            (iff (fn-rii-id-hasp x (fn-rii-kbuild-pins pins base))
                 (or (fn-rii-pin-hasp x pins) (fn-rii-id-hasp x base))))))

(local
 (defthm fn-rii-id-hasp-booleanp
   (booleanp (fn-rii-id-hasp x trie))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-rii-id-hasp)))))

(local
 (defthm fn-rii-knownp-booleanp
   (booleanp (fn-rii-knownp x retention))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-rii-knownp)))))

(defthm fn-rii-kbuild-is-known-okp
  (fn-rii-known-okp (fn-rii-kbuild retention) retention)
  :hints (("Goal" :in-theory (enable fn-rii-known-okp fn-rii-knownp))))

; The tries built from any node, once: the resume of a checkpoint's fold.
(defun fn-rii-ix-of (node)
  (declare (xargs :guard t))
  (cons (fn-mxc-build (fn-state-articles (fn-node-acceptance node)))
        (fn-rii-kbuild (fn-node-retention node))))

(defthm fn-rii-okp-of-ix-of
  (fn-rii-okp (fn-rii-ix-of node) node)
  :hints (("Goal" :in-theory (disable fn-rii-known-okp fn-rii-kbuild))))

; A release moves a known id from the pins to the releases.
(local
 (defthm fn-rii-matching-pin-is-held
   (implies (fn-retain-matching-releasep (fn-retain-find-id id pins)
                                         id subject kind evidence)
            (fn-rii-pin-hasp id pins))
   :hints (("Goal" :induct (fn-retain-find-id id pins)
            :in-theory (enable fn-retain-find-id fn-retain-matching-releasep)))))

(local
 (defthm fn-rii-pin-hasp-of-remove-id
   (implies (fn-rii-pin-hasp id pins)
            (iff (or (equal x id)
                     (fn-rii-pin-hasp x (fn-retain-remove-id id pins)))
                 (fn-rii-pin-hasp x pins)))
   :hints (("Goal" :induct (fn-retain-remove-id id pins)
            :in-theory (enable fn-retain-remove-id)))))

(defthm fn-rii-release-keeps-known
  (equal (fn-rii-knownp x (fn-retain-release s id subject kind evidence))
         (fn-rii-knownp x s))
  :hints (("Goal" :in-theory (e/d (fn-retain-release fn-rii-knownp)
                                  (fn-retain-matching-releasep
                                   fn-retain-statep))
           :use ((:instance fn-rii-pin-hasp-of-remove-id
                            (pins (fn-retain-pins s)))
                 (:instance fn-rii-matching-pin-is-held
                            (pins (fn-retain-pins s)))))))

(defun fn-rii-release-event-p (event)
  (declare (xargs :guard t))
  (and (fn-store-retention-event-p event)
       (not (equal (fn-store-event-kind event) :undertake))))

; A replayed release keeps what the ledger knows.
(defthm fn-rii-release-step-keeps-known
  (implies (and (fn-rii-release-event-p event)
                (consp (fn-replay-apply-record node event)))
           (equal (fn-rii-knownp x (fn-node-retention
                                    (fn-replay-apply-record node event)))
                  (fn-rii-knownp x (fn-node-retention node))))
  :hints (("Goal" :in-theory (e/d (fn-replay-apply-record
                                   fn-replay-apply-retention-event
                                   fn-replay-complete-retention
                                   fn-replay-node-with-retention)
                                  (fn-retain-release fn-node-statep
                                   fn-retain-matching-releasep
                                   fn-retain-admissiblep fn-retain-admit
                                   fn-replay-advance-txid)))))

(in-theory (disable fn-rii-release-event-p))

; The tries after a step from OLD to NEW.  RELEASE is the replayed event (nil
; for a configuration record): a release leaves the id trie.
(defun fn-rii-ix-next (ix old new release)
  (declare (xargs :guard t))
  (let* ((r0 (fn-node-retention old))
         (r1 (fn-node-retention new))
         (p0 (fn-retain-pins r0))
         (p1 (fn-retain-pins r1))
         (ktrie (fn-ag-cdr ix)))
    (cons (fn-mxc-refresh (fn-ag-car ix)
                          (fn-state-articles (fn-node-acceptance old))
                          (fn-state-articles (fn-node-acceptance new)))
          (cond ((equal r1 r0) ktrie)
                ((and (consp p1)
                      (equal (cdr p1) p0)
                      (equal (fn-retain-releases r1) (fn-retain-releases r0)))
                 (fn-rii-id-put (fn-retain-obligation-id (car p1)) ktrie))
                ((fn-rii-release-event-p release) ktrie)
                (t (fn-rii-kbuild r1))))))

(local
 (defthm fn-rii-known-okp-of-pin-cons
   (implies (and (fn-rii-known-okp k r0)
                 (consp (fn-retain-pins r1))
                 (equal (cdr (fn-retain-pins r1)) (fn-retain-pins r0))
                 (equal (fn-retain-releases r1) (fn-retain-releases r0)))
            (fn-rii-known-okp
             (fn-rii-id-put (fn-retain-obligation-id (car (fn-retain-pins r1))) k)
             r1))
   :hints (("Goal"
            :expand ((fn-rii-known-okp
                      (fn-rii-id-put (fn-retain-obligation-id
                                      (car (fn-retain-pins r1))) k)
                      r1)
                     (fn-rii-pin-hasp
                      (fn-rii-known-okp-witness
                       (fn-rii-id-put (fn-retain-obligation-id
                                       (car (fn-retain-pins r1))) k)
                       r1)
                      (fn-retain-pins r1)))
            :in-theory (e/d (fn-rii-knownp) (fn-rii-known-okp-necc))
            :use ((:instance fn-rii-known-okp-necc
                             (ktrie k) (retention r0)
                             (id (fn-rii-known-okp-witness
                                  (fn-rii-id-put (fn-retain-obligation-id
                                                  (car (fn-retain-pins r1))) k)
                                  r1))))))))

(local
 (defthm fn-rii-known-okp-of-release-step
   (implies (and (fn-rii-known-okp k (fn-node-retention node))
                 (fn-rii-release-event-p event)
                 (consp (fn-replay-apply-record node event)))
            (fn-rii-known-okp k (fn-node-retention
                                 (fn-replay-apply-record node event))))
   :hints (("Goal"
            :expand ((fn-rii-known-okp k (fn-node-retention
                                          (fn-replay-apply-record node event))))
            :in-theory (disable fn-rii-known-okp-necc fn-replay-apply-record)
            :use ((:instance fn-rii-known-okp-necc
                             (ktrie k) (retention (fn-node-retention node))
                             (id (fn-rii-known-okp-witness
                                  k (fn-node-retention
                                     (fn-replay-apply-record node event)))))
                  (:instance fn-rii-release-step-keeps-known
                             (x (fn-rii-known-okp-witness
                                 k (fn-node-retention
                                    (fn-replay-apply-record node event))))))))))

; The relation after a step: always, except that a release's step must be the
; replay's step from OLD.
(defthm fn-rii-ix-next-keeps-okp
  (implies (and (fn-rii-okp ix old)
                (or (not (fn-rii-release-event-p release))
                    (and (consp (fn-replay-apply-record old release))
                         (equal new (fn-replay-apply-record old release)))))
           (fn-rii-okp (fn-rii-ix-next ix old new release) new))
  :hints (("Goal" :in-theory (e/d (fn-midx-concrete-refresh-is-refresh)
                                  (fn-rii-known-okp fn-rii-kbuild
                                   fn-replay-apply-record fn-mxc-refresh
                                   fn-midx-build fn-midx-refresh))
           :use ((:instance fn-midx-refresh-preserves-correspondence
                            (index (car ix))
                            (old-articles (fn-state-articles (fn-node-acceptance old)))
                            (new-articles (fn-state-articles (fn-node-acceptance new))))))
          (and stable-under-simplificationp
               '(:in-theory (e/d (fn-midx-correspondencep
                                  fn-midx-concrete-refresh-is-refresh)
                                 (fn-rii-known-okp fn-rii-kbuild
                                  fn-replay-apply-record fn-mxc-refresh
                                  fn-midx-build fn-midx-refresh))))))

(in-theory (disable fn-rii-ix-next fn-rii-okp))

; -----------------------------------------------------------------------------
; 6. The configuration fold, carrying the tries.

; fn-cpr-apply-event through the twin step.
(defun fn-rii-cpr-apply-event (cn event ix)
  (declare (xargs :guard (and (fn-cnode-statep cn)
                              (fn-rii-okp ix (fn-cnode-node cn)))
                  :verify-guards nil))
  (if (and (mbe :logic (fn-cnode-statep cn) :exec t)
           (fn-store-event-p event)
           (fn-cpr-event-servedp cn event))
      (let ((next (fn-rii-apply-record (fn-cnode-node cn) event ix)))
        (if (and (consp next)
                 (mbe :logic (fn-node-statep next) :exec t))
            (fn-cnode-make next (fn-cnode-config cn))
          nil))
    nil))

(defthm fn-rii-cpr-apply-event-is-cpr-apply-event
  (implies (fn-rii-okp ix (fn-cnode-node cn))
           (equal (fn-rii-cpr-apply-event cn event ix)
                  (fn-cpr-apply-event cn event)))
  :hints (("Goal" :in-theory (e/d (fn-rii-cpr-apply-event fn-cpr-apply-event)
                                  (fn-cnode-statep fn-node-statep
                                   fn-store-event-p fn-cpr-event-servedp
                                   fn-replay-apply-record)))))

(verify-guards fn-rii-cpr-apply-event
  :hints (("Goal"
           :use ((:instance fn-replay-apply-record-non-nil-is-node-state
                            (node (fn-cnode-node cn)) (record event)))
           :in-theory (e/d (fn-cnode-statep)
                           (fn-cpr-event-servedp fn-held-p fn-hstxa-p
                            fn-store-event-p fn-node-statep
                            fn-replay-apply-record
                            fn-replay-apply-record-non-nil-is-node-state)))))

(in-theory (disable fn-rii-cpr-apply-event))

(local
 (defthm fn-rii-node-of-cpr-apply-event
   (implies (consp (fn-cpr-apply-event cn event))
            (and (consp (fn-replay-apply-record (fn-cnode-node cn) event))
                 (equal (fn-cnode-node (fn-cpr-apply-event cn event))
                        (fn-replay-apply-record (fn-cnode-node cn) event))))
   :hints (("Goal" :in-theory (e/d (fn-cpr-apply-event)
                                   (fn-cnode-statep fn-node-statep
                                    fn-store-event-p fn-cpr-event-servedp
                                    fn-replay-apply-record))))))

; fn-sco-cpr-prefix carrying IX beside CN.
(defun fn-rii-sco-cpr-prefix (cn configs events config-sequence event-sequence ix)
  (declare (xargs :guard (and (fn-cnode-statep cn)
                              (fn-rii-okp ix (fn-cnode-node cn)))
                  :verify-guards nil
                  :measure (+ (len configs) (len events))))
  (if (not (consp events))
      (fn-sco-paused cn config-sequence event-sequence)
    (let ((position (+ (nfix config-sequence) (nfix event-sequence))))
      (if (mbe :logic (not (fn-cnode-statep cn)) :exec nil)
          (fn-replay-fault cn position :invalid-node)
        (if (fn-cpr-config-firstp configs events)
            (let* ((record (car configs))
                   (txid (fn-cfg-record-txid record))
                   (node (fn-cnode-node cn)))
              (cond ((not (fn-cfg-recordp record))
                     (fn-replay-fault cn position :invalid-config-record))
                    ((not (equal (fn-cfg-record-sequence record) config-sequence))
                     (fn-replay-fault cn position :config-sequence))
                    ((not (fn-replay-advance-okp node txid))
                     (fn-replay-fault cn position :config-txid))
                    (t (let ((at (fn-cnode-make
                                  (fn-replay-advance-txid node txid)
                                  (fn-cnode-config cn))))
                         (if (mbe :logic (not (fn-cnode-statep at)) :exec nil)
                             (fn-replay-fault cn position :invalid-node)
                           (if (not (mbe :logic (fn-cnode-record-acceptablep
                                              at record (fn-cnode-line-ceiling))
                                         :exec (fn-cnode-carried-acceptablep
                                                at record (fn-cnode-line-ceiling))))
                               (fn-replay-fault cn position :config-refusal)
                             (let ((next (fn-cnode-apply-config
                                          at record (fn-cnode-line-ceiling))))
                               (fn-rii-sco-cpr-prefix
                                next (cdr configs) events
                                (+ 1 (nfix config-sequence)) event-sequence
                                (fn-rii-ix-next ix node (fn-cnode-node next)
                                                nil)))))))))
          (let ((event (car events)))
            (cond ((not (fn-store-event-p event))
                   (fn-replay-fault cn position :invalid-event))
                  ((not (equal (fn-store-event-sequence event) event-sequence))
                   (fn-replay-fault cn position :event-sequence))
                  (t (let ((next (fn-rii-cpr-apply-event cn event ix)))
                       (if (mbe :logic (not (fn-cnode-statep next))
                                :exec (not (consp next)))
                           (fn-replay-fault cn position :event-refusal)
                         (fn-rii-sco-cpr-prefix
                          next configs (cdr events)
                          config-sequence (+ 1 (nfix event-sequence))
                          (fn-rii-ix-next ix (fn-cnode-node cn)
                                          (fn-cnode-node next) event))))))))))))

(local
 (defthm fn-rii-not-release-of-nil
   (not (fn-rii-release-event-p nil))
   :hints (("Goal" :in-theory (enable fn-rii-release-event-p)))))

; KEYSTONE (the fold).  Under the relation, the fold carrying the tries is
; the checkpoint's fold, for every configuration and event history.
(defthm fn-rii-sco-cpr-prefix-is-sco-cpr-prefix
  (implies (fn-rii-okp ix (fn-cnode-node cn))
           (equal (fn-rii-sco-cpr-prefix cn configs events config-sequence
                                         event-sequence ix)
                  (fn-sco-cpr-prefix cn configs events config-sequence
                                     event-sequence)))
  :hints (("Goal" :induct (fn-rii-sco-cpr-prefix cn configs events
                                                 config-sequence event-sequence ix)
           :in-theory (e/d (fn-sco-cpr-prefix)
                           (fn-cnode-statep fn-cpr-config-firstp
                            fn-cpr-apply-event fn-cnode-apply-config
                            fn-cnode-record-acceptablep fn-cnode-carried-acceptablep
                            fn-cfg-recordp fn-store-event-p
                            fn-replay-apply-record fn-replay-advance-okp
                            fn-replay-advance-txid)))))

(local
 (defthm fn-rii-cnode-statep-has-node-statep
   (implies (fn-cnode-statep cn) (fn-node-statep (fn-cnode-node cn)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-cnode-statep)))))

(verify-guards fn-rii-sco-cpr-prefix
  :hints (("Goal"
           :use ((:instance fn-cpr-apply-event-statep-iff-consp
                            (event (car events)))
                 (:instance fn-cnode-advanced-node-is-configured
                            (txid (fn-cfg-record-txid (car configs))))
                 (:instance fn-cnode-record-acceptablep-is-the-carried-check
                            (cn (fn-cnode-make
                                 (fn-replay-advance-txid
                                  (fn-cnode-node cn)
                                  (fn-cfg-record-txid (car configs)))
                                 (fn-cnode-config cn)))
                            (record (car configs))
                            (ceiling (fn-cnode-line-ceiling))))
           :in-theory (e/d (fn-cnode-apply-config-preserves-state)
                           (fn-cnode-statep fn-cpr-config-firstp fn-cpr-apply-event
                            fn-cnode-apply-config fn-cnode-record-acceptablep
                            fn-cfg-recordp fn-store-event-p
                            fn-replay-apply-record)))))

; fn-sco-cpr-resume through the twin: the tries are built from the paused
; node once, and only when there is a suffix to replay.
(defun fn-rii-sco-cpr-resume (r configs events)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-sco-pausedp r)
      (let ((cs (fn-sco-at 2 r)) (cn (fn-sco-at 1 r)) (es (fn-sco-at 3 r)))
        (cond ((not (consp events)) (fn-sco-paused cn cs es))
              ((fn-cnode-statep cn)
               (fn-rii-sco-cpr-prefix cn (fn-sco-nthcdr (nfix cs) configs) events
                                      cs es (fn-rii-ix-of (fn-cnode-node cn))))
              (t (fn-sco-cpr-prefix-unconfigured cn events cs es))))
    r))

(defthm fn-rii-sco-cpr-resume-is-sco-cpr-resume
  (equal (fn-rii-sco-cpr-resume r configs events)
         (fn-sco-cpr-resume r configs events))
  :hints (("Goal" :in-theory (e/d (fn-rii-sco-cpr-resume fn-sco-cpr-resume)
                                  (fn-cnode-statep fn-rii-ix-of fn-sco-at
                                   fn-sco-nthcdr))
           :expand ((:free (cf cs es)
                     (fn-sco-cpr-prefix (fn-sco-at 1 r) cf events cs es))))))

(verify-guards fn-rii-sco-cpr-resume
  :hints (("Goal" :in-theory (disable fn-cnode-statep fn-rii-ix-of))))

; The extension the host calls (fn-sco-extend with the fold above).
(defun fn-rii-sco-extend (c configs suffix)
  (declare (xargs :guard t :verify-guards nil))
  (let ((records (true-list-fix (fn-sco-records c))))
    (fn-sco-make (append records suffix)
                 (fn-rii-sco-cpr-resume (fn-sco-cpr c) configs suffix)
                 (fn-replay-identity-loop suffix (fn-sco-identity c))
                 (fn-sco-consumer-resume (fn-sco-consumer c) suffix
                                         (len records))
                 (fn-th-prefix-loop (fn-sco-topic c) suffix)
                 (fn-cei-build-aux suffix (len records)
                                   (fn-sco-event-index c)))))

; KEYSTONE (1).  The host's extension is the checkpoint extension, with no
; hypothesis: host/store-node-host.lisp fn-store-sn-recover and
; fn-store-sn-recover-from-checkpoint, host/owner-host.lisp fn-owner-recover
; and fn-owner-recover-from-checkpoint.
(defthm fn-rii-sco-extend-is-sco-extend
  (equal (fn-rii-sco-extend c configs suffix)
         (fn-sco-extend c configs suffix))
  :hints (("Goal" :in-theory (e/d (fn-rii-sco-extend fn-sco-extend)
                                  (fn-rii-sco-cpr-resume fn-sco-cpr-resume
                                   fn-replay-identity-loop fn-sco-consumer-resume
                                   fn-th-prefix-loop fn-cei-build-aux)))))

(verify-guards fn-rii-sco-extend)

; -----------------------------------------------------------------------------
; 7. The history recognizer, one dispatch per record.

; The four readings of a retained row come from one dispatch:
; books/store-event-fields.lisp fn-event-fields with WIREP nil
; (fn-event-fields-of-rows-is-the-dispatchers; the pack-chain link check reads
; the wire vocabulary through the same function, PKT-721).

(local
 (defthm fn-rii-event-txid-is-natural
   (implies (fn-store-event-p record) (natp (fn-store-event-txid record)))
   :rule-classes (:rewrite :forward-chaining :type-prescription)
   :hints (("Goal" :in-theory (disable fn-store-event-p)))))

; fn-sf-record-listp reading each record's fields in one dispatch.
(defun fn-rii-sf-record-listp (records sequence lower frontier)
  (declare (xargs :guard (and (natp sequence) (natp lower) (natp frontier))
                  :verify-guards nil))
  (if (consp records)
      (let* ((f (fn-event-fields (car records) nil))
             (txid (nth 2 f)))
        (and (nth 0 f)
             (equal (nth 1 f) sequence)
             (<= lower txid)
             (< txid frontier)
             (equal (nth 3 f) txid)
             (fn-rii-sf-record-listp (cdr records) (1+ sequence)
                                     (1+ txid) frontier)))
    (null records)))

(defthm fn-rii-sf-record-listp-is-sf-record-listp
  (equal (fn-rii-sf-record-listp records sequence lower frontier)
         (fn-sf-record-listp records sequence lower frontier))
  :hints (("Goal" :induct (fn-rii-sf-record-listp records sequence lower frontier)
           :in-theory (e/d (fn-sf-record-listp)
                           (fn-store-event-p fn-store-event-sequence
                            fn-store-event-txid fn-store-event-generation)))))

(verify-guards fn-rii-sf-record-listp
  :hints (("Goal" :in-theory (disable fn-store-event-p fn-store-event-sequence
                                      fn-store-event-txid
                                      fn-store-event-generation))))

(in-theory (disable fn-rii-sf-record-listp))

; fn-sf-statep, fn-sn-statep and fn-sn-observed-historyp over the twin.
(defun fn-rii-sf-statep (s)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-sf-shapep s)
       (fn-sf-phasep (fn-sf-phase s))
       (fn-record-uint32p (fn-sf-frontier s))
       (fn-rii-sf-record-listp (fn-sf-records s) 0 0 (fn-sf-frontier s))
       (fn-sf-success-listp (fn-sf-successes s) (fn-sf-records s))
       (natp (fn-sf-barriers s))
       (<= (fn-sf-barriers s) *fn-sf-recovery-barrier-count*)
       (fn-sf-phase-shapep s)))

(defthm fn-rii-sf-statep-is-sf-statep
  (equal (fn-rii-sf-statep s) (fn-sf-statep s))
  :hints (("Goal" :in-theory (e/d (fn-sf-statep)
                                  (fn-sf-record-listp fn-sf-phase-shapep
                                   fn-sf-success-listp fn-sf-phasep)))))

(verify-guards fn-rii-sf-statep
  :hints (("Goal" :use ((:instance fn-rii-sf-statep-is-sf-statep))
           :in-theory (e/d (fn-sf-statep)
                           (fn-rii-sf-statep-is-sf-statep
                            fn-sf-phase-shapep fn-sf-success-listp)))))

(in-theory (disable fn-rii-sf-statep))

(defun fn-rii-sn-statep (s)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-sn-shapep s)
       (fn-string-listp (fn-sn-groups s))
       (fn-no-duplicatesp (fn-sn-groups s))
       (natp (fn-sn-capacity s))
       (fn-rii-sf-statep (fn-sn-files s))
       (fn-node-statep (fn-sn-node s))
       (fn-prin-keyringp (fn-sn-keyring s))
       (natp (fn-sn-keyring-generation s))
       (fn-sn-verdict-listp (fn-sn-verdicts s))
       (fn-sn-keyring-snapshot-listp (fn-sn-keyring-snapshots s))
       (natp (fn-sn-identity-next s))))

(defthm fn-rii-sn-statep-is-sn-statep
  (equal (fn-rii-sn-statep s) (fn-sn-statep s))
  :hints (("Goal" :in-theory (e/d (fn-sn-statep)
                                  (fn-sf-statep fn-node-statep
                                   fn-prin-keyringp fn-sn-verdict-listp
                                   fn-sn-keyring-snapshot-listp)))))

(verify-guards fn-rii-sn-statep)

(in-theory (disable fn-rii-sn-statep))

(defun fn-rii-observed-historyp (frontier records)
  (declare (xargs :guard t))
  (and (fn-record-uint32p frontier)
       (fn-rii-sf-record-listp records 0 0 frontier)))

(defthm fn-rii-observed-historyp-is-observed-historyp
  (equal (fn-rii-observed-historyp frontier records)
         (fn-sn-observed-historyp frontier records))
  :hints (("Goal" :in-theory (enable fn-sn-observed-historyp))))

(in-theory (disable fn-rii-observed-historyp))

; fn-sco-finalize-from with the two recognizer passes over the twin.
(defun fn-rii-sco-finalize-from (replayed c configs frontier)
  (declare (xargs :guard t :verify-guards nil))
  (let ((events (fn-sco-records c)))
    (if (or (null configs)
            (not (fn-rii-observed-historyp frontier events)))
        (fn-sn-open-error :history)
      (if (not (equal (fn-replay-result-kind replayed) :ok))
          (fn-sn-open-error :replay)
        (let* ((cn (fn-replay-result-node replayed))
               (node (fn-cnode-node cn)))
          (if (not (and (fn-cnode-statep cn)
                        (fn-replay-advance-okp node frontier)))
              (fn-sn-open-error :frontier)
            (let* ((advanced (fn-replay-advance-txid node frontier))
                   (config (fn-cnode-config cn))
                   (identity (fn-sco-identity c))
                   (consumer (fn-sco-consumer c))
                   (topic (fn-sco-topic c))
                   (files (fn-sf-make :recovering frontier nil events
                                      nil nil nil 0))
                   (seed (fn-sn-observed-seed
                          (fn-cnode-domain-of config)
                          (fn-cfg-capacity (fn-cfg-value config))
                          frontier events))
                   (opened (fn-sn-with-event-index
                            (fn-sn-with-topic
                             (fn-sn-with-consumer
                              (fn-cpo-install
                               (fn-sn-update-replayed
                                seed files advanced
                                (fn-stx-index-of-store (fn-stx-store advanced) nil)
                                identity)
                               (fn-cnode-make advanced config) configs)
                              (fn-cp-nth 1 consumer))
                             topic)
                            ; field 13 retired (lane history-columns-3)
                            nil)))
              (if (and (equal (fn-stxk-context-kind identity) :ok)
                       (consp consumer) (eq (car consumer) :ok)
                       (eq (fn-th-at 0 topic) :ok)
                       (fn-rii-sn-statep opened))
                  (fn-sn-open-ok opened)
                (fn-sn-open-error :identity)))))))))

(defthm fn-rii-sco-finalize-from-is-sco-finalize-from
  (equal (fn-rii-sco-finalize-from replayed c configs frontier)
         (fn-sco-finalize-from replayed c configs frontier))
  :hints (("Goal" :in-theory (e/d (fn-rii-sco-finalize-from fn-sco-finalize-from)
                                  (fn-sn-statep fn-cnode-statep
                                   fn-replay-advance-okp fn-sn-observed-historyp
                                   fn-sn-with-event-index fn-sn-with-topic
                                   fn-sn-with-consumer fn-cpo-install
                                   fn-sn-update-replayed fn-sn-observed-seed
                                   fn-stx-index-of-store fn-replay-advance-txid)))))

(verify-guards fn-rii-sco-finalize-from
  :hints (("Goal"
           :in-theory (e/d (fn-cnode-statep)
                           (fn-cpr-replay fn-cpr-loop fn-sn-statep
                            fn-sco-cpr-finish fn-sco-cpr-prefix)))))

(in-theory (disable fn-rii-sco-finalize-from))

; -----------------------------------------------------------------------------
; 7a. The open checks the configured node ONCE (lane snapshot-open-2).
;
; fn-sco-finalize-from checks the fold's node with three whole-state
; recognizers (fn-cnode-statep, fn-replay-advance-okp's fn-node-statep, and
; fn-sn-statep's fn-node-statep of the advanced node) and walks the history
; twice (fn-sn-observed-historyp, and fn-sn-statep's fn-sf-record-listp over
; the same records and frontier).  Measured at 40k articles each node check
; is ~0.24 s and grows with the store.  When the fold's result is the
; drain of a paused fold (fn-sco-cpr-finish), a successful result's node is
; configured (fn-cpr-loop-ok-is-configured: the drain's logic starts by
; checking it), so every one of those checks is implied: the node's by
; fn-replay-advance-preserves-node-statep, the files' records by the
; history recognizer already run at the top.  fn-rii-sco-finalize-configured
; is the finalize with those checks dropped, EQUAL to fn-rii-sco-finalize-from
; whenever a successful result's node is configured
; (fn-rii-sco-finalize-configured-is-finalize-from), and the open below
; calls it exactly then.

(defun fn-rii-sf-statep-carried (s)
  (declare (xargs :guard (fn-rii-observed-historyp (fn-sf-frontier s) (fn-sf-records s))
                  :verify-guards nil))
  (and (fn-sf-shapep s)
       (fn-sf-phasep (fn-sf-phase s))
       (fn-record-uint32p (fn-sf-frontier s))
       (fn-sf-success-listp (fn-sf-successes s) (fn-sf-records s))
       (natp (fn-sf-barriers s))
       (<= (fn-sf-barriers s) *fn-sf-recovery-barrier-count*)
       (fn-sf-phase-shapep s)))

(defthm fn-rii-sf-statep-carried-is-sf-statep
  (implies (fn-rii-sf-record-listp (fn-sf-records s) 0 0 (fn-sf-frontier s))
           (equal (fn-rii-sf-statep-carried s) (fn-rii-sf-statep s)))
  :hints (("Goal" :in-theory (e/d (fn-rii-sf-statep)
                                  (fn-rii-sf-statep-is-sf-statep fn-sf-phase-shapep fn-sf-success-listp fn-sf-phasep)))))

(verify-guards fn-rii-sf-statep-carried
  :hints (("Goal" :in-theory (e/d (fn-rii-observed-historyp)
                                  (fn-rii-observed-historyp-is-observed-historyp
                                   fn-sf-phase-shapep fn-sf-success-listp)))))

(defun fn-rii-sn-statep-carried (s)
  (declare (xargs :guard (fn-rii-observed-historyp (fn-sf-frontier (fn-sn-files s))
                                                   (fn-sf-records (fn-sn-files s)))
                  :verify-guards nil))
  (and (fn-sn-shapep s)
       (fn-string-listp (fn-sn-groups s))
       (fn-no-duplicatesp (fn-sn-groups s))
       (natp (fn-sn-capacity s))
       (fn-rii-sf-statep-carried (fn-sn-files s))
       (fn-prin-keyringp (fn-sn-keyring s))
       (natp (fn-sn-keyring-generation s))
       (fn-sn-verdict-listp (fn-sn-verdicts s))
       (fn-sn-keyring-snapshot-listp (fn-sn-keyring-snapshots s))
       (natp (fn-sn-identity-next s))))

(verify-guards fn-rii-sn-statep-carried)

(defthm fn-rii-sn-statep-carried-is-sn-statep
  (implies (and (fn-node-statep (fn-sn-node s))
                (fn-rii-sf-record-listp (fn-sf-records (fn-sn-files s)) 0 0
                                        (fn-sf-frontier (fn-sn-files s))))
           (equal (fn-rii-sn-statep-carried s) (fn-rii-sn-statep s)))
  :hints (("Goal" :in-theory (e/d (fn-rii-sn-statep)
                                  (fn-rii-sn-statep-is-sn-statep fn-rii-sf-statep
                                   fn-rii-sf-statep-carried
                                   fn-node-statep fn-prin-keyringp fn-sn-verdict-listp
                                   fn-sn-keyring-snapshot-listp)))))

(defun fn-rii-advance-idlep (node recorded-txid)
  (declare (xargs :guard (fn-node-statep node) :verify-guards nil))
  (and (natp recorded-txid)
       (null (fn-node-stage node))
       (null (fn-state-pending (fn-node-acceptance node)))
       (equal (fn-state-fenced (fn-node-acceptance node)) nil)
       (<= (fn-state-next-txid (fn-node-acceptance node)) recorded-txid)))

(verify-guards fn-rii-advance-idlep
  :hints (("Goal" :in-theory (enable fn-node-statep fn-statep))))

(defthm fn-rii-advance-idlep-is-advance-okp
  (implies (fn-node-statep node)
           (equal (fn-rii-advance-idlep node recorded-txid)
                  (fn-replay-advance-okp node recorded-txid)))
  :hints (("Goal" :in-theory (e/d (fn-replay-advance-okp) (fn-node-statep)))))
(defthm fn-rii-opened-node-and-files
  (let ((opened (fn-sn-with-event-index
                 (fn-sn-with-topic
                  (fn-sn-with-consumer
                   (fn-cpo-install
                    (fn-sn-update-replayed seed files advanced index identity)
                    (fn-cnode-make advanced config) configs)
                   consumer)
                  topic)
                 event-index)))
    (and (equal (fn-sn-node opened) advanced)
         (equal (fn-sn-files opened) files)))
  :hints (("Goal" :in-theory (e/d (fn-sn-with-event-index fn-sn-with-topic
                                   fn-sn-with-consumer fn-cpo-install
                                   fn-sn-update-replayed fn-cnode-node fn-cnode-make)
                                  (fn-sn-node fn-sn-files fn-sn-make-v6
                                   fn-sn-with-configuration)))))
(defun fn-rii-sco-finalize-configured (replayed c configs frontier)
  (declare (xargs :guard (or (not (equal (fn-replay-result-kind replayed) :ok))
                             (fn-cnode-statep (fn-replay-result-node replayed)))
                  :verify-guards nil))
  (let ((events (fn-sco-records c)))
    (if (or (null configs)
            (not (fn-rii-observed-historyp frontier events)))
        (fn-sn-open-error :history)
      (if (not (equal (fn-replay-result-kind replayed) :ok))
          (fn-sn-open-error :replay)
        (let* ((cn (fn-replay-result-node replayed))
               (node (fn-cnode-node cn)))
          (if (not (fn-rii-advance-idlep node frontier))
              (fn-sn-open-error :frontier)
            (let* ((advanced (fn-replay-advance-txid node frontier))
                   (config (fn-cnode-config cn))
                   (identity (fn-sco-identity c))
                   (consumer (fn-sco-consumer c))
                   (topic (fn-sco-topic c))
                   (files (fn-sf-make :recovering frontier nil events
                                      nil nil nil 0))
                   (seed (fn-sn-observed-seed
                          (fn-cnode-domain-of config)
                          (fn-cfg-capacity (fn-cfg-value config))
                          frontier events))
                   (opened (fn-sn-with-event-index
                            (fn-sn-with-topic
                             (fn-sn-with-consumer
                              (fn-cpo-install
                               (fn-sn-update-replayed
                                seed files advanced
                                (fn-stx-index-of-store (fn-stx-store advanced) nil)
                                identity)
                               (fn-cnode-make advanced config) configs)
                              (fn-cp-nth 1 consumer))
                             topic)
                            (fn-sco-event-index c))))
              (if (and (equal (fn-stxk-context-kind identity) :ok)
                       (consp consumer) (eq (car consumer) :ok)
                       (eq (fn-th-at 0 topic) :ok)
                       (fn-rii-sn-statep-carried opened))
                  (fn-sn-open-ok opened)
                (fn-sn-open-error :identity)))))))))

(defthm fn-rii-sco-finalize-configured-is-finalize-from
  (implies (or (not (equal (fn-replay-result-kind replayed) :ok))
               (fn-cnode-statep (fn-replay-result-node replayed)))
           (equal (fn-rii-sco-finalize-configured replayed c configs frontier)
                  (fn-rii-sco-finalize-from replayed c configs frontier)))
  :hints (("Goal" :in-theory (e/d (fn-rii-sco-finalize-from fn-rii-observed-historyp
                                   fn-rii-cnode-statep-has-node-statep)
                                  (fn-rii-sco-finalize-from-is-sco-finalize-from
                                   fn-rii-observed-historyp-is-observed-historyp
                                   fn-rii-sn-statep-carried fn-rii-sn-statep
                                   fn-rii-sn-statep-is-sn-statep
                                   fn-node-statep fn-cnode-statep
                                   fn-replay-advance-okp fn-rii-advance-idlep
                                   fn-sn-with-event-index fn-sn-with-topic
                                   fn-sn-with-consumer fn-cpo-install
                                   fn-sn-update-replayed fn-sn-observed-seed
                                   fn-stx-index-of-store fn-replay-advance-txid)))))
(verify-guards fn-rii-sco-finalize-configured
  :hints (("Goal" :in-theory (e/d (fn-rii-cnode-statep-has-node-statep)
                                  (fn-cnode-statep fn-node-statep fn-cpr-replay fn-cpr-loop
                                   fn-sco-cpr-finish fn-sco-cpr-prefix)))))

(defthm fn-rii-sco-cpr-finish-ok-is-configured
  (implies (and (fn-sco-pausedp r)
                (equal (fn-replay-result-kind (fn-sco-cpr-finish r configs)) :ok))
           (fn-cnode-statep (fn-replay-result-node (fn-sco-cpr-finish r configs))))
  :hints (("Goal" :in-theory (e/d (fn-sco-cpr-finish) (fn-cnode-statep fn-cpr-loop)))))

; fn-sco-store-open over the twin: (REPLAYED OPENED).  A paused fold's drain
; is finalized without re-checking its node (7a).
(defun fn-rii-sco-store-open (e configs frontier)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((r (fn-sco-cpr e))
         (replayed (fn-sco-cpr-finish r configs)))
    (list replayed
          (if (fn-sco-pausedp r)
              (fn-rii-sco-finalize-configured replayed e configs frontier)
            (fn-rii-sco-finalize-from replayed e configs frontier)))))

(defthm fn-rii-sco-store-open-is-sco-store-open
  (equal (fn-rii-sco-store-open e configs frontier)
         (fn-sco-store-open e configs frontier))
  :hints (("Goal" :in-theory (e/d (fn-rii-sco-store-open fn-sco-store-open
                                   fn-sco-finalize-from-unfolds)
                                  (fn-sco-finalize fn-sco-finalize-from
                                   fn-rii-sco-finalize-configured
                                   fn-rii-sco-finalize-from
                                   fn-sco-cpr-finish fn-cnode-statep)))))

(verify-guards fn-rii-sco-store-open
  :hints (("Goal" :in-theory (disable fn-sco-cpr-finish fn-cnode-statep
                                      fn-rii-sco-finalize-configured-is-finalize-from))))

; The open the host calls (fn-sopc-classified-open over the twin).
(defun fn-rii-classified-open (e configs frontier)
  (declare (xargs :guard t :verify-guards nil))
  (let ((refusal (fn-sopc-open-refusal e)))
    (if refusal refusal (fn-rii-sco-store-open e configs frontier))))

; KEYSTONE (2).  The host's open is the classified open, with no hypothesis:
; host/store-node-host.lisp fn-store-sn-open-extended.
(defthm fn-rii-classified-open-is-classified-open
  (equal (fn-rii-classified-open e configs frontier)
         (fn-sopc-classified-open e configs frontier))
  :hints (("Goal" :in-theory (e/d (fn-rii-classified-open fn-sopc-classified-open)
                                  (fn-rii-sco-store-open fn-sco-store-open
                                   fn-sopc-open-refusal)))))

(verify-guards fn-rii-classified-open)

; -----------------------------------------------------------------------------
; 7b. The extension and its open in one call (lane snapshot-open-2).
;
; The host extended the checkpoint (fn-rii-sco-extend) and then opened the
; extension (fn-rii-classified-open) in two calls; the resume checked the
; checkpoint's node and the drain checked the resumed node again (a second
; whole-node recognizer, ~0.075 s at 40k, O(state)).  After a resume over a
; non-empty suffix the paused node is configured
; (fn-rii-sco-cpr-resume-paused-node-is-configured), so the fused call drains
; it without the check.

(local
 (defthm fn-rii-sco-cpr-prefix-paused-node-is-configured
   (implies (and (consp events)
                 (fn-sco-pausedp (fn-sco-cpr-prefix cn configs events cs es)))
            (fn-cnode-statep (fn-sco-at 1 (fn-sco-cpr-prefix cn configs events cs es))))
   :hints (("Goal" :induct (fn-sco-cpr-prefix cn configs events cs es)
            :in-theory (e/d (fn-sco-cpr-prefix fn-replay-fault fn-sco-paused fn-sco-pausedp)
                            (fn-cnode-statep fn-cnode-apply-config fn-cpr-apply-event
                             fn-cnode-record-acceptablep fn-store-event-p fn-cfg-recordp
                             fn-replay-advance-okp fn-replay-advance-txid))
            :expand ((fn-sco-cpr-prefix cn configs events cs es)))
           ("Subgoal *1/2" :expand ((:free (cn2 c2 s2 e2) (fn-sco-cpr-prefix cn2 c2 nil s2 e2)))))))

(defthm fn-rii-sco-cpr-resume-paused-node-is-configured
  (implies (and (consp suffix)
                (fn-sco-pausedp (fn-sco-cpr-resume r configs suffix)))
           (fn-cnode-statep (fn-sco-at 1 (fn-sco-cpr-resume r configs suffix))))
  :hints (("Goal" :in-theory (e/d (fn-sco-cpr-resume) (fn-cnode-statep fn-sco-cpr-prefix fn-sco-pausedp fn-sco-at)))))

; The drain of a paused fold whose node is known configured: fn-sco-cpr-finish's
; logic (fn-cpr-loop from the paused node) without its executable check.
(defun fn-rii-sco-cpr-finish-configured (r configs)
  (declare (xargs :guard (and (fn-sco-pausedp r) (fn-cnode-statep (fn-sco-at 1 r)))))
  (fn-cpr-loop (fn-sco-at 1 r) (fn-sco-nthcdr (nfix (fn-sco-at 2 r)) configs) nil
               (fn-sco-at 2 r) (fn-sco-at 3 r)))

(defthm fn-rii-sco-cpr-finish-configured-is-finish
  (implies (fn-sco-pausedp r)
           (equal (fn-rii-sco-cpr-finish-configured r configs)
                  (fn-sco-cpr-finish r configs)))
  :hints (("Goal" :in-theory (e/d (fn-sco-cpr-finish) (fn-cpr-loop fn-cnode-statep)))))

; The open of a paused extension whose node is known configured.
(defun fn-rii-sco-store-open-resumed (e configs frontier)
  (declare (xargs :guard (and (fn-sco-pausedp (fn-sco-cpr e))
                              (fn-cnode-statep (fn-sco-at 1 (fn-sco-cpr e))))
                  :guard-hints (("Goal" :in-theory (disable fn-cnode-statep fn-cpr-loop
                                                            fn-rii-sco-cpr-finish-configured-is-finish)
                                 :use ((:instance fn-rii-sco-cpr-finish-ok-is-configured
                                                  (r (fn-sco-cpr e))))))))
  (let ((replayed (fn-rii-sco-cpr-finish-configured (fn-sco-cpr e) configs)))
    (list replayed (fn-rii-sco-finalize-configured replayed e configs frontier))))

(defthm fn-rii-sco-store-open-resumed-is-store-open
  (implies (fn-sco-pausedp (fn-sco-cpr e))
           (equal (fn-rii-sco-store-open-resumed e configs frontier)
                  (fn-rii-sco-store-open e configs frontier)))
  :hints (("Goal" :in-theory (e/d (fn-rii-sco-store-open)
                                  (fn-rii-sco-finalize-configured fn-rii-sco-finalize-from
                                   fn-sco-cpr-finish fn-cnode-statep fn-cpr-loop)))))

; The extension and its classified open in one call (the host's two calls,
; fused): after a resume over a non-empty suffix the paused node is configured
; (fn-rii-sco-cpr-resume-paused-node-is-configured: the resume checked the
; checkpoint's node and every step keeps it), so the drain does not check it
; again.
(defun fn-rii-sco-extend-open (c configs suffix frontier)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((e (fn-rii-sco-extend c configs suffix))
         (refusal (fn-sopc-open-refusal e)))
    (list e
          (if refusal
              refusal
            (if (and (consp suffix) (fn-sco-pausedp (fn-sco-cpr e)))
                (fn-rii-sco-store-open-resumed e configs frontier)
              (fn-rii-sco-store-open e configs frontier))))))

; KEYSTONE (3).  The fused call is the extension and the classified open, with
; no hypothesis: host/store-node-host.lisp fn-store-sn-recover-from-checkpoint
; and fn-store-sn-recover-rows.
(defthm fn-rii-sco-extend-open-is-extend-then-open
  (equal (fn-rii-sco-extend-open c configs suffix frontier)
         (list (fn-rii-sco-extend c configs suffix)
               (fn-rii-classified-open (fn-rii-sco-extend c configs suffix)
                                       configs frontier)))
  :hints (("Goal" :in-theory '(fn-rii-sco-extend-open fn-rii-classified-open)
           :use ((:instance fn-rii-sco-store-open-resumed-is-store-open
                            (e (fn-rii-sco-extend c configs suffix)))))))

(verify-guards fn-rii-sco-extend-open
  :hints (("Goal" :in-theory (e/d (fn-rii-sco-extend)
                                  (fn-rii-sco-cpr-resume fn-cnode-statep fn-sopc-open-refusal
                                   fn-rii-sco-store-open fn-rii-sco-store-open-resumed
                                   fn-replay-identity-loop fn-sco-consumer-resume
                                   fn-th-prefix-loop fn-cei-build-aux))
           :use ((:instance fn-rii-sco-cpr-resume-paused-node-is-configured
                            (r (fn-sco-cpr c)))))))

(in-theory (disable fn-rii-sco-cpr-prefix fn-rii-sco-cpr-resume fn-rii-sco-extend
                    fn-rii-sco-store-open fn-rii-classified-open
                    fn-rii-sf-statep-carried fn-rii-sn-statep-carried
                    fn-rii-advance-idlep fn-rii-sco-finalize-configured
                    fn-rii-sco-cpr-finish-configured fn-rii-sco-store-open-resumed
                    fn-rii-sco-extend-open))
