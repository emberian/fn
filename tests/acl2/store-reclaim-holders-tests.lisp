; fn: witnesses and teeth for books/store-reclaim-holders.lisp and the
; reclamation words of the status report (D13, STO-014, PRF-088).
(in-package "ACL2")
(include-book "../../books/store-reclaim-holders")
(include-book "../../books/native-live-status")
(include-book "../../books/expiry-verdict")
(include-book "must-fail-checked")
(include-book "owner-served-invariants-tests")
; A verified article (*stxt-r1*) and the keyring it verifies under.
(include-book "stx-transit-tests")

; The owner fixture's store, its one article, and a group it is numbered in.
; The completing owner's store after its article completed, as in
; octets-stobj-tests (not included: it depends on the octet buffer books).
(defconst *rht-s0* (fn-own-store (cdr (osi-finish *osi-completing* *osi-cfg* *osi-completing-prior*))))
(defconst *rht-art* (car (fn-state-articles (fn-node-acceptance (fn-sn-node *rht-s0*)))))
; Since the records flip the article holds a payload HANDLE; its stored
; bytes are the handle's in the arena that interned the owner's journal.
(defconst *rht-bytes*
  (fn-hrt-bytes *osi-completing-prior* (fn-article-payload *rht-art*)))
(assert-event (and (natp (fn-article-payload *rht-art*))
                   (fn-cbor-octet-listp *rht-bytes*) (consp *rht-bytes*)))

; The arena of the fixture's history (audit-fixes, 2026-09-27): the payloads
; the host's entry interned from the owner's journal, in handle order, so
; that sealing them in order rebuilds the arena its articles' handles name.
(defun rcl-prior-payloads (prior i fuel)
  (declare (xargs :verify-guards nil :measure (nfix fuel)))
  (if (zp fuel)
      nil
    (let ((b (fn-hrt-bytes prior i)))
      (if (consp b)
          (cons b (rcl-prior-payloads prior (+ 1 i) (- fuel 1)))
        nil))))
(defconst *rht-payloads* (rcl-prior-payloads *osi-completing-prior* 0 64))
(assert-event (equal (nth (fn-article-payload *rht-art*) *rht-payloads*) *rht-bytes*))
(bpr-lift fn-rcl-store-counts 3)
(bpr-lift fn-nls-reclaim-words 3)
(defconst *rht-m* (car (fn-article-memberships *rht-art*)))
(defconst *rht-g* (car *rht-m*))
(defconst *rht-n* (cdr *rht-m*))
(assert-event (and (stringp *rht-g*) (posp *rht-n*)
                   (member-equal *rht-g* (fn-state-groups (fn-node-acceptance
                                                           (fn-sn-node *rht-s0*))))))

; The store with a consumer projection: frontier 5, one consumer at ACK.
(defun rht-with-consumer (s ack)
  (update-nth 11 (fn-cp-state 1 1 5 2 (list (fn-cp-entry 7 1 1 0 0 1 ack))) s))
(defconst *rht-lag* (rht-with-consumer *rht-s0* 3))
(defconst *rht-caught* (rht-with-consumer *rht-s0* 5))
(defconst *rht-rule* '(:released-by-all-holders))

; Keystone witness: a lagging consumer holds the article under a releasing
; rule; caught up, the same article is reclaimable.
(assert-event (fn-rcl-lagging-consumerp (fn-cp-nth 5 (fn-sn-consumer *rht-lag*))
                                        (fn-cp-nth 3 (fn-sn-consumer *rht-lag*))))
(assert-event (equal (fn-rcl-verdict *rht-rule* 0 (fn-rcl-store-holders *rht-lag*) nil *rht-art*)
                     :held-consumer-cursor))
(assert-event (fn-rcl-reclaimable *rht-rule* 0 (fn-rcl-store-holders *rht-caught*) nil *rht-art*))
; Tooth (a lagging consumer): caught up, the conclusion fails.
(must-fail-checked (assert-event (not (fn-rcl-reclaimable *rht-rule* 0
                                                  (fn-rcl-store-holders *rht-caught*)
                                                  nil *rht-art*))))
; Tooth (numbered, posp n): an article with no membership is not held.
(defconst *rht-bare* (fn-make-article (fn-article-msgid *rht-art*) (fn-article-payload *rht-art*)
                                      (fn-article-groups *rht-art*) nil t
                                      (fn-article-stamp *rht-art*)))
(must-fail-checked (assert-event (not (fn-rcl-reclaimable *rht-rule* 0 (fn-rcl-store-holders *rht-lag*)
                                                  nil *rht-bare*))))
; Tooth (the group is served): numbered only in a group the store lacks.
(defconst *rht-other* (fn-make-article (fn-article-msgid *rht-art*) (fn-article-payload *rht-art*)
                                       (fn-article-groups *rht-art*) '(("zz.none" . 1)) t
                                       (fn-article-stamp *rht-art*)))
(must-fail-checked (assert-event (not (fn-rcl-reclaimable *rht-rule* 0 (fn-rcl-store-holders *rht-lag*)
                                                  nil *rht-other*))))

; The verdict list.  Every article the fixture accepted has a verdict
; entry, and each is :absent (no authorship field): the Store's own list
; holds nothing, so the article is reclaimable with it.  An :unverified
; entry for the same Message-ID holds the payload.
(defconst *rht-msgid* (fn-article-msgid *rht-art*))
(assert-event (and (consp (fn-sn-verdicts *rht-caught*))
                   (fn-rcl-verdict-heldp *rht-msgid*
                                         (list (cons *rht-msgid* '(:unverified :signature 0))))
                   (not (fn-rcl-verdict-heldp *rht-msgid* (fn-sn-verdicts *rht-caught*)))))
(assert-event (fn-rcl-reclaimable *rht-rule* 0 (fn-rcl-store-holders *rht-caught*)
                                  (fn-sn-verdicts *rht-caught*) *rht-art*))
; Tooth (the entry is :absent): an :unverified verdict holds the article.
(must-fail-checked (assert-event (fn-rcl-reclaimable *rht-rule* 0 (fn-rcl-store-holders *rht-caught*)
                                             (list (cons *rht-msgid* '(:unverified :signature 0)))
                                             *rht-art*)))

; fn-rcl-absent-verdict-contributes-nothing.  Witness: the fixture's own
; article is :absent under the empty keyring and contributes nothing under
; the keyring that verifies *stxt-r1*.  Tooth (the verdict is :absent):
; *stxt-r1* is :unverified under the empty keyring (its key not enrolled)
; and contributes a statement under *stxt-keyring*.
; by specification: the flip -- the article carries its payload as an arena
; handle (natp); the theorem is about the payload's OCTETS, which are the
; bytes under that handle in the arena that interned the completing journal
; (owner-served-invariants-tests osi-finish; held-rows-tests fn-hrt-bytes).
(defconst *rht-art-octets*
  (fn-hrt-bytes *osi-completing-prior* (fn-article-payload *rht-art*)))
(assert-event (and (natp (fn-article-payload *rht-art*))
                   (consp *rht-art-octets*)))
(assert-event (equal (fn-stx-verdict-token
                      (fn-stx-verdict-of-octets *rht-art-octets* nil 0))
                     :absent))
(assert-event (equal (fn-stx-delta *rht-art-octets* *stxt-keyring*) nil))
(assert-event (equal (fn-stx-verdict-token
                      (fn-stx-verdict-of-octets (fn-article-payload *stxt-r1*) nil 0))
                     :unverified))
(must-fail-checked (assert-event (equal (fn-stx-delta (fn-article-payload *stxt-r1*) *stxt-keyring*)
                                nil)))

; The counts: caught up, the article is counted reclaimable (its stored
; octets among the reclaimable octets) and nothing held; lagging, nothing is
; reclaimable and it is counted held.
(assert-event (let ((c (in-arena-fn-rcl-store-counts *rht-payloads* *rht-rule* 0 *rht-caught*)))
                (and (<= 1 (nth 0 c)) (<= (len *rht-bytes*) (nth 1 c))
                     (equal (nth 4 c) 0))))
(assert-event (let ((c (in-arena-fn-rcl-store-counts *rht-payloads* *rht-rule* 0 *rht-lag*)))
                (and (equal (nth 0 c) 0) (<= 1 (nth 4 c)))))
; Keep-forever (no row): nothing reclaimable, nothing counted held.
(assert-event (equal (in-arena-fn-rcl-store-counts *rht-payloads* '(:keep-forever) 0 *rht-caught*) (list 0 0 0 0 0)))

; The status words over the configuration's rule (no row: keep-forever).
(assert-event
 (equal (in-arena-fn-nls-reclaim-words *rht-payloads* *rht-caught* (fn-cfg-initial) '(nil nil (:full-replay :absent) nil))
        (fn-record-string-octets
         "reclaim rule=keep-forever reclaimable=0 reclaimable-octets=0 held=0 reclaimed=0 freed-octets=0 signed=0 kept=3")))

; -----------------------------------------------------------------------------
; The counts over the arena (audit-fixes, 2026-09-27; KEYSTONE
; fn-rcl-store-counts-is-the-model-over-alpha).  Before this the counts read
; each article's HANDLE as its octets: the caught-up store (three articles,
; all reclaimable under the releasing rule) answered (3 0 0 0 0), no
; reclaimable octet, where its articles hold 23, 23 and 328 octets.
(bpr-lift fn-rcl-articles-alpha 1)
(defconst *rht-articles* (fn-state-articles (fn-node-acceptance (fn-sn-node *rht-caught*))))
(defconst *rht-counts* (in-arena-fn-rcl-store-counts *rht-payloads* *rht-rule* 0 *rht-caught*))
(defun rht-lens (payloads)
  (if (consp payloads) (+ (len (car payloads)) (rht-lens (cdr payloads))) 0))
(assert-event (and (equal (len *rht-articles*) 3) (equal (len *rht-payloads*) 3)))
(assert-event (equal *rht-counts* (list 3 (rht-lens *rht-payloads*) 0 0 0)))
(assert-event (equal (rht-lens *rht-payloads*) 374))
(assert-event (< 0 (len *rht-bytes*)))
; The keystone, evaluated: the counts are the octet-list model's over ALPHA.
(defconst *rht-alpha* (in-arena-fn-rcl-articles-alpha *rht-payloads* *rht-articles*))
(assert-event
 (equal *rht-counts*
        (append (fn-rcl-summary *rht-rule* 0 (fn-rcl-store-holders *rht-caught*)
                                (fn-sn-verdicts *rht-caught*) *rht-alpha*)
                (list (fn-rcl-held-count *rht-rule* 0 (fn-rcl-store-holders *rht-caught*)
                                         (fn-sn-verdicts *rht-caught*) *rht-alpha*)))))
; The model over the handles themselves (what the counts computed before the
; fix): no reclaimable octet.
(assert-event
 (equal (fn-rcl-summary *rht-rule* 0 (fn-rcl-store-holders *rht-caught*)
                        (fn-sn-verdicts *rht-caught*) *rht-articles*)
        (list 3 0 0 0)))

; Tooth (the arena is what the counts read): an arena whose handle holds
; fewer octets changes the reclaimable octets.
(defun rht-with-payload (payloads i bytes)
  (declare (xargs :verify-guards nil))
  (update-nth i bytes payloads))
(defconst *rht-short-payloads*
  (rht-with-payload *rht-payloads* (fn-article-payload *rht-art*) (take 3 *rht-bytes*)))
(assert-event
 (equal (in-arena-fn-rcl-store-counts *rht-short-payloads* *rht-rule* 0 *rht-caught*)
        (list 3 (+ 3 (- (rht-lens *rht-payloads*) (len *rht-bytes*))) 0 0 0)))

; A reclaimed article: its handle holds the tombstone of its bytes.  It is
; counted reclaimed, with the octets its tombstone records as freed, and no
; longer reclaimable; over the handle alone it was counted reclaimable again.
(defconst *rht-tomb* (fn-rcl-tombstone-of *rht-bytes* (fn-record-string-octets *rht-msgid*)))
(assert-event (fn-rcl-tombstonep *rht-tomb*))
(defconst *rht-tomb-payloads*
  (rht-with-payload *rht-payloads* (fn-article-payload *rht-art*) *rht-tomb*))
(assert-event
 (equal (in-arena-fn-rcl-store-counts *rht-tomb-payloads* *rht-rule* 0 *rht-caught*)
        (list 2 (- (rht-lens *rht-payloads*) (len *rht-bytes*))
              1 (nfix (- (fn-rcl-tomb-length *rht-tomb*) (len *rht-tomb*))) 0)))
(assert-event (< 0 (nfix (- (fn-rcl-tomb-length *rht-tomb*) (len *rht-tomb*)))))
(assert-event (equal (fn-rcl-tomb-length *rht-tomb*) (len *rht-bytes*)))

; The status line under the releasing rule (the configuration row `retention
; set released-by-all-holders' writes): the reclaimable octets are the
; articles' stored lengths (374), not 0.
(defconst *rht-release-cfg*
  (fn-cfg-make 1 (fn-cfg-apply (fn-cfg-empty-value) 1 nil (fn-rcl-rule-deltas *rht-rule*))))
(assert-event (equal (fn-rcl-config-rule (fn-cfg-value *rht-release-cfg*)) *rht-rule*))
(assert-event
 (equal (in-arena-fn-nls-reclaim-words *rht-payloads* *rht-caught* *rht-release-cfg*
                                       '(nil nil (:full-replay :absent) nil))
        (append (fn-record-string-octets "reclaim rule=released-by-all-holders reclaimable=3")
                (fn-record-string-octets " reclaimable-octets=374")
                (fn-record-string-octets " held=0 reclaimed=0 freed-octets=0 signed=0 kept=0"))))

; -----------------------------------------------------------------------------
; The retention classes (PKT-844, lane bp-retention-leftovers).  The same
; caught-up store with an :unverified authorship verdict recorded for
; *rht-art* (a signed article: what a kind-4 composite's verdict is): the
; article is :signed under every rule, the other two stay where the rule
; puts them, and the five counts sum to the three articles.
(bpr-lift fn-rcl-store-classes 3)
(defconst *rht-signed*
  (update-nth 7 (cons (cons *rht-msgid* '(:unverified :signature 0))
                      (fn-sn-verdicts *rht-caught*))
              *rht-caught*))
(assert-event (fn-rcl-verdict-heldp *rht-msgid* (fn-sn-verdicts *rht-signed*)))
(defun rht-sum (counts classes)
  (+ (nth 0 counts) (nth 2 counts) (nth 4 counts) (nth 0 classes) (nth 1 classes)))

; KEYSTONE fn-rcl-store-classes-partition-the-articles: witnesses under the
; releasing rule (two reclaimable, one signed), keep-forever (one signed, two
; kept), a lagging consumer (two held, one signed) and a tombstone (one
; reclaimed, two reclaimable, none signed on the unsigned store).
(defconst *rht-sc* (in-arena-fn-rcl-store-counts *rht-payloads* *rht-rule* 0 *rht-signed*))
(defconst *rht-sk* (in-arena-fn-rcl-store-classes *rht-payloads* *rht-rule* 0 *rht-signed*))
(assert-event (and (equal (nth 0 *rht-sc*) 2) (equal *rht-sk* '(1 0))
                   (equal (rht-sum *rht-sc* *rht-sk*) (len *rht-articles*))))
(assert-event
 (let ((c (in-arena-fn-rcl-store-counts *rht-payloads* '(:keep-forever) 0 *rht-signed*))
       (k (in-arena-fn-rcl-store-classes *rht-payloads* '(:keep-forever) 0 *rht-signed*)))
   (and (equal c '(0 0 0 0 0)) (equal k '(1 2)) (equal (rht-sum c k) 3))))
(defconst *rht-signed-lag*
  (update-nth 7 (fn-sn-verdicts *rht-signed*) *rht-lag*))
(assert-event
 (let ((c (in-arena-fn-rcl-store-counts *rht-payloads* *rht-rule* 0 *rht-signed-lag*))
       (k (in-arena-fn-rcl-store-classes *rht-payloads* *rht-rule* 0 *rht-signed-lag*)))
   (and (equal (nth 4 c) 2) (equal k '(1 0)) (equal (rht-sum c k) 3))))
(assert-event
 (let ((c (in-arena-fn-rcl-store-counts *rht-tomb-payloads* *rht-rule* 0 *rht-caught*))
       (k (in-arena-fn-rcl-store-classes *rht-tomb-payloads* *rht-rule* 0 *rht-caught*)))
   (and (equal (nth 2 c) 1) (equal k '(0 0)) (equal (rht-sum c k) 3))))
; Tooth (the signed class): without it the statement article is in no
; class and the counts fall short of the articles, as the power-loss
; campaign's status did (articles=232 against 208).
(must-fail-checked
 (assert-event (equal (+ (nth 0 *rht-sc*) (nth 2 *rht-sc*) (nth 4 *rht-sc*)
                         (nth 1 *rht-sk*))
                      (len *rht-articles*))))
; Tooth (the kept class): under keep-forever the rule-kept articles are the
; rest.
(must-fail-checked
 (assert-event
  (let ((c (in-arena-fn-rcl-store-counts *rht-payloads* '(:keep-forever) 0 *rht-signed*))
        (k (in-arena-fn-rcl-store-classes *rht-payloads* '(:keep-forever) 0 *rht-signed*)))
    (equal (+ (nth 0 c) (nth 2 c) (nth 4 c) (nth 0 k)) 3))))

; fn-rcl-signed-article-is-never-reclaimable.  Witness: under the releasing
; rule with every holder caught up, the signed article is not reclaimable.
(assert-event
 (and (fn-rcl-verdict-heldp *rht-msgid* (fn-sn-verdicts *rht-signed*))
      (not (fn-rcl-reclaimable *rht-rule* 0 (fn-rcl-store-holders *rht-signed*)
                               (fn-sn-verdicts *rht-signed*) *rht-art*))))
; Tooth (the verdict is held): the store's own :absent verdicts release it.
(must-fail-checked
 (assert-event (and (fn-rcl-verdict-heldp *rht-msgid* (fn-sn-verdicts *rht-caught*))
                    (not (fn-rcl-reclaimable *rht-rule* 0
                                             (fn-rcl-store-holders *rht-caught*)
                                             (fn-sn-verdicts *rht-caught*)
                                             *rht-art*)))))

; The status line: `signed' and `kept' beside the reclaim counts.
(assert-event
 (equal (in-arena-fn-nls-reclaim-words *rht-payloads* *rht-signed* *rht-release-cfg*
                                       '(nil nil (:full-replay :absent) nil))
        (append (fn-record-string-octets "reclaim rule=released-by-all-holders reclaimable=2")
                (fn-record-string-octets " reclaimable-octets=")
                (fn-nls-nat (- 374 (len *rht-bytes*)))
                (fn-record-string-octets " held=0 reclaimed=0 freed-octets=0 signed=1 kept=0"))))

; The three per-article counts execute by loops (lane format10-import: `store
; status' over 1,000,000 articles died in 837,983 frames of
; fn-rcl-summary-in).  Each entry is guard-verified, so the :exec loop runs,
; and every count above (in-arena-fn-rcl-store-counts, -classes) is the loop's.
(assert-event
 (equal (list (symbol-class 'fn-rcl-summary-in (w state))
              (symbol-class 'fn-rcl-held-count-in (w state))
              (symbol-class 'fn-rcl-class-count-in (w state)))
        '(:common-lisp-compliant :common-lisp-compliant :common-lisp-compliant)))

; -----------------------------------------------------------------------------
; PRF-361 (PKT-878, lane health-truth-status): the counts ask the verdict test
; of the held verdicts only.  *rht-signed*'s list is the fixture's :absent
; entries (one per accepted article) with one :unverified entry in front.
(defconst *rht-held* (fn-rcl-held-verdicts (fn-sn-verdicts *rht-signed*)))
; Witness: the filter keeps exactly the :unverified entry and drops every
; :absent one (the list shrinks: this is the work the render no longer does).
(assert-event
 (and (equal *rht-held* (list (cons *rht-msgid* '(:unverified :signature 0))))
      (< (len *rht-held*) (len (fn-sn-verdicts *rht-signed*)))
      (fn-rcl-verdict-heldp *rht-msgid* *rht-held*)
      (equal (fn-rcl-verdict-heldp *rht-msgid* *rht-held*)
             (fn-rcl-verdict-heldp *rht-msgid* (fn-sn-verdicts *rht-signed*)))))
; Tooth (the filter keeps the held entry): dropping every entry -- a filter
; that also removed the :unverified one -- changes the answer, so
; fn-rcl-verdict-heldp-of-held-verdicts is not true of any shrinking.
(must-fail-checked
 (assert-event (equal (fn-rcl-verdict-heldp *rht-msgid* nil)
                      (fn-rcl-verdict-heldp *rht-msgid* (fn-sn-verdicts *rht-signed*)))))
; Tooth (an :absent entry holds nothing): the filter does drop it.
(must-fail-checked
 (assert-event (member-equal (car (fn-sn-verdicts *rht-caught*))
                             (fn-rcl-held-verdicts (fn-sn-verdicts *rht-caught*)))))
; The class count over EVERY verdict of *rht-signed* (the keystone's right
; side), in the arena the fixture's payloads seal.
(defun rht-cc-a (payloads class h verdicts arts fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let ((fn-arena (fn-arn-seal-many payloads fn-arena)))
    (mv (fn-rcl-class-count-in class *rht-rule* 0 h verdicts arts fn-arena) fn-arena)))
(defun rht-class-count-full (class h arts)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (r fn-arena)
      (rht-cc-a *rht-payloads* class h (fn-sn-verdicts *rht-signed*) arts fn-arena)
      r)))
; KEYSTONE fn-rcl-store-classes-over-every-verdict, witness: the classes the
; host reads (over the held verdicts) are the classes over every verdict,
; and they are not degenerate: the signed article is counted.
(assert-event
 (let ((h (fn-rcl-store-holders *rht-signed*))
       (arts (fn-state-articles (fn-node-acceptance (fn-sn-node *rht-signed*)))))
   (and (equal (in-arena-fn-rcl-store-classes *rht-payloads* *rht-rule* 0 *rht-signed*)
               (list (rht-class-count-full :signed h arts)
                     (rht-class-count-full :kept h arts)))
        (equal (nth 0 (in-arena-fn-rcl-store-classes *rht-payloads* *rht-rule* 0
                                                     *rht-signed*))
               1))))

; -----------------------------------------------------------------------------
; The canonical BP retention pin (RECLAIM-RETENTION, 2026-10-03; KEYSTONE
; fn-rcl-store-holders-never-reclaim-a-forward-pinned-article).  The pin is
; made by the Store's own retention step (books/replay
; fn-replay-apply-retention-event, what the finish of an owner's :undertake
; event runs), on the subject of the article's archive binding, exactly as
; the BP workflow takes it (books/bp-workflow fn-bp-prepare-enqueue).
(defconst *rht-binding*
  (fn-node-find-binding *rht-msgid* (fn-node-bindings (fn-sn-node *rht-caught*))))
(defconst *rht-subject* (fn-node-binding-subject *rht-binding*))
(assert-event (and (consp *rht-binding*) (stringp *rht-subject*)
                   (member-equal *rht-binding* (fn-node-bindings (fn-sn-node *rht-caught*)))))
(defun rht-retention (s kind id subject)
  (declare (xargs :verify-guards nil))
  (let* ((node (fn-sn-node s))
         (txid (fn-state-next-txid (fn-node-acceptance node)))
         (event (fn-store-retention-event-make kind 0 txid txid id subject
                                               "fwd-evidence" (if (equal kind :undertake) 4 0)))
         (next (fn-replay-apply-retention-event node event)))
    (if (consp next) (fn-sn-update s (fn-sn-files s) next) nil)))
(defconst *rht-pinned* (rht-retention *rht-caught* :undertake "fwd-1" *rht-subject*))
(defconst *rht-pin*
  (fn-retain-find-id "fwd-1" (fn-retain-pins (fn-node-retention (fn-sn-node *rht-pinned*)))))
; Positive witness, every literal of the keystone: the pin is live and
; :forward, the binding is the article's and has the pin's subject, and the
; article is held by the BP slot under the releasing rule (consumer caught up,
; verdicts nil), so not reclaimable.
(assert-event
 (let ((node (fn-sn-node *rht-pinned*)))
   (and (consp *rht-pinned*)
        (member-equal *rht-pin* (fn-retain-pins (fn-node-retention node)))
        (equal (fn-retain-obligation-kind *rht-pin*) :forward)
        (member-equal *rht-binding* (fn-node-bindings node))
        (equal (fn-node-binding-subject *rht-binding*) (fn-retain-obligation-subject *rht-pin*))
        (equal (fn-node-binding-msgid *rht-binding*) (fn-article-msgid *rht-art*))
        (equal (fn-rcl-verdict *rht-rule* 0 (fn-rcl-store-holders *rht-pinned*) nil *rht-art*)
               :held-bp-obligation)
        (not (fn-rcl-reclaimable *rht-rule* 0 (fn-rcl-store-holders *rht-pinned*) nil
                                 *rht-art*)))))
; Tooth (the conclusion can fail): the same article, unpinned, is reclaimable.
(must-fail-checked
 (assert-event (not (fn-rcl-reclaimable *rht-rule* 0 (fn-rcl-store-holders *rht-caught*) nil
                                        *rht-art*))))
; Tooth (the pin is live): after the receipt's :release event the same pin
; is gone and the next reclaim takes the article.
(defconst *rht-released* (rht-retention *rht-pinned* :release "fwd-1" *rht-subject*))
(assert-event (and (consp *rht-released*)
                   (not (member-equal *rht-pin* (fn-retain-pins (fn-node-retention
                                                                 (fn-sn-node *rht-released*)))))
                   (fn-rcl-reclaimable *rht-rule* 0 (fn-rcl-store-holders *rht-released*) nil
                                       *rht-art*)))
; Tooth (the pin is not an archive pin): the article's own archive pin has
; the binding's subject and holds nothing.
(defconst *rht-archive-pin*
  (fn-retain-find-id (fn-node-binding-id *rht-binding*)
                     (fn-retain-pins (fn-node-retention (fn-sn-node *rht-caught*)))))
(assert-event (and (equal (fn-retain-obligation-kind *rht-archive-pin*) :archive)
                   (equal (fn-retain-obligation-subject *rht-archive-pin*) *rht-subject*)
                   (fn-rcl-reclaimable *rht-rule* 0 (fn-rcl-store-holders *rht-caught*) nil
                                       *rht-art*)))
; Tooth (the binding has the pin's subject): a :forward pin on another
; subject holds nothing.
(defconst *rht-elsewhere* (rht-retention *rht-caught* :undertake "fwd-2" "other-subject"))
(assert-event (and (consp *rht-elsewhere*)
                   (fn-rcl-reclaimable *rht-rule* 0 (fn-rcl-store-holders *rht-elsewhere*) nil
                                       *rht-art*)))
; Tooth (the binding is the article's): another article (another Message-ID)
; is not held by the pin on this one's subject.
(defconst *rht-stranger* (fn-make-article "<stranger@x>" (fn-article-payload *rht-art*)
                                          (fn-article-groups *rht-art*)
                                          (fn-article-memberships *rht-art*) t
                                          (fn-article-stamp *rht-art*)))
(assert-event (fn-rcl-reclaimable *rht-rule* 0 (fn-rcl-store-holders *rht-pinned*) nil
                                  *rht-stranger*))
; MUTATION (labelled; not a hypothesis removal): the holders with the BP slot
; dropped -- what the slot was before this lane, literally nil -- reclaim the
; pinned article.
(assert-event (fn-rcl-reclaimable *rht-rule* 0
                                  (update-nth 3 nil (fn-rcl-store-holders *rht-pinned*))
                                  nil *rht-art*))
; The expiry release reads the same slot: an article the policy has expired
; is still kept by the pin (books/expiry-verdict).
(assert-event
 (let ((expired (make-fast-alist (list (cons *rht-msgid* t)))))
   (and (not (fn-xpy-releasablep '(:keep-forever) 0 (fn-rcl-store-holders *rht-pinned*) nil
                                 expired *rht-art*))
        (fn-xpy-releasablep '(:keep-forever) 0 (fn-rcl-store-holders *rht-released*) nil
                            expired *rht-art*))))
; The status counts the pinned article held.
(assert-event (let ((c (in-arena-fn-rcl-store-counts *rht-payloads* *rht-rule* 0 *rht-pinned*)))
                (equal (nth 4 c) 1)))
