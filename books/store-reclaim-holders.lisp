; fn: the holders a Store itself carries, and the reclamation counts the
; status report prints (D13, STO-014, PRF-088).
;
; `fn-rcl-verdict' (books/store-reclaim) takes the holders as an argument:
; (pins cursors feeds bp).  This book reads the ones the Store state
; carries.  What it reads, and what it cannot:
;
;   consumer cursors  the E2 consumer projection (`fn-sn-consumer'): a
;                     registered consumer acknowledges a Store journal
;                     position, not a group number.  Mapping that position
;                     to the articles after it needs the record sequence of
;                     each article, which the acceptance state does not
;                     keep.  So the reading is conservative: a consumer whose
;                     acknowledgement is below the committed frontier holds
;                     EVERY article (a cursor at 0 in every group).  Sound,
;                     and coarse: nothing is reclaimable while any consumer
;                     lags.  The precise reading is open (PRF-088).
;   reader pins       none: a reader's pin lives in its connection and has no
;                     durable form.  `store reclaim' is offline (refused
;                     while an owner runs), so no connection exists when it
;                     decides; the live status count is advisory.
;   feeds, BP         not in this Store's state (feed state is the feed
;                     service's, FNBS rows the BP node's); open (PRF-088).
;
; Keystone: `fn-rcl-store-holders-hold-behind-a-lagging-consumer'.
(in-package "ACL2")
(include-book "store-reclaim")
(include-book "store-node")
(include-book "payload-arena")

; A registered consumer whose acknowledgement is below FRONTIER.
(defun fn-rcl-lagging-consumerp (entries frontier)
  (declare (xargs :guard t))
  (if (consp entries)
      (or (let ((ack (fn-cp-nth 7 (car entries))))
            (and (natp ack) (natp frontier) (< ack frontier)))
          (fn-rcl-lagging-consumerp (cdr entries) frontier))
    nil))

(defun fn-rcl-cursors-at-zero (groups)
  (declare (xargs :guard t))
  (if (consp groups)
      (if (stringp (car groups))
          (cons (cons (car groups) 0) (fn-rcl-cursors-at-zero (cdr groups)))
        (fn-rcl-cursors-at-zero (cdr groups)))
    nil))

(defun fn-rcl-store-holders (s)
  (declare (xargs :guard t :verify-guards nil))
  (let ((cp (fn-sn-consumer s)))
    (list nil
          (if (fn-rcl-lagging-consumerp (fn-cp-nth 5 cp) (fn-cp-nth 3 cp))
              (fn-rcl-cursors-at-zero
               (fn-state-groups (fn-node-acceptance (fn-sn-node s))))
            nil)
          nil
          nil)))

(local
 (defthm fn-rcl-above-zero-in-cursors
   (implies (and (member-equal g groups) (stringp g)
                 (member-equal (cons g n) (true-list-fix memberships))
                 (posp n))
            (fn-rcl-unacknowledged-p memberships (fn-rcl-cursors-at-zero groups)))
   :hints (("Goal" :induct (fn-rcl-cursors-at-zero groups)))))

(local
 (defthm fn-rcl-above-p-of-member
   (implies (and (member-equal (cons g n) (true-list-fix memberships)) (posp n))
            (fn-rcl-above-p g 0 memberships))))

;  KEYSTONE (the conservative consumer reading).  While any registered
; consumer's acknowledgement is below the committed frontier, no article
; numbered in a group the Store serves is reclaimable, whatever the rule,
; clock or verdicts.
(defthm fn-rcl-store-holders-hold-behind-a-lagging-consumer
  (let ((cp (fn-sn-consumer s)))
    (implies (and (fn-rcl-lagging-consumerp (fn-cp-nth 5 cp) (fn-cp-nth 3 cp))
                  (member-equal g (fn-state-groups (fn-node-acceptance (fn-sn-node s))))
                  (stringp g) (posp n)
                  (member-equal (cons g n) (true-list-fix (fn-article-memberships article))))
             (not (fn-rcl-reclaimable rule now (fn-rcl-store-holders s) verdicts article))))
  :hints (("Goal" :use ((:instance fn-rcl-above-zero-in-cursors
                                   (groups (fn-state-groups
                                            (fn-node-acceptance (fn-sn-node s))))
                                   (memberships (fn-article-memberships article))))
                  :in-theory (disable fn-rcl-tombstonep fn-rcl-rulep fn-rcl-rule-permits
                                      fn-rcl-pinned-p fn-rcl-undelivered-p
                                      fn-rcl-unacknowledged-p fn-rcl-above-zero-in-cursors
                                      fn-rcl-cursors-at-zero
                                      fn-rcl-verdict-heldp fn-sn-consumer))))

; -----------------------------------------------------------------------------
; The counts `status' prints: (reclaimable reclaimable-octets reclaimed
; freed-octets held).  HELD counts articles some holder keeps (reader pin,
; consumer, feed, BP), not those the rule or a verdict keeps.

(defun fn-rcl-heldp (verdict)
  (declare (xargs :guard t))
  (if (member-eq verdict '(:held-reader-pin :held-consumer-cursor :held-feed
                           :held-bp-obligation))
      t nil))

(defun fn-rcl-held-count (rule now h verdicts articles)
  (declare (xargs :guard t))
  (if (consp articles)
      (+ (if (fn-rcl-heldp (fn-rcl-verdict rule now h verdicts (car articles))) 1 0)
         (fn-rcl-held-count rule now h verdicts (cdr articles)))
    0))

; -----------------------------------------------------------------------------
; The counts over the arena (audit-fixes, 2026-09-27).  Since the acceptance
; flip an article's payload is a HANDLE into the arena
; (books/payload-arena.lisp).  `fn-rcl-summary' is the octet-list model: it
; reads the payload as octets, so over handles its two octet figures were 0
; for every article and it never saw a tombstone (an already-reclaimed
; article was counted again by its holders).  ALPHA of an article replaces its
; handle by the octets the arena holds there (an octet payload is its own);
; the counts the host calls read each length and the tombstone's fixed head
; through the arena, never copying an article's bytes, and are the model's
; counts over ALPHA (KEYSTONE fn-rcl-store-counts-is-the-model-over-alpha).
(fn-payload-kind fn-rcl-payload-bytes :handle "reads the arena at the handle")
(defun fn-rcl-payload-bytes (p fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (natp p)
      (if (< p (fn-arena-count fn-arena)) (fn-arena-payload p fn-arena) nil)
    p))
(defun fn-rcl-article-alpha (a fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (fn-make-article (fn-article-msgid a)
                   (fn-rcl-payload-bytes (fn-article-payload a) fn-arena)
                   (fn-article-groups a) (fn-article-memberships a)
                   (fn-article-pin a) (fn-article-stamp a)))
(defun fn-rcl-articles-alpha (articles fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (consp articles)
      (cons (fn-rcl-article-alpha (car articles) fn-arena)
            (fn-rcl-articles-alpha (cdr articles) fn-arena))
    nil))
(defun fn-rcl-arena-prefixp (prefix h i fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (true-listp prefix) (natp h) (natp i)
                              (< h (fn-arena-count fn-arena)))
                  :measure (len prefix)))
  (if (consp prefix)
      (and (< i (fn-arena-payload-len h fn-arena))
           (equal (car prefix) (fn-arena-get h i fn-arena))
           (fn-rcl-arena-prefixp (cdr prefix) h (+ 1 i) fn-arena))
    t))
(encapsulate ()
  (local (defthm fn-rcl-car-nthcdr (equal (car (nthcdr i xs)) (nth i xs))))
  (local (defthm fn-rcl-cdr-nthcdr
           (implies (natp i) (equal (cdr (nthcdr i xs)) (nthcdr (+ 1 i) xs)))))
  (local (defthm fn-rcl-nthcdr-of-nil (equal (nthcdr i nil) nil)))
  (local (defthm fn-rcl-consp-nthcdr
           (implies (natp i) (iff (consp (nthcdr i xs)) (< i (len xs))))))
  (local (in-theory (disable nthcdr nth)))
  (defthm fn-rcl-arena-prefixp-is-rcl-prefixp
    (implies (natp i)
             (equal (fn-rcl-arena-prefixp prefix h i fn-arena)
                    (fn-rcl-prefixp prefix (nthcdr i (nth h fn-arena)))))
    :hints (("Goal" :induct (fn-rcl-arena-prefixp prefix h i fn-arena)
             :in-theory (enable fn-rcl-prefixp fn-arena-get-is-nth
                                fn-arena-payload-len-is-len-nth)))))
(defthm fn-rcl-arena-prefixp-at-0
  (equal (fn-rcl-arena-prefixp prefix h 0 fn-arena)
         (fn-rcl-prefixp prefix (nth h fn-arena)))
  :hints (("Goal" :use ((:instance fn-rcl-arena-prefixp-is-rcl-prefixp (i 0)))
           :in-theory (enable nthcdr))))
(local
 (defthm fn-rcl-at-leastp-is-len
   (implies (natp n)
            (equal (fn-rcl-at-leastp n xs) (<= n (len xs))))
   :hints (("Goal" :in-theory (enable fn-rcl-at-leastp)))))
(local
 (defthm fn-rcl-tombstonep-unfolds
   (equal (fn-rcl-tombstonep payload)
          (and (<= *fn-rcl-tombstone-fixed* (len payload))
               (fn-rcl-prefixp *fn-rcl-magic* payload)))
   :hints (("Goal" :in-theory '(fn-rcl-tombstonep fn-rcl-at-leastp-is-len
                                 (:e natp))))))
(fn-payload-kind fn-rcl-payload-len :handle "reads the arena at the handle")
(defun fn-rcl-payload-len (p fn-arena)
  (declare (xargs :stobjs fn-arena :guard t
                  :guard-hints (("Goal" :in-theory '(fn-rcl-payload-bytes
                                                     fn-arena-payload-is-nth
                                                     fn-arena-count-is-len
                                                     fn-arena-payload-len-is-len-nth)))))
  (mbe :logic (len (fn-rcl-payload-bytes p fn-arena))
       :exec (if (and (natp p) (< p (fn-arena-count fn-arena)))
                 (fn-arena-payload-len p fn-arena)
               (len (fn-rcl-payload-bytes p fn-arena)))))
(fn-payload-kind fn-rcl-payload-tombstonep :handle "reads the arena at the handle")
(defun fn-rcl-payload-tombstonep (p fn-arena)
  (declare (xargs :stobjs fn-arena :guard t
                  :guard-hints (("Goal" :in-theory '(fn-rcl-tombstonep-unfolds
                                                     fn-rcl-payload-bytes
                                                     fn-arena-payload-is-nth
                                                     fn-arena-count-is-len
                                                     fn-arena-payload-len-is-len-nth
                                                     fn-rcl-arena-prefixp-at-0)))))
  (mbe :logic (fn-rcl-tombstonep (fn-rcl-payload-bytes p fn-arena))
       :exec (if (and (natp p) (< p (fn-arena-count fn-arena)))
                 (and (<= *fn-rcl-tombstone-fixed* (fn-arena-payload-len p fn-arena))
                      (fn-rcl-arena-prefixp *fn-rcl-magic* p 0 fn-arena))
               (fn-rcl-tombstonep (fn-rcl-payload-bytes p fn-arena)))))
; A tombstone is small (its fixed 89 octets and the Path agent), so its
; length field is read from its bytes.
(fn-payload-kind fn-rcl-payload-tomb-length :handle "reads the arena at the handle")
(defun fn-rcl-payload-tomb-length (p fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (fn-rcl-tomb-length (fn-rcl-payload-bytes p fn-arena)))

(defun fn-rcl-verdict-in (rule now h verdicts a fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (fn-rcl-payload-tombstonep (fn-article-payload a) fn-arena)
      :already-reclaimed
    (fn-rcl-standing-verdict rule now h verdicts a)))

;; `store status' over 1,000,000 articles (the format-10 syn1m-2k, lane
;; format10-import, 2026-09-28) died in 837,983 control-stack frames of
;; fn-rcl-summary-in (hbox, developer image, FN_NATIVE_FAULT_BACKTRACE): the
;; three counts below recursed once per article, and `status' runs them over
;; every article.  Each executes by a forward loop (PKT-693's pattern, lane
;; thread-stacks): the :logic is the recursion, unchanged, and the guard proof
;; is the equality (fn-rcl-summary-loop-is-the-summary,
;; fn-rcl-held-count-loop-is-the-count, fn-rcl-class-count-loop-is-the-count).
(defun fn-rcl-summary-loop (rule now h verdicts articles c0 c1 c2 c3 fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (natp c0) (natp c1) (natp c2) (natp c3))))
  (if (consp articles)
      (let* ((a (car articles))
             (p (fn-article-payload a))
             (verdict (fn-rcl-verdict-in rule now h verdicts a fn-arena)))
        (cond ((equal verdict :reclaimable)
               (fn-rcl-summary-loop rule now h verdicts (cdr articles)
                                    (+ 1 c0) (+ (fn-rcl-payload-len p fn-arena) c1)
                                    c2 c3 fn-arena))
              ((equal verdict :already-reclaimed)
               (fn-rcl-summary-loop rule now h verdicts (cdr articles)
                                    c0 c1 (+ 1 c2)
                                    (+ (nfix (- (fn-rcl-payload-tomb-length p fn-arena)
                                                (fn-rcl-payload-len p fn-arena)))
                                       c3)
                                    fn-arena))
              (t (fn-rcl-summary-loop rule now h verdicts (cdr articles)
                                      c0 c1 c2 c3 fn-arena))))
    (list c0 c1 c2 c3)))

(defun fn-rcl-summary-in (rule now h verdicts articles fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (mbe
   :logic
   (if (consp articles)
       (let* ((rest (fn-rcl-summary-in rule now h verdicts (cdr articles) fn-arena))
              (a (car articles))
              (p (fn-article-payload a))
              (verdict (fn-rcl-verdict-in rule now h verdicts a fn-arena)))
         (cond ((equal verdict :reclaimable)
                (list (+ 1 (nfix (nth 0 rest)))
                      (+ (fn-rcl-payload-len p fn-arena) (nfix (nth 1 rest)))
                      (nfix (nth 2 rest)) (nfix (nth 3 rest))))
               ((equal verdict :already-reclaimed)
                (list (nfix (nth 0 rest)) (nfix (nth 1 rest))
                      (+ 1 (nfix (nth 2 rest)))
                      (+ (nfix (- (fn-rcl-payload-tomb-length p fn-arena)
                                  (fn-rcl-payload-len p fn-arena)))
                         (nfix (nth 3 rest)))))
               (t (list (nfix (nth 0 rest)) (nfix (nth 1 rest))
                        (nfix (nth 2 rest)) (nfix (nth 3 rest))))))
     (list 0 0 0 0))
   :exec (fn-rcl-summary-loop rule now h verdicts articles 0 0 0 0 fn-arena)))

(local
 (defthm fn-rcl-payload-len-natp
   (natp (fn-rcl-payload-len p fn-arena))
   :rule-classes :type-prescription))

(local
 (defthm fn-rcl-summary-in-natp-shape
   (and (true-listp (fn-rcl-summary-in rule now h verdicts articles fn-arena))
        (equal (len (fn-rcl-summary-in rule now h verdicts articles fn-arena)) 4)
        (natp (nth 0 (fn-rcl-summary-in rule now h verdicts articles fn-arena)))
        (natp (nth 1 (fn-rcl-summary-in rule now h verdicts articles fn-arena)))
        (natp (nth 2 (fn-rcl-summary-in rule now h verdicts articles fn-arena)))
        (natp (nth 3 (fn-rcl-summary-in rule now h verdicts articles fn-arena))))
   :hints (("Goal" :induct (fn-rcl-summary-in rule now h verdicts articles fn-arena)
            :in-theory (e/d (fn-rcl-summary-in) (fn-rcl-verdict-in
                                                 fn-rcl-payload-len
                                                 fn-rcl-payload-tomb-length))))))

(local
 (defthm fn-rcl-summary-loop-is-summary-plus
   (implies (and (natp c0) (natp c1) (natp c2) (natp c3))
            (equal (fn-rcl-summary-loop rule now h verdicts articles c0 c1 c2 c3 fn-arena)
                   (let ((s (fn-rcl-summary-in rule now h verdicts articles fn-arena)))
                     (list (+ c0 (nth 0 s)) (+ c1 (nth 1 s))
                           (+ c2 (nth 2 s)) (+ c3 (nth 3 s))))))
   :hints (("Goal" :induct (fn-rcl-summary-loop rule now h verdicts articles c0 c1 c2 c3 fn-arena)
            :in-theory (e/d () (fn-rcl-verdict-in fn-rcl-payload-len
                                fn-rcl-payload-tomb-length fn-rcl-summary-in-natp-shape)))
           ("Subgoal *1/3" :use ((:instance fn-rcl-summary-in-natp-shape
                                            (articles (cdr articles)))))
           ("Subgoal *1/2" :use ((:instance fn-rcl-summary-in-natp-shape
                                            (articles (cdr articles)))))
           ("Subgoal *1/1" :use ((:instance fn-rcl-summary-in-natp-shape
                                            (articles (cdr articles))))))))

(local
 (defthm fn-rcl-four-list-is-its-elements
   (implies (and (true-listp x) (equal (len x) 4))
            (equal (list (car x) (nth 1 x) (nth 2 x) (nth 3 x)) x))
   :hints (("Goal" :expand ((len x) (len (cdr x)) (len (cddr x)) (len (cdddr x))
                            (len (cddddr x)))))
   :rule-classes nil))

; The guard proof of fn-rcl-summary-in: the loop from zero is the summary.
(defthm fn-rcl-summary-loop-is-the-summary
  (equal (fn-rcl-summary-loop rule now h verdicts articles 0 0 0 0 fn-arena)
         (fn-rcl-summary-in rule now h verdicts articles fn-arena))
  :hints (("Goal" :in-theory (disable fn-rcl-summary-in fn-rcl-summary-loop
                                      fn-rcl-summary-in-natp-shape)
           :use ((:instance fn-rcl-summary-in-natp-shape)
                 (:instance fn-rcl-four-list-is-its-elements
                            (x (fn-rcl-summary-in rule now h verdicts articles fn-arena)))))))

(verify-guards fn-rcl-summary-in
  :hints (("Goal" :in-theory (e/d (fn-rcl-summary-loop-is-the-summary)
                                  (fn-rcl-summary-in fn-rcl-summary-loop fn-rcl-verdict-in
                                   fn-rcl-payload-len fn-rcl-payload-tomb-length))
           :expand ((fn-rcl-summary-in rule now h verdicts articles fn-arena)))))

(local (in-theory (disable fn-rcl-summary-in-natp-shape)))

(defun fn-rcl-held-count-loop (rule now h verdicts articles acc fn-arena)
  (declare (xargs :stobjs fn-arena :guard (natp acc)))
  (if (consp articles)
      (fn-rcl-held-count-loop rule now h verdicts (cdr articles)
                              (if (fn-rcl-heldp (fn-rcl-verdict-in rule now h verdicts
                                                                   (car articles) fn-arena))
                                  (+ 1 acc)
                                acc)
                              fn-arena)
    acc))

(defun fn-rcl-held-count-in (rule now h verdicts articles fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (mbe :logic
       (if (consp articles)
           (+ (if (fn-rcl-heldp (fn-rcl-verdict-in rule now h verdicts (car articles) fn-arena)) 1 0)
              (fn-rcl-held-count-in rule now h verdicts (cdr articles) fn-arena))
         0)
       :exec (fn-rcl-held-count-loop rule now h verdicts articles 0 fn-arena)))

(local
 (defthm fn-rcl-held-count-loop-is-count-plus
   (implies (acl2-numberp acc)
            (equal (fn-rcl-held-count-loop rule now h verdicts articles acc fn-arena)
                   (+ acc (fn-rcl-held-count-in rule now h verdicts articles fn-arena))))
   :hints (("Goal" :induct (fn-rcl-held-count-loop rule now h verdicts articles acc fn-arena)
            :in-theory (disable fn-rcl-verdict-in fn-rcl-heldp)))))

(defthm fn-rcl-held-count-loop-is-the-count
  (equal (fn-rcl-held-count-loop rule now h verdicts articles 0 fn-arena)
         (fn-rcl-held-count-in rule now h verdicts articles fn-arena))
  :hints (("Goal" :in-theory (disable fn-rcl-held-count-in fn-rcl-held-count-loop))))

(verify-guards fn-rcl-held-count-in
  :hints (("Goal" :in-theory (e/d (fn-rcl-held-count-loop-is-the-count)
                                  (fn-rcl-held-count-in fn-rcl-held-count-loop fn-rcl-verdict-in
                                   fn-rcl-heldp))
           :expand ((fn-rcl-held-count-in rule now h verdicts articles fn-arena)))))

; PKT-878 (PRF-361, lane health-truth-status).  The Store's verdict list has
; one (msgid . verdict) entry per acceptance since the open (and the replayed
; signed ones), and `fn-rcl-verdict-heldp' scans it for an entry of MSGID
; that is not :absent -- to the END of the list for an unsigned article,
; whose own entry is :absent.  Asked once per article by the counts below,
; that made `status' O(articles x acceptances): on a 100k store after
; 20k live POSTs it passed the operator's 10 s control deadline and `status'
; exited uncertain (fitness f1, 7 of 8 samples).  Only the entries that are
; not :absent can make the test true, so the counts ask it of those
; (`fn-rcl-held-verdicts', one walk per render): O(articles x signed).
; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-rcl-held-verdicts-loop (verdicts acc)
  (declare (xargs :guard (true-listp acc) :verify-guards nil))
  (if (consp verdicts)
      (if (and (consp (car verdicts))
               (not (and (consp (cdr (car verdicts)))
                         (equal (car (cdr (car verdicts))) :absent))))
          (fn-rcl-held-verdicts-loop (cdr verdicts) (cons (car verdicts) acc))
        (fn-rcl-held-verdicts-loop (cdr verdicts) acc))
    (revappend acc nil)))

(defun fn-rcl-held-verdicts (verdicts)
  "The entries of VERDICTS that `fn-rcl-verdict-heldp' can answer true for:
a (MSGID . VERDICT) pair whose verdict is not :absent."
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp verdicts)
           (if (and (consp (car verdicts))
                    (not (and (consp (cdr (car verdicts)))
                              (equal (car (cdr (car verdicts))) :absent))))
               (cons (car verdicts) (fn-rcl-held-verdicts (cdr verdicts)))
             (fn-rcl-held-verdicts (cdr verdicts)))
         nil)
       :exec (fn-rcl-held-verdicts-loop verdicts nil)))

(local
 (defthm fn-rcl-held-verdicts-loop-is-revappend
   (equal (fn-rcl-held-verdicts-loop verdicts acc)
          (revappend acc (fn-rcl-held-verdicts verdicts)))
   :hints (("Goal" :induct (fn-rcl-held-verdicts-loop verdicts acc)
                   :in-theory (union-theories '(fn-rcl-held-verdicts-loop fn-rcl-held-verdicts revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-rcl-held-verdicts-loop)

(verify-guards fn-rcl-held-verdicts
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-rcl-held-verdicts)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-rcl-held-verdicts-loop-is-revappend (acc nil))))))


(defthm fn-rcl-verdict-heldp-of-held-verdicts
  (equal (fn-rcl-verdict-heldp msgid (fn-rcl-held-verdicts verdicts))
         (fn-rcl-verdict-heldp msgid verdicts))
  :hints (("Goal" :in-theory (enable fn-rcl-verdict-heldp))))

(defthm fn-rcl-standing-verdict-of-held-verdicts
  (equal (fn-rcl-standing-verdict rule now h (fn-rcl-held-verdicts verdicts) article)
         (fn-rcl-standing-verdict rule now h verdicts article))
  :hints (("Goal" :in-theory '(fn-rcl-standing-verdict
                               fn-rcl-verdict-heldp-of-held-verdicts))))

(defthm fn-rcl-verdict-in-of-held-verdicts
  (equal (fn-rcl-verdict-in rule now h (fn-rcl-held-verdicts verdicts) a fn-arena)
         (fn-rcl-verdict-in rule now h verdicts a fn-arena))
  :hints (("Goal" :in-theory '(fn-rcl-verdict-in
                               fn-rcl-standing-verdict-of-held-verdicts))))

(defthm fn-rcl-summary-in-of-held-verdicts
  (equal (fn-rcl-summary-in rule now h (fn-rcl-held-verdicts verdicts) articles fn-arena)
         (fn-rcl-summary-in rule now h verdicts articles fn-arena))
  :hints (("Goal" :induct (fn-rcl-summary-in rule now h verdicts articles fn-arena)
           :in-theory (e/d (fn-rcl-summary-in)
                           (fn-rcl-verdict-in fn-rcl-held-verdicts
                            fn-rcl-payload-len fn-rcl-payload-tomb-length)))))

(defthm fn-rcl-held-count-in-of-held-verdicts
  (equal (fn-rcl-held-count-in rule now h (fn-rcl-held-verdicts verdicts) articles fn-arena)
         (fn-rcl-held-count-in rule now h verdicts articles fn-arena))
  :hints (("Goal" :induct (fn-rcl-held-count-in rule now h verdicts articles fn-arena)
           :in-theory (e/d (fn-rcl-held-count-in)
                           (fn-rcl-verdict-in fn-rcl-held-verdicts fn-rcl-heldp)))))

(in-theory (disable fn-rcl-held-verdicts))

; (reclaimable reclaimable-octets reclaimed reclaimed-octets-freed held):
; what `status' prints and the reclaim verbs report.
(defun fn-rcl-store-counts (rule now s fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (let ((h (fn-rcl-store-holders s))
        (verdicts (fn-rcl-held-verdicts (fn-sn-verdicts s)))
        (articles (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
    (append (fn-rcl-summary-in rule now h verdicts articles fn-arena)
            (list (fn-rcl-held-count-in rule now h verdicts articles fn-arena)))))

(local
 (defthm fn-rcl-article-alpha-accessors
   (and (equal (fn-article-msgid (fn-rcl-article-alpha a fn-arena)) (fn-article-msgid a))
        (equal (fn-article-memberships (fn-rcl-article-alpha a fn-arena))
               (fn-article-memberships a))
        (equal (fn-article-stamp (fn-rcl-article-alpha a fn-arena)) (fn-article-stamp a))
        (equal (fn-article-payload (fn-rcl-article-alpha a fn-arena))
               (fn-rcl-payload-bytes (fn-article-payload a) fn-arena)))
   :hints (("Goal" :in-theory (e/d (fn-rcl-article-alpha) (fn-rcl-payload-bytes))))))

(local
 (defthm fn-rcl-tombstonep-of-an-atom
   (implies (not (consp p)) (not (fn-rcl-tombstonep p)))
   :hints (("Goal" :in-theory (enable fn-rcl-tombstonep fn-rcl-at-leastp)))))

; The verdict reads the payload only for the tombstone test, so the verdict
; of ALPHA is the tombstone test of the bytes, else the standing verdict of
; the article itself (which reads no payload).
(local
 (defthm fn-rcl-verdict-of-alpha
   (equal (fn-rcl-verdict rule now h verdicts (fn-rcl-article-alpha a fn-arena))
          (if (fn-rcl-tombstonep (fn-rcl-payload-bytes (fn-article-payload a) fn-arena))
              :already-reclaimed
            (fn-rcl-standing-verdict rule now h verdicts a)))
   :hints (("Goal" :in-theory (e/d (fn-rcl-verdict fn-rcl-standing-verdict
                                    fn-rcl-article-alpha-accessors)
                                   (fn-rcl-tombstonep fn-rcl-rulep fn-rcl-rule-permits
                                    fn-rcl-verdict-heldp fn-rcl-pinned-p
                                    fn-rcl-unacknowledged-p fn-rcl-undelivered-p
                                    fn-rcl-article-alpha fn-rcl-payload-bytes))))))

(defthm fn-rcl-verdict-in-is-verdict-of-alpha
  (equal (fn-rcl-verdict-in rule now h verdicts a fn-arena)
         (fn-rcl-verdict rule now h verdicts (fn-rcl-article-alpha a fn-arena)))
  :hints (("Goal" :in-theory '(fn-rcl-verdict-in fn-rcl-payload-tombstonep
                               fn-rcl-verdict-of-alpha))))

(defthm fn-rcl-summary-in-is-summary-of-alpha
  (equal (fn-rcl-summary-in rule now h verdicts articles fn-arena)
         (fn-rcl-summary rule now h verdicts (fn-rcl-articles-alpha articles fn-arena)))
  :hints (("Goal" :induct (fn-rcl-summary-in rule now h verdicts articles fn-arena)
           :in-theory (e/d (fn-rcl-summary fn-rcl-summary-in fn-rcl-articles-alpha
                            fn-rcl-payload-len fn-rcl-payload-tomb-length
                            fn-rcl-article-alpha-accessors)
                           (fn-rcl-verdict fn-rcl-verdict-in fn-rcl-standing-verdict
                            fn-rcl-tombstonep
                            fn-rcl-tomb-length fn-rcl-payload-bytes fn-rcl-article-alpha)))))

(defthm fn-rcl-held-count-in-is-held-count-of-alpha
  (equal (fn-rcl-held-count-in rule now h verdicts articles fn-arena)
         (fn-rcl-held-count rule now h verdicts (fn-rcl-articles-alpha articles fn-arena)))
  :hints (("Goal" :induct (fn-rcl-held-count-in rule now h verdicts articles fn-arena)
           :in-theory (e/d (fn-rcl-held-count fn-rcl-held-count-in fn-rcl-articles-alpha)
                           (fn-rcl-verdict fn-rcl-verdict-in fn-rcl-standing-verdict
                            fn-rcl-heldp fn-rcl-article-alpha)))))

; KEYSTONE.  The counts the host calls (status's reclaim line,
; books/native-live-status.lisp fn-nls-reclaim-words; the reclaim verb's
; decision, books/store-log-reclaim.lisp fn-lgr-decide(-stream)) are the
; octet-list model's summary and held count
; over ALPHA of the Store's articles: each reclaimable article counts its
; stored octets, each tombstone its freed octets.
(defthm fn-rcl-store-counts-is-the-model-over-alpha
  (let ((h (fn-rcl-store-holders s))
        (verdicts (fn-sn-verdicts s))
        (alpha (fn-rcl-articles-alpha
                (fn-state-articles (fn-node-acceptance (fn-sn-node s))) fn-arena)))
    (equal (fn-rcl-store-counts rule now s fn-arena)
           (append (fn-rcl-summary rule now h verdicts alpha)
                   (list (fn-rcl-held-count rule now h verdicts alpha)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-rcl-summary-in-of-held-verdicts
                                   (h (fn-rcl-store-holders s))
                                   (verdicts (fn-sn-verdicts s))
                                   (articles (fn-state-articles
                                              (fn-node-acceptance (fn-sn-node s)))))
                        (:instance fn-rcl-held-count-in-of-held-verdicts
                                   (h (fn-rcl-store-holders s))
                                   (verdicts (fn-sn-verdicts s))
                                   (articles (fn-state-articles
                                              (fn-node-acceptance (fn-sn-node s))))))
           :in-theory '(fn-rcl-store-counts fn-rcl-summary-in-is-summary-of-alpha
                        fn-rcl-held-count-in-is-held-count-of-alpha))))

; The books above reason about the counts as they did before the flip: the
; equalities stay off unless a proof names them.
(in-theory (disable fn-rcl-verdict-in-is-verdict-of-alpha
                    fn-rcl-summary-in-is-summary-of-alpha
                    fn-rcl-held-count-in-is-held-count-of-alpha))

; -----------------------------------------------------------------------------
; Why an :absent verdict holds nothing (`fn-rcl-verdict-heldp',
; books/store-reclaim).  The statement index is re-derived from the stored
; payloads at open (`fn-stx-index-of-store' over `fn-stx-delta' of each
; payload, under the keyring of that open).  The verdict the Store recorded
; for an article is `fn-stx-verdict-of-octets' of its payload under the
; keyring of its acceptance (`fn-sn-finish-records-the-acceptance-verdict',
; books/store-node-invariants).  When that verdict is :absent the payload
; contributes nothing to the index under EVERY keyring, and neither does the
; tombstone that replaces it (`fn-rcl-tombstone-contributes-nothing',
; books/reclaim-admission), so reclaiming it cannot change the index any
; later open derives from the payloads.
(defthm fn-rcl-absent-verdict-contributes-nothing
  (implies (equal (fn-stx-verdict-token (fn-stx-verdict-of-octets payload k1 g))
                  :absent)
           (equal (fn-stx-delta payload k2) nil))
  :hints (("Goal" :in-theory (enable (:d fn-stx-verdict-of-octets) (:d fn-stx-verdict)
                                     (:d fn-stx-delta) (:d fn-stx-verifiedp)
                                     (:d fn-stx-statement-of) fn-prin-verifiedp
                                     fn-stx-make-verdict fn-stx-verdict-token))))

; -----------------------------------------------------------------------------
; The retention classes (PKT-844, lane bp-retention-leftovers).  `status'
; printed articles=N beside reclaimable, held and reclaimed, and an article
; that an authorship verdict keeps (a signed article: every kind-4 composite,
; a served key statement among them) or that the rule keeps (keep-forever,
; too recent, an unusable rule) was in none of them: 24 statement
; composites were missing from the accounting in ack-before-barrier's
; power-loss campaign.  ACL2 decides each article's class:
;
;   :reclaimed    its payload is a tombstone;
;   :signed       an accepted authorship verdict other than :absent names it
;                 (STO-008): its payload is retained with the identity state
;                 that verdict belongs to, under EVERY rule, clock and holder
;                 set -- article retention never expires it
;                 (`fn-rcl-signed-article-is-never-reclaimable');
;   :reclaimable  the rule releases it now;
;   :held         a holder keeps it (reader pin, consumer, feed, BP);
;   :kept         the rule keeps it (keep-forever, too recent, a rule the
;                 store cannot apply).
;
; A signed article is :signed whatever the rule says: its reason to stay is
; the verdict, which no rule overrides.  The classes partition the articles
; (`fn-rcl-store-classes-partition-the-articles').
(defun fn-rcl-class-in (rule now h verdicts a fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (let ((verdict (fn-rcl-verdict-in rule now h verdicts a fn-arena)))
    (cond ((equal verdict :already-reclaimed) :reclaimed)
          ((fn-rcl-verdict-heldp (fn-article-msgid a) verdicts) :signed)
          ((equal verdict :reclaimable) :reclaimable)
          ((fn-rcl-heldp verdict) :held)
          (t :kept))))

(verify-guards fn-rcl-class-in)

(defun fn-rcl-class-count-loop (class rule now h verdicts articles acc fn-arena)
  (declare (xargs :stobjs fn-arena :guard (natp acc)))
  (if (consp articles)
      (fn-rcl-class-count-loop class rule now h verdicts (cdr articles)
                               (if (equal (fn-rcl-class-in rule now h verdicts
                                                           (car articles) fn-arena)
                                          class)
                                   (+ 1 acc)
                                 acc)
                               fn-arena)
    acc))

(defun fn-rcl-class-count-in (class rule now h verdicts articles fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (mbe :logic
       (if (consp articles)
           (+ (if (equal (fn-rcl-class-in rule now h verdicts (car articles) fn-arena)
                         class)
                  1 0)
              (fn-rcl-class-count-in class rule now h verdicts (cdr articles) fn-arena))
         0)
       :exec (fn-rcl-class-count-loop class rule now h verdicts articles 0 fn-arena)))

(local
 (defthm fn-rcl-class-count-loop-is-count-plus
   (implies (acl2-numberp acc)
            (equal (fn-rcl-class-count-loop class rule now h verdicts articles acc fn-arena)
                   (+ acc (fn-rcl-class-count-in class rule now h verdicts articles
                                                 fn-arena))))
   :hints (("Goal" :induct (fn-rcl-class-count-loop class rule now h verdicts articles
                                                    acc fn-arena)
            :in-theory (disable fn-rcl-class-in)))))

(defthm fn-rcl-class-count-loop-is-the-count
  (equal (fn-rcl-class-count-loop class rule now h verdicts articles 0 fn-arena)
         (fn-rcl-class-count-in class rule now h verdicts articles fn-arena))
  :hints (("Goal" :in-theory (disable fn-rcl-class-count-in fn-rcl-class-count-loop))))

(verify-guards fn-rcl-class-count-in
  :hints (("Goal" :in-theory (e/d (fn-rcl-class-count-loop-is-the-count)
                                  (fn-rcl-class-count-in fn-rcl-class-count-loop fn-rcl-class-in))
           :expand ((fn-rcl-class-count-in class rule now h verdicts articles fn-arena)))))

; (signed kept): the two classes `status' prints beside the reclaim counts.
(defun fn-rcl-store-classes (rule now s fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (let ((h (fn-rcl-store-holders s))
        (verdicts (fn-rcl-held-verdicts (fn-sn-verdicts s)))
        (articles (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
    (list (fn-rcl-class-count-in :signed rule now h verdicts articles fn-arena)
          (fn-rcl-class-count-in :kept rule now h verdicts articles fn-arena))))

;  KEYSTONE (PRF-361, PKT-878).  The classes the host prints (`status',
; books/native-live-status.lisp fn-nls-reclaim-words) are read over the held
; verdicts only, and they are the classes over EVERY verdict the Store
; carries: filtering the :absent entries out changes no article's class.
; With fn-rcl-store-counts-is-the-model-over-alpha (whose statement names the
; full verdict list), both halves of the reclaim line are the model's.
(defthm fn-rcl-class-in-of-held-verdicts
  (equal (fn-rcl-class-in rule now h (fn-rcl-held-verdicts verdicts) a fn-arena)
         (fn-rcl-class-in rule now h verdicts a fn-arena))
  :hints (("Goal" :in-theory '(fn-rcl-class-in fn-rcl-verdict-in-of-held-verdicts
                               fn-rcl-verdict-heldp-of-held-verdicts))))

(defthm fn-rcl-class-count-in-of-held-verdicts
  (equal (fn-rcl-class-count-in class rule now h (fn-rcl-held-verdicts verdicts)
                                articles fn-arena)
         (fn-rcl-class-count-in class rule now h verdicts articles fn-arena))
  :hints (("Goal" :induct (fn-rcl-class-count-in class rule now h verdicts articles
                                                 fn-arena)
           :in-theory (e/d (fn-rcl-class-count-in)
                           (fn-rcl-class-in fn-rcl-held-verdicts)))))

(defthm fn-rcl-store-classes-over-every-verdict
  (let ((h (fn-rcl-store-holders s))
        (verdicts (fn-sn-verdicts s))
        (articles (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
    (equal (fn-rcl-store-classes rule now s fn-arena)
           (list (fn-rcl-class-count-in :signed rule now h verdicts articles fn-arena)
                 (fn-rcl-class-count-in :kept rule now h verdicts articles fn-arena))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-rcl-store-classes
                               fn-rcl-class-count-in-of-held-verdicts))))

; A signed article is never released by article retention: whatever the
; rule, the instant and the holders, its verdict is not :reclaimable (the
; verdict test precedes the holder tests and the release, books/store-
; reclaim `fn-rcl-verdict').
(defthm fn-rcl-signed-article-is-never-reclaimable
  (implies (fn-rcl-verdict-heldp (fn-article-msgid article) verdicts)
           (not (fn-rcl-reclaimable rule now h verdicts article)))
  :hints (("Goal" :in-theory '(fn-rcl-reclaimable fn-rcl-standing-verdict))))

(local
 (defthm fn-rcl-class-count-in-of-cons
   (implies (consp articles)
            (equal (fn-rcl-class-count-in class rule now h verdicts articles fn-arena)
                   (+ (if (equal (fn-rcl-class-in rule now h verdicts (car articles)
                                                  fn-arena)
                                 class)
                          1 0)
                      (fn-rcl-class-count-in class rule now h verdicts (cdr articles)
                                             fn-arena))))
   :hints (("Goal" :in-theory '(fn-rcl-class-count-in)))))

(local
 (defthm fn-rcl-summary-in-shape
   (and (true-listp (fn-rcl-summary-in rule now h verdicts articles fn-arena))
        (equal (len (fn-rcl-summary-in rule now h verdicts articles fn-arena)) 4)
        (natp (nth 0 (fn-rcl-summary-in rule now h verdicts articles fn-arena)))
        (natp (nth 2 (fn-rcl-summary-in rule now h verdicts articles fn-arena))))
   :hints (("Goal" :induct (fn-rcl-summary-in rule now h verdicts articles fn-arena)
            :in-theory (e/d (fn-rcl-summary-in) (fn-rcl-verdict-in
                                                 fn-rcl-payload-len
                                                 fn-rcl-payload-tomb-length))))))

; A signed article's verdict is never a holder's and never :reclaimable.
(local
 (defthm fn-rcl-signed-verdict-in
   (implies (fn-rcl-verdict-heldp (fn-article-msgid a) verdicts)
            (and (not (equal (fn-rcl-verdict-in rule now h verdicts a fn-arena)
                             :reclaimable))
                 (not (fn-rcl-heldp (fn-rcl-verdict-in rule now h verdicts a
                                                       fn-arena)))))
   :hints (("Goal" :in-theory '(fn-rcl-verdict-in fn-rcl-standing-verdict
                                fn-rcl-heldp
                                (:e member-equal) member-equal
                                (:e fn-rcl-heldp))))))

(local
 (defthm fn-rcl-summary-in-counts-of-cons
   (implies (consp articles)
            (let ((v (fn-rcl-verdict-in rule now h verdicts (car articles) fn-arena))
                  (rest (fn-rcl-summary-in rule now h verdicts (cdr articles) fn-arena)))
              (and (equal (nth 0 (fn-rcl-summary-in rule now h verdicts articles fn-arena))
                          (+ (if (equal v :reclaimable) 1 0) (nth 0 rest)))
                   (equal (nth 2 (fn-rcl-summary-in rule now h verdicts articles fn-arena))
                          (+ (if (equal v :already-reclaimed) 1 0) (nth 2 rest))))))
   :hints (("Goal" :expand ((fn-rcl-summary-in rule now h verdicts articles fn-arena))
            :use ((:instance fn-rcl-summary-in-shape (articles (cdr articles))))
            :in-theory (e/d () (fn-rcl-summary-in fn-rcl-verdict-in
                                fn-rcl-payload-len fn-rcl-payload-tomb-length
                                fn-rcl-summary-in-shape))))))

(local
 (defthm fn-rcl-held-count-in-of-cons
   (implies (consp articles)
            (equal (fn-rcl-held-count-in rule now h verdicts articles fn-arena)
                   (+ (if (fn-rcl-heldp (fn-rcl-verdict-in rule now h verdicts
                                                           (car articles) fn-arena))
                          1 0)
                      (fn-rcl-held-count-in rule now h verdicts (cdr articles)
                                            fn-arena))))
   :hints (("Goal" :in-theory '(fn-rcl-held-count-in)))))

; One article is in exactly one class.
(local
 (defthm fn-rcl-one-article-one-class
   (let ((v (fn-rcl-verdict-in rule now h verdicts a fn-arena))
         (c (fn-rcl-class-in rule now h verdicts a fn-arena)))
     (equal (+ (if (equal v :reclaimable) 1 0)
               (if (equal v :already-reclaimed) 1 0)
               (if (fn-rcl-heldp v) 1 0)
               (if (equal c :signed) 1 0)
               (if (equal c :kept) 1 0))
            1))
   :hints (("Goal" :use ((:instance fn-rcl-signed-verdict-in))
            :in-theory '(fn-rcl-class-in fn-rcl-heldp (:e member-equal)
                         member-equal (:e fn-rcl-heldp))))))

(local
 (defthm fn-rcl-classes-partition-in
   (equal (+ (nth 0 (fn-rcl-summary-in rule now h verdicts articles fn-arena))
             (nth 2 (fn-rcl-summary-in rule now h verdicts articles fn-arena))
             (fn-rcl-held-count-in rule now h verdicts articles fn-arena)
             (fn-rcl-class-count-in :signed rule now h verdicts articles fn-arena)
             (fn-rcl-class-count-in :kept rule now h verdicts articles fn-arena))
          (len articles))
   :hints (("Goal" :induct (len articles)
            :in-theory (e/d (len)
                            (fn-rcl-summary-in fn-rcl-held-count-in
                             fn-rcl-class-count-in fn-rcl-class-in
                             fn-rcl-verdict-in fn-rcl-heldp fn-rcl-verdict-heldp
                             fn-rcl-payload-len fn-rcl-payload-tomb-length)))
           ("Subgoal *1/2" :expand ((fn-rcl-summary-in rule now h verdicts articles fn-arena)
                                    (fn-rcl-held-count-in rule now h verdicts articles fn-arena)
                                    (fn-rcl-class-count-in :signed rule now h verdicts articles
                                                           fn-arena)
                                    (fn-rcl-class-count-in :kept rule now h verdicts articles
                                                           fn-arena)))
           ("Subgoal *1/1" :use ((:instance fn-rcl-one-article-one-class
                                             (a (car articles))))))))

(local
 (defthm fn-rcl-nth-of-four-and-one
   (implies (and (true-listp l) (equal (len l) 4))
            (and (equal (nth 0 (append l (list x))) (nth 0 l))
                 (equal (nth 2 (append l (list x))) (nth 2 l))
                 (equal (nth 4 (append l (list x))) x)))
   :hints (("Goal" :expand ((len l) (len (cdr l)) (len (cddr l)) (len (cdddr l))
                            (len (cddddr l)) (true-listp l) (true-listp (cdr l))
                            (true-listp (cddr l)) (true-listp (cdddr l))
                            (true-listp (cddddr l)))))))

;  KEYSTONE (PKT-844: every article is in exactly one class).  The counts
; `status' prints (books/native-live-status.lisp fn-nls-reclaim-words:
; reclaimable, reclaimed and held from `fn-rcl-store-counts', signed and kept
; from `fn-rcl-store-classes') sum to the Store's article count, the
; articles=N of the same report.
(defthm fn-rcl-store-classes-partition-the-articles
  (let ((counts (fn-rcl-store-counts rule now s fn-arena))
        (classes (fn-rcl-store-classes rule now s fn-arena)))
    (equal (+ (nth 0 counts) (nth 2 counts) (nth 4 counts)
              (nth 0 classes) (nth 1 classes))
           (len (fn-state-articles (fn-node-acceptance (fn-sn-node s))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-rcl-classes-partition-in
                                   (h (fn-rcl-store-holders s))
                                   (verdicts (fn-rcl-held-verdicts (fn-sn-verdicts s)))
                                   (articles (fn-state-articles
                                              (fn-node-acceptance (fn-sn-node s))))))
           :in-theory '(fn-rcl-store-counts fn-rcl-store-classes
                        fn-rcl-summary-in-shape fn-rcl-nth-of-four-and-one
                        nth-0-cons nth-add1 car-cons cdr-cons (:e nth)
                        (:e zp) (:e binary-+) (:e unary--)))))
