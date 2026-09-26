; fn: the owner's automatic checkpoint publication through the octet buffer,
; decided before it is encoded (lane checkpoint-capture-stream, 2026-09-26;
; PKT-492, PKT-315, PKT-191; D27).
;
; `fn-ock-publication' (owner-checkpoint-open) is the list codec's
; publication: `(fn-scc-file-octets (fn-sco-freeze next) seg)', five to six
; octet-list copies of the file at sixteen bytes per octet.  On the served
; owner that killed the process: at N = 32,729 x 2 KiB the automatic capture
; exhausted SBCL's 32,000 MiB dynamic space inside `fn-scc-frames'
; (planning/evidence/service-envelope-2026-09-26.md), every connection lost
; and one POST uncertain.  The verb already publishes as a plan over the
; octet buffer (`fn-sccb-plan', store-checkpoint-buffer, PRF-133); the owner
; did not.
;
; This book is the owner's entry over the buffer, `fn-ock-publication-stream',
; and the decision that precedes the encode:
;
; 1. The ESTIMATE `fn-ockb-file-len' is the encoded file's length, computed
;    by a walk that allocates nothing (`fn-ockb-len-acc': the cdr recursion
;    in tail position with the count of owed CONS ops, as `fn-sccb-renc'
;    writes; a payload leaf costs its `len', never a copy).  It IS the
;    length, not a bound: `fn-ockb-file-len-is-len-file-octets'.
; 2. The BUDGET is the operator's profile: `fn-ock-capture-budget' is the
;    file bound the open already refuses a checkpoint past
;    (`fn-sccr-file-read-bound', store-checkpoint-reader: three times
;    max-history-octets plus one segment's framing; `fn-sco-select' then
;    answers (:full-replay :checkpoint-exceeds-bound)).  The owner never
;    spends an encode on a file the open would refuse.  It bounds the work of
;    one publication by the profile's declared history (D27: a constant that
;    caps data is a defect; a profile bound is the operator's), never the
;    data a store may hold.
; 3. The DECISION: the codec's refusal first (:unencodable, exactly where
;    `fn-ock-publication' answers it:
;    `fn-ock-publication-stream-refuses-what-the-codec-refuses'); then the
;    deferral by name, (:deferred :exceeds-budget ESTIMATE BUDGET), exactly
;    when the file's length exceeds the budget
;    (`fn-ock-publication-stream-defers-by-the-estimate'); else the plan.  A
;    recorded deferral blocks the next attempt while the budget is below its
;    estimate (`fn-ock-publication-blockedp', on the due path,
;    host/owner-host.lisp `fn-owner-sco-due'): the estimate only grows with
;    the history, so a retry at every commit would be an O(N) walk per POST
;    for nothing; the deferral lifts when the profile's budget is raised, or
;    at the next owner start.
;
; KEYSTONE `fn-ock-publication-stream-writes-the-file' (PRF-183): when the
; verdict is a plan, the plan's octets over the buffer it leaves
; (`fn-sccb-plan-octets', what the host writes) are `fn-ock-publication''s
; file octets, `fn-scc-file-octets' of the same frozen checkpoint, by
; `fn-sccb-plan-is-file-octets' (PRF-133, cited); NEXT is
; `fn-ock-publication''s NEXT, so `fn-ock-publication-is-the-capture-at-the-
; capture-point' (PRF-104) transfers.  The host (host/native/owner.lisp
; `fnn-owner-publish-captured') calls this entry on the publication thread
; with the PUBLICATION buffer `fn-octets-pub' below, a second stobj
; congruent to `fn-octets': the served POST fills and reads `fn-octets' under
; the service mutex (`fnn-owner-attempt'), the publication runs off it, and
; one buffer per thread is the discipline.

(in-package "ACL2")
(include-book "owner-checkpoint-open")
(include-book "store-checkpoint-reader")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; The publication buffer: a second abstract stobj congruent to `fn-octets'
; (the same foundation, the same :logic/:exec pairs, new names), admitted by
; the congruent stobj's obligations (octets-stobj); its live object is its
; own (`create-fn-octets$c' once per abstract stobj).  `fn-sccb-plan',
; written over `fn-octets', takes it as the congruent argument.

(defabsstobj fn-octets-pub
  :foundation fn-octets$c
  :recognizer (fn-octets-pub-p :logic fn-octets$ap :exec fn-octets$cp)
  :creator (create-fn-octets-pub :logic create-fn-octets$a :exec create-fn-octets$c)
  :exports ((fn-octets-pub-len :logic fn-octets$a-len :exec fn-octets$c-len)
            (fn-octets-pub-get :logic fn-octets$a-get :exec fn-octets$c-get)
            (fn-octets-pub-put :logic fn-octets$a-put :exec fn-octets$c-put :protect t)
            (fn-octets-pub-append-octet :logic fn-octets$a-append-octet
                                        :exec fn-octets$c-append-octet :protect t)
            (fn-octets-pub-clear :logic fn-octets$a-clear :exec fn-octets$c-clear)
            (fn-octets-pub-reserve :logic fn-octets$a-reserve :exec fn-octets$c-reserve
                                   :protect t)
            (fn-octets-pub-list :logic fn-octets$a-list :exec fn-octets$c-list)
            (fn-octets-pub-from-list :logic fn-octets$a-from-list
                                     :exec fn-octets$c-from-list :protect t)
            (fn-octets-pub-append-list :logic fn-octets$a-append-list
                                       :exec fn-oct-write-list :protect t))
  :congruent-to fn-octets)

; -----------------------------------------------------------------------------
; The estimate: the encoded file's length, before any encode.

(local
 (defthm fn-ockb-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))

; The length of `fn-scc-program x', plus N (the CONS ops the callers' spines
; owe) plus ACC, in the recursion `fn-sccb-renc' writes with: the car owes
; nothing, the cdr owes one more.  A value the codec refuses is not measured
; (the branch is behind `fn-sccb-treep' in the entry).
(defun fn-ockb-len-acc (x n acc)
  (declare (xargs :guard (and (natp n) (natp acc))
                  :measure (acl2-count x)
                  :verify-guards nil))
  (cond ((fn-scc-octets-valuep x)
         (+ acc 1 (len (fn-scc-nat-octets (len x))) (len x) (nfix n)))
        ((consp x)
         (fn-ockb-len-acc (cdr x) (+ 1 (nfix n)) (fn-ockb-len-acc (car x) 0 acc)))
        ((fn-scc-atomp x)
         (+ acc (len (fn-scc-atom-octets x)) (nfix n)))
        (t (+ acc (nfix n)))))

(defthm fn-ockb-len-acc-natp
  (implies (natp acc) (natp (fn-ockb-len-acc x n acc)))
  :rule-classes :type-prescription)

(verify-guards fn-ockb-len-acc)

(defthm fn-ockb-len-acc-is-len-program
  (implies (fn-scc-treep x)
           (equal (fn-ockb-len-acc x n acc)
                  (+ (fix acc) (nfix n) (len (fn-scc-program x)))))
  :hints (("Goal" :induct (fn-ockb-len-acc x n acc)
           :in-theory (e/d () (fn-scc-atom-octets fn-scc-nat-octets fn-scc-atomp
                               fn-scc-octets-valuep)))))

(defun fn-ockb-program-len (x)
  (declare (xargs :guard t))
  (fn-ockb-len-acc x 0 0))

(defthm fn-ockb-program-len-is-len-program
  (implies (fn-scc-treep x)
           (equal (fn-ockb-program-len x) (len (fn-scc-program x)))))

(defthm fn-ockb-program-len-natp
  (natp (fn-ockb-program-len x))
  :rule-classes :type-prescription)

(in-theory (disable fn-ockb-program-len))

; One header and one trailer per segment.
(defconst *fn-ockb-frame-octets*
  (+ *fn-scc-segment-header-octets* *fn-frame-trailer-octets*))

(defun fn-ockb-file-len (c seg)
  (declare (xargs :guard (natp seg)))
  (let ((p (fn-ockb-program-len c)))
    (+ p (* (fn-sccb-chunk-count p seg) *fn-ockb-frame-octets*))))

; The frames' lengths, from the codec's own shape: a header is 37 octets, a
; seal of an octet chain 32, a chunk its own length.  (The seal and header
; facts are the reader's local lemmas restated; the chain's trailers are
; octet lists by `fn-frame-trailer-is-a-digest'.)
(local
 (defthm fn-ockb-octet-listp-append
   (implies (and (fn-scc-octet-listp a) (fn-scc-octet-listp b))
            (fn-scc-octet-listp (append a b)))))

(local
 (defthm fn-ockb-header-shape
   (and (fn-scc-octet-listp (fn-scc-header index count length sequence))
        (equal (len (fn-scc-header index count length sequence))
               *fn-scc-segment-header-octets*))
   :hints (("Goal" :in-theory (enable fn-scc-header)))))

(local
 (defthm fn-ockb-seal-is-digest
   (implies (and (fn-scc-octet-listp prev) (fn-scc-octet-listp header)
                 (fn-scc-octet-listp chunk))
            (and (fn-scc-octet-listp (fn-scc-seal prev header chunk))
                 (equal (len (fn-scc-seal prev header chunk)) *fn-frame-trailer-octets*)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-frame-trailer-is-a-digest
                             (octets (append prev header chunk))))
            :in-theory (e/d (fn-scc-seal fn-frame-digestp)
                            (fn-frame-trailer-is-a-digest))))))

(defun fn-ockb-sum-len (chunks)
  (declare (xargs :guard t))
  (if (consp chunks) (+ (len (car chunks)) (fn-ockb-sum-len (cdr chunks))) 0))

(defun fn-ockb-octet-list-listp (chunks)
  (declare (xargs :guard t))
  (if (consp chunks)
      (and (fn-scc-octet-listp (car chunks)) (fn-ockb-octet-list-listp (cdr chunks)))
    t))

(local
 (defthm fn-ockb-len-true-list-fix
   (equal (len (true-list-fix x)) (len x))))

(local
 (defthm fn-ockb-concat-of-frames-len
   (implies (and (fn-scc-octet-listp prev) (fn-ockb-octet-list-listp chunks))
            (equal (len (fn-scc-concat (fn-scc-frames chunks index count sequence prev)))
                   (+ (fn-ockb-sum-len chunks)
                      (* *fn-ockb-frame-octets* (len chunks)))))
   :hints (("Goal" :induct (fn-scc-frames chunks index count sequence prev)
            :in-theory (e/d () (fn-scc-header fn-scc-seal))))))

(local
 (defthm fn-ockb-long-enoughp-is-len
   (implies (natp n)
            (equal (fn-scc-long-enoughp n xs) (<= n (len xs))))))

(local
 (defthm fn-ockb-octet-listp-take
   (implies (and (fn-scc-octet-listp p) (natp k) (<= k (len p)))
            (fn-scc-octet-listp (take k p)))))

(local
 (defthm fn-ockb-octet-listp-nthcdr
   (implies (fn-scc-octet-listp p)
            (fn-scc-octet-listp (nthcdr k p)))))

(local
 (defthm fn-ockb-len-take
   (equal (len (take k x)) (nfix k))))

(local
 (defthm fn-ockb-len-nthcdr
   (implies (and (natp n) (<= n (len xs)))
            (equal (len (nthcdr n xs)) (- (len xs) n)))))

(local
 (defthm fn-ockb-chunks-octet-lists
   (implies (fn-scc-octet-listp p)
            (fn-ockb-octet-list-listp (fn-scc-chunks p seg)))
   :hints (("Goal" :induct (fn-scc-chunks p seg)))))

(local
 (defthm fn-ockb-sum-len-of-chunks
   (implies (true-listp p)
            (equal (fn-ockb-sum-len (fn-scc-chunks p seg)) (len p)))
   :hints (("Goal" :induct (fn-scc-chunks p seg)))))

(local
 (defthm fn-ockb-octet-listp-true-listp
   (implies (fn-scc-octet-listp p) (true-listp p))))

; The estimate is the encoded file's length, for every value the buffer
; codec encodes (`fn-sccb-treep': `fn-scc-treep' with every leaf's octets
; octets, the domain of PRF-133).
(defthm fn-ockb-file-len-is-len-file-octets
  (implies (fn-sccb-treep c)
           (equal (len (fn-scc-file-octets c seg)) (fn-ockb-file-len c seg)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-sccb-treep-encodes-octets (x c))
                 (:instance fn-sccb-treep-is-treep (x c))
                 (:instance fn-sccb-chunk-count-is-len-chunks (p (fn-scc-program c)))
                 (:instance fn-ockb-program-len-is-len-program (x c))
                 (:instance fn-ockb-concat-of-frames-len
                            (chunks (fn-scc-chunks (fn-scc-program c) seg))
                            (index 0)
                            (count (len (fn-scc-chunks (fn-scc-program c) seg)))
                            (sequence (fn-scc-value-sequence c))
                            (prev *fn-scc-genesis*)))
           :in-theory (e/d (fn-scc-file-octets fn-scc-segments fn-ockb-file-len
                            fn-scc-encode-is-program)
                           (fn-scc-frames fn-scc-chunks fn-scc-concat fn-scc-program
                            fn-scc-treep fn-sccb-treep fn-scc-value-sequence
                            fn-sccb-chunk-count fn-sccb-treep-encodes-octets
                            fn-sccb-chunk-count-is-len-chunks
                            fn-ockb-program-len-is-len-program
                            fn-sccb-treep-is-treep fn-ockb-concat-of-frames-len)))))

; -----------------------------------------------------------------------------
; The budget and the decision.

; The profile's file bound for a checkpoint: what the open refuses a file
; past (store-checkpoint-reader `fn-sccr-file-read-bound'; the same
; derivation host/store-node-host.lisp `fn-store-sco-file-read-bound' hands
; the reader).
(defun fn-ock-capture-budget (profile)
  (declare (xargs :guard t))
  (fn-sccr-file-read-bound (fn-bs-profile-max-history-octets profile)
                           (fn-bs-profile-max-record-octets profile)))

(defthm fn-ock-capture-budget-natp
  (natp (fn-ock-capture-budget profile))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (fn-sccr-file-read-bound fn-scc-segment-max-octets)
                                  (fn-bs-profile-max-history-octets
                                   fn-bs-profile-max-record-octets)))))

; A recorded deferral (:deferred REASON ESTIMATE BUDGET0) blocks the next
; attempt while BUDGET is below its ESTIMATE.
(defun fn-ock-publication-blockedp (deferred budget)
  (declare (xargs :guard t))
  (and (consp deferred) (eq (car deferred) :deferred)
       (consp (cdr deferred)) (consp (cddr deferred))
       (natp (caddr deferred))
       (< (nfix budget) (caddr deferred))))

; The host-called entry (host/native/owner.lisp `fnn-owner-publish-captured',
; on the publication thread, with the publication buffer): (mv NEXT VERDICT
; fn-octets).  NEXT is `fn-ock-publication''s.  VERDICT is :unencodable (the
; codec's refusal), (:deferred :exceeds-budget ESTIMATE BUDGET) (the owner's
; deferral; nothing was encoded), or (:plan PLAN ESTIMATE) with the program
; in the buffer and PLAN over it (`fn-sccb-plan').
(defun fn-ock-publication-stream (base configs records segment-octets budget fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp segment-octets) (natp budget))
                  :verify-guards nil))
  (let* ((next (fn-ock-next-checkpoint base configs records))
         (frozen (fn-sco-freeze next)))
    (if (not (fn-sccb-treep frozen))
        (mv next :unencodable fn-octets)
      (let ((estimate (fn-ockb-file-len frozen segment-octets)))
        (if (< budget estimate)
            (mv next (list :deferred :exceeds-budget estimate budget) fn-octets)
          (mv-let (plan fn-octets)
            (fn-sccb-plan frozen segment-octets fn-octets)
            (mv next (list :plan plan estimate) fn-octets)))))))

(verify-guards fn-ock-publication-stream)

; NEXT is the list entry's NEXT: the capture of the history at the capture
; point (fn-ock-publication-is-the-capture-at-the-capture-point, cited).
(defthm fn-ock-publication-stream-next-is-the-capture
  (implies (fn-sn-observed-historyp frontier records)
           (equal (mv-nth 0 (fn-ock-publication-stream (fn-sco-capture configs prefix)
                                                       configs records seg budget fn-octets))
                  (fn-sco-capture configs records)))
  :hints (("Goal" :use fn-ock-next-checkpoint-is-the-capture
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-ock-publication-stream mv-nth car-cons)))))

; KEYSTONE (PRF-183).  When the entry answers a plan, the plan's octets over
; the buffer it leaves are the list publication's file octets: byte for
; byte what `fn-ock-publication' would have listed, by
; fn-sccb-plan-is-file-octets (PRF-133).
(defthm fn-ock-publication-stream-writes-the-file
  (implies (equal (car (mv-nth 1 (fn-ock-publication-stream base configs records seg
                                                            budget fn-octets)))
                  :plan)
           (equal (fn-sccb-plan-octets
                   (cadr (mv-nth 1 (fn-ock-publication-stream base configs records seg
                                                              budget fn-octets)))
                   (mv-nth 2 (fn-ock-publication-stream base configs records seg
                                                        budget fn-octets)))
                  (cadr (fn-ock-publication base configs records seg))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-sccb-plan-is-file-octets
                            (c (fn-sco-freeze (fn-ock-next-checkpoint base configs records)))
                            (seg seg)))
           :in-theory (e/d (fn-ock-publication-stream fn-ock-publication)
                           (fn-ock-next-checkpoint fn-sco-freeze fn-sccb-treep
                            fn-ockb-file-len fn-sccb-plan fn-sccb-plan-octets
                            fn-scc-file-octets fn-sccb-plan-is-file-octets)))))

; Where the list codec refused, the entry refuses, and nothing else is a
; refusal: the :unencodable cases agree.
(defthm fn-ock-publication-stream-refuses-what-the-codec-refuses
  (implies (not (fn-scc-treep (fn-sco-freeze (fn-ock-next-checkpoint base configs records))))
           (and (equal (mv-nth 1 (fn-ock-publication-stream base configs records seg
                                                            budget fn-octets))
                       :unencodable)
                (equal (cadr (fn-ock-publication base configs records seg))
                       :unencodable)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-sccb-treep-is-treep
                            (x (fn-sco-freeze (fn-ock-next-checkpoint base configs records)))))
           :in-theory (e/d (fn-ock-publication-stream fn-ock-publication
                            fn-scc-file-octets fn-scc-segments)
                           (fn-ock-next-checkpoint fn-sco-freeze fn-sccb-treep fn-scc-treep
                            fn-ockb-file-len fn-sccb-plan fn-scc-frames fn-scc-chunks
                            fn-scc-encode fn-scc-concat fn-scc-value-sequence
                            fn-sccb-treep-is-treep)))))

; The refusal theorem of PKT-492.  For an encodable checkpoint the entry
; defers exactly when the file it would write is longer than the budget,
; names the file's length and the budget, and otherwise answers the plan.
(defthm fn-ock-publication-stream-defers-by-the-estimate
  (implies (fn-sccb-treep (fn-sco-freeze (fn-ock-next-checkpoint base configs records)))
           (let ((estimate (len (fn-scc-file-octets
                                 (fn-sco-freeze (fn-ock-next-checkpoint base configs records))
                                 seg)))
                 (verdict (mv-nth 1 (fn-ock-publication-stream base configs records seg
                                                               budget fn-octets))))
             (and (iff (< budget estimate) (equal (car verdict) :deferred))
                  (implies (< budget estimate)
                           (equal verdict (list :deferred :exceeds-budget estimate budget)))
                  (implies (not (< budget estimate))
                           (equal (car verdict) :plan)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-ockb-file-len-is-len-file-octets
                            (c (fn-sco-freeze (fn-ock-next-checkpoint base configs records)))
                            (seg seg)))
           :in-theory (e/d (fn-ock-publication-stream)
                           (fn-ock-next-checkpoint fn-sco-freeze fn-sccb-treep
                            fn-ockb-file-len fn-sccb-plan fn-scc-file-octets
                            fn-ockb-file-len-is-len-file-octets)))))

; A deferral blocks while the budget is below the estimate it named, by
; definition (the due path, host/owner-host.lisp `fn-owner-sco-due').  A
; deferred verdict only comes from an encodable value (an unencodable one
; is refused first), so no tree hypothesis is stated: the weakened theorem
; is the one proved.
(defthm fn-ock-publication-blockedp-by-definition
  (implies (equal (car (mv-nth 1 (fn-ock-publication-stream base configs records seg
                                                            budget fn-octets)))
                  :deferred)
           (iff (fn-ock-publication-blockedp
                 (mv-nth 1 (fn-ock-publication-stream base configs records seg budget fn-octets))
                 later-budget)
                (< (nfix later-budget)
                   (len (fn-scc-file-octets
                         (fn-sco-freeze (fn-ock-next-checkpoint base configs records))
                         seg)))))
  :hints (("Goal" :do-not-induct t
           :cases ((fn-sccb-treep (fn-sco-freeze (fn-ock-next-checkpoint base configs records))))
           :use fn-ock-publication-stream-defers-by-the-estimate
           :in-theory (e/d (fn-ock-publication-blockedp fn-ock-publication-stream)
                           (fn-ock-next-checkpoint fn-sco-freeze fn-sccb-treep
                            fn-scc-file-octets fn-ockb-file-len fn-sccb-plan
                            fn-ock-publication-stream-defers-by-the-estimate)))))

(in-theory (disable fn-ockb-len-acc fn-ockb-file-len fn-ock-publication-stream
                    fn-ock-publication-blockedp fn-ock-capture-budget))
