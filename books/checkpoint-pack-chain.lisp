; fn: chained packs (M5, D27 packet P5; specs/storage.md "Chained packs").
;
; A pack is one link of a chain.  Link N covers the Store events
; [LOWER, BOUNDARY) and names its predecessor by generation and by the
; predecessor's frame digest (the 32-octet trailer the host's seal appended).
; Links are contiguous: a link's LOWER is its predecessor's BOUNDARY and its
; lower frontier is its predecessor's frontier.  The first link has LOWER 0 and
; no predecessor; a version-0 pack (books/checkpoint-compaction) is such a
; first link.  The selection marker names the newest link.
;
; A compaction packs only the uncovered suffix, one link per scheduling
; quantum (`*fn-cc-max-events*' events and `*fn-cc-max-octets*' octets, the
; open's largest single read), and always at least one event, so no record
; size is refused by the quantum.  The quantum bounds work per link, never
; the history: the chain has at most BOUNDARY links, and BOUNDARY is at most
; the committed count, which the profile's max-transactions bounds
; (`fn-ccc-walk-bound', the fuel the host's walk is given).
;
; The subjects the host calls (host/checkpoint-host.lisp):
;   `fn-ccc-capture-link'   `fn-store-checkpoint-chain-capture'
;   `fn-ccc-entry-step'     `fn-store-checkpoint-chain-step' (the walk)
;   `fn-ccc-observe-chain'  `fn-store-checkpoint-chain-observe' (the open)
;   `fn-ccc-coverage-chain' `fn-store-checkpoint-chain-coverage'
;   `fn-ccc-retire-plan'    `fn-store-checkpoint-chain-retire-plan'
;   `fn-ccc-walk-bound'     `fn-store-checkpoint-chain-walk-bound'
(in-package "ACL2")
(include-book "checkpoint-compaction-preservation")
(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (disable fn-cc-decode-exact fn-store-event-decode-exact
                           fn-cc-recover-observation)))

(defconst *fn-ccc-version* 1)

; -----------------------------------------------------------------------------
; The link

; (:fn-pack-link 1 lower boundary lower-frontier frontier pred-generation
;                pred-digest events)
(defun fn-ccc-make (lower boundary lower-frontier frontier pred-generation
                          pred-digest events)
  (declare (xargs :guard t))
  (list :fn-pack-link 1 lower boundary lower-frontier frontier pred-generation
        pred-digest events))
(defun fn-ccc-lower (l) (declare (xargs :guard t)) (fn-cc-nth 2 l))
(defun fn-ccc-boundary (l) (declare (xargs :guard t)) (fn-cc-nth 3 l))
(defun fn-ccc-lower-frontier (l) (declare (xargs :guard t)) (fn-cc-nth 4 l))
(defun fn-ccc-frontier (l) (declare (xargs :guard t)) (fn-cc-nth 5 l))
(defun fn-ccc-pred-generation (l) (declare (xargs :guard t)) (fn-cc-nth 6 l))
(defun fn-ccc-pred-digest (l) (declare (xargs :guard t)) (fn-cc-nth 7 l))
(defun fn-ccc-events (l) (declare (xargs :guard t)) (fn-cc-nth 8 l))

(defun fn-ccc-linkp (l)
  (declare (xargs :guard t :verify-guards nil))
  (and (true-listp l) (equal (len l) 9)
       (equal (fn-cc-nth 0 l) :fn-pack-link)
       (equal (fn-cc-nth 1 l) 1)
       (fn-record-uint32p (fn-ccc-lower l))
       (fn-record-uint32p (fn-ccc-boundary l))
       (fn-record-uint32p (fn-ccc-lower-frontier l))
       (fn-record-uint32p (fn-ccc-frontier l))
       (fn-record-uint32p (fn-ccc-pred-generation l))
       (fn-cbor-octet-listp (fn-ccc-pred-digest l))
       (< (fn-ccc-lower l) (fn-ccc-boundary l))
       (<= (fn-ccc-lower-frontier l) (fn-ccc-frontier l))
       (equal (len (fn-ccc-events l))
              (- (fn-ccc-boundary l) (fn-ccc-lower l)))
       (fn-cc-octet-event-listp (fn-ccc-events l) (fn-ccc-lower l)
                                (fn-ccc-lower-frontier l) (fn-ccc-frontier l))))

; A version-0 pack is the first link of its chain.
(defun fn-ccc-link-of-summary (summary)
  (declare (xargs :guard t))
  (fn-ccc-make 0 (fn-cc-sequence summary) 0 (fn-cc-frontier summary) 0 nil
               (fn-cc-events summary)))

; -----------------------------------------------------------------------------
; The chain the host walked, newest first: ENTRIES are (GENERATION LINK DIGEST)
; with LINK decoded; `fn-ccc-decode-entries' below produces them from bytes.

(defun fn-ccc-entry-generation (e) (declare (xargs :guard t)) (fn-cc-nth 0 e))
(defun fn-ccc-entry-link (e) (declare (xargs :guard t)) (fn-cc-nth 1 e))
(defun fn-ccc-entry-digest (e) (declare (xargs :guard t)) (fn-cc-nth 2 e))

(defun fn-ccc-links-okp (entries)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp entries)
      (let ((l (fn-ccc-entry-link (car entries))))
        (and (fn-ccc-linkp l)
             (if (zp (fn-ccc-lower l))
                 (and (equal (fn-ccc-lower-frontier l) 0)
                      (null (cdr entries)))
               (and (consp (cdr entries))
                    (let ((p (cadr entries)))
                      (and (equal (fn-ccc-lower l)
                                  (fn-ccc-boundary (fn-ccc-entry-link p)))
                           (equal (fn-ccc-lower-frontier l)
                                  (fn-ccc-frontier (fn-ccc-entry-link p)))
                           (equal (fn-ccc-pred-generation l)
                                  (fn-ccc-entry-generation p))
                           (equal (fn-ccc-pred-digest l)
                                  (fn-ccc-entry-digest p))))
                    (fn-ccc-links-okp (cdr entries))))))
    nil))

; The chain's records, oldest link first.
(defun fn-ccc-links-events (entries)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp entries)
      (append (fn-ccc-links-events (cdr entries))
              (fn-ccc-events (fn-ccc-entry-link (car entries))))
    nil))

(defun fn-ccc-head-link (entries)
  (declare (xargs :guard t))
  (fn-ccc-entry-link (fn-cc-nth 0 entries)))

(local
 (defthm fn-ccc-nth-0-of-cons
   (implies (consp x) (equal (fn-cc-nth 0 x) (car x)))
   :hints (("Goal" :in-theory (enable fn-cc-nth)))))

(local
 (defthm fn-ccc-nth-of-cons
   (implies (not (zp n))
            (equal (fn-cc-nth n (cons a b)) (fn-cc-nth (1- n) b)))
   :hints (("Goal" :in-theory (enable fn-cc-nth)))))

; The whole chain as one prefix summary: every link's records from sequence
; 0, under the newest link's frontier.  The PRF-073 machinery
; (`fn-cc-recover-observation') applies to it unchanged.
(defun fn-ccc-chain-summary (entries)
  (declare (xargs :guard t :verify-guards nil))
  (fn-cc-make (fn-ccc-boundary (fn-ccc-head-link entries))
              (fn-ccc-frontier (fn-ccc-head-link entries))
              (fn-ccc-links-events entries)))

; -----------------------------------------------------------------------------
; Composition: contiguous links are one valid prefix

(local
 (defthm fn-ccc-event-list-lower-weakens
   (implies (and (fn-cc-octet-event-listp events s lower upper)
                 (rationalp low2) (<= low2 lower))
            (fn-cc-octet-event-listp events s low2 upper))
   :hints (("Goal" :in-theory (enable fn-cc-octet-event-listp)))))

(local
 (defthm fn-ccc-event-list-upper-weakens
   (implies (and (fn-cc-octet-event-listp events s lower upper)
                 (rationalp up2) (<= upper up2))
            (fn-cc-octet-event-listp events s lower up2))
   :hints (("Goal" :in-theory (enable fn-cc-octet-event-listp)))))

(local
 (defun fn-ccc-append-induct (a s lower)
   (declare (xargs :verify-guards nil :measure (len a)))
   (if (consp a)
       (fn-ccc-append-induct
        (cdr a) (+ 1 s)
        (+ 1 (fn-store-event-txid
              (fn-cc-nth 1 (fn-store-event-decode-exact (car a))))))
     (list s lower))))

(local
 (defthm fn-ccc-event-list-head-integer
   (implies (and (fn-cc-octet-event-listp records sequence lower frontier)
                 (consp records))
            (integerp (fn-store-event-generation
                       (fn-cc-nth 1 (fn-store-event-decode-exact (car records))))))
   :rule-classes ((:forward-chaining
                   :trigger-terms ((fn-cc-octet-event-listp records sequence lower frontier))))
   :hints (("Goal" :in-theory (enable fn-cc-octet-event-listp)
            :use ((:instance fn-replay-record-counters-are-natural
                   (record (fn-cc-nth 1 (fn-store-event-decode-exact (car records))))))))))

(local
 (defthm fn-ccc-event-list-append
   (implies (and (fn-cc-octet-event-listp a s lower mid)
                 (fn-cc-octet-event-listp b (+ s (len a)) mid upper)
                 (rationalp lower) (integerp mid) (rationalp upper)
                 (<= lower mid) (<= mid upper)
                 (acl2-numberp s))
            (fn-cc-octet-event-listp (append a b) s lower upper))
   :hints (("Goal" :induct (fn-ccc-append-induct a s lower)
            :in-theory (enable fn-cc-octet-event-listp)))))

(local
 (defthm fn-ccc-event-list-true-listp
   (implies (fn-cc-octet-event-listp events s lower upper)
            (true-listp events))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-cc-octet-event-listp)))))

(local
 (defthm fn-ccc-links-step-composes
   (implies (and (fn-cc-octet-event-listp prev 0 0 mid)
                 (equal (len prev) lo)
                 (fn-cc-octet-event-listp ev lo mid up)
                 (fn-record-uint32p mid) (fn-record-uint32p up) (<= mid up))
            (fn-cc-octet-event-listp (append prev ev) 0 0 up))
   :hints (("Goal" :use (:instance fn-ccc-event-list-append
                                   (a prev) (b ev) (s 0) (lower 0)
                                   (upper up))
            :in-theory (e/d (fn-record-uint32p)
                            (fn-ccc-event-list-append))))))

; KEYSTONE (composition).  A chain the walk accepts is one valid prefix
; history: its records are exactly BOUNDARY events from sequence 0 under the
; newest frontier, each a canonical Store event with ascending sequence and
; transaction id.
(defthm fn-ccc-links-okp-composes-a-prefix
  (implies (fn-ccc-links-okp entries)
           (and (equal (len (fn-ccc-links-events entries))
                       (fn-ccc-boundary (fn-ccc-head-link entries)))
                (fn-cc-octet-event-listp (fn-ccc-links-events entries) 0 0
                                         (fn-ccc-frontier
                                          (fn-ccc-head-link entries)))))
  :hints (("Goal" :induct (fn-ccc-links-okp entries)
           :in-theory (e/d (fn-ccc-linkp fn-record-uint32p)
                           (fn-ccc-event-list-append
                            fn-ccc-event-list-lower-weakens
                            fn-ccc-event-list-upper-weakens)))))

(local
 (defthm fn-ccc-event-list-within-frontier
   (implies (and (natp lower) (integerp frontier) (<= lower frontier)
                 (fn-cc-octet-event-listp records sequence lower frontier))
            (<= (+ lower (len records)) frontier))
   :rule-classes nil
   :hints (("Goal" :induct (fn-cc-octet-event-listp records sequence lower frontier)
            :in-theory (enable fn-cc-octet-event-listp)))))

(defthm fn-ccc-links-okp-head-linkp
  (implies (fn-ccc-links-okp entries)
           (and (consp entries)
                (fn-ccc-linkp (fn-ccc-head-link entries))))
  :rule-classes :forward-chaining
  :hints (("Goal" :expand ((fn-ccc-links-okp entries)))))

(defthm fn-ccc-links-okp-boundary-positive
  (implies (fn-ccc-links-okp entries)
           (< 0 (fn-ccc-boundary (fn-ccc-head-link entries))))
  :rule-classes :linear
  :hints (("Goal" :use fn-ccc-links-okp-head-linkp
           :in-theory (e/d (fn-ccc-linkp fn-record-uint32p)
                           (fn-ccc-links-okp-head-linkp fn-ccc-links-okp
                            fn-cc-octet-event-listp)))))

(defthm fn-ccc-links-okp-chain-summary
  (implies (fn-ccc-links-okp entries)
           (fn-cc-summaryp (fn-ccc-chain-summary entries)))
  :hints (("Goal"
           :use ((:instance fn-ccc-links-okp-composes-a-prefix)
                 (:instance fn-ccc-links-okp-head-linkp)
                 (:instance fn-ccc-event-list-within-frontier
                            (records (fn-ccc-links-events entries))
                            (sequence 0) (lower 0)
                            (frontier (fn-ccc-frontier (fn-ccc-head-link entries)))))
           :in-theory (e/d (fn-cc-summaryp fn-cc-make fn-cc-sequence
                            fn-cc-frontier fn-cc-events fn-cc-nth
                            fn-record-uint32p fn-ccc-linkp)
                           (fn-ccc-links-okp-composes-a-prefix
                            fn-ccc-links-okp-head-linkp
                            fn-ccc-links-okp fn-ccc-head-link
                            fn-ccc-links-events fn-cc-octet-event-listp))
           :do-not-induct t)))

; The walk's length: every link covers at least one record, so a chain has at
; most BOUNDARY links.  The host's walk is given the profile's
; max-transactions as fuel (`fn-ccc-walk-bound'); an admitted open has at most
; that many committed records, so the fuel is never the reason a walk stops.
(defthm fn-ccc-links-count-within-boundary
  (implies (fn-ccc-links-okp entries)
           (<= (len entries) (fn-ccc-boundary (fn-ccc-head-link entries))))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-ccc-links-okp entries)
           :in-theory (enable fn-ccc-linkp fn-record-uint32p))))

(defun fn-ccc-walk-bound (profile)
  (declare (xargs :guard t))
  (fn-bs-profile-max-transactions profile))

; -----------------------------------------------------------------------------
; Capture: the uncovered suffix, one quantum at a time

; How many of EVENTS one link takes: as many as fit in OCTETS within COUNT
; events, and at least one.
(defun fn-ccc-fit-aux (events size octets count)
  (declare (xargs :guard (and (natp size) (natp count)) :verify-guards nil))
  (if (or (not (consp events)) (zp count))
      0
    (let ((next (+ size (len (car events)) 5)))
      (if (< octets next) 0
        (+ 1 (fn-ccc-fit-aux (cdr events) next octets (1- count)))))))

(defun fn-ccc-fit (events)
  (declare (xargs :guard t :verify-guards nil))
  (min (len events)
       (max 1 (fn-ccc-fit-aux events 32 *fn-cc-max-octets* *fn-cc-max-events*))))

(defun fn-ccc-event-txid (event-octets)
  (declare (xargs :guard t :verify-guards nil))
  (fn-store-event-txid (fn-cc-nth 1 (fn-store-event-decode-exact event-octets))))

; RECORDS: the committed history the open reconstructed.  LOWER and
; LOWER-FRONTIER: the selected chain's boundary and frontier (0 and 0 without
; one).  PRED-GENERATION and PRED-DIGEST: the selected head's generation and
; frame digest (ignored when LOWER is 0).  The link's frontier is one above
; its last transaction id, so the next link's events start above it.
(defun fn-ccc-capture-link (records lower lower-frontier pred-generation
                                    pred-digest)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((rest (nthcdr (nfix lower) records))
         (k (fn-ccc-fit rest))
         (events (take k rest))
         (link (fn-ccc-make (nfix lower) (+ (nfix lower) k) lower-frontier
                            (if (consp events)
                                (+ 1 (nfix (fn-ccc-event-txid
                                            (car (last events)))))
                              0)
                            (if (zp lower) 0 pred-generation)
                            (if (zp lower) nil pred-digest)
                            events)))
    (if (and (natp lower) (< lower (len records)) (fn-ccc-linkp link))
        (list :ok link)
      (list :error :history))))

(defun fn-ccc-prefixp (prefix whole)
  (declare (xargs :guard t))
  (if (consp prefix)
      (and (consp whole) (equal (car prefix) (car whole))
           (fn-ccc-prefixp (cdr prefix) (cdr whole)))
    t))

(defthm fn-ccc-prefix-length
  (implies (fn-ccc-prefixp p all) (<= (len p) (len all)))
  :rule-classes :linear)

(local
 (defthm fn-ccc-prefixp-append-take
   (implies (and (fn-ccc-prefixp p whole) (natp k)
                 (<= (+ (len p) k) (len whole)))
            (fn-ccc-prefixp (append p (take k (nthcdr (len p) whole))) whole))
   :hints (("Goal" :induct (fn-ccc-prefixp p whole)))))

(local
 (defthm fn-ccc-fit-aux-within-len
   (<= (fn-ccc-fit-aux events size octets count) (len events))
   :rule-classes :linear))

(local
 (defthm fn-ccc-fit-within-len
   (<= (fn-ccc-fit events) (len events))
   :rule-classes :linear))

(local
 (defthm fn-ccc-nthcdr-below-len-consp
   (implies (and (natp n) (< n (len x))) (consp (nthcdr n x)))))

(local
 (defthm fn-ccc-len-nthcdr
   (implies (and (natp n) (<= n (len x)))
            (equal (len (nthcdr n x)) (- (len x) n)))))

(local
 (defthm fn-ccc-fit-positive
   (implies (consp events) (<= 1 (fn-ccc-fit events)))
   :rule-classes :linear))

(defthm fn-ccc-capture-link-events
  (implies (equal (car (fn-ccc-capture-link records lower lf gen digest)) :ok)
           (let ((l (cadr (fn-ccc-capture-link records lower lf gen digest))))
             (and (fn-ccc-linkp l)
                  (equal (fn-ccc-lower l) lower)
                  (equal (fn-ccc-lower-frontier l) lf)
                  (equal (fn-ccc-events l)
                         (take (- (fn-ccc-boundary l) lower)
                               (nthcdr lower records)))
                  (< lower (fn-ccc-boundary l))
                  (<= (fn-ccc-boundary l) (len records))
                  (equal (len (fn-ccc-events l))
                         (- (fn-ccc-boundary l) lower))
                  (equal (fn-ccc-pred-generation l) (if (zp lower) 0 gen))
                  (equal (fn-ccc-pred-digest l) (if (zp lower) nil digest)))))
  :hints (("Goal" :in-theory (e/d (fn-ccc-linkp fn-ccc-make fn-ccc-lower
                                   fn-ccc-boundary fn-ccc-lower-frontier
                                   fn-ccc-events fn-ccc-pred-generation
                                   fn-ccc-pred-digest fn-cc-nth
                                   fn-record-uint32p)
                                  (fn-ccc-fit fn-cc-octet-event-listp
                                   fn-ccc-event-txid)))))

(defthm fn-ccc-event-list-last-at-least-lower
   (implies (and (fn-cc-octet-event-listp x s lo up) (consp x))
            (<= lo (fn-store-event-txid (fn-cc-nth 1 (fn-store-event-decode-exact (car (last x)))))))
   :rule-classes :linear
   :hints (("Goal" :induct (fn-ccc-append-induct x s lo)
            :in-theory (enable fn-cc-octet-event-listp))))

(defthm fn-ccc-event-list-last-below-upper
   (implies (and (fn-cc-octet-event-listp x s lo up) (consp x))
            (< (fn-store-event-txid (fn-cc-nth 1 (fn-store-event-decode-exact (car (last x))))) up))
   :rule-classes :linear
   :hints (("Goal" :induct (fn-ccc-append-induct x s lo)
            :in-theory (enable fn-cc-octet-event-listp))))

(local
 (defun fn-ccc-take-induct (k x s lo)
   (declare (xargs :verify-guards nil :measure (nfix k)))
   (if (or (zp k) (atom x)) (list x s lo)
     (fn-ccc-take-induct (1- k) (cdr x) (+ 1 s)
                         (+ 1 (fn-ccc-event-txid (car x)))))))

; A leading run of a valid history is valid under one above its last
; transaction id: what the capture of one link checks.
(defthm fn-ccc-take-event-list
  (implies (and (fn-cc-octet-event-listp x s lo up)
                (natp k) (< 0 k) (<= k (len x)))
           (fn-cc-octet-event-listp
            (take k x) s lo (+ 1 (fn-ccc-event-txid (car (last (take k x)))))))
  :hints (("Goal" :induct (fn-ccc-take-induct k x s lo)
           :in-theory (enable fn-cc-octet-event-listp))))

(defthm fn-ccc-event-list-last-integer
  (implies (and (fn-cc-octet-event-listp x s lo up) (consp x))
           (integerp (fn-store-event-txid (fn-cc-nth 1 (fn-store-event-decode-exact (car (last x)))))))
  :hints (("Goal" :induct (fn-ccc-append-induct x s lo)
           :in-theory (enable fn-cc-octet-event-listp))
          ("Subgoal *1/1" :use ((:instance fn-replay-record-counters-are-natural
                                 (record (fn-cc-nth 1 (fn-store-event-decode-exact (car x)))))))))

(local
 (defthm fn-ccc-take-event-list-within
   (implies (and (fn-cc-octet-event-listp x s lo up) (natp k) (<= k (len x)))
            (fn-cc-octet-event-listp (take k x) s lo up))
   :hints (("Goal" :induct (fn-ccc-take-induct k x s lo)
            :in-theory (enable fn-cc-octet-event-listp)))))

(local
 (defthm fn-ccc-len-take
   (equal (len (take n x)) (nfix n))))

(local
 (defthm fn-ccc-take-consp
   (implies (and (consp x) (posp k)) (consp (take k x)))))

; The capture of the next link succeeds on a history whose records above the
; chain are valid from the chain's frontier: the open's own check.
(defthm fn-ccc-capture-link-succeeds
  (implies (and (natp lower) (< lower (len records))
                (fn-record-uint32p (len records))
                (fn-record-uint32p lf) (fn-record-uint32p frontier)
                (fn-cc-octet-event-listp (nthcdr lower records) lower lf frontier)
                (fn-record-uint32p gen) (fn-cbor-octet-listp digest))
           (equal (car (fn-ccc-capture-link records lower lf gen digest)) :ok))
  :hints (("Goal"
           :use ((:instance fn-ccc-fit-positive (events (nthcdr lower records)))
                 (:instance fn-ccc-fit-within-len (events (nthcdr lower records)))
                 (:instance fn-ccc-nthcdr-below-len-consp (n lower) (x records))
                 (:instance fn-ccc-take-event-list
                            (x (nthcdr lower records)) (s lower) (lo lf)
                            (up frontier)
                            (k (fn-ccc-fit (nthcdr lower records))))
                 (:instance fn-ccc-event-list-last-at-least-lower
                            (x (take (fn-ccc-fit (nthcdr lower records))
                                     (nthcdr lower records)))
                            (s lower) (lo lf)
                            (up (+ 1 (fn-ccc-event-txid
                                      (car (last (take (fn-ccc-fit (nthcdr lower records))
                                                       (nthcdr lower records))))))))
                 (:instance fn-ccc-event-list-last-below-upper
                            (x (take (fn-ccc-fit (nthcdr lower records))
                                     (nthcdr lower records)))
                            (s lower) (lo lf) (up frontier))
                 (:instance fn-ccc-take-event-list-within
                            (x (nthcdr lower records)) (s lower) (lo lf)
                            (up frontier)
                            (k (fn-ccc-fit (nthcdr lower records))))
                 (:instance fn-ccc-event-list-last-integer
                            (x (take (fn-ccc-fit (nthcdr lower records))
                                     (nthcdr lower records)))
                            (s lower) (lo lf)
                            (up (+ 1 (fn-ccc-event-txid
                                      (car (last (take (fn-ccc-fit (nthcdr lower records))
                                                       (nthcdr lower records)))))))))
           :in-theory (e/d (fn-ccc-capture-link fn-ccc-linkp fn-ccc-make
                            fn-ccc-lower fn-ccc-boundary fn-ccc-lower-frontier
                            fn-ccc-frontier fn-ccc-events fn-ccc-pred-generation
                            fn-ccc-pred-digest fn-cc-nth fn-record-uint32p)
                           (fn-ccc-take-event-list fn-ccc-fit take
                            fn-ccc-fit-positive fn-ccc-fit-within-len
                            fn-ccc-nthcdr-below-len-consp
                            fn-ccc-take-event-list-within
                            fn-ccc-event-list-last-integer
                            fn-ccc-event-list-last-at-least-lower
                            fn-ccc-event-list-last-below-upper
                            fn-cc-octet-event-listp))
           :do-not-induct t)))

(in-theory (disable fn-ccc-capture-link))

(local
 (defthm fn-ccc-links-events-of-cons
   (equal (fn-ccc-links-events (cons e rest))
          (append (fn-ccc-links-events rest)
                  (fn-ccc-events (fn-ccc-entry-link e))))))

(local
 (defthm fn-ccc-capture-link-prefix
   (implies (and (fn-ccc-prefixp p records)
                 (equal (car (fn-ccc-capture-link records (len p) lf gen digest))
                        :ok))
            (fn-ccc-prefixp
             (append p (fn-ccc-events
                        (cadr (fn-ccc-capture-link records (len p) lf gen digest))))
             records))
   :hints (("Goal"
            :use ((:instance fn-ccc-capture-link-events (lower (len p)))
                  (:instance fn-ccc-prefixp-append-take
                             (whole records)
                             (k (- (fn-ccc-boundary
                                    (cadr (fn-ccc-capture-link records (len p)
                                                               lf gen digest)))
                                   (len p)))))
            :in-theory (disable fn-ccc-capture-link-events
                                fn-ccc-prefixp-append-take)))))

; KEYSTONE (compaction extends the chain).  The host captures from the
; selected chain's boundary, frontier, generation and digest; the new link
; published under GENERATION with frame digest DIGEST and consed onto the
; chain is again a chain the walk accepts, its records are again a prefix of
; the committed history, and it covers strictly more of it.  Earlier links
; are never repacked: the old chain is the new chain's tail.
(defthm fn-ccc-capture-extends-the-chain
  (let* ((head (fn-ccc-head-link entries))
         (lower (if (consp entries) (fn-ccc-boundary head) 0))
         (lf (if (consp entries) (fn-ccc-frontier head) 0))
         (captured (fn-ccc-capture-link
                    records lower lf
                    (fn-ccc-entry-generation (car entries))
                    (fn-ccc-entry-digest (car entries))))
         (new (cons (list generation (cadr captured) digest) entries)))
    (implies (and (or (null entries) (fn-ccc-links-okp entries))
                  (fn-ccc-prefixp (fn-ccc-links-events entries) records)
                  (equal (car captured) :ok))
             (and (fn-ccc-links-okp new)
                  (equal (cdr new) entries)
                  (fn-ccc-prefixp (fn-ccc-links-events new) records)
                  (< (len (fn-ccc-links-events entries))
                     (len (fn-ccc-links-events new))))))
  :hints (("Goal"
           :use ((:instance fn-ccc-capture-link-events
                            (lower (if (consp entries)
                                       (fn-ccc-boundary (fn-ccc-head-link entries))
                                     0))
                            (lf (if (consp entries)
                                    (fn-ccc-frontier (fn-ccc-head-link entries))
                                  0))
                            (gen (fn-ccc-entry-generation (car entries)))
                            (digest (fn-ccc-entry-digest (car entries))))
                 (:instance fn-ccc-links-okp-composes-a-prefix)
                 (:instance fn-ccc-links-okp-boundary-positive)
                 (:instance fn-ccc-capture-link-prefix
                            (p (fn-ccc-links-events entries))
                            (lf (if (consp entries)
                                    (fn-ccc-frontier (fn-ccc-head-link entries))
                                  0))
                            (gen (fn-ccc-entry-generation (car entries)))
                            (digest (fn-ccc-entry-digest (car entries)))))
           :expand ((fn-ccc-links-okp
                     (cons (list generation
                                 (cadr (fn-ccc-capture-link
                                        records
                                        (if (consp entries)
                                            (fn-ccc-boundary (fn-ccc-head-link entries))
                                          0)
                                        (if (consp entries)
                                            (fn-ccc-frontier (fn-ccc-head-link entries))
                                          0)
                                        (fn-ccc-entry-generation (car entries))
                                        (fn-ccc-entry-digest (car entries))))
                                 digest)
                           entries)))
           :in-theory (e/d (fn-ccc-entry-link
                            fn-ccc-entry-generation fn-ccc-entry-digest
                            fn-ccc-head-link)
                           (fn-ccc-capture-link-events
                            fn-ccc-links-okp-composes-a-prefix
                            fn-ccc-links-okp-boundary-positive
                            fn-ccc-capture-link-prefix
                            fn-ccc-linkp fn-cc-octet-event-listp)))))

; -----------------------------------------------------------------------------
; The link's bytes: `fn-x' version 1
;
;   bytes "fn-x", uint 1, uint lower, uint boundary, uint lower-frontier,
;   uint frontier, uint pred-generation, bytes pred-digest, uint count,
;   then COUNT byte strings, each one canonical Store event.
;
; A version-0 pack decodes as the first link of its chain.

; One link file is at most this many octets: the scheduling quantum, or one
; record of the profile's R when a single record is larger, plus the header.
(defconst *fn-ccc-link-header-octets* 128)
(defun fn-ccc-link-octet-bound (profile)
  (declare (xargs :guard t))
  (+ *fn-ccc-link-header-octets*
     (max *fn-cc-max-octets* (fn-bs-profile-max-record-octets profile))))

(defun fn-ccc-encode-link (l)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-ccc-linkp l)) nil
    (append (fn-cbor-encode (cons :bytes *fn-cc-magic*))
            (fn-cbor-encode (cons :uint *fn-ccc-version*))
            (fn-cbor-encode (cons :uint (fn-ccc-lower l)))
            (fn-cbor-encode (cons :uint (fn-ccc-boundary l)))
            (fn-cbor-encode (cons :uint (fn-ccc-lower-frontier l)))
            (fn-cbor-encode (cons :uint (fn-ccc-frontier l)))
            (fn-cbor-encode (cons :uint (fn-ccc-pred-generation l)))
            (fn-cbor-encode-bounded (cons :bytes (fn-ccc-pred-digest l))
                                    *fn-frame-trailer-octets*)
            (fn-cbor-encode (cons :uint (len (fn-ccc-events l))))
            (fn-cc-encode-events (fn-ccc-events l)))))

(defun fn-ccc-uint-itemp (x)
  (declare (xargs :guard t))
  (and (consp x) (equal (car x) :uint)))

(defun fn-ccc-bytes-itemp (x)
  (declare (xargs :guard t))
  (and (consp x) (equal (car x) :bytes)))

(defun fn-ccc-decode-link (octets max-octets)
  (declare (xargs :guard t :verify-guards nil))
  (if (or (not (fn-cbor-octet-listp octets)) (not (natp max-octets))
          (< max-octets (len octets)))
      (list :error :octets)
    (let ((v0 (fn-cc-decode-exact octets)))
      (if (equal (car v0) :ok)
          (let ((l (fn-ccc-link-of-summary (fn-cc-nth 1 v0))))
            (if (fn-ccc-linkp l) (list :ok l) (list :error :summary)))
        (let ((header (fn-stmt-decode-prefix-items-bounded
                       9 octets max-octets max-octets)))
          (if (not (equal (car header) :ok))
              (list :error :header)
            (let ((v (fn-cc-nth 1 header)))
              (if (or (not (equal (fn-cc-nth 0 v) (cons :bytes *fn-cc-magic*)))
                      (not (equal (fn-cc-nth 1 v) (cons :uint *fn-ccc-version*)))
                      (not (fn-ccc-uint-itemp (fn-cc-nth 2 v)))
                      (not (fn-ccc-uint-itemp (fn-cc-nth 3 v)))
                      (not (fn-ccc-uint-itemp (fn-cc-nth 4 v)))
                      (not (fn-ccc-uint-itemp (fn-cc-nth 5 v)))
                      (not (fn-ccc-uint-itemp (fn-cc-nth 6 v)))
                      (not (fn-ccc-bytes-itemp (fn-cc-nth 7 v)))
                      (not (fn-ccc-uint-itemp (fn-cc-nth 8 v)))
                      (< *fn-cc-max-events* (cdr (fn-cc-nth 8 v))))
                  (list :error :header)
                (let* ((body (fn-stmt-decode-prefix-items-bounded
                              (cdr (fn-cc-nth 8 v)) (fn-cc-nth 2 header)
                              max-octets max-octets))
                       (events (if (equal (car body) :ok)
                                   (fn-cc-values-event-octets (fn-cc-nth 1 body))
                                 :bad))
                       (l (fn-ccc-make (cdr (fn-cc-nth 2 v)) (cdr (fn-cc-nth 3 v))
                                       (cdr (fn-cc-nth 4 v)) (cdr (fn-cc-nth 5 v))
                                       (cdr (fn-cc-nth 6 v)) (cdr (fn-cc-nth 7 v))
                                       events)))
                  (if (or (not (equal (car body) :ok))
                          (consp (fn-cc-nth 2 body))
                          (equal events :bad)
                          (not (fn-ccc-linkp l)))
                      (list :error :link)
                    (list :ok l)))))))))))

(defthm fn-ccc-decode-link-is-a-link
  (implies (equal (car (fn-ccc-decode-link octets max-octets)) :ok)
           (fn-ccc-linkp (cadr (fn-ccc-decode-link octets max-octets)))))

(in-theory (disable fn-ccc-decode-link fn-ccc-encode-link))

; -----------------------------------------------------------------------------
; The chain as the host reads it: FRAMED is newest first, each entry
; (GENERATION FRAME-OCTETS DIGEST), the digest the host computed of the file.

(defun fn-ccc-framed-link (framed digest max-octets)
  (declare (xargs :guard t :verify-guards nil))
  (if (or (not (fn-cbor-octet-listp framed))
          (< (len framed) *fn-frame-trailer-octets*))
      (list :error :frame)
    (let ((n (- (len framed) *fn-frame-trailer-octets*)))
      (if (not (equal (nthcdr n framed) digest))
          (list :error :integrity)
        (fn-ccc-decode-link (take n framed) max-octets)))))

(defun fn-ccc-decode-entries (framed max-octets)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp framed)
      (let* ((e (car framed))
             (d (fn-ccc-framed-link (fn-cc-nth 1 e) (fn-cc-nth 2 e) max-octets))
             (rest (fn-ccc-decode-entries (cdr framed) max-octets)))
        (if (or (not (equal (car d) :ok)) (equal rest :bad))
            :bad
          (cons (list (fn-cc-nth 0 e) (cadr d) (fn-cc-nth 2 e)) rest)))
    (if (null framed) nil :bad)))

; One step of the host's walk: the link's LOWER (0 ends the walk) and the
; predecessor generation to read next.
(defun fn-ccc-entry-step (framed digest max-octets)
  (declare (xargs :guard t :verify-guards nil))
  (let ((d (fn-ccc-framed-link framed digest max-octets)))
    (if (not (equal (car d) :ok)) d
      (list :ok (fn-ccc-lower (cadr d)) (fn-ccc-pred-generation (cadr d))))))

; The open (host/native/checkpoint.lisp `fnn-pack-recover-records').
(defun fn-ccc-observe-chain (framed observed frontier max-octets)
  (declare (xargs :guard t :verify-guards nil))
  (let ((entries (fn-ccc-decode-entries framed max-octets)))
    (cond ((equal entries :bad) '(:error :integrity))
          ((not (fn-ccc-links-okp entries)) '(:error :chain))
          (t (fn-cc-recover-observation (fn-ccc-chain-summary entries)
                                        observed frontier)))))

(defun fn-ccc-chain-boundary (framed max-octets)
  (declare (xargs :guard t :verify-guards nil))
  (fn-cc-sequence (fn-ccc-chain-summary (fn-ccc-decode-entries framed max-octets))))

; The coverage the reclaim plan and the namespace observation read, at every
; open and before a reclaim (`fnn-pack-selected-raw-and-coverage').
(defun fn-ccc-coverage-chain (framed observed-count frontier max-octets)
  (declare (xargs :guard t :verify-guards nil))
  (let ((entries (fn-ccc-decode-entries framed max-octets)))
    (cond ((equal entries :bad) '(:error :integrity))
          ((not (fn-ccc-links-okp entries)) '(:error :chain))
          (t (let ((summary (fn-ccc-chain-summary entries)))
               (if (or (< observed-count (fn-cc-sequence summary))
                       (< frontier (fn-cc-frontier summary)))
                   '(:error :coverage)
                 (list :ok (fn-cc-sequence summary) (fn-cc-frontier summary))))))))

(defthm fn-ccc-coverage-is-the-chain-boundary-by-definition
  (implies (equal (car (fn-ccc-coverage-chain framed count frontier max)) :ok)
           (equal (cadr (fn-ccc-coverage-chain framed count frontier max))
                  (fn-ccc-chain-boundary framed max))))

(in-theory (disable fn-ccc-chain-summary))

; -----------------------------------------------------------------------------
; PRF-073 over a chain

(defthm fn-ccc-covered-deletion-keeps-reconstruction
  (implies (and (equal (car (fn-ccc-observe-chain framed observed frontier max))
                       :ok)
                (fn-ccp-covered-sublistp after observed
                                         (fn-ccc-chain-boundary framed max)))
           (equal (fn-ccc-observe-chain framed after frontier max)
                  (fn-ccc-observe-chain framed observed frontier max)))
  :hints (("Goal" :in-theory (enable fn-cc-recover-observation))))

(local
 (defthm fn-ccc-subsetp-transitive
   (implies (and (subsetp-equal a b) (subsetp-equal b c))
            (subsetp-equal a c))))

; KEYSTONE (reclaim over a chain).  Deleting any subset of the reclaim plan
; computed at the chain's boundary (every cut of the reclaim program leaves
; such a subset) keeps the namespace observation valid and the reconstructed
; record list unchanged.
(defthm fn-ccc-reclaim-preserves-reconstructed-history
  (let* ((before (fn-profile-txn-observation names maximum lower))
         (after (fn-profile-txn-observation
                 (fn-ccp-remove-names names gone) maximum lower)))
    (implies (and (not (equal before :invalid))
                  (subsetp-equal gone
                                 (fn-bs-pack-reclaim-plan names maximum lower))
                  (equal lower (fn-ccc-chain-boundary framed max))
                  (equal (car (fn-ccc-observe-chain
                               framed (fn-ccp-read (third before) contents)
                               frontier max))
                         :ok))
             (and (not (equal after :invalid))
                  (equal (fn-ccc-observe-chain
                          framed (fn-ccp-read (third after) contents)
                          frontier max)
                         (fn-ccc-observe-chain
                          framed (fn-ccp-read (third before) contents)
                          frontier max)))))
  :hints (("Goal"
           :use ((:instance fn-ccp-reclaim-keeps-namespace-observation)
                 (:instance fn-ccp-reclaim-plan-names-are-below)
                 (:instance fn-ccp-removed-read-is-a-covered-sublist (s 0))
                 (:instance fn-ccc-covered-deletion-keeps-reconstruction
                            (observed (fn-ccp-read
                                       (third (fn-profile-txn-observation
                                               names maximum lower))
                                       contents))
                            (after (fn-ccp-read
                                    (fn-ccp-remove-pairs
                                     (third (fn-profile-txn-observation
                                             names maximum lower))
                                     gone)
                                    contents))))
           :in-theory (e/d (fn-profile-txn-observation
                            fn-bs-txn-observation-selected)
                           (fn-ccp-reclaim-plan-names-are-below
                            fn-ccp-reclaim-keeps-namespace-observation
                            fn-ccp-removed-read-is-a-covered-sublist
                            fn-ccc-covered-deletion-keeps-reconstruction
                            fn-ccc-observe-chain
                            fn-ccc-chain-boundary)))))

; -----------------------------------------------------------------------------
; The chain reconstructs the history

(local
 (defthm fn-ccc-prefix-nth
   (implies (and (fn-ccc-prefixp events all) (natp n) (< n (len events)))
            (equal (nth n events) (nth n all)))))

; OBSERVED holds, for each sequence it names, the record H holds there.
(defun fn-ccc-pairs-match (observed h)
  (declare (xargs :guard (true-listp h)))
  (if (consp observed)
      (and (consp (car observed)) (consp (cdar observed))
           (natp (caar observed))
           (equal (cadar observed) (nth (caar observed) h))
           (fn-ccc-pairs-match (cdr observed) h))
    t))

(local
 (defthm fn-ccc-prefix-observation-agrees
   (implies (and (fn-ccp-contiguousp observed n)
                 (fn-ccc-prefixp events all)
                 (fn-ccc-pairs-match observed all))
            (fn-cc-observation-agrees observed events (len events)))
   :hints (("Goal" :induct (fn-ccp-contiguousp observed n)
            :in-theory (enable fn-cc-observation-agrees)))))

(local
 (defthm fn-ccc-nthcdr-opens
   (implies (and (natp n) (< n (len x)))
            (equal (nthcdr n x) (cons (nth n x) (nthcdr (+ 1 n) x))))))

(local
 (defthm fn-ccc-nthcdr-past
   (implies (and (natp n) (<= (len x) n)) (not (consp (nthcdr n x))))))

(local
 (defthm fn-ccc-nthcdr-len-true-list
   (implies (true-listp h) (equal (nthcdr (len h) h) nil))))

(local
 (defthm fn-ccc-matched-records
   (implies (and (fn-ccp-contiguousp observed n) (natp n)
                 (fn-ccc-pairs-match observed h) (true-listp h)
                 (equal (+ n (len observed)) (len h)))
            (equal (fn-ccp-records observed) (nthcdr n h)))
   :hints (("Goal" :induct (fn-ccp-contiguousp observed n)
            :in-theory (disable nthcdr)))))

; KEYSTONE (the reconstruction from a chain is the reconstruction from the
; history).  The host's open over the chain it walked and a complete
; transaction observation of the history H (a record for every sequence of
; H, each the record H holds there: the store before any reclaim) answers
; exactly H, when the chain's records are a prefix of H (what
; `fn-ccc-capture-extends-the-chain' keeps) and the records above the chain
; are a valid suffix under the final frontier (the open's own check).  With
; `fn-ccc-reclaim-preserves-reconstructed-history', the answer stays H at
; every cut of the reclaim.
(defthm fn-ccc-chain-reconstructs-the-history
  (let ((entries (fn-ccc-decode-entries framed max)))
    (implies (and (not (equal entries :bad))
                  (fn-ccc-links-okp entries)
                  (fn-ccc-prefixp (fn-ccc-links-events entries) h)
                  (true-listp h)
                  (fn-ccp-contiguousp observed 0)
                  (fn-ccc-pairs-match observed h)
                  (equal (len observed) (len h))
                  (fn-cc-valid-suffixp (fn-ccc-chain-summary entries)
                                       (fn-cc-observation-suffix
                                        observed
                                        (len (fn-ccc-links-events entries)))
                                       frontier))
             (equal (fn-ccc-observe-chain framed observed frontier max)
                    (list :ok h frontier))))
  :hints (("Goal"
           :use ((:instance fn-ccc-links-okp-chain-summary
                            (entries (fn-ccc-decode-entries framed max)))
                 (:instance fn-ccc-links-okp-composes-a-prefix
                            (entries (fn-ccc-decode-entries framed max)))
                 (:instance fn-ccc-prefix-observation-agrees
                            (n 0) (all h)
                            (events (fn-ccc-links-events
                                     (fn-ccc-decode-entries framed max))))
                 (:instance fn-ccp-contiguous-agreement-reconstructs
                            (n 0)
                            (events (fn-ccc-links-events
                                     (fn-ccc-decode-entries framed max))))
                 (:instance fn-ccc-matched-records (n 0))
                 (:instance fn-ccc-prefix-length
                            (p (fn-ccc-links-events
                                (fn-ccc-decode-entries framed max)))
                            (all h)))
           :in-theory (e/d (fn-cc-recover-observation fn-cc-expand
                            fn-ccc-chain-summary fn-cc-make fn-cc-sequence
                            fn-cc-events fn-cc-frontier fn-cc-valid-suffixp
                            fn-cc-nth)
                           (fn-ccc-links-okp-chain-summary
                            fn-ccc-links-okp-composes-a-prefix
                            fn-ccc-prefix-observation-agrees
                            fn-ccp-contiguous-agreement-reconstructs
                            fn-ccc-matched-records fn-ccc-prefix-length
                            fn-cc-summaryp fn-ccc-links-okp
                            fn-ccc-decode-entries fn-cc-octet-event-listp))
           :do-not-induct t)))

; -----------------------------------------------------------------------------
; Retire keeps the selected chain

(defun fn-ccc-entries-generations (entries)
  (declare (xargs :guard t))
  (if (consp entries)
      (cons (fn-ccc-entry-generation (car entries))
            (fn-ccc-entries-generations (cdr entries)))
    nil))

; The generations to unlink: every pack generation the selected chain does
; not name.  Called by `fn-store-checkpoint-chain-retire-plan' with the
; generations `fnn-pack-generations' listed and the chain the walk read.
(defun fn-ccc-retire-plan (generations framed max-octets)
  (declare (xargs :guard t :verify-guards nil))
  (let ((entries (fn-ccc-decode-entries framed max-octets)))
    (if (or (equal entries :bad) (not (fn-ccc-links-okp entries))
            (not (true-listp generations)))
        :invalid
      (set-difference-equal generations (fn-ccc-entries-generations entries)))))

(local
 (defthm fn-ccc-subsetp-cons
   (implies (subsetp-equal a b) (subsetp-equal a (cons x b)))))

(local
 (defthm fn-ccc-set-difference-subset
   (subsetp-equal (set-difference-equal a b) a)))

(local
 (defthm fn-ccc-member-set-difference
   (implies (member-equal x b)
            (not (member-equal x (set-difference-equal a b))))))

(defthm fn-ccc-retire-plan-keeps-the-chain
  (let ((plan (fn-ccc-retire-plan generations framed max)))
    (implies (not (equal plan :invalid))
             (and (subsetp-equal plan generations)
                  (implies (member-equal g (fn-ccc-entries-generations
                                            (fn-ccc-decode-entries framed max)))
                           (not (member-equal g plan))))))
  :hints (("Goal" :in-theory (disable fn-ccc-decode-entries fn-ccc-links-okp
                                      fn-ccc-entries-generations)
           :do-not-induct t)))

; -----------------------------------------------------------------------------
; Publishing a link: every crash image walks the old chain or the new one

; The walk the host performs one `fn-ccc-entry-step' at a time, over FILES:
; an alist from generation to (FRAME-OCTETS . DIGEST).
(defun fn-ccc-walk (files generation fuel max-octets)
  (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
  (if (zp fuel) :bad
    (let ((f (assoc-equal generation files)))
      (if (not (consp f)) :bad
        (let* ((framed (cadr f)) (digest (cddr f))
               (step (fn-ccc-entry-step framed digest max-octets))
               (entry (list generation framed digest)))
          (cond ((not (equal (car step) :ok)) :bad)
                ((zp (cadr step)) (list entry))
                (t (let ((rest (fn-ccc-walk files (caddr step) (1- fuel)
                                            max-octets)))
                     (if (equal rest :bad) :bad (cons entry rest))))))))))

(defun fn-ccc-files-agree (files image gens)
  (declare (xargs :guard (and (alistp files) (alistp image))))
  (if (consp gens)
      (and (equal (assoc-equal (car gens) image) (assoc-equal (car gens) files))
           (fn-ccc-files-agree files image (cdr gens)))
    t))

(local
 (defthm fn-ccc-walk-generations-agree
   (implies (and (not (equal (fn-ccc-walk files g fuel max) :bad))
                 (fn-ccc-files-agree files image
                                     (fn-ccc-entries-generations
                                      (fn-ccc-walk files g fuel max))))
            (equal (fn-ccc-walk image g fuel max)
                   (fn-ccc-walk files g fuel max)))
   :hints (("Goal" :induct (fn-ccc-walk files g fuel max)
            :in-theory (disable fn-ccc-entry-step)))))

(local
 (defun fn-ccc-walk-fuel-induct (files g fuel more max)
   (declare (xargs :verify-guards nil :measure (nfix fuel)))
   (if (zp fuel) (list files g more max)
     (fn-ccc-walk-fuel-induct
      files
      (caddr (fn-ccc-entry-step (cadr (assoc-equal g files))
                                (cddr (assoc-equal g files)) max))
      (1- fuel) (1- more) max))))

(local
 (defthm fn-ccc-walk-more-fuel
   (implies (and (not (equal (fn-ccc-walk files g fuel max) :bad))
                 (natp more) (<= (nfix fuel) more))
            (equal (fn-ccc-walk files g more max)
                   (fn-ccc-walk files g fuel max)))
   :hints (("Goal" :induct (fn-ccc-walk-fuel-induct files g fuel more max)
            :in-theory (disable fn-ccc-entry-step)))))

; KEYSTONE (chain publication crash).  Publishing link NEW (an immutable
; generation, then the selection marker) leaves, at every cut, an image whose
; marker is the old head or NEW with NEW's complete bytes
; (`fn-cpp-crash-selects-old-authority-or-complete-candidate', the program
; the host runs for packs), and whose files keep every generation of the old
; chain unchanged (publication only adds a name;
; `fn-cprt-unissued-generation-survives-crash').  Under exactly those two
; facts, the walk from the image's marker reads the old chain, or the new
; link followed by the old chain: never a partial or foreign chain.
(defthm fn-ccc-publication-crash-walks-old-or-new-chain
  (let ((old-chain (fn-ccc-walk files old fuel max)))
    (implies (and (natp fuel)
                  (not (equal old-chain :bad))
                  (fn-ccc-files-agree files image
                                      (fn-ccc-entries-generations old-chain))
                  (or (equal marker old)
                      (and (equal marker new)
                           (equal (assoc-equal new image)
                                  (cons new (cons framed digest)))
                           (equal (fn-ccc-entry-step framed digest max)
                                  (list :ok lower old))
                           (not (zp lower)))))
             (or (equal (fn-ccc-walk image marker (+ 1 fuel) max)
                        old-chain)
                 (equal (fn-ccc-walk image marker (+ 1 fuel) max)
                        (cons (list new framed digest) old-chain)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-ccc-walk-generations-agree (g old))
                 (:instance fn-ccc-walk-more-fuel (files image) (g old)
                            (more (+ 1 fuel)))
                 (:instance fn-ccc-walk-more-fuel (files image) (g old)
                            (more fuel)))
           :expand ((fn-ccc-walk image new (+ 1 fuel) max)
                    (fn-ccc-walk image marker (+ 1 fuel) max))
           :in-theory (disable fn-ccc-walk-generations-agree fn-ccc-entry-step
                               fn-ccc-walk-more-fuel fn-ccc-walk))))

(deftheory fn-checkpoint-pack-chain-vocabulary
  '(fn-ccc-linkp fn-ccc-links-okp fn-ccc-links-events fn-ccc-capture-link
    fn-ccc-observe-chain fn-ccc-coverage-chain fn-ccc-chain-boundary
    fn-ccc-decode-entries fn-ccc-framed-link fn-ccc-entry-step
    fn-ccc-retire-plan fn-ccc-walk fn-ccc-fit fn-ccc-fit-aux))
(in-theory (disable fn-checkpoint-pack-chain-vocabulary))
