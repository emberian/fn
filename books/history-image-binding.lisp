; fn: the history image adopted from its committed root and bound to the
; exact log prefix (lane composed-owner, 2026-09-29, rows A2-A4 of
; build/coordinator/COMPLETE-BEFORE-6.6.0.md; GPT-6's review of 2026-09-28,
; "Representation and page-store calls").  Prefix fn-hib-.
;
; books/history-records.lisp's reads keep the history faithful over a page
; file that HOLDS the image (`fn-hrecs-disk-faithful': every unverified page
; at its address is the image's), and books/history-records-disk.lisp's
; decode takes that as a hypothesis (`fn-hrs-disk-holds').  Nothing
; establishes it, and nothing could without reading every page.  This book
; replaces it by what the open can establish:
;
;   ROOT-HOLDS  the tables of the adopted root name the digests of H's
;               image pages (`fn-hib-root-holds'; at the open, the root the
;               binding names: `fn-hib-root-is-image');
;   DISK-BOUND  the page file holds no BLAKE3 second preimage of an image
;               page at the address the table names (`fn-hib-disk-bound';
;               `fn-hib-file-bound') -- the narrow cryptographic-failure
;               assumption, as a hypothesis on the actual file; the
;               pessimistic figure is the collision bound, 2^-128 per pair.
;
; Under them a fill verifies a page exactly when its words ARE H's page;
; any other words (damage, a torn write, another history's page) are
; refused by the page store's check, by name -- never answered, never
; absence.
;
; KEYSTONES (each over the function the host will call)
;   fn-hib-fill-rel            a fill of the words the file holds keeps the
;                              history faithful (no disk-faithful)
;   fn-hib-get-keeps           the read loop keeps it; :ok is record SEQ
;   fn-hib-hrecs-get-fuel-enough  the loop never runs out of fuel, with no
;                              relation to the disk at all
;   fn-hib-adopt-establishes   ADOPTION ESTABLISHES faithfulness: the root
;                              opened, page 0 filled and checked, the header
;                              read from page 0 (not from a handle), the
;                              count checked against the binding's
;   fn-hib-complete-keeps      an asynchronous page request's completion
;                              keeps it; a late one (root or entry changed)
;                              changes nothing, refused :stale-root /
;                              :stale-page (fn-hib-complete-stale)
;   fn-hib-evict-keeps, fn-hib-undone-evict, fn-hib-complete-progress
;                              eviction respecting pins keeps it, and an
;                              operation that pins what it filled completes
;                              within the image's page count of its own reads
;   fn-hib-open-binds-prefix   the binding's TRAIL (the log's chain value) is
;                              an identity of the prefix, not its count
;   fn-hib-open-is-log-prefix  alpha of the selected image is the history of
;                              exactly the log's prefix [0, COUNT)
;   fn-hib-replay-extends      the running state is that prefix extended by
;                              the log's suffix
;
; Sections: A. digests and the fill of an unverified page; B. the fill
; without disk-faithful; C. the read loop; F. adoption; E. asynchronous page
; requests; D. eviction and progress; G. the binding.  Teeth:
; tests/acl2/history-image-binding-tests.lisp (live runs over committed
; page files, and row A3's adversarial cases).
(in-package "ACL2")
(include-book "history-records-disk")
(include-book "store-log")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; A. The page digest the check compares, and the fill over an unverified page.

(defun fn-hib-page-digest (w)
  (declare (xargs :guard t :verify-guards nil))
  (pgs-octets-be-nat (fn-blake3 (pgs-words-le-octets (take 2048 w)))))
(defthm fn-hib-page-digest-of-open-page
  (implies (natp i)
           (equal (mv-nth 0 (pgs-x-page-digest i pgs-mem fn-octets-pg))
                  (fn-hib-page-digest (nthcdr (* 2048 i) (nth *pgs-wi* pgs-mem)))))
  :hints (("Goal" :in-theory (e/d (pgs-x-page-digest pgs-x-arr) (fn-blake3 pgs-words-le-octets take nthcdr)))))

(local
 (defthm fn-hib-agree-rep-outside
   (implies (and (natp a) (natp j) (or (<= (+ a (nfix n)) j) (<= (+ j (len x)) a)))
            (fn-hp-agree a n (fn-hp-rep w j x) w))
   :hints (("Goal" :induct (fn-hp-agree a n (fn-hp-rep w j x) w) :in-theory (disable fn-hp-rep nth)))))
(defthm fn-hib-page-of-rep-other
  (implies (and (natp p) (natp q) (not (equal p q)) (equal (len x) 2048))
           (equal (take 2048 (nthcdr (* 2048 q) (fn-hp-rep w (* 2048 p) x)))
                  (take 2048 (nthcdr (* 2048 q) w))))
  :hints (("Goal" :use ((:instance fn-hp-agree-is-take (a (* 2048 q)) (n 2048) (x (fn-hp-rep w (* 2048 p) x)) (y w))
                        (:instance fn-hib-agree-rep-outside (a (* 2048 q)) (n 2048) (j (* 2048 p))))
           :in-theory (disable fn-hp-agree-is-take fn-hib-agree-rep-outside fn-hp-rep take nthcdr))
          ("Subgoal 1" :cases ((< p q)))))

(defthmd fn-hib-pgs-vi-same
  (implies (equal (nth *pgs-vi* m2) (nth *pgs-vi* m))
           (equal (pgs-vi q m2) (pgs-vi q m)))
  :hints (("Goal" :in-theory (enable pgs-vi))))

(defthm fn-hib-vhold-rep-unverified
  (implies (and (fn-hp-vhold s np m iw) (natp s) (natp p) (not (equal (pgs-vi p m) 2)) (equal (len x) 2048)
                (equal (nth *pgs-vi* m2) (nth *pgs-vi* m))
                (equal (nth *pgs-wi* m2) (fn-hp-rep (nth *pgs-wi* m) (* 2048 p) x)))
           (fn-hp-vhold s np m2 iw))
  :hints (("Goal" :induct (fn-hp-vhold s np m iw)
           :in-theory (e/d ((:induction fn-hp-vhold)) ((:definition fn-hp-vhold) fn-hp-rep take nthcdr nth pgs-vi adt-nth-0)))
          ("Subgoal *1/3" :expand ((fn-hp-vhold s np m iw)))
          ("Subgoal *1/2" :use ((:instance fn-hib-page-of-rep-other (q (nfix s)) (w (nth *pgs-wi* m)))
                                (:instance fn-hib-pgs-vi-same (q s))
                                (:instance fn-hib-pgs-vi-same (q p)))
           :expand ((fn-hp-vhold s np m iw) (fn-hp-vhold s np m2 iw) (fn-hp-vhold p np m iw) (fn-hp-vhold p np m2 iw)))
          ("Subgoal *1/1" :expand ((fn-hp-vhold s np m2 iw))))
  :rule-classes nil)

(defthm fn-hib-open-page-cases
  (implies (natp i)
           (let ((r (pgs-x-open-page i txid :eager m oct)))
             (if (mv-nth 0 r)
                 (equal (mv-nth 1 r) m)
               (and (equal (mv-nth 1 r) (update-pgs-vi i 2 m))
                    (equal (fn-hib-page-digest (nthcdr (* 2048 i) (nth *pgs-wi* m)))
                           (third (pgs-x-get-entry 2 0 i m)))))))
  :hints (("Goal" :in-theory (e/d (pgs-entry-verdict pgs-entry-checked-p)
                                  (fn-hib-page-digest pgs-x-get-entry nthcdr floor pgs-x-page-digest))))
  :rule-classes nil)

(local
 (defthm fn-hib-take-take
   (equal (take n (take n x)) (take n x))
   :hints (("Goal" :in-theory (enable take)))))
(defthm fn-hib-page-digest-take
  (equal (fn-hib-page-digest (take 2048 x)) (fn-hib-page-digest x))
  :hints (("Goal" :in-theory (disable fn-blake3 pgs-words-le-octets pgs-octets-be-nat take))))
(in-theory (disable fn-hib-page-digest))

(local
 (defthm fn-hib-word2-of-update-wi
   (and (equal (pgs-x-word 2 i (update-pgs-wi j v m)) (pgs-x-word 2 i m))
        (equal (pgs-t-length (update-pgs-wi j v m)) (pgs-t-length m)))
   :hints (("Goal" :in-theory (enable pgs-x-word$inline pgs-ti update-pgs-wi pgs-t-length)))))
(defthm fn-hib-get-entry-of-put
  (equal (pgs-x-get-entry 2 base i (fn-hrs-put j ws pgs-mem)) (pgs-x-get-entry 2 base i pgs-mem))
  :hints (("Goal" :induct (fn-hrs-put j ws pgs-mem)
           :in-theory (e/d (pgs-x-get-entry pgs-x-dig4 pgs-x-len$inline) (pgs-x-word$inline pgs-h64 pgs-x-eaddr)))))

(defthm fn-hib-fill-pgs-vhold
  (implies (and (natp p) (true-listp iw)
                (fn-hp-vhold 0 (pgs-v-length m) m iw)
                (equal (third (pgs-x-get-entry 2 0 p m)) (fn-hib-page-digest (take 2048 (nthcdr (* 2048 p) iw))))
                (implies (equal (fn-hib-page-digest w) (fn-hib-page-digest (take 2048 (nthcdr (* 2048 p) iw))))
                         (equal w (take 2048 (nthcdr (* 2048 p) iw)))))
           (let ((m2 (mv-nth 1 (fn-hrs-fill-pgs p w txid m oct))))
             (and (equal (pgs-v-length m2) (pgs-v-length m))
                  (fn-hp-vhold 0 (pgs-v-length m2) m2 iw))))
  :hints (("Goal" :do-not-induct t
           :cases ((equal w (take 2048 (nthcdr (* 2048 p) iw)))))
          ("Subgoal 2"
           :use ((:instance fn-hrs-fill-pgs-unchanged (words w) (pgs-mem m) (fn-octets-pg oct))
                 (:instance fn-hib-open-page-cases (i p) (m (fn-hrs-put (* 2048 p) w m)))
                 (:instance fn-hib-vhold-rep-unverified (s 0) (np (pgs-v-length m)) (x w)
                            (m2 (fn-hrs-put (* 2048 p) w m)))
                 (:instance fn-hrs-put-words (j (* 2048 p)) (ws w) (pgs-mem m))
                 (:instance fn-hrs-put-rest (j (* 2048 p)) (ws w) (pgs-mem m))
                 (:instance fn-hrs-rep-block (o (* 2048 p)) (b (nth *pgs-wi* m)) (x w))
                 (:instance fn-hib-page-digest-take (x (nthcdr (* 2048 p) (nth *pgs-wi* (fn-hrs-put (* 2048 p) w m))))))
           :in-theory (e/d (pgs-w-length) (fn-hrs-fill-pgs-unchanged fn-hib-page-digest fn-hp-vhold fn-hrs-put pgs-x-open-page
                                           fn-hrs-put-words fn-hrs-put-rest fn-hrs-rep-block fn-hib-page-digest-take
                                           take nthcdr fn-hp-rep fn-hp-u64-listp pgs-x-get-entry))
           :expand ((fn-hrs-fill-pgs p w txid m oct)))
          ("Subgoal 1" :use ((:instance fn-hrs-fill-pgs-vhold (words w) (pgs-mem m) (fn-octets-pg oct)))
           :in-theory (disable fn-hrs-fill-pgs-vhold fn-hrs-fill-pgs fn-hp-vhold take nthcdr))))

; -----------------------------------------------------------------------------
; B. The fill keeps the history faithful without assuming the disk holds it.

(defun-nx fn-hib-tabs (p n h c)
  ; entries P..N-1 of the loaded table name the digests of H's image pages
  (declare (xargs :measure (nfix (- (nfix n) (nfix p)))))
  (if (zp (- (nfix n) (nfix p)))
      t
    (and (equal (third (pgs-x-get-entry 2 0 (nfix p) (fn-hrc-pgs c)))
                (fn-hib-page-digest (fn-hrs-image-page (nfix p) h c)))
         (fn-hib-tabs (+ 1 (nfix p)) n h c))))

(defun-nx fn-hib-nc (file p n h c)
  ; pages P..N-1: the words the page file holds at the address the table
  ; names are H's image page, or their digest is not that page's
  (declare (xargs :measure (nfix (- (nfix n) (nfix p)))))
  (if (zp (- (nfix n) (nfix p)))
      t
    (and (let ((w (fn-pgs-page-words file (first (pgs-x-get-entry 2 0 (nfix p) (fn-hrc-pgs c)))))
               (iw (fn-hrs-image-page (nfix p) h c)))
           (implies (equal (fn-hib-page-digest w) (fn-hib-page-digest iw)) (equal w iw)))
         (fn-hib-nc file (+ 1 (nfix p)) n h c))))

(defthm fn-hib-tabs-page
  (implies (and (fn-hib-tabs p n h c) (natp p) (natp q) (<= p q) (< q (nfix n)))
           (equal (third (pgs-x-get-entry 2 0 q (fn-hrc-pgs c)))
                  (fn-hib-page-digest (fn-hrs-image-page q h c))))
  :hints (("Goal" :induct (fn-hib-tabs p n h c) :in-theory (disable fn-hrs-image-page pgs-x-get-entry))))

(defthm fn-hib-nc-page
  (implies (and (fn-hib-nc file p n h c) (natp p) (natp q) (<= p q) (< q (nfix n))
                (equal (fn-hib-page-digest (fn-pgs-page-words file (first (pgs-x-get-entry 2 0 q (fn-hrc-pgs c)))))
                       (fn-hib-page-digest (fn-hrs-image-page q h c))))
           (equal (fn-pgs-page-words file (first (pgs-x-get-entry 2 0 q (fn-hrc-pgs c))))
                  (fn-hrs-image-page q h c)))
  :hints (("Goal" :induct (fn-hib-nc file p n h c) :in-theory (disable fn-hrs-image-page pgs-x-get-entry))))

; The image's tables are H's: every entry of the loaded table names the
; digest of H's image page (the root the binding names was committed for
; H; section F establishes it at adoption).
(defun-nx fn-hib-root-holds (h c) (fn-hib-tabs 0 (pgs-v-length (fn-hrc-pgs c)) h c))

; The narrow cryptographic-failure assumption, as a hypothesis on the
; actual page file: no page the table names holds a BLAKE3 second
; preimage of H's image page (words other than the page, with its digest).
; The pessimistic figure is the collision bound, 2^-128 per pair.  Where the
; file holds other words (damage, a torn write, another history's page),
; the check refuses them: :page-damaged, never an answer.
(defun-nx fn-hib-disk-bound (file h c) (fn-hib-nc file 0 (pgs-v-length (fn-hrc-pgs c)) h c))

(defthm fn-hib-fill-img-ok
  (implies (and (fn-hrs-img-ok img c) (natp p) (true-listp img)
                (equal (fn-hrc-img c) 1) (< p (pgs-v-length (fn-hrc-pgs c)))
                (equal (third (pgs-x-get-entry 2 0 p (fn-hrc-pgs c)))
                       (fn-hib-page-digest (take 2048 (nthcdr (* 2048 p) (fn-hp-piw img (fn-hrc-salt c) (fn-hrc-starts c) (fn-hrc-npages c))))))
                (implies (equal (fn-hib-page-digest words)
                                (fn-hib-page-digest (take 2048 (nthcdr (* 2048 p) (fn-hp-piw img (fn-hrc-salt c) (fn-hrc-starts c) (fn-hrc-npages c))))))
                         (equal words (take 2048 (nthcdr (* 2048 p) (fn-hp-piw img (fn-hrc-salt c) (fn-hrc-starts c) (fn-hrc-npages c)))))))
           (fn-hrs-img-ok img (mv-nth 1 (fn-hrc-fill p words c))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-hrs-img-ok) (fn-hrc-fill fn-hrs-fill-pgs fn-hp-okp fn-hp-lens fn-hp-piw fn-hp-vhold adt-placement-ok take nthcdr
                                             fn-hib-fill-pgs-vhold fn-hrs-fill-pgs-vhold))
           :use ((:instance fn-hib-fill-pgs-vhold (txid (fn-hrc-txid c)) (m (fn-hrc-pgs c)) (w words)
                            (oct (fn-hrc-oct c))
                            (iw (fn-hp-piw img (fn-hrc-salt c) (fn-hrc-starts c) (fn-hrc-npages c))))))))

(defthm fn-hib-fill-rel
  (implies (and (fn-hrc-wfp c) (fn-hrs-rel h c) (natp p)
                (fn-hib-root-holds h c) (fn-hib-disk-bound file h c))
           (let ((c2 (mv-nth 1 (fn-hrc-fill p (fn-pgs-fill-realize file (fn-hrc-phys p c)) c))))
             (and (fn-hrc-wfp c2) (fn-hrs-rel h c2))))
  :hints (("Goal" :do-not-induct t
           :cases ((and (equal (fn-hrc-img c) 1) (< p (pgs-v-length (fn-hrc-pgs c)))
                        (not (equal (pgs-vi p (fn-hrc-pgs c)) 2)))))
          ("Subgoal 2" :use ((:instance fn-hrc-fill-rel (fn-hrecs$c c) (words (fn-pgs-fill-realize file (fn-hrc-phys p c)))))
           :in-theory (disable fn-hrc-fill-rel fn-hrc-fill fn-hrs-rel fn-hrc-wfp fn-hib-root-holds fn-hib-disk-bound))
          ("Subgoal 1" :use ((:instance fn-hrc-fill-rel (fn-hrecs$c c) (words (fn-hrs-image-page p h c)))
                             (:instance fn-hib-fill-img-ok (img (take (fn-hrc-nimg c) h))
                                        (words (fn-pgs-fill-realize file (fn-hrc-phys p c))))
                             (:instance fn-hib-tabs-page (p 0) (q p) (n (pgs-v-length (fn-hrc-pgs c))))
                             (:instance fn-hib-nc-page (p 0) (q p) (n (pgs-v-length (fn-hrc-pgs c)))))
           :in-theory (e/d (fn-hrs-rel fn-hib-root-holds fn-hib-disk-bound fn-hrc-phys fn-hrs-image-page)
                           (fn-hrc-fill-rel fn-hrc-fill fn-hrc-wfp fn-hib-fill-img-ok fn-hib-tabs-page fn-hib-nc-page
                            fn-hib-tabs fn-hib-nc fn-hp-piw take nthcdr pgs-x-get-entry fn-hrs-img-ok fn-hrs-fill-pgs pgs-x-open-page floor fn-hrs-put pgs-x-words-digest-is-blake3)))))

(local
 (defthm fn-hib-word2-of-update-vi
   (and (equal (pgs-x-word 2 i (update-pgs-vi j v m)) (pgs-x-word 2 i m))
        (equal (pgs-t-length (update-pgs-vi j v m)) (pgs-t-length m)))
   :hints (("Goal" :in-theory (enable pgs-x-word$inline pgs-ti update-pgs-vi pgs-t-length)))))
(defthm fn-hib-get-entry-of-update-vi
  (equal (pgs-x-get-entry 2 base i (update-pgs-vi j v pgs-mem)) (pgs-x-get-entry 2 base i pgs-mem))
  :hints (("Goal" :in-theory (e/d (pgs-x-get-entry pgs-x-dig4 pgs-x-len$inline) (pgs-x-word$inline pgs-h64 pgs-x-eaddr)))))
(defthm fn-hib-get-entry-of-fill-pgs
  (implies (natp p)
           (equal (pgs-x-get-entry 2 base i (mv-nth 1 (fn-hrs-fill-pgs p words txid pgs-mem oct)))
                  (pgs-x-get-entry 2 base i pgs-mem)))
  :hints (("Goal" :use ((:instance fn-hib-open-page-cases (m (fn-hrs-put (* 2048 p) words pgs-mem)) (i p)))
           :in-theory (disable pgs-x-get-entry fn-hrs-put pgs-x-open-page))))
(defthm fn-hib-v-length-of-fill-pgs
  (implies (natp p)
           (equal (pgs-v-length (mv-nth 1 (fn-hrs-fill-pgs p words txid pgs-mem oct)))
                  (pgs-v-length pgs-mem)))
  :hints (("Goal" :use ((:instance fn-hib-open-page-cases (m (fn-hrs-put (* 2048 p) words pgs-mem)) (i p)))
           :in-theory (disable pgs-x-get-entry fn-hrs-put pgs-x-open-page))))

(defthm fn-hib-image-page-of-fill
  (equal (fn-hrs-image-page q h (mv-nth 1 (fn-hrc-fill p words c))) (fn-hrs-image-page q h c))
  :hints (("Goal" :in-theory (disable fn-hrc-fill fn-hp-piw take nthcdr fn-hrs-fill-pgs))))
(defthm fn-hib-entry-of-fill
  (implies (natp p)
           (equal (pgs-x-get-entry 2 0 i (fn-hrc-pgs (mv-nth 1 (fn-hrc-fill p words c))))
                  (pgs-x-get-entry 2 0 i (fn-hrc-pgs c))))
  :hints (("Goal" :in-theory (disable fn-hrc-fill fn-hrs-fill-pgs pgs-x-get-entry))))
(defthm fn-hib-tabs-of-fill
  (implies (natp p)
           (equal (fn-hib-tabs s n h (mv-nth 1 (fn-hrc-fill p words c))) (fn-hib-tabs s n h c)))
  :hints (("Goal" :induct (fn-hib-tabs s n h c)
           :in-theory (disable fn-hrc-fill fn-hrc-fill-shape fn-hrs-fill-pgs pgs-x-get-entry fn-hrs-image-page))))
(defthm fn-hib-nc-of-fill
  (implies (natp p)
           (equal (fn-hib-nc file s n h (mv-nth 1 (fn-hrc-fill p words c))) (fn-hib-nc file s n h c)))
  :hints (("Goal" :induct (fn-hib-nc file s n h c)
           :in-theory (disable fn-hrc-fill fn-hrc-fill-shape fn-hrs-fill-pgs pgs-x-get-entry fn-hrs-image-page))))
(defthm fn-hib-v-length-of-fill
  (implies (natp p)
           (equal (pgs-v-length (fn-hrc-pgs (mv-nth 1 (fn-hrc-fill p words c)))) (pgs-v-length (fn-hrc-pgs c))))
  :hints (("Goal" :in-theory (disable fn-hrs-fill-pgs))))
(defthm fn-hib-root-holds-of-fill
  (implies (natp p)
           (and (equal (fn-hib-root-holds h (mv-nth 1 (fn-hrc-fill p words c))) (fn-hib-root-holds h c))
                (equal (fn-hib-disk-bound file h (mv-nth 1 (fn-hrc-fill p words c))) (fn-hib-disk-bound file h c))))
  :hints (("Goal" :in-theory (disable fn-hrc-fill fn-hrc-fill-shape fn-hrs-fill-pgs fn-hib-tabs fn-hib-nc))))

; -----------------------------------------------------------------------------
; C. The read loop over the adopted image: faithful, and progress without any
; relation to the disk.

(defthm fn-hib-get-keeps
  (implies (and (fn-hrc-wfp c) (fn-hrs-rel h c) (fn-hib-root-holds h c) (fn-hib-disk-bound file h c) (natp seq))
           (let ((r (fn-hrc-get seq file fuel c)))
             (and (fn-hrc-wfp (mv-nth 2 r))
                  (fn-hrs-rel h (mv-nth 2 r))
                  (fn-hib-root-holds h (mv-nth 2 r))
                  (fn-hib-disk-bound file h (mv-nth 2 r))
                  (implies (equal (mv-nth 0 r) :ok)
                           (equal (mv-nth 1 r) (if (< seq (len h)) (list :ok (nth seq h)) (list :refused :seq)))))))
  :hints (("Goal" :induct (fn-hrc-get seq file fuel c)
           :in-theory (e/d (fn-hrc-get) (fn-hrc-at fn-hrc-fill fn-hrc-phys fn-hrc-wfp fn-hrs-rel fn-hib-root-holds fn-hib-disk-bound
                               fn-hrc-fill-shape fn-hrs-fill-pgs fn-hib-fill-rel fn-hrc-at-is-nth fn-pgs-fill-realize-is-page-words floor mod)))
          ("Subgoal *1/1" :use ((:instance fn-hib-fill-rel (p (cadr (mv-nth 0 (fn-hrc-at seq c))))) (:instance fn-hrc-at-is-nth (fn-hrecs$c c))))
          ("Subgoal *1/2" :use ((:instance fn-hib-fill-rel (p (cadr (mv-nth 0 (fn-hrc-at seq c))))) (:instance fn-hrc-at-is-nth (fn-hrecs$c c))))
          ("Subgoal *1/3" :use ((:instance fn-hib-fill-rel (p (cadr (mv-nth 0 (fn-hrc-at seq c))))) (:instance fn-hrc-at-is-nth (fn-hrecs$c c))))
          ("Subgoal *1/4" :use ((:instance fn-hib-fill-rel (p (cadr (mv-nth 0 (fn-hrc-at seq c))))) (:instance fn-hrc-at-is-nth (fn-hrecs$c c))))
          ("Subgoal *1/5" :use ((:instance fn-hib-fill-rel (p (cadr (mv-nth 0 (fn-hrc-at seq c))))) (:instance fn-hrc-at-is-nth (fn-hrecs$c c))))
          ("Subgoal *1/6" :use ((:instance fn-hib-fill-rel (p (cadr (mv-nth 0 (fn-hrc-at seq c))))) (:instance fn-hrc-at-is-nth (fn-hrecs$c c))))))

(defthm fn-hib-serve-p
  (implies (and (fn-hrecs-p st) (natp p))
           (fn-hrecs-p (mv-nth 1 (fn-hrecs-serve p file st))))
  :hints (("Goal" :in-theory (disable fn-hrc-fill fn-hrs-fill-pgs fn-hrc-wfp))))

(defthm fn-hib-hrecs-get-fuel-enough
  (implies (and (fn-hrecs-p st) (natp seq)
                (<= (fn-hrs-open-count 0 (pgs-v-length (fn-hrc-pgs (cdr st))) st) (nfix fuel)))
           (not (equal (mv-nth 0 (fn-hrecs-get seq file fuel st)) (list :refused :fuel))))
  :hints (("Goal" :induct (fn-hrecs-get seq file fuel st)
           :in-theory (disable fn-hrecs-serve fn-hrecs-at fn-hrecs-faithful fn-hrecs-disk-faithful fn-hrecs-p
                               fn-hrecs-page-open fn-hrs-open-count))))

; -----------------------------------------------------------------------------
; F. Adoption: the committed image at the root the binding names, its header
; read from page 0.

(defun fn-hib-open-root (file rec fn-hrecs$c)
  ; The page store opened at the committed root REC of FILE: the directory
  ; and every table page checked (:eager), the image sized, no data page
  ; read.  (mv VERDICT fn-hrecs$c), VERDICT nil when it landed.
  (declare (xargs :stobjs fn-hrecs$c :guard (fn-hrc-wfp fn-hrecs$c)
                  :guard-hints (("Goal" :in-theory (disable fn-hrs-open-pgs fn-hrc-wfp fn-hrecs$cp)))))
  (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c))
              (fn-octets-pg (fn-hrc-oct fn-hrecs$c)))
             (v pgs-mem fn-octets-pg)
             (fn-hrs-open-pgs file rec pgs-mem fn-octets-pg)
             (mv v fn-hrecs$c)))

(defun fn-hib-header (np fn-hrecs$c)
  ; the image's header check over page 0 (`fn-hp-x-header'): (mv VERDICT RESULT)
  (declare (xargs :stobjs fn-hrecs$c :guard (natp np)))
  (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c)))
             (v r)
             (fn-hp-x-header np pgs-mem)
             (mv v r)))

(defun fn-hib-headerp (hr)
  (declare (xargs :guard t))
  (and (true-listp hr) (equal (len hr) 4) (eq (nth 0 hr) :ok) (natp (nth 1 hr))
       (nat-listp (nth 2 hr)) (equal (len (nth 2 hr)) 5)
       (nat-listp (nth 3 hr)) (equal (len (nth 3 hr)) 5)))

(defthm fn-hib-open-root-wfp
  (implies (fn-hrc-wfp fn-hrecs$c)
           (fn-hrc-wfp (mv-nth 1 (fn-hib-open-root file rec fn-hrecs$c))))
  :hints (("Goal" :in-theory (disable fn-hrs-open-pgs fn-hrecs$cp fn-hrc-wfp))))

(defun fn-hib-adopt (file rec salt count fn-hrecs$c)
  ; The committed image at root REC of FILE, adopted: the page store
  ; opened (`fn-hib-open-root'), page 0 filled from the file and checked
  ; against its table entry, the header read from page 0 (never from a
  ; handle), its count checked against COUNT (the binding's), then the
  ; header adopted with SALT and REC's txid; the suffix empty.
  ; (mv VERDICT fn-hrecs$c): nil when adopted, else by name:
  ;   the page store's refusal of the root (the directory or a table page),
  ;   (:refused :image-pages)       the root holds no page
  ;   (:page-damaged 0 PHYS)        page 0 does not verify (or the page
;                                 store's other refusal of the fill)
  ;   (:refused :header R)          page 0 is no image header (R the check's)
  ;   (:refused :count N COUNT)     the image holds N events, the binding COUNT
  ; Work: the directory and table pages, one data page.
  (declare (xargs :stobjs fn-hrecs$c :guard (and (natp salt) (natp count) (fn-hrc-wfp fn-hrecs$c))
                  :guard-hints (("Goal" :in-theory (disable fn-hib-open-root fn-hrc-fill fn-hrc-fill-shape fn-hib-header fn-hrc-phys
                                                            fn-hrc-adopt fn-hrc-wfp fn-hrecs$cp)))))
  (mv-let (v fn-hrecs$c)
    (fn-hib-open-root file rec fn-hrecs$c)
    (if v
        (mv v fn-hrecs$c)
      (let ((np (pgs-rec-npages rec)))
        (if (zp np)
            (mv (list :refused :image-pages) fn-hrecs$c)
          (mv-let (fv fn-hrecs$c)
            (fn-hrc-fill 0 (fn-pgs-fill-realize file (fn-hrc-phys 0 fn-hrecs$c)) fn-hrecs$c)
            (if (not (eq fv :ok))
                (mv (if (consp fv) fv (list :refused :page0 fv)) fn-hrecs$c)
              (mv-let (hv hr)
                (fn-hib-header np fn-hrecs$c)
                (cond ((not (and (eq hv :ok) (fn-hib-headerp hr)))
                       (mv (list :refused :header (if (eq hv :ok) hr hv)) fn-hrecs$c))
                      ((not (equal (nth 1 hr) count))
                       (mv (list :refused :count (nth 1 hr) count) fn-hrecs$c))
                      (t (let ((fn-hrecs$c (fn-hrc-adopt salt count (nth 2 hr) (nth 3 hr) np (pgs-rec-txid rec)
                                                        fn-hrecs$c)))
                           (mv nil fn-hrecs$c))))))))))))

(local
 (defthm fn-hib-vi-of-put
   (equal (nth *pgs-vi* (pgs-x-put sel i v pgs-mem)) (nth *pgs-vi* pgs-mem))
   :hints (("Goal" :in-theory (enable pgs-x-put$inline update-pgs-mi update-pgs-ti)))))
(local
 (defthm fn-hib-vi-of-x-fill
   (equal (nth *pgs-vi* (pgs-x-fill sel a ws pgs-mem)) (nth *pgs-vi* pgs-mem))
   :hints (("Goal" :induct (pgs-x-fill sel a ws pgs-mem) :in-theory (e/d (pgs-x-fill) (pgs-x-put$inline))))))
(local
 (defthm fn-hib-vi-of-fill-run
   (equal (nth *pgs-vi* (fn-hrs-fill-run file addr k sel a pgs-mem)) (nth *pgs-vi* pgs-mem))
   :hints (("Goal" :induct (fn-hrs-fill-run file addr k sel a pgs-mem)
            :in-theory (union-theories '(fn-hrs-fill-run fn-hib-vi-of-x-fill (:induction fn-hrs-fill-run))
                                       (theory 'minimal-theory))))))

(local
 (defthm fn-hib-vi-of-open-table-page
   (equal (nth *pgs-vi* (mv-nth 1 (pgs-x-open-table-page tp rec mode pgs-mem oct))) (nth *pgs-vi* pgs-mem))
   :hints (("Goal" :in-theory (e/d (update-pgs-tvi) (pgs-x-words-digest pgs-x-table-verdict pgs-x-ntables))))))
(local
 (defthm fn-hib-vi-of-load-tables
   (equal (nth *pgs-vi* (mv-nth 1 (fn-hrs-load-tables tabs file rec pgs-mem oct))) (nth *pgs-vi* pgs-mem))
   :hints (("Goal" :induct (fn-hrs-load-tables tabs file rec pgs-mem oct)
            :in-theory (e/d (fn-hrs-load-tables) (pgs-x-open-table-page fn-hrs-fill-run))))))
(local
 (defthm fn-hib-vi-of-resizes
   (and (equal (nth *pgs-vi* (resize-pgs-v n m)) (resize-list (nth *pgs-vi* m) n 0))
        (equal (nth *pgs-vi* (resize-pgs-w n m)) (nth *pgs-vi* m))
        (equal (nth *pgs-vi* (resize-pgs-d n m)) (nth *pgs-vi* m))
        (equal (nth *pgs-vi* (resize-pgs-m n m)) (nth *pgs-vi* m))
        (equal (nth *pgs-vi* (resize-pgs-t n m)) (nth *pgs-vi* m))
        (equal (nth *pgs-vi* (resize-pgs-tv n m)) (nth *pgs-vi* m)))
   :hints (("Goal" :in-theory (enable resize-pgs-v resize-pgs-w resize-pgs-d resize-pgs-m resize-pgs-t resize-pgs-tv)))))
(local
 (defthm fn-hib-resize-list-zero
   (equal (resize-list (resize-list x 0 d) n d) (resize-list nil n d))
   :hints (("Goal" :expand ((resize-list x 0 d))))))
(local
 (defthm fn-hib-vi-of-load-dir
   (equal (nth *pgs-vi* (mv-nth 1 (fn-hrs-load-dir file rec pgs-mem oct))) (nth *pgs-vi* pgs-mem))
   :hints (("Goal" :in-theory (e/d (fn-hrs-load-dir) (nth adt-nth-0 adt-nth-1+ resize-pgs-m fn-hrs-fill-run pgs-x-open-dir pgs-x-ntables))))))
(local
 (defthm fn-hib-vi-of-reset-table
   (equal (nth *pgs-vi* (pgs-x-reset-table n pgs-mem)) (nth *pgs-vi* pgs-mem))
   :hints (("Goal" :in-theory (e/d (pgs-x-reset-table pgs-x-resize) (nth adt-nth-0 adt-nth-1+ resize-pgs-t resize-pgs-tv pgs-x-ntables))))))
(local
 (defthm fn-hib-vi-of-size-image
   (equal (nth *pgs-vi* (fn-hrs-size-image np pgs-mem)) (resize-list nil np 0))
   :hints (("Goal" :in-theory (e/d (fn-hrs-size-image) (nth adt-nth-0 adt-nth-1+ resize-pgs-v resize-pgs-w resize-pgs-d))))))
(local
 (defthm fn-hib-vi-of-open-pgs
   (implies (not (mv-nth 0 (fn-hrs-open-pgs file rec pgs-mem oct)))
            (equal (nth *pgs-vi* (mv-nth 1 (fn-hrs-open-pgs file rec pgs-mem oct)))
                   (resize-list nil (pgs-rec-npages rec) 0)))
   :hints (("Goal" :in-theory (e/d (fn-hrs-open-pgs)
                                   (nth adt-nth-0 adt-nth-1+ fn-hrs-load-tables fn-hrs-load-dir fn-hrs-size-image pgs-x-reset-table
                                    pgs-x-open-tables pgs-x-ntables))))))

(local
 (defun fn-hib-qn-ind (q n)
   (if (or (zp n) (zp q)) (list q n) (fn-hib-qn-ind (1- q) (1- n)))))
(local
 (defthm fn-hib-nth-zeros-not-2
   (not (equal (nth q (resize-list nil n 0)) 2))
   :hints (("Goal" :induct (fn-hib-qn-ind q n) :in-theory (enable resize-list nth))
           ("Subgoal *1/1" :expand ((resize-list nil n 0))))))
(local
 (defthm fn-hib-vi-zeros
   (implies (equal (nth *pgs-vi* m) (resize-list nil n 0))
            (not (equal (pgs-vi q m) 2)))
   :hints (("Goal" :in-theory (e/d (pgs-vi) (nth adt-nth-0 adt-nth-1+ resize-list))))))
(defthm fn-hib-vhold-none-verified
  (implies (equal (nth *pgs-vi* m) (resize-list nil n 0))
           (fn-hp-vhold s np m iw))
  :hints (("Goal" :induct (fn-hp-vhold s np m iw)
           :in-theory (e/d ((:induction fn-hp-vhold)) (pgs-vi take nthcdr nth resize-list adt-nth-0 adt-nth-1+)))))

(defun-nx fn-hib-tw (p n iw pgs-mem)
  ; entries P..N-1 of PGS-MEM's loaded table name the digests of IW's pages
  (declare (xargs :measure (nfix (- (nfix n) (nfix p)))))
  (if (zp (- (nfix n) (nfix p)))
      t
    (and (equal (third (pgs-x-get-entry 2 0 (nfix p) pgs-mem))
                (fn-hib-page-digest (take 2048 (nthcdr (* 2048 (nfix p)) iw))))
         (fn-hib-tw (+ 1 (nfix p)) n iw pgs-mem))))

(defun-nx fn-hib-nw (file p n iw pgs-mem)
  ; pages P..N-1: the page file's words at the address the table names are
  ; IW's page, or their digest is not that page's
  (declare (xargs :measure (nfix (- (nfix n) (nfix p)))))
  (if (zp (- (nfix n) (nfix p)))
      t
    (and (let ((w (fn-pgs-page-words file (first (pgs-x-get-entry 2 0 (nfix p) pgs-mem))))
               (ip (take 2048 (nthcdr (* 2048 (nfix p)) iw))))
           (implies (equal (fn-hib-page-digest w) (fn-hib-page-digest ip)) (equal w ip)))
         (fn-hib-nw file (+ 1 (nfix p)) n iw pgs-mem))))

(defthmd fn-hib-tabs-is-tw
  (equal (fn-hib-tabs p n h c)
         (fn-hib-tw p n (fn-hp-piw (take (fn-hrc-nimg c) h) (fn-hrc-salt c) (fn-hrc-starts c) (fn-hrc-npages c))
                    (fn-hrc-pgs c)))
  :hints (("Goal" :induct (fn-hib-tabs p n h c) :in-theory (disable fn-hp-piw take nthcdr pgs-x-get-entry))))

(defthmd fn-hib-nc-is-nw
  (equal (fn-hib-nc file p n h c)
         (fn-hib-nw file p n (fn-hp-piw (take (fn-hrc-nimg c) h) (fn-hrc-salt c) (fn-hrc-starts c) (fn-hrc-npages c))
                    (fn-hrc-pgs c)))
  :hints (("Goal" :induct (fn-hib-nc file p n h c) :in-theory (disable fn-hp-piw take nthcdr pgs-x-get-entry))))

(defthm fn-hib-tw-page
  (implies (and (fn-hib-tw p n iw m) (natp p) (natp q) (<= p q) (< q (nfix n)))
           (equal (third (pgs-x-get-entry 2 0 q m)) (fn-hib-page-digest (take 2048 (nthcdr (* 2048 q) iw)))))
  :hints (("Goal" :induct (fn-hib-tw p n iw m) :in-theory (disable take nthcdr pgs-x-get-entry))))

(defthm fn-hib-nw-page
  (implies (and (fn-hib-nw file p n iw m) (natp p) (natp q) (<= p q) (< q (nfix n))
                (equal (fn-hib-page-digest (fn-pgs-page-words file (first (pgs-x-get-entry 2 0 q m))))
                       (fn-hib-page-digest (take 2048 (nthcdr (* 2048 q) iw)))))
           (equal (fn-pgs-page-words file (first (pgs-x-get-entry 2 0 q m)))
                  (take 2048 (nthcdr (* 2048 q) iw))))
  :hints (("Goal" :induct (fn-hib-nw file p n iw m) :in-theory (disable take nthcdr pgs-x-get-entry))))

(defthm fn-hib-open-root-pgs
  (implies (not (mv-nth 0 (fn-hib-open-root file rec c)))
           (let ((m (fn-hrc-pgs (mv-nth 1 (fn-hib-open-root file rec c)))))
             (and (equal (nth *pgs-vi* m) (resize-list nil (pgs-rec-npages rec) 0))
                  (equal (pgs-v-length m) (pgs-rec-npages rec)))))
  :hints (("Goal" :in-theory (e/d (pgs-v-length) (fn-hrs-open-pgs nth adt-nth-0 adt-nth-1+ resize-list)))))
(defthm fn-hib-tw-of-fill-pgs
  (implies (natp q)
           (equal (fn-hib-tw p n iw (mv-nth 1 (fn-hrs-fill-pgs q words txid m oct))) (fn-hib-tw p n iw m)))
  :hints (("Goal" :induct (fn-hib-tw p n iw m) :in-theory (disable fn-hrs-fill-pgs pgs-x-get-entry take nthcdr))))
(defthm fn-hib-nw-of-fill-pgs
  (implies (natp q)
           (equal (fn-hib-nw file p n iw (mv-nth 1 (fn-hrs-fill-pgs q words txid m oct))) (fn-hib-nw file p n iw m)))
  :hints (("Goal" :induct (fn-hib-nw file p n iw m) :in-theory (disable fn-hrs-fill-pgs pgs-x-get-entry take nthcdr))))

(defthm fn-hib-adopt-fill-vhold
  (implies (and (natp np) (true-listp iw)
                (equal (nth *pgs-vi* (fn-hrc-pgs c1)) (resize-list nil np 0))
                (equal (pgs-v-length (fn-hrc-pgs c1)) np) (< 0 np)
                (fn-hib-tw 0 np iw (fn-hrc-pgs c1)) (fn-hib-nw file 0 np iw (fn-hrc-pgs c1)))
           (let ((m2 (fn-hrc-pgs (mv-nth 1 (fn-hrc-fill 0 (fn-pgs-fill-realize file (fn-hrc-phys 0 c1)) c1)))))
             (and (fn-hp-vhold 0 np m2 iw) (equal (pgs-v-length m2) np)
                  (fn-hib-tw 0 np iw m2) (fn-hib-nw file 0 np iw m2))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hib-fill-pgs-vhold (p 0) (m (fn-hrc-pgs c1)) (oct (fn-hrc-oct c1)) (txid (fn-hrc-txid c1))
                            (w (fn-pgs-fill-realize file (fn-hrc-phys 0 c1))))
                 (:instance fn-hib-vhold-none-verified (s 0) (n np) (m (fn-hrc-pgs c1)))
                 (:instance fn-hib-tw-page (p 0) (q 0) (n np) (m (fn-hrc-pgs c1)))
                 (:instance fn-hib-nw-page (p 0) (q 0) (n np) (m (fn-hrc-pgs c1))))
           :in-theory (e/d (fn-hrc-phys) (fn-hib-fill-pgs-vhold fn-hib-vhold-none-verified fn-hib-tw-page fn-hib-nw-page
                                          fn-hrs-fill-pgs fn-hib-tw fn-hib-nw fn-hp-vhold pgs-x-get-entry take nthcdr
                                          nth adt-nth-0 adt-nth-1+ resize-list)))))
(local
 (defthm fn-hib-take-len
   (implies (true-listp h) (equal (take (len h) h) h))
   :hints (("Goal" :in-theory (enable take)))))

(defthm fn-hib-adopt-fields
  (let ((c2 (fn-hrc-adopt salt n lens starts np txid c)))
    (and (equal (fn-hrc-img c2) 1) (equal (fn-hrc-salt c2) salt) (equal (fn-hrc-nimg c2) n)
         (equal (fn-hrc-lens c2) lens) (equal (fn-hrc-starts c2) starts) (equal (fn-hrc-npages c2) np)
         (equal (fn-hrc-txid c2) txid) (equal (fn-hrc-lo c2) 0) (equal (fn-hrc-hi c2) 0)
         (equal (fn-hrc-pgs c2) (fn-hrc-pgs c)) (equal (fn-hrc-oct c2) (fn-hrc-oct c))
         (equal (fn-hrc-sfx-length c2) (fn-hrc-sfx-length c)))))


(defthm fn-hib-adopt-wfp
  (implies (and (fn-hrc-wfp c) (natp salt) (natp n) (nat-listp lens) (equal (len lens) 5)
                (nat-listp starts) (equal (len starts) 5) (natp np) (natp txid))
           (fn-hrc-wfp (fn-hrc-adopt salt n lens starts np txid c))))

(defthm fn-hib-events-okp-true-listp
  (implies (fn-hp-events-okp h) (true-listp h))
  :rule-classes :forward-chaining
  :hints (("Goal" :induct (true-listp h) :in-theory (union-theories '(fn-hp-events-okp true-listp) (theory 'minimal-theory)))))
(defthm fn-hib-okp-true-listp
  (implies (fn-hp-okp h salt) (true-listp h))
  :rule-classes :forward-chaining
  :hints (("Goal" :use fn-hib-events-okp-true-listp
           :in-theory (union-theories '(fn-hp-okp) (theory 'minimal-theory)))))

(defthm fn-hib-sfx-list-empty
  (equal (fn-hrc-sfx-list i i c) nil)
  :hints (("Goal" :expand ((fn-hrc-sfx-list i i c)))))
(local
 (defthm fn-hib-nthcdr-len
   (implies (true-listp h) (equal (nthcdr (len h) h) nil))))

; KEYSTONE (adoption ESTABLISHES faithfulness).  When the root the host
; opens holds H's image -- its tables name the digests of H's placed image
; pages (the snapshot of H committed it; section G ties the root to the
; binding) -- and the page file holds no second preimage of an image page,
; an adoption that lands has read H's header from page 0 (the count is
; H's), and leaves the concrete holding H: `fn-hrs-rel' (the relation
; `fn-hrecs-faithful' is), the root's tables H's, and the disk bound to
; H's pages.  Nothing about the disk is assumed beyond the digest bound:
; a page 0 that is not H's is refused by name.
(defthm fn-hib-adopt-establishes
  (let* ((c1 (mv-nth 1 (fn-hib-open-root file rec c)))
         (np (pgs-rec-npages rec))
         (iw (fn-hp-piw h salt starts np))
         (r (fn-hib-adopt file rec salt count c))
         (c2 (mv-nth 1 r)))
    (implies (and (fn-hrc-wfp c) (natp salt) (natp count)
                  (fn-hp-okp h salt) (fn-hp-starts-okp starts) (adt-placement-ok starts (fn-hp-lens h salt) np)
                  (fn-hib-tw 0 np iw (fn-hrc-pgs c1))
                  (fn-hib-nw file 0 np iw (fn-hrc-pgs c1))
                  (not (mv-nth 0 r)))
             (and (equal (len h) count)
                  (fn-hrc-wfp c2)
                  (fn-hrs-rel h c2)
                  (fn-hib-root-holds h c2)
                  (fn-hib-disk-bound file h c2))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hib-open-root-pgs) (:instance fn-hrc-fill-wfp (p 0) (fn-hrecs$c (mv-nth 1 (fn-hib-open-root file rec c))) (words (fn-pgs-fill-realize file (fn-hrc-phys 0 (mv-nth 1 (fn-hib-open-root file rec c))))))
                 (:instance fn-hib-adopt-fill-vhold (c1 (mv-nth 1 (fn-hib-open-root file rec c))) (np (pgs-rec-npages rec))
                            (iw (fn-hp-piw h salt starts (pgs-rec-npages rec))))
                 (:instance fn-hp-x-header-is-placed (np (pgs-rec-npages rec))
                            (pgs-mem (fn-hrc-pgs (mv-nth 1 (fn-hrc-fill 0 (fn-pgs-fill-realize file (fn-hrc-phys 0 (mv-nth 1 (fn-hib-open-root file rec c))))
                                                                         (mv-nth 1 (fn-hib-open-root file rec c))))))))
           :in-theory (e/d (fn-hib-adopt fn-hib-header fn-hrs-rel fn-hrs-img-ok fn-hib-root-holds fn-hib-disk-bound
                            fn-hib-tabs-is-tw fn-hib-nc-is-nw)
                           (fn-hib-open-root-pgs fn-hib-adopt-fill-vhold fn-hp-x-header-is-placed
                            fn-hib-open-root fn-hrc-fill fn-hrc-fill-shape fn-hrc-phys fn-hrc-adopt fn-hp-x-header
                            fn-hp-piw fn-hp-piw-caps-extend fn-hp-placement-mono fn-hp-wreps-commute fn-hp-hdr2 adt-zeros (:e adt-zeros) (:e fn-hp-hdr2) fn-hp-okp fn-hp-lens pgs-rec-npages pgs-rec-txid fn-pgs-fill-realize-is-page-words fn-hp-starts-okp adt-placement-ok fn-hp-vhold
                            fn-hib-tw fn-hib-nw fn-hrc-wfp take nthcdr resize-list nth adt-nth-0 adt-nth-1+)))))

; -----------------------------------------------------------------------------
; E. Asynchronous page faults: a need becomes a request bound to the active
; root and the page's identity; its completion arrives outside the owner.

(defun fn-hib-entry (p fn-hrecs$c)
  ; the loaded table's entry for image page P: (PHYS TXID DIGEST)
  (declare (xargs :stobjs fn-hrecs$c :guard (natp p)))
  (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c))) (e) (pgs-x-get-entry 2 0 p pgs-mem) e))

(defun fn-hib-request (op p fn-hrecs$c)
  ; A read's need for page P, as a request the host serves OUTSIDE the
  ; owner: (:page-request OP ROOT P PHYS DIGEST) -- the operation OP that
  ; asked, the active root's generation ROOT (the committed record's txid),
  ; the logical page, the address its entry names and the digest the
  ; words must have.
  (declare (xargs :stobjs fn-hrecs$c :guard (natp p)))
  (let ((e (fn-hib-entry p fn-hrecs$c)))
    (list :page-request op (fn-hrc-txid fn-hrecs$c) p (first e) (third e))))

(defun fn-hib-requestp (q)
  (declare (xargs :guard t))
  (and (true-listp q) (equal (len q) 6) (eq (nth 0 q) :page-request)
       (natp (nth 2 q)) (natp (nth 3 q)) (natp (nth 4 q))))

(defun fn-hib-q-root (q) (declare (xargs :guard (fn-hib-requestp q))) (nth 2 q))
(defun fn-hib-q-page (q) (declare (xargs :guard (fn-hib-requestp q))) (nth 3 q))
(defun fn-hib-q-phys (q) (declare (xargs :guard (fn-hib-requestp q))) (nth 4 q))
(defun fn-hib-q-digest (q) (declare (xargs :guard (fn-hib-requestp q))) (nth 5 q))

(defthm fn-hib-entry-shape
  (true-listp (fn-hib-entry p c))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable pgs-x-get-entry))))
(defun fn-hib-complete (q words fn-hrecs$c)
  ; The completion of request Q with WORDS, the host's read at Q's PHYS
  ; (done outside the owner; it may arrive late).  (mv VERDICT fn-hrecs$c):
  ;   (:refused :stale-root ROOT-Q ROOT)  the active root changed since Q:
  ;                                       nothing changes, the reader asks
  ;                                       again (never damage, never absence)
  ;   (:refused :stale-page P)            P's entry is not the one Q named:
  ;                                       nothing changes
  ;   :ok                                 P verified (or it already was)
  ;   the page store's refusal of the words ((:page-damaged P PHYS)): the
  ;                                       page file does not hold the page
  ;                                       (a recovery event)
  (declare (xargs :stobjs fn-hrecs$c :guard (and (fn-hib-requestp q) (fn-hrc-wfp fn-hrecs$c))
                  :guard-hints (("Goal" :in-theory (union-theories '(fn-hib-requestp fn-hib-q-page fn-hib-entry-shape natp len
                                                                     (:e len) (:e natp))
                                                                   (theory 'minimal-theory))))))
  (let ((p (fn-hib-q-page q)) (e (fn-hib-entry (fn-hib-q-page q) fn-hrecs$c)))
    (cond ((not (equal (fn-hib-q-root q) (fn-hrc-txid fn-hrecs$c)))
           (mv (list :refused :stale-root (fn-hib-q-root q) (fn-hrc-txid fn-hrecs$c)) fn-hrecs$c))
          ((not (and (equal (fn-hib-q-phys q) (first e)) (equal (fn-hib-q-digest q) (third e))))
           (mv (list :refused :stale-page p) fn-hrecs$c))
          (t (fn-hrc-fill p words fn-hrecs$c)))))


(defthm fn-hib-complete-stale
  (let ((r (fn-hib-complete q words c)))
    (and (implies (not (equal (fn-hib-q-root q) (fn-hrc-txid c)))
                  (and (equal (mv-nth 1 r) c)
                       (equal (mv-nth 0 r) (list :refused :stale-root (fn-hib-q-root q) (fn-hrc-txid c)))))
         (implies (and (equal (fn-hib-q-root q) (fn-hrc-txid c))
                       (not (and (equal (fn-hib-q-phys q) (first (fn-hib-entry (fn-hib-q-page q) c)))
                                 (equal (fn-hib-q-digest q) (third (fn-hib-entry (fn-hib-q-page q) c))))))
                  (and (equal (mv-nth 1 r) c)
                       (equal (mv-nth 0 r) (list :refused :stale-page (fn-hib-q-page q)))))))
  :hints (("Goal" :in-theory (disable fn-hrc-fill fn-hrc-fill-shape fn-hib-entry fn-hrs-fill-pgs))))

(defthm fn-hib-entry-phys
  (equal (first (fn-hib-entry p c)) (fn-hrc-phys p c))
  :hints (("Goal" :in-theory (disable pgs-x-get-entry))))

; KEYSTONE (the asynchronous fault's completion).  A completion whose words
; are what the page file holds at the request's address keeps the history
; faithful, the root's tables H's and the disk bound, whatever it answers;
; a stale one (the root or the entry changed since the request) changes
; nothing and says so by name.
(defthm fn-hib-complete-keeps
  (implies (and (fn-hrc-wfp c) (fn-hrs-rel h c) (fn-hib-root-holds h c) (fn-hib-disk-bound file h c)
                (fn-hib-requestp q))
           (let ((c2 (mv-nth 1 (fn-hib-complete q (fn-pgs-fill-realize file (fn-hib-q-phys q)) c))))
             (and (fn-hrc-wfp c2) (fn-hrs-rel h c2) (fn-hib-root-holds h c2) (fn-hib-disk-bound file h c2))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hib-complete-stale (words (fn-pgs-fill-realize file (fn-hib-q-phys q))))
                 (:instance fn-hib-fill-rel (p (fn-hib-q-page q)))
                 (:instance fn-hib-root-holds-of-fill (p (fn-hib-q-page q))
                            (words (fn-pgs-fill-realize file (fn-hib-q-phys q)))))
           :in-theory (union-theories '(fn-hib-complete fn-hib-entry-phys fn-hib-requestp fn-hib-q-page fn-hib-q-root
                                        fn-hib-q-phys fn-hib-q-digest natp mv-nth car-cons cdr-cons)
                                      (theory 'minimal-theory)))))

(defthm fn-hib-entry-phys-natp
  (natp (first (pgs-x-get-entry sel base i m)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (pgs-x-get-entry) (pgs-x-word$inline pgs-x-dig4 pgs-x-eaddr pgs-x-len$inline)))))
(defthm fn-hib-request-p
  (implies (and (natp p) (fn-hrc-wfp c))
           (fn-hib-requestp (fn-hib-request op p c)))
  :hints (("Goal" :in-theory (union-theories '(fn-hib-request fn-hib-requestp fn-hib-entry fn-hib-entry-phys-natp fn-hrc-wfp
                                               nth-0-cons nth-add1 len true-listp (:e zp) zp (:e len) (:e nfix) natp
                                               (:e natp) car-cons cdr-cons)
                                             (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; D. Eviction and the progress of an operation that pins what it filled.

(defun fn-hib-evict (p pins fn-hrecs$c)
  ; Release image page P (the bounded cache's eviction): refused while an
  ; operation in progress pins it; otherwise the page is no longer verified
  ; and the next read that touches it asks for it again.  (mv VERDICT
  ; fn-hrecs$c).  In this representation (one words array for the image)
  ; the release forgets the verification and frees no memory; the page-frame
  ; table that frees it is the representation step after this one.
  (declare (xargs :stobjs fn-hrecs$c :guard (and (natp p) (true-listp pins))
                  :guard-hints (("Goal" :in-theory (enable fn-hrc-vlen)))))
  (cond ((member p pins) (mv (list :refused :pinned p) fn-hrecs$c))
        ((not (< p (fn-hrc-vlen fn-hrecs$c))) (mv (list :refused :evict-range p) fn-hrecs$c))
        (t (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c)))
                      (pgs-mem)
                      (update-pgs-vi p 0 pgs-mem)
                      (mv :ok fn-hrecs$c)))))

(defthm fn-hib-vhold-clear-flag
  (implies (and (fn-hp-vhold s np m iw) (natp p))
           (fn-hp-vhold s np (update-pgs-vi p 0 m) iw))
  :hints (("Goal" :induct (fn-hp-vhold s np m iw)
           :in-theory (e/d (pgs-vi update-pgs-vi) (take nthcdr)))))

(defthm fn-hib-v-length-of-clear
  (implies (and (natp p) (< p (pgs-v-length m)))
           (equal (pgs-v-length (update-pgs-vi p v m)) (pgs-v-length m)))
  :hints (("Goal" :in-theory (enable pgs-v-length update-pgs-vi))))

(defthm fn-hib-tw-of-clear
  (equal (fn-hib-tw s n iw (update-pgs-vi p v m)) (fn-hib-tw s n iw m))
  :hints (("Goal" :in-theory (disable pgs-x-get-entry take nthcdr) :induct (fn-hib-tw s n iw m))))
(defthm fn-hib-nw-of-clear
  (equal (fn-hib-nw file s n iw (update-pgs-vi p v m)) (fn-hib-nw file s n iw m))
  :hints (("Goal" :in-theory (disable pgs-x-get-entry take nthcdr) :induct (fn-hib-nw file s n iw m))))

(defthm fn-hib-evict-shape
  (equal (mv-nth 1 (fn-hib-evict p pins c))
         (if (or (member p pins) (not (< p (pgs-v-length (fn-hrc-pgs c)))))
             c
           (update-fn-hrc-pgs (update-pgs-vi p 0 (fn-hrc-pgs c)) c)))
  :hints (("Goal" :in-theory (disable update-pgs-vi pgs-v-length))))

(defthm fn-hib-rel-of-clear
  (implies (and (fn-hrs-rel h c) (natp p) (< p (pgs-v-length (fn-hrc-pgs c))))
           (fn-hrs-rel h (update-fn-hrc-pgs (update-pgs-vi p 0 (fn-hrc-pgs c)) c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-hrs-rel fn-hrs-img-ok fn-hrc-row-pgs fn-hib-v-length-of-clear
                                        fn-hrs-sfx-list-of-updates natp)
                                      (theory 'minimal-theory))
           :use ((:instance fn-hib-vhold-clear-flag (s 0) (np (pgs-v-length (fn-hrc-pgs c))) (m (fn-hrc-pgs c))
                            (iw (fn-hp-piw (take (fn-hrc-nimg c) h) (fn-hrc-salt c) (fn-hrc-starts c) (fn-hrc-npages c))))))))

(defthm fn-hib-wfp-of-update-pgs
  (equal (fn-hrc-wfp (update-fn-hrc-pgs x c)) (fn-hrc-wfp c))
  :hints (("Goal" :in-theory (enable fn-hrc-wfp))))

(defthm fn-hib-root-holds-of-clear
  (implies (and (natp p) (< p (pgs-v-length (fn-hrc-pgs c))))
           (and (equal (fn-hib-root-holds h (update-fn-hrc-pgs (update-pgs-vi p 0 (fn-hrc-pgs c)) c))
                       (fn-hib-root-holds h c))
                (equal (fn-hib-disk-bound file h (update-fn-hrc-pgs (update-pgs-vi p 0 (fn-hrc-pgs c)) c))
                       (fn-hib-disk-bound file h c))))
  :hints (("Goal" :in-theory (union-theories '(fn-hib-root-holds fn-hib-disk-bound fn-hib-tabs-is-tw fn-hib-nc-is-nw
                                               fn-hrc-row-pgs fn-hib-v-length-of-clear fn-hib-tw-of-clear fn-hib-nw-of-clear)
                                             (theory 'minimal-theory)))))

(defthm fn-hib-evict-keeps
  (implies (and (fn-hrc-wfp c) (fn-hrs-rel h c) (natp p))
           (let ((c2 (mv-nth 1 (fn-hib-evict p pins c))))
             (and (fn-hrc-wfp c2) (fn-hrs-rel h c2)
                  (equal (fn-hib-root-holds h c2) (fn-hib-root-holds h c))
                  (equal (fn-hib-disk-bound file h c2) (fn-hib-disk-bound file h c)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hib-evict-shape) (:instance fn-hib-rel-of-clear) (:instance fn-hib-root-holds-of-clear))
           :in-theory (union-theories '(fn-hib-wfp-of-update-pgs) (theory 'minimal-theory)))))

(defun-nx fn-hib-undone (q n pins c)
  ; the pages in [Q, N) an operation holding PINS has not yet made safe:
  ; not (verified and pinned by it)
  (declare (xargs :measure (nfix (- (nfix n) (nfix q)))))
  (if (zp (- (nfix n) (nfix q)))
      0
    (+ (if (and (equal (pgs-vi (nfix q) (fn-hrc-pgs c)) 2) (member-equal (nfix q) pins)) 0 1)
       (fn-hib-undone (+ 1 (nfix q)) n pins c))))

(defthm fn-hib-undone-bound
  (<= (fn-hib-undone q n pins c) (nfix (- (nfix n) (nfix q))))
  :rule-classes :linear)

(defthm fn-hib-vi-of-update-vi
  (implies (and (natp q) (natp p))
           (equal (pgs-vi q (update-pgs-vi p v m)) (if (equal q p) v (pgs-vi q m))))
  :hints (("Goal" :in-theory (enable pgs-vi update-pgs-vi))))

(defthm fn-hib-undone-clear
  (implies (and (natp p) (not (member-equal p opins)))
           (equal (fn-hib-undone q n opins (update-fn-hrc-pgs (update-pgs-vi p 0 (fn-hrc-pgs c)) c))
                  (fn-hib-undone q n opins c)))
  :hints (("Goal" :induct (fn-hib-undone q n opins c)
           :in-theory (disable update-pgs-vi pgs-vi))))

(local
 (defthm fn-hib-subsetp-member
   (implies (and (subsetp-equal x y) (member-equal a x)) (member-equal a y))))
(defthm fn-hib-undone-evict
  (implies (and (subsetp-equal opins pins) (natp p))
           (equal (fn-hib-undone q n opins (mv-nth 1 (fn-hib-evict p pins c))) (fn-hib-undone q n opins c)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hib-evict-shape) (:instance fn-hib-undone-clear)
                 (:instance fn-hib-subsetp-member (a p) (x opins) (y pins)))
           :in-theory (e/d () (fn-hib-evict fn-hib-evict-shape fn-hib-undone-clear fn-hib-undone update-pgs-vi pgs-vi
                               fn-hib-subsetp-member)))))

(defthm fn-hib-fill-verdict
  (equal (mv-nth 0 (fn-hrc-fill p words c))
         (mv-nth 0 (fn-hrs-fill-pgs p words (fn-hrc-txid c) (fn-hrc-pgs c) (fn-hrc-oct c))))
  :hints (("Goal" :in-theory (disable fn-hrs-fill-pgs))))
(defthm fn-hib-fill-flag-frame
  (implies (natp p)
           (let ((m2 (fn-hrc-pgs (mv-nth 1 (fn-hrc-fill p words c)))))
             (and (implies (not (equal (nfix q) p)) (equal (pgs-vi q m2) (pgs-vi q (fn-hrc-pgs c))))
                  (implies (not (equal (pgs-vi p m2) (pgs-vi p (fn-hrc-pgs c)))) (equal (pgs-vi p m2) 2))
                  (implies (and (equal (mv-nth 0 (fn-hrc-fill p words c)) :ok)
                                (< p (pgs-v-length (fn-hrc-pgs c))))
                           (equal (pgs-vi p m2) 2)))))
  :hints (("Goal" :use ((:instance fn-hrs-fill-pgs-frame (txid (fn-hrc-txid c)) (pgs-mem (fn-hrc-pgs c))
                                   (fn-octets-pg (fn-hrc-oct c))))
           :in-theory (union-theories '(fn-hrc-fill-shape fn-hib-fill-verdict fn-hrc-row-oct fn-hrc-row-pgs)
                                      (theory 'minimal-theory)))))

(defthm fn-hib-undone-fill-le
  (implies (natp p)
           (<= (fn-hib-undone qq n pins (mv-nth 1 (fn-hrc-fill p words c))) (fn-hib-undone qq n pins c)))
  :hints (("Goal" :induct (fn-hib-undone qq n pins c)
           :in-theory (disable fn-hrc-fill fn-hrc-fill-shape fn-hib-fill-verdict pgs-vi fn-hib-fill-flag-frame fn-hib-undone-bound))
          ("Subgoal *1/2" :use ((:instance fn-hib-fill-flag-frame (q (nfix qq))))))
  :rule-classes :linear)

(defthm fn-hib-undone-more-pins
  (<= (fn-hib-undone qq n (cons a pins) c) (fn-hib-undone qq n pins c))
  :hints (("Goal" :induct (fn-hib-undone qq n pins c) :in-theory (disable pgs-vi fn-hib-undone-bound))
          ("Subgoal *1/2" :expand ((fn-hib-undone qq n (cons a pins) c) (fn-hib-undone qq n pins c)))
          ("Subgoal *1/1" :expand ((fn-hib-undone qq n (cons a pins) c) (fn-hib-undone qq n pins c))))
  :rule-classes :linear)

(defthm fn-hib-undone-fill-drop
  (implies (and (natp p) (natp qq) (<= qq p) (< p (nfix n))
                (not (equal (pgs-vi p (fn-hrc-pgs c)) 2))
                (equal (pgs-vi p (fn-hrc-pgs (mv-nth 1 (fn-hrc-fill p words c)))) 2))
           (< (fn-hib-undone qq n (cons p pins) (mv-nth 1 (fn-hrc-fill p words c))) (fn-hib-undone qq n pins c)))
  :hints (("Goal" :induct (fn-hib-undone qq n pins c)
           :in-theory (disable fn-hrc-fill fn-hrc-fill-shape fn-hib-fill-verdict pgs-vi fn-hib-fill-flag-frame
                               fn-hib-undone-bound fn-hib-undone-fill-le fn-hib-undone-more-pins))
          ("Subgoal *1/2" :use ((:instance fn-hib-fill-flag-frame (q (nfix qq)))
                                (:instance fn-hib-undone-fill-le (qq (+ 1 (nfix qq))))
                                (:instance fn-hib-undone-more-pins (qq (+ 1 (nfix qq))) (a p)
                                           (c (mv-nth 1 (fn-hrc-fill p words c)))))
           :expand ((fn-hib-undone qq n (cons p pins) (mv-nth 1 (fn-hrc-fill p words c)))
                    (fn-hib-undone qq n pins c))))
  :rule-classes :linear)

(defthm fn-hib-complete-ok-is-fill
  (implies (equal (mv-nth 0 (fn-hib-complete q words c)) :ok)
           (equal (fn-hib-complete q words c) (fn-hrc-fill (fn-hib-q-page q) words c)))
  :hints (("Goal" :in-theory (union-theories '(fn-hib-complete mv-nth car-cons cdr-cons (:e equal) (:e car))
                                             (theory 'minimal-theory)))))

; PROGRESS (eviction-aware).  An operation pins each page its read asked
; for once the completion lands.  Its measure `fn-hib-undone' over the
; image's pages is bounded by the page count, never moved by an eviction
; that respects the pins (`fn-hib-undone-evict'), never raised by any
; other fill (`fn-hib-undone-fill-le'), and dropped by each completion of
; one of its own requests (below): so an operation completes after at most
; as many of its own page reads as the image has pages, whatever the other
; operations and the cache do meanwhile.
(defthm fn-hib-complete-progress
  (let* ((p (fn-hib-q-page q)) (r (fn-hib-complete q words c)))
    (implies (and (fn-hib-requestp q) (equal (mv-nth 0 r) :ok)
                  (< p (pgs-v-length (fn-hrc-pgs c))) (not (equal (pgs-vi p (fn-hrc-pgs c)) 2))
                  (natp qq) (<= qq p) (< p (nfix n)))
             (< (fn-hib-undone qq n (cons p pins) (mv-nth 1 r)) (fn-hib-undone qq n pins c))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hib-complete-ok-is-fill)
                 (:instance fn-hib-undone-fill-drop (p (fn-hib-q-page q)))
                 (:instance fn-hib-fill-flag-frame (p (fn-hib-q-page q)) (q (fn-hib-q-page q))))
           :in-theory (union-theories '(fn-hib-requestp fn-hib-q-page natp nfix mv-nth) (theory 'minimal-theory))))
  :rule-classes :linear)

; -----------------------------------------------------------------------------
; G. The binding: the selected root bound to the exact log prefix.
;
; A BINDING (written by the snapshot, beside the fold state the checkpoint
; carries) is (:hib NODE CODEC COUNT TRAIL REC SALT):
;   NODE   the store's identity: the genesis record's node identity
;   CODEC  the interpretation of the image: *fn-hib-codec*
;   COUNT  the prefix's length: the records [0, COUNT) the image holds
;   TRAIL  the prefix's IDENTITY: the log's chain value after the entries
;          that hold records [0, COUNT) (the trailer of the last one; the
;          genesis trailer for the empty prefix) -- not its count
;   REC    the page store's commit record of the image, exactly
;   SALT   the image's Message-ID key salt (the genesis record's)
; The open checks the binding against the store (NODE, SALT), the image
; format it reads (CODEC), the log (TRAIL against the chain value the log's
; suffix continues from) and the page file (REC in a valid root slot); the
; adoption then reads the image's header from page 0 and checks COUNT.
; Each refusal is named; none is absence.

(defconst *fn-hib-codec* (list :fnadtsn2 *adt-version* *fn-scc-schema*))

(defun fn-hib-binding (node codec count trail rec salt)
  (declare (xargs :guard t))
  (list :hib node codec count trail rec salt))

(defun fn-hib-bindingp (b)
  (declare (xargs :guard t))
  (and (true-listp b) (equal (len b) 7) (eq (nth 0 b) :hib)
       (natp (nth 3 b)) (natp (nth 6 b))))

(defun fn-hib-b-node (b) (declare (xargs :guard (fn-hib-bindingp b))) (nth 1 b))
(defun fn-hib-b-codec (b) (declare (xargs :guard (fn-hib-bindingp b))) (nth 2 b))
(defun fn-hib-b-count (b) (declare (xargs :guard (fn-hib-bindingp b))) (nth 3 b))
(defun fn-hib-b-trail (b) (declare (xargs :guard (fn-hib-bindingp b))) (nth 4 b))
(defun fn-hib-b-rec (b) (declare (xargs :guard (fn-hib-bindingp b))) (nth 5 b))
(defun fn-hib-b-salt (b) (declare (xargs :guard (fn-hib-bindingp b))) (nth 6 b))

(defun fn-hib-check (b node salt trail)
  ; The binding B against the store's NODE and SALT (its genesis record's)
  ; and the log's chain value TRAIL at the binding's prefix: nil, or the
  ; refusal by name.
  (declare (xargs :guard t))
  (cond ((not (fn-hib-bindingp b)) (list :refused :binding))
        ((not (equal (fn-hib-b-codec b) *fn-hib-codec*)) (list :refused :codec (fn-hib-b-codec b)))
        ((not (equal (fn-hib-b-node b) node)) (list :refused :store-identity))
        ((not (equal (fn-hib-b-salt b) salt)) (list :refused :salt))
        ((not (equal (fn-hib-b-trail b) trail)) (list :refused :prefix (fn-hib-b-count b)))
        (t nil)))

(defun fn-hib-slot-has (rec slots)
  ; SLOTS as the page store reads the root file (`pgs-x-read-rec' per
  ; slot): each (RECORD CHECK), CHECK the digest observed over its words.
  (declare (xargs :guard t))
  (and (consp slots)
       (or (and (consp (car slots)) (consp (cdr (car slots)))
                (equal (car (car slots)) rec) (pgs-rec-ok rec (cadr (car slots))))
           (fn-hib-slot-has rec (cdr slots)))))

(defun fn-hib-select (b slots)
  ; The binding's root among the page file's root SLOTS: nil when a slot
  ; holds exactly B's record and it checks; else (:refused :root-absent) --
  ; the image the binding names is not the page file's (the publications
  ; out of order, or a file from another store or generation).
  (declare (xargs :guard (fn-hib-bindingp b)))
  (if (fn-hib-slot-has (fn-hib-b-rec b) slots)
      nil
    (list :refused :root-absent)))

(defun fn-hib-open (b node salt trail slots file fn-hrecs$c)
  ; The served open's adoption of the image the selected binding names:
  ; (mv VERDICT fn-hrecs$c), VERDICT nil when adopted (then the concrete
  ; holds the image of records [0, COUNT) and an empty suffix).
  (declare (xargs :stobjs fn-hrecs$c :guard (fn-hrc-wfp fn-hrecs$c)
                  :guard-hints (("Goal" :in-theory (union-theories '(fn-hib-check fn-hib-bindingp fn-hib-b-salt fn-hib-b-count
                                                                     natp (:e natp) len (:e len))
                                                                   (theory 'minimal-theory))))))
  (let ((v (fn-hib-check b node salt trail)))
    (if v
        (mv v fn-hrecs$c)
      (let ((v (fn-hib-select b slots)))
        (if v
            (mv v fn-hrecs$c)
          (fn-hib-adopt file (fn-hib-b-rec b) (fn-hib-b-salt b) (fn-hib-b-count b) fn-hrecs$c))))))

; The model's exact identity of a log prefix: its ENTRIES (each a chunk of
; records, framed and chained as the log writes them, books/store-log.lisp
; fn-lg-frame / fn-lg-trailer).  The prefix's records are the entries'
; records in order; its chain value from the genesis trailer T0 is what
; the binding's TRAIL carries.
(defun fn-hib-chain (prev entries)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom entries)
      prev
    (fn-hib-chain (fn-lg-trailer (fn-lg-frame prev (car entries))) (cdr entries))))

(defun fn-hib-flat (entries)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom entries) nil (append (true-list-fix (car entries)) (fn-hib-flat (cdr entries)))))

; The narrow cryptographic-failure assumption for the prefix, as a
; hypothesis on the two logs actually compared: two entry lists chained from
; the same genesis trailer that reach the same chain value are the same
; entries.  Its failure needs a collision (or a second preimage of the
; genesis trailer) of the frame digest -- BLAKE3 since store format 10 --
; among these frames; the pessimistic figure is the collision bound, 2^-128
; per pair.  No universal injectivity is assumed or claimed.
(defun-nx fn-hib-chain-distinct (t0 e1 e2)
  (implies (equal (fn-hib-chain t0 e1) (fn-hib-chain t0 e2)) (equal e1 e2)))

; KEYSTONE (exact prefix binding).  When the open accepts a binding whose
; TRAIL is the chain value of the log entries its snapshot covered (EW), and
; the log's chain value at that prefix is its entries' (EL), the snapshot
; covered exactly the log's prefix: the same entries -- the same records,
; in the same order, framed the same way -- not merely as many.
(defthm fn-hib-open-binds-prefix
  (implies (and (not (mv-nth 0 (fn-hib-open b node salt trail slots file c)))
                (equal (fn-hib-b-trail b) (fn-hib-chain t0 ew))
                (equal trail (fn-hib-chain t0 el))
                (fn-hib-chain-distinct t0 ew el))
           (equal ew el))
  :hints (("Goal" :in-theory (union-theories '(fn-hib-open fn-hib-check fn-hib-chain-distinct mv-nth car-cons cdr-cons (:e zp) zp (:e not) (:e equal))
                                             (theory 'minimal-theory))))
  :rule-classes nil)

; The root REC of FILE holds H's image: the tables the page store's open
; loads from it name the digests of H's placed image pages.  The snapshot
; that committed REC for H establishes it; after a restart it is what the
; open's digest checks of the directory and table pages establish, under
; the same digest bound as the data pages.
(defun-nx fn-hib-root-is-image (file rec h salt starts c)
  (let ((np (pgs-rec-npages rec)))
    (and (fn-hp-okp h salt) (fn-hp-starts-okp starts) (adt-placement-ok starts (fn-hp-lens h salt) np)
         (fn-hib-tw 0 np (fn-hp-piw h salt starts np) (fn-hrc-pgs (mv-nth 1 (fn-hib-open-root file rec c)))))))

; The page file holds no second preimage of an image page at the addresses
; the root's tables name (the digest bound, as a hypothesis on this file).
(defun-nx fn-hib-file-bound (file rec h salt starts c)
  (let ((np (pgs-rec-npages rec)))
    (fn-hib-nw file 0 np (fn-hp-piw h salt starts np) (fn-hrc-pgs (mv-nth 1 (fn-hib-open-root file rec c))))))

; KEYSTONE (alpha of the selected image is the log's prefix, at open).
; The open accepts the binding a snapshot wrote: its TRAIL the chain value
; of the log entries EW the snapshot covered, its root holding the image of
; the history HW the snapshot held.  Against a log whose chain value at that
; prefix is its entries EL's, the adopted concrete holds exactly HW
; (`fn-hrs-rel', the relation `fn-hrecs-faithful' is), with the root's
; tables and the page file bound to it, HW's length is the binding's count,
; and EW is EL: the history the image holds is the snapshot's of exactly
; the log's prefix [0, COUNT).  Established by the checks the open makes;
; the host assumes none of it.
(defthm fn-hib-open-is-log-prefix
  (let ((r (fn-hib-open b node salt trail slots file c)))
    (implies (and (fn-hrc-wfp c)
                  (equal (fn-hib-b-trail b) (fn-hib-chain t0 ew))
                  (fn-hib-root-is-image file (fn-hib-b-rec b) hw (fn-hib-b-salt b) starts c)
                  (fn-hib-file-bound file (fn-hib-b-rec b) hw (fn-hib-b-salt b) starts c)
                  (equal trail (fn-hib-chain t0 el))
                  (fn-hib-chain-distinct t0 ew el)
                  (not (mv-nth 0 r)))
             (and (fn-hrc-wfp (mv-nth 1 r))
                  (fn-hrs-rel hw (mv-nth 1 r))
                  (fn-hib-root-holds hw (mv-nth 1 r))
                  (fn-hib-disk-bound file hw (mv-nth 1 r))
                  (equal (len hw) (fn-hib-b-count b))
                  (equal ew el))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hib-open-binds-prefix)
                 (:instance fn-hib-adopt-establishes (h hw) (rec (fn-hib-b-rec b)) (salt (fn-hib-b-salt b))
                            (count (fn-hib-b-count b))))
           :in-theory (union-theories '(fn-hib-open fn-hib-check fn-hib-select fn-hib-root-is-image fn-hib-file-bound
                                        fn-hib-bindingp fn-hib-b-salt fn-hib-b-count natp mv-nth car-cons cdr-cons
                                        (:e zp) zp (:e not) (:e equal) len (:e len))
                                      (theory 'minimal-theory))))
  :rule-classes nil)

(defthm fn-hib-load-events-fields
  (let ((c2 (fn-hrc-load-events q c)))
    (and (equal (fn-hrc-pgs c2) (fn-hrc-pgs c)) (equal (fn-hrc-nimg c2) (fn-hrc-nimg c))
         (equal (fn-hrc-salt c2) (fn-hrc-salt c)) (equal (fn-hrc-starts c2) (fn-hrc-starts c))
         (equal (fn-hrc-npages c2) (fn-hrc-npages c))))
  :hints (("Goal" :induct (fn-hrc-load-events q c) :in-theory (enable fn-hrc-load-events))))

(local
 (defthm fn-hib-take-append-short
   (implies (and (natp n) (<= n (len h))) (equal (take n (append h x)) (take n h)))
   :hints (("Goal" :in-theory (enable take)))))

(defthm fn-hib-root-holds-extend
  (implies (and (natp (fn-hrc-nimg c)) (<= (fn-hrc-nimg c) (len h)))
           (and (equal (fn-hib-root-holds (append h x) c) (fn-hib-root-holds h c))
                (equal (fn-hib-disk-bound file (append h x) c) (fn-hib-disk-bound file h c))))
  :hints (("Goal" :in-theory (e/d (fn-hib-root-holds fn-hib-disk-bound fn-hib-tabs-is-tw fn-hib-nc-is-nw)
                                  (fn-hib-tw fn-hib-nw fn-hp-piw take)))))

(defthm fn-hib-root-holds-of-load-events
  (and (equal (fn-hib-root-holds h (fn-hrc-load-events q c)) (fn-hib-root-holds h c))
       (equal (fn-hib-disk-bound file h (fn-hrc-load-events q c)) (fn-hib-disk-bound file h c)))
  :hints (("Goal" :in-theory (e/d (fn-hib-root-holds fn-hib-disk-bound fn-hib-tabs-is-tw fn-hib-nc-is-nw)
                                  (fn-hib-tw fn-hib-nw fn-hp-piw take fn-hrc-load-events)))))

(defthm fn-hib-wfp-nimg
  (implies (fn-hrc-wfp c) (natp (fn-hrc-nimg c)))
  :rule-classes :forward-chaining)
; KEYSTONE (the running state extends the prefix by the suffix).  Replaying
; the log's suffix Q onto the adopted image (the suffix array, no page
; touched) holds the prefix followed by Q, with the root and disk bound
; unchanged.
(defthm fn-hib-replay-extends
  (implies (and (fn-hrc-wfp c) (fn-hrs-rel h c) (fn-hib-root-holds h c) (fn-hib-disk-bound file h c))
           (let ((c2 (fn-hrc-load-events q c)) (h2 (append h (true-list-fix q))))
             (and (fn-hrc-wfp c2) (fn-hrs-rel h2 c2)
                  (fn-hib-root-holds h2 c2) (fn-hib-disk-bound file h2 c2))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrc-load-events-rel (fn-hrecs$c c) (events q))
                 (:instance fn-hib-root-holds-extend (x (true-list-fix q)) (c (fn-hrc-load-events q c))))
           :in-theory (e/d (fn-hrs-rel) (fn-hrc-load-events-rel fn-hib-root-holds-extend fn-hrc-load-events fn-hib-root-holds
                                         fn-hib-disk-bound fn-hrc-wfp fn-hrs-img-ok take nthcdr fn-hrc-sfx-list)))))
