; fn: the history image adopted from its committed root and bound to the
; exact log prefix (lane composed-owner, 2026-09-29, rows A2-A4 of
; build/coordinator/COMPLETE-BEFORE-6.6.0.md).  Prefix fn-hib-.
(in-package "ACL2")
(include-book "history-records-disk")
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
