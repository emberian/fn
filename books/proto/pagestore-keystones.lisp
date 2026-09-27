; fn: the page store's keystones (lane proto-pagestore, 2026-09-27).
;
; Over the model of books/proto/pagestore.lisp:
;   pgs-open-after-commit   commit-then-open denotes the committed state:
;                           after the complete commit of DIRTY on root R,
;                           R opens on the next transaction and the state
;                           with each dirty page replaced.
;   pgs-open-after-crash    a crash anywhere in that commit (any subset of
;                           its page and table writes reached the disk; the
;                           record old, torn or new) opens on the committed
;                           state or on the previous one, and on the
;                           previous one whenever the record did not land.
;   pgs-crash-isolates-other-roots, pgs-fork-denotes
;                           fork isolation: a commit (complete or crashed)
;                           on R leaves every other root's open unchanged,
;                           and a fork opens on its source's state.
; The torn-write keystone takes `pgs-writes-faithful' (a stale page whose
; digest equals the intended page's IS that page: A-CRYPTO's collision
; resistance, instantiated) and a torn record that fails its check; the
; test book shows both are needed.
(in-package "ACL2")
(include-book "pagestore")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; Writes and the addresses they touch.

(defun pgs-write-addrs (writes)
  (if (atom writes)
      nil
    (if (consp (car writes))
        (cons (caar writes) (pgs-write-addrs (cdr writes)))
      (pgs-write-addrs (cdr writes)))))

(defun pgs-avoids (xs ys)
  ; No element of XS is in YS.
  (if (atom xs) t (and (not (member-equal (car xs) ys)) (pgs-avoids (cdr xs) ys))))

(defthm pgs-lookup-of-apply-pages-outside
  (implies (not (member-equal a (pgs-write-addrs writes)))
           (equal (pgs-lookup a (pgs-apply-pages writes keep pages))
                  (pgs-lookup a pages))))

(defthm pgs-lookup-of-cons
  (equal (pgs-lookup a (cons (cons b c) pages))
         (if (equal a b) c (pgs-lookup a pages))))

(in-theory (disable pgs-lookup))

; -----------------------------------------------------------------------------
; Locality: a record's try reads only the addresses it keeps.

(defthm pgs-check-pages-of-apply-pages
  (implies (pgs-avoids (pgs-ptab-physes ptab) (pgs-write-addrs writes))
           (equal (pgs-check-pages ptab txid mode (pgs-apply-pages writes keep pages) i)
                  (pgs-check-pages ptab txid mode pages i))))

(defthm pgs-contents-of-apply-pages
  (implies (pgs-avoids (pgs-ptab-physes ptab) (pgs-write-addrs writes))
           (equal (pgs-contents ptab (pgs-apply-pages writes keep pages))
                  (pgs-contents ptab pages)))
  :hints (("Goal" :induct (pgs-ptab-physes ptab))))

(defthm pgs-avoids-append
  (equal (pgs-avoids (append xs ys) zs)
         (and (pgs-avoids xs zs) (pgs-avoids ys zs))))

(defthm pgs-run-first
  (implies (not (zp m)) (member-equal a (pgs-run a m))))

(defthm pgs-avoids-member
  (implies (and (pgs-avoids xs ys) (member-equal a xs))
           (not (member-equal a ys))))

(defthm pgs-ptab-verdict-when-not-ptab-p
  (implies (not (pgs-ptab-p ptab))
           (pgs-ptab-verdict rec ptab observed)))

(defthm pgs-rec-keeps-avoids-physes
  (implies (and (pgs-ptab-p ptab) (pgs-avoids (pgs-rec-keeps rec ptab) w))
           (pgs-avoids (pgs-ptab-physes ptab) w)))

(defthm pgs-avoids-run-first
  (implies (and (pgs-avoids (pgs-run a m) w) (not (zp m)))
           (not (member-equal a w))))

(defthm pgs-rec-keeps-avoids-addr
  (implies (pgs-avoids (pgs-rec-keeps rec ptab) w)
           (not (member-equal (pgs-rec-ptab-addr rec) w)))
  :hints (("Goal" :in-theory (disable pgs-avoids-run-first pgs-rec-ptab-addr)
                  :use ((:instance pgs-avoids-run-first
                                   (a (pgs-rec-ptab-addr rec))
                                   (m (pgs-ptab-run-pages (pgs-rec-ptab-len rec))))))))

(in-theory (disable pgs-rec-keeps))

(defthm pgs-try-of-apply-pages
  (implies (pgs-avoids (pgs-rec-keeps rec (pgs-lookup (pgs-rec-ptab-addr rec) pages))
                       (pgs-write-addrs writes))
           (equal (pgs-try rec (pgs-apply-pages writes keep pages) mode)
                  (pgs-try rec pages mode)))
  :hints (("Goal" :in-theory (disable pgs-check-pages pgs-contents pgs-ptab-verdict
                                      pgs-ptab-p pgs-lookup pgs-apply-pages
                                      pgs-rec-ptab-addr pgs-rec-txid pgs-rec-ptab-len
                                      pgs-rec-ptab-digest pgs-rec-keeps-avoids-addr)
                  :cases ((pgs-ptab-p (pgs-lookup (pgs-rec-ptab-addr rec) pages)))
                  :use ((:instance pgs-rec-keeps-avoids-addr
                                   (ptab (pgs-lookup (pgs-rec-ptab-addr rec) pages))
                                   (w (pgs-write-addrs writes)))))))

(defun pgs-order-valid (order slots)
  (if (atom order)
      t
    (and (member-equal (car order) '(0 1))
         (pgs-rec-valid (pgs-slot (car order) slots))
         (pgs-order-valid (cdr order) slots))))

(defthm pgs-order-valid-of-open-order
  (pgs-order-valid (pgs-open-order (pgs-slot 0 slots) (pgs-rec-valid (pgs-slot 0 slots))
                                   (pgs-slot 1 slots) (pgs-rec-valid (pgs-slot 1 slots)))
                   slots))

(defthm pgs-slot-keeps-avoid
  (implies (and (pgs-avoids (pgs-slots-keeps slots pages) w)
                (member-equal k '(0 1))
                (pgs-rec-valid (pgs-slot k slots)))
           (pgs-avoids (pgs-rec-keeps (pgs-slot k slots)
                                      (pgs-lookup (pgs-rec-ptab-addr (pgs-slot k slots)) pages))
                       w))
  :hints (("Goal" :in-theory (disable pgs-rec-valid pgs-slot pgs-lookup))))

(defthm pgs-try-slot-of-apply-pages
  (implies (and (member-equal k '(0 1))
                (pgs-rec-valid (pgs-slot k slots))
                (pgs-avoids (pgs-slots-keeps slots pages) (pgs-write-addrs writes)))
           (equal (pgs-try (pgs-slot k slots) (pgs-apply-pages writes keep pages) mode)
                  (pgs-try (pgs-slot k slots) pages mode)))
  :hints (("Goal" :in-theory (disable pgs-try pgs-rec-valid pgs-slot pgs-slots-keeps
                                      pgs-lookup pgs-apply-pages
                                      pgs-slot-keeps-avoid pgs-try-of-apply-pages)
                  :use ((:instance pgs-slot-keeps-avoid (w (pgs-write-addrs writes)))
                        (:instance pgs-try-of-apply-pages (rec (pgs-slot k slots)))))))

(defthm pgs-try-in-order-of-apply-pages
  (implies (and (pgs-order-valid order slots)
                (pgs-avoids (pgs-slots-keeps slots pages) (pgs-write-addrs writes)))
           (equal (pgs-try-in-order order slots (pgs-apply-pages writes keep pages) mode refusals)
                  (pgs-try-in-order order slots pages mode refusals)))
  :hints (("Goal" :induct (pgs-try-in-order order slots pages mode refusals)
                  :in-theory (disable pgs-try pgs-rec-valid pgs-slot pgs-slots-keeps
                                      pgs-lookup pgs-apply-pages pgs-rec-shape-p
                                      pgs-slot-keeps-avoid pgs-try-of-apply-pages))))

(defthm pgs-open-slots-of-apply-pages
  (implies (pgs-avoids (pgs-slots-keeps slots pages) (pgs-write-addrs writes))
           (equal (pgs-open-slots slots (pgs-apply-pages writes keep pages) mode)
                  (pgs-open-slots slots pages mode)))
  :hints (("Goal" :in-theory (disable pgs-try-in-order pgs-rec-valid pgs-slot pgs-slots-keeps
                                      pgs-lookup pgs-apply-pages pgs-open-order))))

(defthm pgs-slots-keeps-of-nil
  (equal (pgs-slots-keeps nil pages) nil))

(defthm pgs-roots-keeps-cover
  (implies (pgs-avoids (pgs-roots-keeps roots pages) w)
           (pgs-avoids (pgs-slots-keeps (cdr (hons-assoc-equal r roots)) pages) w))
  :hints (("Goal" :induct (pgs-roots-keeps roots pages)
                  :in-theory (disable pgs-slots-keeps))))

; -----------------------------------------------------------------------------
; Allocation: fresh addresses are outside the kept set, and distinct.

(defthm pgs-mark-member
  (iff (hons-assoc-equal a (pgs-mark xs fal))
       (or (member-equal a xs) (hons-assoc-equal a fal)))
  :hints (("Goal" :induct (pgs-mark xs fal))))

(defthm pgs-find-singles-fresh
  (implies (member-equal x (pgs-find-singles n a bound used))
           (not (hons-assoc-equal x used))))

(defthm pgs-find-singles-above
  (implies (and (member-equal x (pgs-find-singles n a bound used)) (natp a))
           (and (natp x) (<= a x))))

(defthm pgs-find-singles-not-below
  (implies (and (natp a) (natp b) (< b a))
           (not (member-equal b (pgs-find-singles n a bound used))))
  :hints (("Goal" :use ((:instance pgs-find-singles-above (x b)))
                  :in-theory (disable pgs-find-singles-above))))

(defthm pgs-find-singles-distinct
  (implies (natp a)
           (no-duplicatesp-equal (pgs-find-singles n a bound used)))
  :hints (("Goal" :induct (pgs-find-singles n a bound used))))

(defthm pgs-free-run-fresh
  (implies (and (pgs-free-run-p a m used) (member-equal x (pgs-run a m)) (natp a))
           (not (hons-assoc-equal x used)))
  :hints (("Goal" :induct (pgs-free-run-p a m used))))

(defthm pgs-find-run-free
  (implies (natp (pgs-find-run a m bound used))
           (pgs-free-run-p (pgs-find-run a m bound used) m used)))

(defthm pgs-find-run-fresh
  (implies (and (natp (pgs-find-run a m bound used))
                (member-equal x (pgs-run (pgs-find-run a m bound used) m)))
           (not (hons-assoc-equal x used)))
  :hints (("Goal" :in-theory (disable pgs-free-run-fresh pgs-find-run-free)
                  :use ((:instance pgs-free-run-fresh (a (pgs-find-run a m bound used)))
                        (:instance pgs-find-run-free)))))

(defthm pgs-alloc-run-fresh
  (implies (and (consp (pgs-alloc n m hwm used))
                (member-equal x (pgs-run (car (pgs-alloc n m hwm used)) m)))
           (not (hons-assoc-equal x used)))
  :hints (("Goal" :in-theory (enable pgs-alloc))))

(defthm pgs-alloc-start-natp
  (implies (consp (pgs-alloc n m hwm used))
           (natp (car (pgs-alloc n m hwm used))))
  :hints (("Goal" :in-theory (enable pgs-alloc)))
  :rule-classes ((:rewrite) (:type-prescription :corollary
                             (implies (consp (pgs-alloc n m hwm used))
                                      (natp (car (pgs-alloc n m hwm used)))))))

(defthm pgs-alloc-singles-fresh
  (implies (and (consp (pgs-alloc n m hwm used))
                (member-equal x (cdr (pgs-alloc n m hwm used))))
           (and (not (hons-assoc-equal x used))
                (not (member-equal x (pgs-run (car (pgs-alloc n m hwm used)) m)))))
  :hints (("Goal" :in-theory (e/d (pgs-alloc) (pgs-find-singles-fresh))
                  :use ((:instance pgs-find-singles-fresh
                                   (a 0) (bound (+ hwm m n))
                                   (used (pgs-mark (pgs-run (pgs-find-run 0 m (+ hwm m n) used) m)
                                                   used)))))))

(defthm pgs-alloc-singles-shape
  (implies (consp (pgs-alloc n m hwm used))
           (and (no-duplicatesp-equal (cdr (pgs-alloc n m hwm used)))
                (equal (len (cdr (pgs-alloc n m hwm used))) (nfix n))))
  :hints (("Goal" :in-theory (enable pgs-alloc))))

; -----------------------------------------------------------------------------
; Fresh addresses avoid every kept address.

(defun pgs-all-fresh (xs used)
  (if (atom xs) t (and (not (hons-assoc-equal (car xs) used)) (pgs-all-fresh (cdr xs) used))))

(defthm pgs-all-fresh-of-find-singles
  (pgs-all-fresh (pgs-find-singles n a bound used) used))

(defthm pgs-all-fresh-of-mark
  (implies (pgs-all-fresh xs (pgs-mark ys fal))
           (and (pgs-all-fresh xs fal) (pgs-avoids xs ys))))

(defthm pgs-all-fresh-of-alloc
  (implies (consp (pgs-alloc n m hwm used))
           (and (pgs-all-fresh (cdr (pgs-alloc n m hwm used)) used)
                (pgs-avoids (cdr (pgs-alloc n m hwm used))
                            (pgs-run (car (pgs-alloc n m hwm used)) m))))
  :hints (("Goal" :in-theory (enable pgs-alloc)
                  :use ((:instance pgs-all-fresh-of-mark
                                   (xs (pgs-find-singles n 0 (+ hwm m n)
                                                         (pgs-mark (pgs-run (pgs-find-run 0 m (+ hwm m n) used) m)
                                                                   used)))
                                   (ys (pgs-run (pgs-find-run 0 m (+ hwm m n) used) m))
                                   (fal used))))))

(defthm pgs-avoids-of-all-fresh-mark-nil
  (implies (pgs-all-fresh xs (pgs-mark ys nil))
           (pgs-avoids xs ys)))

(defthm pgs-avoids-cons
  (equal (pgs-avoids xs (cons y ys))
         (and (not (member-equal y xs)) (pgs-avoids xs ys))))

(defthm pgs-avoids-nil
  (pgs-avoids xs nil))

(defthm pgs-avoids-symmetric
  (equal (pgs-avoids xs ys) (pgs-avoids ys xs))
  :rule-classes nil)

; The commit's writes and their addresses.

(defthm pgs-write-addrs-append
  (equal (pgs-write-addrs (append a b))
         (append (pgs-write-addrs a) (pgs-write-addrs b))))

(defthm pgs-write-addrs-of-page-writes
  (implies (equal (len fresh) (len dirty))
           (equal (pgs-write-addrs (pgs-page-writes dirty fresh))
                  (true-list-fix fresh))))

(defthm pgs-member-append
  (iff (member-equal x (append a b))
       (or (member-equal x a) (member-equal x b))))

(defthm pgs-member-true-list-fix
  (iff (member-equal x (true-list-fix a)) (member-equal x a)))

(defthm pgs-avoids-append-right
  (equal (pgs-avoids xs (append ys zs))
         (and (pgs-avoids xs ys) (pgs-avoids xs zs))))

(defthm pgs-avoids-true-list-fix
  (equal (pgs-avoids xs (true-list-fix ys)) (pgs-avoids xs ys)))

; -----------------------------------------------------------------------------
; Where the writes land.

(defun pgs-lands (dirty fresh pages)
  ; Each dirty page's content is at its fresh address.
  (if (atom dirty)
      t
    (and (equal (pgs-lookup (car fresh) pages) (cdar dirty))
         (pgs-lands (cdr dirty) (cdr fresh) pages))))

(defun pgs-lands-ind (dirty fresh pages)
  (if (atom dirty)
      pages
    (pgs-lands-ind (cdr dirty) (cdr fresh) (cons (cons (car fresh) (cdar dirty)) pages))))

(defthm pgs-lands-of-apply-pages
  (implies (and (no-duplicatesp-equal fresh)
                (equal (len fresh) (len dirty))
                (pgs-avoids fresh (pgs-write-addrs tail)))
           (pgs-lands dirty fresh
                      (pgs-apply-pages (append (pgs-page-writes dirty fresh) tail) nil pages)))
  :hints (("Goal" :induct (pgs-lands-ind dirty fresh pages))))

(defun pgs-content-of (a ws)
  (if (atom ws)
      nil
    (if (and (consp (car ws)) (equal (caar ws) a))
        (cdar ws)
      (pgs-content-of a (cdr ws)))))

(defthm pgs-lookup-of-apply-pages-all
  (implies (and (no-duplicatesp-equal (pgs-write-addrs ws))
                (member-equal a (pgs-write-addrs ws)))
           (equal (pgs-lookup a (pgs-apply-pages ws nil pages))
                  (pgs-content-of a ws))))

(defthm pgs-lookup-of-apply-pages-some
  (implies (and (no-duplicatesp-equal (pgs-write-addrs ws))
                (member-equal a (pgs-write-addrs ws)))
           (or (equal (pgs-lookup a (pgs-apply-pages ws keep pages))
                      (pgs-content-of a ws))
               (equal (pgs-lookup a (pgs-apply-pages ws keep pages))
                      (pgs-lookup a pages))))
  :rule-classes nil)

; With distinct write addresses, a crash image holds at each address either
; what the complete commit holds there or what was there before.
(defthm pgs-lookup-of-apply-pages-crash
  (implies (no-duplicatesp-equal (pgs-write-addrs writes))
           (or (equal (pgs-lookup a (pgs-apply-pages writes keep pages))
                      (pgs-lookup a (pgs-apply-pages writes nil pages)))
               (equal (pgs-lookup a (pgs-apply-pages writes keep pages))
                      (pgs-lookup a pages))))
  :rule-classes nil
  :hints (("Goal" :cases ((member-equal a (pgs-write-addrs writes)))
                  :use ((:instance pgs-lookup-of-apply-pages-some (ws writes))))))

; -----------------------------------------------------------------------------
; Table predicates, entry by entry, and what the planner keeps of them.

(defun pgs-entries-good (ptab txid mode pages)
  ; Every entry the mode checks verifies.
  (if (atom ptab)
      t
    (and (not (eq (pgs-entry-verdict (car ptab) txid mode
                                     (pgs-digest (pgs-lookup (first (car ptab)) pages)))
                  :damaged))
         (pgs-entries-good (cdr ptab) txid mode pages))))

(defthm pgs-check-pages-iff-good
  (iff (pgs-check-pages ptab txid mode pages i)
       (not (pgs-entries-good ptab txid mode pages))))

(defun pgs-entry-sound (e txid mode p1 p2)
  ; Reading entry E's page in P2 either gives what P1 holds there, or the
  ; check refuses it.
  (or (equal (pgs-lookup (first e) p2) (pgs-lookup (first e) p1))
      (and (pgs-entry-checked-p e txid mode)
           (not (equal (pgs-digest (pgs-lookup (first e) p2)) (third e))))))

(defun pgs-entries-sound (ptab txid mode p1 p2)
  (if (atom ptab)
      t
    (and (pgs-entry-sound (car ptab) txid mode p1 p2)
         (pgs-entries-sound (cdr ptab) txid mode p1 p2))))

(defthm pgs-contents-when-sound-and-good
  (implies (and (pgs-entries-sound ptab txid mode p1 p2)
                (pgs-entries-good ptab txid mode p2))
           (equal (pgs-contents ptab p2) (pgs-contents ptab p1))))

; update-nth keeps each entrywise predicate.
(defthm pgs-entries-good-of-update-nth
  (implies (and (pgs-entries-good ptab txid mode pages)
                (not (eq (pgs-entry-verdict e txid mode (pgs-digest (pgs-lookup (first e) pages)))
                         :damaged))
                (< (nfix i) (len ptab)))
           (pgs-entries-good (update-nth i e ptab) txid mode pages))
  :hints (("Goal" :induct (update-nth i e ptab))))

(defthm pgs-entries-sound-of-update-nth
  (implies (and (pgs-entries-sound ptab txid mode p1 p2)
                (pgs-entry-sound e txid mode p1 p2)
                (< (nfix i) (len ptab)))
           (pgs-entries-sound (update-nth i e ptab) txid mode p1 p2))
  :hints (("Goal" :induct (update-nth i e ptab) :in-theory (disable pgs-entry-sound))))

(defthm pgs-ptab-p-of-update-nth
  (implies (and (pgs-ptab-p ptab) (pgs-entry-p e) (< (nfix i) (len ptab)))
           (pgs-ptab-p (update-nth i e ptab)))
  :hints (("Goal" :induct (update-nth i e ptab))))

(defthm pgs-txids-ok-of-update-nth
  (implies (and (pgs-ptab-txids-ok ptab txid) (pgs-entry-p e) (<= (second e) (nfix txid))
                (< (nfix i) (len ptab)))
           (pgs-ptab-txids-ok (update-nth i e ptab) txid))
  :hints (("Goal" :induct (update-nth i e ptab))))

(defthm pgs-len-of-update-entry
  (equal (len (pgs-update-entry i e ptab)) (len ptab)))

(defthm pgs-len-of-plan-ptab
  (equal (len (pgs-plan-ptab ptab lpages fresh digests txid)) (len ptab))
  :hints (("Goal" :induct (pgs-plan-ptab ptab lpages fresh digests txid)
                  :in-theory (disable pgs-update-entry))))

(defthm pgs-contents-of-update-nth
  (implies (< (nfix i) (len ptab))
           (equal (pgs-contents (update-nth i e ptab) pages)
                  (update-nth i (pgs-lookup (first e) pages) (pgs-contents ptab pages))))
  :hints (("Goal" :induct (update-nth i e ptab))))

(defthm pgs-len-of-contents
  (equal (len (pgs-contents ptab pages)) (len ptab)))

(defthm pgs-contents-of-update-entry
  (equal (pgs-contents (pgs-update-entry i e ptab) pages)
         (if (< (nfix i) (len ptab))
             (update-nth (nfix i) (pgs-lookup (first e) pages) (pgs-contents ptab pages))
           (pgs-contents ptab pages))))

(defun pgs-plan-ind (ptab dirty fresh contents txid)
  (if (atom dirty)
      (list ptab fresh contents txid)
    (pgs-plan-ind (pgs-update-entry (nfix (caar dirty))
                                    (list (nfix (car fresh)) (nfix txid)
                                          (nfix (pgs-digest (cdar dirty))))
                                    ptab)
                  (cdr dirty) (cdr fresh)
                  (if (< (nfix (caar dirty)) (len contents))
                      (update-nth (nfix (caar dirty)) (cdar dirty) contents)
                    contents)
                  txid)))

; The planner over the model's dirty list: the table after the commit, read
; where the dirty pages landed, is the state with the dirty pages replaced.
(defthm pgs-contents-of-plan-ptab
  (implies (and (pgs-lands dirty fresh pages) (nat-listp fresh) (<= (len dirty) (len fresh)))
           (equal (pgs-contents (pgs-plan-ptab ptab (pgs-dirty-lpages dirty) fresh
                                               (pgs-dirty-digests dirty) txid)
                                pages)
                  (pgs-apply-dirty (pgs-contents ptab pages) dirty)))
  :hints (("Goal" :induct (pgs-plan-ind ptab dirty fresh (pgs-contents ptab pages) txid)
                  :in-theory (disable pgs-update-entry))))

(defthm pgs-entries-good-of-update-entry
  (implies (and (pgs-entries-good ptab txid mode pages)
                (not (eq (pgs-entry-verdict e txid mode (pgs-digest (pgs-lookup (first e) pages)))
                         :damaged)))
           (pgs-entries-good (pgs-update-entry i e ptab) txid mode pages)))

(defthm pgs-entries-sound-of-update-entry
  (implies (and (pgs-entries-sound ptab txid mode p1 p2)
                (pgs-entry-sound e txid mode p1 p2))
           (pgs-entries-sound (pgs-update-entry i e ptab) txid mode p1 p2))
  :hints (("Goal" :in-theory (disable pgs-entry-sound))))

(defthm pgs-ptab-p-of-update-entry
  (implies (and (pgs-ptab-p ptab) (pgs-entry-p e))
           (pgs-ptab-p (pgs-update-entry i e ptab))))

(defthm pgs-txids-ok-of-update-entry
  (implies (and (pgs-ptab-txids-ok ptab txid) (pgs-entry-p e) (<= (second e) (nfix txid)))
           (pgs-ptab-txids-ok (pgs-update-entry i e ptab) txid)))

(in-theory (disable pgs-update-entry))

(defthm pgs-entries-good-of-plan-ptab
  (implies (and (pgs-entries-good ptab txid mode pages)
                (pgs-lands dirty fresh pages) (nat-listp fresh) (<= (len dirty) (len fresh))
                (natp txid))
           (pgs-entries-good (pgs-plan-ptab ptab (pgs-dirty-lpages dirty) fresh
                                            (pgs-dirty-digests dirty) txid)
                             txid mode pages))
  :hints (("Goal" :induct (pgs-plan-ind ptab dirty fresh nil txid))))

(defthm pgs-ptab-p-of-plan-ptab
  (implies (pgs-ptab-p ptab)
           (pgs-ptab-p (pgs-plan-ptab ptab lpages fresh digests txid))))

(defthm pgs-txids-ok-of-plan-ptab
  (implies (pgs-ptab-txids-ok ptab txid)
           (pgs-ptab-txids-ok (pgs-plan-ptab ptab lpages fresh digests txid) txid)))

(defthm pgs-txids-ok-monotone
  (implies (and (pgs-ptab-txids-ok ptab t0) (<= (nfix t0) (nfix t1)))
           (pgs-ptab-txids-ok ptab t1)))

(defthm pgs-entries-good-at-later-txid
  (implies (and (pgs-entries-good ptab t0 mode pages)
                (pgs-ptab-txids-ok ptab t0)
                (natp t0) (< t0 t1))
           (pgs-entries-good ptab t1 mode pages)))

(defthm pgs-entries-good-of-apply-pages
  (implies (pgs-avoids (pgs-ptab-physes ptab) (pgs-write-addrs writes))
           (equal (pgs-entries-good ptab txid mode (pgs-apply-pages writes keep pages))
                  (pgs-entries-good ptab txid mode pages)))
  :hints (("Goal" :induct (pgs-ptab-physes ptab))))

; Soundness of a crash image against the complete commit.
(defthm pgs-entries-sound-of-unwritten
  (implies (pgs-avoids (pgs-ptab-physes ptab) (pgs-write-addrs writes))
           (pgs-entries-sound ptab txid mode
                              (pgs-apply-pages writes nil pages)
                              (pgs-apply-pages writes keep pages))))

; -----------------------------------------------------------------------------
; What a successful try and a successful open say.

(defthm pgs-try-ok-facts
  (implies (equal (car (pgs-try rec pages mode)) :ok)
           (let ((ptab (pgs-lookup (pgs-rec-ptab-addr rec) pages)))
             (and (pgs-ptab-p ptab)
                  (equal (len ptab) (pgs-rec-ptab-len rec))
                  (pgs-ptab-txids-ok ptab (pgs-rec-txid rec))
                  (equal (pgs-digest ptab) (pgs-rec-ptab-digest rec))
                  (pgs-entries-good ptab (pgs-rec-txid rec) mode pages)
                  (equal (pgs-try rec pages mode)
                         (list :ok (pgs-rec-txid rec) (pgs-contents ptab pages))))))
  :rule-classes nil)

(defthm pgs-try-when-facts
  (let ((ptab (pgs-lookup (pgs-rec-ptab-addr rec) pages)))
    (implies (and (pgs-ptab-p ptab)
                  (equal (len ptab) (pgs-rec-ptab-len rec))
                  (pgs-ptab-txids-ok ptab (pgs-rec-txid rec))
                  (equal (pgs-digest ptab) (pgs-rec-ptab-digest rec))
                  (pgs-entries-good ptab (pgs-rec-txid rec) mode pages))
             (equal (pgs-try rec pages mode)
                    (list :ok (pgs-rec-txid rec) (pgs-contents ptab pages)))))
  :rule-classes nil)

(defthm pgs-try-shape
  (implies (equal (car (pgs-try rec pages mode)) :ok)
           (equal (list :ok (cadr (pgs-try rec pages mode)) (caddr (pgs-try rec pages mode)))
                  (pgs-try rec pages mode))))

(defthm pgs-try-in-order-ok
  (let ((o (pgs-try-in-order order slots pages mode refs)))
    (implies (and (equal (car o) :ok) (pgs-order-valid order slots))
             (and (member-equal (second o) '(0 1))
                  (pgs-rec-valid (pgs-slot (second o) slots))
                  (equal (pgs-try (pgs-slot (second o) slots) pages mode)
                         (list :ok (third o) (fourth o)))
                  (true-listp o))))
  :hints (("Goal" :induct (pgs-try-in-order order slots pages mode refs)
                  :in-theory (disable pgs-try pgs-rec-valid pgs-slot)))
  :rule-classes nil)

(defthm pgs-open-slots-ok
  (let ((o (pgs-open-slots slots pages mode)))
    (implies (equal (car o) :ok)
             (and (member-equal (second o) '(0 1))
                  (pgs-rec-valid (pgs-slot (second o) slots))
                  (equal (pgs-try (pgs-slot (second o) slots) pages mode)
                         (list :ok (third o) (fourth o)))
                  (true-listp o))))
  :hints (("Goal" :in-theory (disable pgs-try pgs-rec-valid pgs-slot pgs-try-in-order
                                      pgs-open-order pgs-order-valid-of-open-order)
                  :use ((:instance pgs-order-valid-of-open-order)
                        (:instance pgs-try-in-order-ok
                                   (order (pgs-open-order (pgs-slot 0 slots)
                                                          (pgs-rec-valid (pgs-slot 0 slots))
                                                          (pgs-slot 1 slots)
                                                          (pgs-rec-valid (pgs-slot 1 slots))))
                                   (refs (pgs-slot-refusals (pgs-slot 0 slots)
                                                            (pgs-rec-valid (pgs-slot 0 slots))
                                                            (pgs-slot 1 slots)
                                                            (pgs-rec-valid (pgs-slot 1 slots))))))))
  :rule-classes nil)

; The record a commit writes.
(defthm pgs-make-rec-fields
  (implies (and (natp txid) (natp a) (natp n))
           (and (pgs-rec-valid (pgs-make-rec txid a n (pgs-digest x)))
                (equal (pgs-rec-txid (pgs-make-rec txid a n d)) txid)
                (equal (pgs-rec-ptab-addr (pgs-make-rec txid a n d)) a)
                (equal (pgs-rec-ptab-len (pgs-make-rec txid a n d)) n)
                (equal (pgs-rec-ptab-digest (pgs-make-rec txid a n (pgs-digest x))) (pgs-digest x))
                (pgs-rec-shape-p (pgs-make-rec txid a n (pgs-digest x))))))

; -----------------------------------------------------------------------------
; One commit step, over a root's slots (the disk-level keystones instantiate
; it).  CUR is the slot K0 the open used; the commit writes the dirty pages
; to FRESH, the table PTAB2 to RS and the record to the other slot.

(defun pgs-step-ptab2 (ptab dirty fresh txid)
  (pgs-plan-ptab (true-list-fix ptab) (pgs-dirty-lpages dirty) fresh
                 (pgs-dirty-digests dirty) txid))

(defun pgs-step-writes (dirty fresh rs ptab2)
  (append (pgs-page-writes dirty fresh) (list (cons rs ptab2))))

(in-theory (disable pgs-rec-txid pgs-rec-ptab-addr pgs-rec-ptab-len pgs-rec-ptab-digest))

(defun pgs-step-hyps (cur pages mode dirty fresh rs txid)
  (and (pgs-rec-valid cur)
       (equal (car (pgs-try cur pages mode)) :ok)
       (natp txid) (< (pgs-rec-txid cur) txid)
       (nat-listp fresh) (no-duplicatesp-equal fresh)
       (equal (len fresh) (len dirty))
       (natp rs) (not (member-equal rs fresh))
       (pgs-avoids (pgs-rec-keeps cur (pgs-lookup (pgs-rec-ptab-addr cur) pages))
                   (append fresh (list rs)))))

(defthm pgs-write-addrs-of-step-writes
  (implies (equal (len fresh) (len dirty))
           (equal (pgs-write-addrs (pgs-step-writes dirty fresh rs ptab2))
                  (append (true-list-fix fresh) (list rs)))))

(defthm pgs-no-dups-append-single
  (implies (and (no-duplicatesp-equal xs) (not (member-equal y xs)))
           (no-duplicatesp-equal (append xs (list y)))))

(defthm pgs-no-dups-true-list-fix
  (equal (no-duplicatesp-equal (true-list-fix xs)) (no-duplicatesp-equal xs)))

(defthm pgs-content-of-step-table
  (implies (and (equal (len fresh) (len dirty)) (not (member-equal rs fresh)))
           (equal (pgs-content-of rs (pgs-step-writes dirty fresh rs ptab2)) ptab2)))

(defthm pgs-step-hyps-facts
  (implies (pgs-step-hyps cur pages mode dirty fresh rs txid)
           (and (pgs-rec-valid cur)
                (equal (car (pgs-try cur pages mode)) :ok)
                (natp txid) (< (pgs-rec-txid cur) txid)
                (nat-listp fresh) (no-duplicatesp-equal fresh)
                (equal (len fresh) (len dirty))
                (natp rs) (not (member-equal rs fresh))
                (pgs-avoids (pgs-rec-keeps cur (pgs-lookup (pgs-rec-ptab-addr cur) pages))
                            (append fresh (list rs)))
                (pgs-avoids (pgs-rec-keeps cur (pgs-lookup (pgs-rec-ptab-addr cur) pages))
                            fresh)
                (not (member-equal rs (pgs-rec-keeps cur (pgs-lookup (pgs-rec-ptab-addr cur) pages))))))
  :hints (("Goal" :in-theory (union-theories '(pgs-step-hyps pgs-avoids-append-right
                                               pgs-avoids-cons pgs-avoids-nil)
                                             (theory 'minimal-theory))))
  :rule-classes :forward-chaining)

(in-theory (disable pgs-step-hyps))

(defthm pgs-step-cur-physes-avoid
  (implies (pgs-step-hyps cur pages mode dirty fresh rs txid)
           (pgs-avoids (pgs-ptab-physes (pgs-lookup (pgs-rec-ptab-addr cur) pages))
                       (append fresh (list rs))))
  :hints (("Goal" :in-theory (disable pgs-rec-keeps-avoids-physes pgs-try pgs-rec-valid
                                      pgs-avoids pgs-ptab-physes pgs-ptab-p
                                      pgs-avoids-append-right)
                  :use ((:instance pgs-try-ok-facts (rec cur))
                        (:instance pgs-rec-keeps-avoids-physes
                                   (rec cur)
                                   (ptab (pgs-lookup (pgs-rec-ptab-addr cur) pages))
                                   (w (append fresh (list rs))))))))

(defthm pgs-ptab-p-true-listp
  (implies (pgs-ptab-p x) (true-listp x))
  :rule-classes (:forward-chaining :rewrite))

(defthm pgs-true-list-fix-when-true-listp
  (implies (true-listp x) (equal (true-list-fix x) x)))

(defthm pgs-step-cur-facts
  (implies (pgs-step-hyps cur pages mode dirty fresh rs txid)
           (let ((ptab (pgs-lookup (pgs-rec-ptab-addr cur) pages)))
             (and (pgs-ptab-p ptab)
                  (pgs-ptab-txids-ok ptab (pgs-rec-txid cur))
                  (pgs-entries-good ptab (pgs-rec-txid cur) mode pages)
                  (equal (pgs-try cur pages mode)
                         (list :ok (pgs-rec-txid cur) (pgs-contents ptab pages))))))
  :hints (("Goal" :in-theory (disable pgs-try)
                  :use ((:instance pgs-try-ok-facts (rec cur))))))

(defthm pgs-rec-txid-natp
  (natp (pgs-rec-txid x))
  :hints (("Goal" :in-theory (enable pgs-rec-txid)))
  :rule-classes :type-prescription)

(defthm pgs-step-lookup-table
  (implies (pgs-step-hyps cur pages mode dirty fresh rs txid)
           (equal (pgs-lookup rs (pgs-apply-pages (pgs-step-writes dirty fresh rs ptab2) nil pages))
                  ptab2))
  :hints (("Goal" :in-theory (disable pgs-step-writes pgs-lookup-of-apply-pages-all)
                  :use ((:instance pgs-lookup-of-apply-pages-all
                                   (a rs) (ws (pgs-step-writes dirty fresh rs ptab2)))))))

(defthm pgs-step-lands
  (implies (pgs-step-hyps cur pages mode dirty fresh rs txid)
           (pgs-lands dirty fresh
                      (pgs-apply-pages (pgs-step-writes dirty fresh rs ptab2) nil pages)))
  :hints (("Goal" :in-theory (disable pgs-lands-of-apply-pages)
                  :use ((:instance pgs-lands-of-apply-pages (tail (list (cons rs ptab2))))))))

(defthm pgs-step-txids-at-new
  (implies (pgs-step-hyps cur pages mode dirty fresh rs txid)
           (pgs-ptab-txids-ok (pgs-lookup (pgs-rec-ptab-addr cur) pages) txid))
  :hints (("Goal" :in-theory (disable pgs-txids-ok-monotone)
                  :use ((:instance pgs-txids-ok-monotone
                                   (ptab (pgs-lookup (pgs-rec-ptab-addr cur) pages))
                                   (t0 (pgs-rec-txid cur)) (t1 txid))))))

(defthm pgs-step-good-at-new
  (implies (pgs-step-hyps cur pages mode dirty fresh rs txid)
           (pgs-entries-good (pgs-lookup (pgs-rec-ptab-addr cur) pages) txid mode
                             (pgs-apply-pages (pgs-step-writes dirty fresh rs ptab2) keep pages)))
  :hints (("Goal" :in-theory (disable pgs-entries-good-at-later-txid pgs-step-writes)
                  :use ((:instance pgs-entries-good-at-later-txid
                                   (ptab (pgs-lookup (pgs-rec-ptab-addr cur) pages))
                                   (t0 (pgs-rec-txid cur)) (t1 txid)
                                   (pages (pgs-apply-pages (pgs-step-writes dirty fresh rs ptab2)
                                                           keep pages)))))))

(defthm pgs-step-try-new
  (let* ((ptab (pgs-lookup (pgs-rec-ptab-addr cur) pages))
         (ptab2 (pgs-step-ptab2 ptab dirty fresh txid))
         (rec (pgs-make-rec txid rs (len ptab2) (pgs-digest ptab2)))
         (p1 (pgs-apply-pages (pgs-step-writes dirty fresh rs ptab2) nil pages)))
    (implies (pgs-step-hyps cur pages mode dirty fresh rs txid)
             (equal (pgs-try rec p1 mode)
                    (list :ok txid (pgs-apply-dirty (pgs-contents ptab pages) dirty)))))
  :hints (("Goal" :in-theory (disable pgs-try pgs-step-writes pgs-make-rec pgs-apply-pages)
                  :use ((:instance pgs-try-when-facts
                                   (rec (pgs-make-rec txid rs
                                                      (len (pgs-step-ptab2 (pgs-lookup (pgs-rec-ptab-addr cur) pages)
                                                                           dirty fresh txid))
                                                      (pgs-digest (pgs-step-ptab2 (pgs-lookup (pgs-rec-ptab-addr cur) pages)
                                                                                  dirty fresh txid))))
                                   (pages (pgs-apply-pages
                                           (pgs-step-writes dirty fresh rs
                                                            (pgs-step-ptab2 (pgs-lookup (pgs-rec-ptab-addr cur) pages)
                                                                            dirty fresh txid))
                                           nil pages)))))))

; -----------------------------------------------------------------------------
; A crash image read through the new record: what it verifies is what the
; complete commit holds.

(defun pgs-writes-faithful (writes pages)
  ; A-CRYPTO, instantiated: an address a write targets holds, before the
  ; write, either the written content or content with another digest.
  (if (atom writes)
      t
    (and (or (atom (car writes))
             (not (equal (pgs-digest (pgs-lookup (caar writes) pages))
                         (pgs-digest (cdar writes))))
             (equal (pgs-lookup (caar writes) pages) (cdar writes)))
         (pgs-writes-faithful (cdr writes) pages))))

(defthm pgs-writes-faithful-append
  (equal (pgs-writes-faithful (append a b) pages)
         (and (pgs-writes-faithful a pages) (pgs-writes-faithful b pages))))

(defun pgs-crash-local (xs p1 p2 p0)
  (if (atom xs)
      t
    (and (or (equal (pgs-lookup (car xs) p2) (pgs-lookup (car xs) p1))
             (equal (pgs-lookup (car xs) p2) (pgs-lookup (car xs) p0)))
         (pgs-crash-local (cdr xs) p1 p2 p0))))

(defthm pgs-crash-local-of-apply
  (implies (no-duplicatesp-equal (pgs-write-addrs writes))
           (pgs-crash-local xs (pgs-apply-pages writes nil pages)
                            (pgs-apply-pages writes keep pages) pages))
  :hints (("Goal" :induct (len xs))
          ("Subgoal *1/1" :use ((:instance pgs-lookup-of-apply-pages-crash (a (car xs)))))))

(defun pgs-new-sound (dirty fresh txid mode p1 p2)
  (if (atom dirty)
      t
    (and (pgs-entry-sound (list (nfix (car fresh)) (nfix txid) (nfix (pgs-digest (cdar dirty))))
                          txid mode p1 p2)
         (pgs-new-sound (cdr dirty) (cdr fresh) txid mode p1 p2))))

(defthm pgs-new-sound-from-faithful
  (implies (and (pgs-lands dirty fresh p1)
                (pgs-crash-local fresh p1 p2 p0)
                (pgs-writes-faithful (pgs-page-writes dirty fresh) p0)
                (nat-listp fresh) (natp txid)
                (<= (len dirty) (len fresh)))
           (pgs-new-sound dirty fresh txid mode p1 p2))
  :hints (("Goal" :induct (pgs-page-writes dirty fresh))))

(defthm pgs-entries-sound-of-plan-ptab
  (implies (and (pgs-entries-sound ptab txid mode p1 p2)
                (pgs-new-sound dirty fresh txid mode p1 p2))
           (pgs-entries-sound (pgs-plan-ptab ptab (pgs-dirty-lpages dirty) fresh
                                             (pgs-dirty-digests dirty) txid)
                              txid mode p1 p2))
  :hints (("Goal" :induct (pgs-plan-ind ptab dirty fresh nil txid)
                  :in-theory (disable pgs-entry-sound))))

(defthm pgs-step-contents-new
  (implies (pgs-step-hyps cur pages mode dirty fresh rs txid)
           (equal (pgs-contents (pgs-step-ptab2 (pgs-lookup (pgs-rec-ptab-addr cur) pages)
                                                dirty fresh txid)
                                (pgs-apply-pages (pgs-step-writes dirty fresh rs ptab2) nil pages))
                  (pgs-apply-dirty (pgs-contents (pgs-lookup (pgs-rec-ptab-addr cur) pages) pages)
                                   dirty)))
  :hints (("Goal" :in-theory (disable pgs-step-writes pgs-apply-pages))))

(defthm pgs-step-faithful-table
  (implies (and (pgs-writes-faithful (pgs-step-writes dirty fresh rs ptab2) pages)
                (equal (pgs-digest (pgs-lookup rs pages)) (pgs-digest ptab2)))
           (equal (pgs-lookup rs pages) ptab2)))

(defthm pgs-step-table-in-crash
  ; The table the new record names, read from a crash image, is either the
  ; planned table or has another digest.
  (implies (and (pgs-step-hyps cur pages mode dirty fresh rs txid)
                (pgs-writes-faithful (pgs-step-writes dirty fresh rs ptab2) pages)
                (equal (pgs-digest (pgs-lookup rs (pgs-apply-pages (pgs-step-writes dirty fresh rs ptab2)
                                                                   keep pages)))
                       (pgs-digest ptab2)))
           (equal (pgs-lookup rs (pgs-apply-pages (pgs-step-writes dirty fresh rs ptab2) keep pages))
                  ptab2))
  :hints (("Goal" :in-theory (disable pgs-step-writes pgs-apply-pages)
                  :use ((:instance pgs-lookup-of-apply-pages-crash
                                   (a rs) (writes (pgs-step-writes dirty fresh rs ptab2)))))))

(defthm pgs-step-sound-new-table
  (implies (and (pgs-step-hyps cur pages mode dirty fresh rs txid)
                (pgs-writes-faithful (pgs-step-writes dirty fresh rs ptab2) pages))
           (pgs-entries-sound (pgs-step-ptab2 (pgs-lookup (pgs-rec-ptab-addr cur) pages)
                                              dirty fresh txid)
                              txid mode
                              (pgs-apply-pages (pgs-step-writes dirty fresh rs ptab2) nil pages)
                              (pgs-apply-pages (pgs-step-writes dirty fresh rs ptab2) keep pages)))
  :hints (("Goal" :in-theory (e/d (pgs-step-writes)
                                  (pgs-apply-pages pgs-entries-sound-of-unwritten
                                   pgs-new-sound-from-faithful pgs-crash-local-of-apply))
                  :use ((:instance pgs-entries-sound-of-unwritten
                                   (ptab (pgs-lookup (pgs-rec-ptab-addr cur) pages))
                                   (writes (pgs-step-writes dirty fresh rs ptab2)))
                        (:instance pgs-crash-local-of-apply
                                   (xs fresh) (writes (pgs-step-writes dirty fresh rs ptab2)))
                        (:instance pgs-new-sound-from-faithful
                                   (p1 (pgs-apply-pages (pgs-step-writes dirty fresh rs ptab2) nil pages))
                                   (p2 (pgs-apply-pages (pgs-step-writes dirty fresh rs ptab2) keep pages))
                                   (p0 pages))))))

(defthm pgs-step-try-crash
  (let* ((ptab (pgs-lookup (pgs-rec-ptab-addr cur) pages))
         (ptab2 (pgs-step-ptab2 ptab dirty fresh txid))
         (rec (pgs-make-rec txid rs (len ptab2) (pgs-digest ptab2)))
         (writes (pgs-step-writes dirty fresh rs ptab2))
         (p2 (pgs-apply-pages writes keep pages)))
    (implies (and (pgs-step-hyps cur pages mode dirty fresh rs txid)
                  (pgs-writes-faithful writes pages)
                  (equal (car (pgs-try rec p2 mode)) :ok))
             (equal (pgs-try rec p2 mode)
                    (list :ok txid (pgs-apply-dirty (pgs-contents ptab pages) dirty)))))
  :hints (("Goal" :in-theory (disable pgs-try pgs-step-writes pgs-make-rec pgs-apply-pages
                                      pgs-step-ptab2 pgs-contents-when-sound-and-good)
                  :use ((:instance pgs-try-ok-facts
                                   (rec (pgs-make-rec txid rs
                                                      (len (pgs-step-ptab2 (pgs-lookup (pgs-rec-ptab-addr cur) pages)
                                                                           dirty fresh txid))
                                                      (pgs-digest (pgs-step-ptab2 (pgs-lookup (pgs-rec-ptab-addr cur) pages)
                                                                                  dirty fresh txid))))
                                   (pages (pgs-apply-pages
                                           (pgs-step-writes dirty fresh rs
                                                            (pgs-step-ptab2 (pgs-lookup (pgs-rec-ptab-addr cur) pages)
                                                                            dirty fresh txid))
                                           keep pages)))
                        (:instance pgs-contents-when-sound-and-good
                                   (ptab (pgs-step-ptab2 (pgs-lookup (pgs-rec-ptab-addr cur) pages)
                                                         dirty fresh txid))
                                   (p1 (pgs-apply-pages
                                        (pgs-step-writes dirty fresh rs
                                                         (pgs-step-ptab2 (pgs-lookup (pgs-rec-ptab-addr cur) pages)
                                                                         dirty fresh txid))
                                        nil pages))
                                   (p2 (pgs-apply-pages
                                        (pgs-step-writes dirty fresh rs
                                                         (pgs-step-ptab2 (pgs-lookup (pgs-rec-ptab-addr cur) pages)
                                                                         dirty fresh txid))
                                        keep pages)))))))

(defthm pgs-rec-valid-shape
  (implies (pgs-rec-valid x)
           (and (pgs-rec-shape-p x) (true-listp x) (consp x)))
  :rule-classes :forward-chaining)

(defthm pgs-step-try-cur-crash
  (implies (pgs-step-hyps cur pages mode dirty fresh rs txid)
           (equal (pgs-try cur (pgs-apply-pages (pgs-step-writes dirty fresh rs ptab2) keep pages) mode)
                  (list :ok (pgs-rec-txid cur)
                        (pgs-contents (pgs-lookup (pgs-rec-ptab-addr cur) pages) pages))))
  :hints (("Goal" :in-theory (disable pgs-try pgs-step-writes pgs-apply-pages)
                  :use ((:instance pgs-try-of-apply-pages
                                   (rec cur) (writes (pgs-step-writes dirty fresh rs ptab2)))))))

(defthm pgs-step-open-complete
  (let* ((ptab (pgs-lookup (pgs-rec-ptab-addr cur) pages))
         (ptab2 (pgs-step-ptab2 ptab dirty fresh txid))
         (rec (pgs-make-rec txid rs (len ptab2) (pgs-digest ptab2)))
         (p1 (pgs-apply-pages (pgs-step-writes dirty fresh rs ptab2) nil pages)))
    (implies (and (pgs-step-hyps cur pages mode dirty fresh rs txid)
                  (or (equal slots2 (cons cur rec)) (equal slots2 (cons rec cur))))
             (equal (pgs-view (pgs-open-slots slots2 p1 mode))
                    (list txid (pgs-apply-dirty (pgs-contents ptab pages) dirty)))))
  :hints (("Goal" :in-theory (disable pgs-try pgs-step-writes pgs-make-rec pgs-apply-pages
                                      pgs-step-ptab2 pgs-rec-valid))))

(defthm pgs-step-open-crash
  (let* ((ptab (pgs-lookup (pgs-rec-ptab-addr cur) pages))
         (ptab2 (pgs-step-ptab2 ptab dirty fresh txid))
         (rec (pgs-make-rec txid rs (len ptab2) (pgs-digest ptab2)))
         (writes (pgs-step-writes dirty fresh rs ptab2))
         (p2 (pgs-apply-pages writes keep pages)))
    (implies (and (pgs-step-hyps cur pages mode dirty fresh rs txid)
                  (pgs-writes-faithful writes pages)
                  (or (equal sv rec) (not (pgs-rec-valid sv)))
                  (or (equal slots2 (cons cur sv)) (equal slots2 (cons sv cur))))
             (member-equal (pgs-view (pgs-open-slots slots2 p2 mode))
                           (list (list txid (pgs-apply-dirty (pgs-contents ptab pages) dirty))
                                 (list (pgs-rec-txid cur) (pgs-contents ptab pages))))))
  :hints (("Goal" :in-theory (disable pgs-try pgs-step-writes pgs-make-rec pgs-apply-pages
                                      pgs-step-ptab2 pgs-rec-valid pgs-rec-shape-p)
                  :cases ((equal (car (pgs-try sv (pgs-apply-pages
                                                   (pgs-step-writes dirty fresh rs
                                                                    (pgs-step-ptab2 (pgs-lookup (pgs-rec-ptab-addr cur) pages)
                                                                                    dirty fresh txid))
                                                   keep pages)
                                               mode))
                                 :ok)))))

; -----------------------------------------------------------------------------
; The commit on a disk, named in parts.

(defun pgs-c-k0 (disk r mode) (second (pgs-open disk r mode)))
(defun pgs-c-cur (disk r mode) (pgs-slot (pgs-c-k0 disk r mode) (pgs-root-slots r disk)))
(defun pgs-c-ptab (disk r mode)
  (pgs-lookup (pgs-rec-ptab-addr (pgs-c-cur disk r mode)) (pgs-pages disk)))
(defun pgs-c-keeps (disk) (pgs-roots-keeps (pgs-roots disk) (pgs-pages disk)))
(defun pgs-c-alloc (disk r mode dirty)
  (pgs-alloc (len dirty) (pgs-ptab-run-pages (len (pgs-c-ptab disk r mode)))
             (pgs-hwm (pgs-c-keeps disk)) (pgs-mark (pgs-c-keeps disk) nil)))
(defun pgs-c-txid (disk r) (pgs-next-txid (pgs-root-slots r disk)))
(defun pgs-c-ptab2 (disk r mode dirty)
  (pgs-step-ptab2 (pgs-c-ptab disk r mode) dirty (cdr (pgs-c-alloc disk r mode dirty))
                  (pgs-c-txid disk r)))
(defun pgs-c-rec (disk r mode dirty)
  (pgs-make-rec (pgs-c-txid disk r) (car (pgs-c-alloc disk r mode dirty))
                (len (pgs-c-ptab2 disk r mode dirty))
                (pgs-digest (pgs-c-ptab2 disk r mode dirty))))
(defun pgs-c-writes (disk r mode dirty)
  (pgs-step-writes dirty (cdr (pgs-c-alloc disk r mode dirty))
                   (car (pgs-c-alloc disk r mode dirty))
                   (pgs-c-ptab2 disk r mode dirty)))

(defthm pgs-len-of-step-ptab2
  (equal (len (pgs-step-ptab2 ptab dirty fresh txid)) (len ptab)))

(defthm pgs-plan-commit-unfold
  (implies (and (equal (car (pgs-open disk r mode)) :ok)
                (true-listp (pgs-open disk r mode))
                (consp (pgs-c-alloc disk r mode dirty)))
           (equal (pgs-plan-commit disk r mode dirty)
                  (list :plan (pgs-c-writes disk r mode dirty)
                        (if (equal (pgs-c-k0 disk r mode) 1) 0 1)
                        (pgs-c-rec disk r mode dirty))))
  :hints (("Goal" :in-theory (disable pgs-open pgs-alloc pgs-plan-ptab pgs-make-rec
                                      pgs-page-writes pgs-roots-keeps pgs-mark pgs-hwm
                                      pgs-next-txid pgs-slot pgs-root-slots))))

(defthm pgs-plan-commit-refuses-without-alloc
  (implies (not (consp (pgs-c-alloc disk r mode dirty)))
           (not (equal (car (pgs-plan-commit disk r mode dirty)) :plan)))
  :hints (("Goal" :in-theory (disable pgs-open pgs-alloc pgs-plan-ptab pgs-make-rec
                                      pgs-page-writes pgs-roots-keeps pgs-mark pgs-hwm
                                      pgs-next-txid pgs-slot pgs-root-slots))))

(defthm pgs-plan-commit-refuses-without-open
  (implies (not (equal (car (pgs-open disk r mode)) :ok))
           (not (equal (car (pgs-plan-commit disk r mode dirty)) :plan)))
  :hints (("Goal" :in-theory (disable pgs-open))))

(defthm pgs-next-txid-above
  (implies (and (member-equal k '(0 1)) (pgs-rec-valid (pgs-slot k slots)))
           (< (pgs-rec-txid (pgs-slot k slots)) (pgs-next-txid slots)))
  :hints (("Goal" :in-theory (disable pgs-rec-valid pgs-slot)
                  :cases ((equal k 0))))
  :rule-classes :linear)

(defthm pgs-next-txid-natp
  (natp (pgs-next-txid slots))
  :rule-classes :type-prescription)

(defthm pgs-nat-listp-of-find-singles
  (implies (natp a) (nat-listp (pgs-find-singles n a bound used))))

(defthm pgs-nat-listp-of-alloc
  (implies (consp (pgs-alloc n m hwm used))
           (nat-listp (cdr (pgs-alloc n m hwm used))))
  :hints (("Goal" :in-theory (enable pgs-alloc))))

(defthm pgs-alloc-start-not-single
  (implies (and (consp (pgs-alloc n m hwm used)) (not (zp m)))
           (not (member-equal (car (pgs-alloc n m hwm used)) (cdr (pgs-alloc n m hwm used)))))
  :hints (("Goal" :in-theory (disable pgs-alloc-singles-fresh)
                  :use ((:instance pgs-alloc-singles-fresh (x (car (pgs-alloc n m hwm used))))))))

(defthm pgs-alloc-avoids-kept
  (implies (and (consp (pgs-alloc n m hwm (pgs-mark keeps nil))) (not (zp m)))
           (pgs-avoids keeps (append (cdr (pgs-alloc n m hwm (pgs-mark keeps nil)))
                                     (list (car (pgs-alloc n m hwm (pgs-mark keeps nil)))))))
  :hints (("Goal" :in-theory (disable pgs-alloc-run-fresh pgs-all-fresh-of-alloc pgs-alloc)
                  :use ((:instance pgs-alloc-run-fresh (used (pgs-mark keeps nil))
                                   (x (car (pgs-alloc n m hwm (pgs-mark keeps nil)))))
                        (:instance pgs-all-fresh-of-alloc (used (pgs-mark keeps nil)))
                        (:instance pgs-avoids-symmetric
                                   (xs keeps) (ys (cdr (pgs-alloc n m hwm (pgs-mark keeps nil)))))))))

(defthm pgs-rec-valid-of-nil
  (not (pgs-rec-valid nil)))

(in-theory (disable (:e pgs-rec-valid)))

(defthm pgs-open-is-open-slots
  (equal (pgs-open disk r mode)
         (pgs-open-slots (pgs-root-slots r disk) (pgs-pages disk) mode))
  :rule-classes nil)

(defthm pgs-c-open-facts
  (implies (equal (car (pgs-open disk r mode)) :ok)
           (and (member-equal (pgs-c-k0 disk r mode) '(0 1))
                (pgs-rec-valid (pgs-c-cur disk r mode))
                (equal (pgs-try (pgs-c-cur disk r mode) (pgs-pages disk) mode)
                       (list :ok (third (pgs-open disk r mode)) (fourth (pgs-open disk r mode))))
                (true-listp (pgs-open disk r mode))))
  :hints (("Goal" :in-theory (disable pgs-open pgs-open-slots pgs-try pgs-rec-valid pgs-slot)
                  :use ((:instance pgs-open-is-open-slots)
                        (:instance pgs-open-slots-ok (slots (pgs-root-slots r disk))
                                   (pages (pgs-pages disk)))))))

(defthm pgs-c-step-hyps
  (implies (and (equal (car (pgs-open disk r mode)) :ok)
                (consp (pgs-c-alloc disk r mode dirty)))
           (pgs-step-hyps (pgs-c-cur disk r mode) (pgs-pages disk) mode dirty
                          (cdr (pgs-c-alloc disk r mode dirty))
                          (car (pgs-c-alloc disk r mode dirty))
                          (pgs-c-txid disk r)))
  :hints (("Goal" :in-theory (e/d (pgs-step-hyps)
                                  (pgs-open pgs-try pgs-rec-valid pgs-slot pgs-alloc
                                   pgs-roots-keeps pgs-slots-keeps pgs-rec-keeps pgs-mark
                                   pgs-next-txid pgs-c-open-facts
                                   pgs-roots-keeps-cover pgs-slot-keeps-avoid
                                   pgs-alloc-avoids-kept pgs-next-txid-above))
                  :use ((:instance pgs-c-open-facts)
                        (:instance pgs-next-txid-above (k (pgs-c-k0 disk r mode))
                                   (slots (pgs-root-slots r disk)))
                        (:instance pgs-alloc-avoids-kept
                                   (n (len dirty))
                                   (m (pgs-ptab-run-pages (len (pgs-c-ptab disk r mode))))
                                   (hwm (pgs-hwm (pgs-c-keeps disk)))
                                   (keeps (pgs-c-keeps disk)))
                        (:instance pgs-roots-keeps-cover
                                   (roots (pgs-roots disk)) (pages (pgs-pages disk))
                                   (w (append (cdr (pgs-c-alloc disk r mode dirty))
                                              (list (car (pgs-c-alloc disk r mode dirty))))))
                        (:instance pgs-slot-keeps-avoid
                                   (k (pgs-c-k0 disk r mode))
                                   (slots (pgs-root-slots r disk)) (pages (pgs-pages disk))
                                   (w (append (cdr (pgs-c-alloc disk r mode dirty))
                                              (list (car (pgs-c-alloc disk r mode dirty))))))))))

; -----------------------------------------------------------------------------
; The keystones.

(defthm pgs-open-of-crash
  (equal (pgs-open (pgs-crash disk r writes keep k sv) r2 mode)
         (if (equal r2 r)
             (pgs-open-slots (pgs-set-slot k sv (pgs-root-slots r disk))
                             (pgs-apply-pages writes keep (pgs-pages disk)) mode)
           (pgs-open-slots (pgs-root-slots r2 disk)
                           (pgs-apply-pages writes keep (pgs-pages disk)) mode)))
  :hints (("Goal" :in-theory (disable pgs-open-slots pgs-apply-pages pgs-set-slot))))

(defthm pgs-set-other-slot
  (implies (member-equal k0 '(0 1))
           (or (equal (pgs-set-slot (if (equal k0 1) 0 1) v slots)
                      (cons (pgs-slot k0 slots) v))
               (equal (pgs-set-slot (if (equal k0 1) 0 1) v slots)
                      (cons v (pgs-slot k0 slots)))))
  :rule-classes nil)

(defthm pgs-c-fourth-is-contents
  (implies (and (equal (car (pgs-open disk r mode)) :ok)
                (consp (pgs-c-alloc disk r mode dirty)))
           (and (equal (fourth (pgs-open disk r mode))
                       (pgs-contents (pgs-c-ptab disk r mode) (pgs-pages disk)))
                (equal (third (pgs-open disk r mode))
                       (pgs-rec-txid (pgs-c-cur disk r mode)))))
  :hints (("Goal" :in-theory (union-theories '(pgs-c-ptab pgs-c-cur car-cons cdr-cons)
                                             (theory 'minimal-theory))
                  :use ((:instance pgs-c-open-facts)
                        (:instance pgs-c-step-hyps)
                        (:instance pgs-step-cur-facts
                                   (cur (pgs-c-cur disk r mode)) (pages (pgs-pages disk))
                                   (fresh (cdr (pgs-c-alloc disk r mode dirty)))
                                   (rs (car (pgs-c-alloc disk r mode dirty)))
                                   (txid (pgs-c-txid disk r)))))))

; Commit-then-open denotes the committed state.
(defthm pgs-open-after-commit
  (implies (equal (car (pgs-plan-commit disk r mode dirty)) :plan)
           (equal (pgs-view (pgs-open (pgs-commit disk r mode dirty) r mode))
                  (list (pgs-next-txid (pgs-root-slots r disk))
                        (pgs-apply-dirty (fourth (pgs-open disk r mode)) dirty))))
  :hints (("Goal" :in-theory (union-theories '(pgs-commit pgs-c-writes pgs-c-rec pgs-c-ptab2
                                               pgs-c-ptab pgs-c-cur pgs-c-txid
                                               pgs-plan-commit-unfold pgs-open-of-crash
                                               pgs-c-fourth-is-contents car-cons cdr-cons)
                                             (theory 'minimal-theory))
                  :use ((:instance pgs-plan-commit-refuses-without-alloc)
                        (:instance pgs-plan-commit-refuses-without-open)
                        (:instance pgs-c-open-facts)
                        (:instance pgs-c-step-hyps)
                        (:instance pgs-set-other-slot (k0 (pgs-c-k0 disk r mode))
                                   (v (pgs-c-rec disk r mode dirty))
                                   (slots (pgs-root-slots r disk)))
                        (:instance pgs-step-open-complete
                                   (cur (pgs-c-cur disk r mode)) (pages (pgs-pages disk))
                                   (fresh (cdr (pgs-c-alloc disk r mode dirty)))
                                   (rs (car (pgs-c-alloc disk r mode dirty)))
                                   (txid (pgs-c-txid disk r))
                                   (slots2 (pgs-set-slot (if (equal (pgs-c-k0 disk r mode) 1) 0 1)
                                                         (pgs-c-rec disk r mode dirty)
                                                         (pgs-root-slots r disk))))))))

(defthm pgs-step-open-torn
  (let* ((ptab (pgs-lookup (pgs-rec-ptab-addr cur) pages))
         (ptab2 (pgs-step-ptab2 ptab dirty fresh txid))
         (writes (pgs-step-writes dirty fresh rs ptab2))
         (p2 (pgs-apply-pages writes keep pages)))
    (implies (and (pgs-step-hyps cur pages mode dirty fresh rs txid)
                  (not (pgs-rec-valid sv))
                  (or (equal slots2 (cons cur sv)) (equal slots2 (cons sv cur))))
             (equal (pgs-view (pgs-open-slots slots2 p2 mode))
                    (list (pgs-rec-txid cur) (pgs-contents ptab pages)))))
  :hints (("Goal" :in-theory (disable pgs-try pgs-step-writes pgs-make-rec pgs-apply-pages
                                      pgs-step-ptab2 pgs-rec-valid pgs-rec-shape-p))))

(defthm pgs-slot-of-set-same
  (implies (member-equal k '(0 1))
           (equal (pgs-slot j (pgs-set-slot k (pgs-slot k slots) slots))
                  (pgs-slot j slots))))

(defthm pgs-try-in-order-of-set-same
  (implies (member-equal k '(0 1))
           (equal (pgs-try-in-order order (pgs-set-slot k (pgs-slot k slots) slots) pages mode refs)
                  (pgs-try-in-order order slots pages mode refs)))
  :hints (("Goal" :induct (pgs-try-in-order order slots pages mode refs)
                  :in-theory (disable pgs-try pgs-set-slot pgs-slot pgs-rec-shape-p))))

(defthm pgs-open-slots-of-set-same
  (implies (member-equal k '(0 1))
           (equal (pgs-open-slots (pgs-set-slot k (pgs-slot k slots) slots) pages mode)
                  (pgs-open-slots slots pages mode)))
  :hints (("Goal" :in-theory (disable pgs-try-in-order pgs-rec-valid pgs-open-order
                                      pgs-set-slot pgs-slot pgs-slot-refusals))))

(defthm pgs-c-avoids
  ; The commit's writes avoid every root's kept addresses.
  (implies (and (equal (car (pgs-open disk r mode)) :ok)
                (consp (pgs-c-alloc disk r mode dirty)))
           (pgs-avoids (pgs-slots-keeps (pgs-root-slots r2 disk) (pgs-pages disk))
                       (pgs-write-addrs (pgs-c-writes disk r mode dirty))))
  :hints (("Goal" :in-theory (e/d (pgs-c-writes)
                                  (pgs-open pgs-alloc pgs-roots-keeps pgs-slots-keeps pgs-mark
                                   pgs-roots-keeps-cover pgs-alloc-avoids-kept
                                   pgs-step-writes pgs-c-step-hyps))
                  :use ((:instance pgs-c-step-hyps)
                        (:instance pgs-alloc-avoids-kept
                                   (n (len dirty))
                                   (m (pgs-ptab-run-pages (len (pgs-c-ptab disk r mode))))
                                   (hwm (pgs-hwm (pgs-c-keeps disk)))
                                   (keeps (pgs-c-keeps disk)))
                        (:instance pgs-roots-keeps-cover
                                   (r r2) (roots (pgs-roots disk)) (pages (pgs-pages disk))
                                   (w (append (cdr (pgs-c-alloc disk r mode dirty))
                                              (list (car (pgs-c-alloc disk r mode dirty))))))))))

; A crash anywhere in the commit opens on the committed state or on the
; previous one; on the previous one unless the new record landed whole.
(defthm pgs-view-of-ok
  (implies (and (equal (car o) :ok) (true-listp o))
           (equal (pgs-view o) (list (third o) (fourth o)))))

(defthm pgs-open-after-crash
  (let* ((o (pgs-open disk r mode))
         (p (pgs-plan-commit disk r mode dirty))
         (image (pgs-crash disk r (second p) keep (third p) sv)))
    (implies (and (equal (car p) :plan)
                  (pgs-writes-faithful (second p) (pgs-pages disk))
                  (or (equal sv (pgs-slot (third p) (pgs-root-slots r disk)))
                      (equal sv (fourth p))
                      (not (pgs-rec-valid sv))))
             (and (member-equal (pgs-view (pgs-open image r mode))
                                (list (pgs-view (pgs-open (pgs-commit disk r mode dirty) r mode))
                                      (pgs-view o)))
                  (implies (not (equal sv (fourth p)))
                           (equal (pgs-view (pgs-open image r mode)) (pgs-view o))))))
  :hints (("Goal" :in-theory (union-theories '(pgs-c-writes pgs-c-ptab2 pgs-c-ptab pgs-c-rec
                                               pgs-c-cur pgs-c-txid pgs-plan-commit-unfold
                                               pgs-open-of-crash pgs-c-fourth-is-contents
                                               pgs-view-of-ok member-equal car-cons cdr-cons)
                                             (theory 'minimal-theory))
                  :use ((:instance pgs-plan-commit-refuses-without-alloc)
                        (:instance pgs-plan-commit-refuses-without-open)
                        (:instance pgs-view-of-ok (o (pgs-open disk r mode)))
                        (:instance pgs-c-open-facts)
                        (:instance pgs-c-step-hyps)
                        (:instance pgs-open-is-open-slots)
                        (:instance pgs-open-after-commit)
                        (:instance pgs-c-avoids (r2 r))
                        (:instance pgs-open-slots-of-apply-pages
                                   (slots (pgs-root-slots r disk)) (pages (pgs-pages disk))
                                   (writes (pgs-c-writes disk r mode dirty)))
                        (:instance pgs-open-slots-of-set-same
                                   (k (if (equal (pgs-c-k0 disk r mode) 1) 0 1))
                                   (slots (pgs-root-slots r disk))
                                   (pages (pgs-apply-pages (pgs-c-writes disk r mode dirty)
                                                           keep (pgs-pages disk))))
                        (:instance pgs-set-other-slot (k0 (pgs-c-k0 disk r mode)) (v sv)
                                   (slots (pgs-root-slots r disk)))
                        (:instance pgs-step-open-crash
                                   (cur (pgs-c-cur disk r mode)) (pages (pgs-pages disk))
                                   (fresh (cdr (pgs-c-alloc disk r mode dirty)))
                                   (rs (car (pgs-c-alloc disk r mode dirty)))
                                   (txid (pgs-c-txid disk r))
                                   (slots2 (pgs-set-slot (if (equal (pgs-c-k0 disk r mode) 1) 0 1)
                                                         sv (pgs-root-slots r disk))))
                        (:instance pgs-step-open-torn
                                   (cur (pgs-c-cur disk r mode)) (pages (pgs-pages disk))
                                   (fresh (cdr (pgs-c-alloc disk r mode dirty)))
                                   (rs (car (pgs-c-alloc disk r mode dirty)))
                                   (txid (pgs-c-txid disk r))
                                   (slots2 (pgs-set-slot (if (equal (pgs-c-k0 disk r mode) 1) 0 1)
                                                         sv (pgs-root-slots r disk))))))))

; Fork isolation: a commit on R, complete or crashed anywhere, leaves every
; other root's open exactly as it was (refusals included).
(defthm pgs-refused-plan-writes-nothing
  (implies (not (equal (car (pgs-plan-commit disk r mode dirty)) :plan))
           (equal (pgs-write-addrs (second (pgs-plan-commit disk r mode dirty))) nil))
  :hints (("Goal" :in-theory (disable pgs-open pgs-alloc pgs-plan-ptab pgs-make-rec
                                      pgs-page-writes pgs-roots-keeps pgs-mark pgs-hwm
                                      pgs-next-txid pgs-slot pgs-root-slots))))

(defthm pgs-crash-isolates-other-roots
  (let ((p (pgs-plan-commit disk r mode dirty)))
    (implies (not (equal r2 r))
             (equal (pgs-open (pgs-crash disk r (second p) keep (third p) sv) r2 mode2)
                    (pgs-open disk r2 mode2))))
  :hints (("Goal" :in-theory (union-theories '(pgs-plan-commit-unfold pgs-open-of-crash
                                               pgs-avoids-nil
                                               car-cons cdr-cons)
                                             (theory 'minimal-theory))
                  :cases ((equal (car (pgs-plan-commit disk r mode dirty)) :plan)))
          ("Subgoal 2" :use ((:instance pgs-refused-plan-writes-nothing)
                             (:instance pgs-open-is-open-slots (r r2) (mode mode2))
                             (:instance pgs-open-slots-of-apply-pages
                                        (slots (pgs-root-slots r2 disk)) (pages (pgs-pages disk))
                                        (mode mode2)
                                        (writes (second (pgs-plan-commit disk r mode dirty))))))
          ("Subgoal 1"
                  :in-theory (union-theories '(pgs-plan-commit-unfold pgs-open-of-crash
                                               car-cons cdr-cons)
                                             (theory 'minimal-theory))
                  :use ((:instance pgs-plan-commit-refuses-without-alloc)
                        (:instance pgs-plan-commit-refuses-without-open)
                        (:instance pgs-c-open-facts)
                        (:instance pgs-c-avoids)
                        (:instance pgs-open-is-open-slots (r r2) (mode mode2))
                        (:instance pgs-open-slots-of-apply-pages
                                   (slots (pgs-root-slots r2 disk)) (pages (pgs-pages disk))
                                   (mode mode2)
                                   (writes (pgs-c-writes disk r mode dirty)))))))

(defthm pgs-fork-parts
  (implies (and (equal (car (pgs-open disk r mode)) :ok)
                (true-listp (pgs-open disk r mode))
                (not (equal r2 r)))
           (and (equal (pgs-pages (pgs-fork disk r r2 mode)) (pgs-pages disk))
                (equal (pgs-root-slots r2 (pgs-fork disk r r2 mode))
                       (cons (pgs-c-cur disk r mode) nil))
                (equal (pgs-root-slots r (pgs-fork disk r r2 mode))
                       (pgs-root-slots r disk))))
  :hints (("Goal" :in-theory (disable pgs-open pgs-slot))))

(defthm pgs-open-slots-single
  (implies (and (pgs-rec-valid cur) (equal (car (pgs-try cur pages mode)) :ok))
           (equal (pgs-open-slots (cons cur nil) pages mode)
                  (list :ok 0 (cadr (pgs-try cur pages mode)) (caddr (pgs-try cur pages mode)) nil)))
  :hints (("Goal" :in-theory (disable pgs-try pgs-rec-valid pgs-rec-shape-p))))

; A fork opens on its source's state, and leaves the source as it was.
(defthm pgs-fork-denotes
  (implies (and (equal (car (pgs-open disk r mode)) :ok)
                (not (equal r2 r)))
           (and (equal (pgs-view (pgs-open (pgs-fork disk r r2 mode) r2 mode))
                       (pgs-view (pgs-open disk r mode)))
                (equal (pgs-open (pgs-fork disk r r2 mode) r mode2)
                       (pgs-open disk r mode2))))
  :hints (("Goal" :in-theory (union-theories '(pgs-fork-parts pgs-view
                                               true-listp car-cons cdr-cons)
                                             (theory 'minimal-theory))
                  :use ((:instance pgs-c-open-facts)
                        (:instance pgs-view-of-ok (o (pgs-open disk r mode)))
                        (:instance pgs-open-slots-single (cur (pgs-c-cur disk r mode))
                                   (pages (pgs-pages disk)))
                        (:instance pgs-open-is-open-slots (r r2)
                                   (disk (pgs-fork disk r r2 mode)))
                        (:instance pgs-open-is-open-slots (mode mode2))
                        (:instance pgs-open-is-open-slots (mode mode2)
                                   (disk (pgs-fork disk r r2 mode)))))))
