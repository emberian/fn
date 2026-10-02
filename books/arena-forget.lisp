; fn: forgetting a reclaimed payload while the owner serves (lane
; arena-forget, 2026-10-03; row ARENA-FORGET; the served defect found by
; cold-read-ownership-2: online reclaim never gave back the disk of a file
; that held a reclaimed article, because the arena had no export that takes
; a payload away and the reclaimed record's old handle kept naming the file).
;
; The arena's forget (books/payload-arena.lisp fn-arena-forget) empties one
; handle.  This book decides WHEN the owner may call it, and proves that no
; holder of a handle reads it afterwards.  The decision is the arena readers'
; generation machine (books/arena-reader-pins.lisp, fn-arpn-step), which the
; host already drives for staged pages and dropped files; nothing new is
; scanned:
;
;   - a handle the served state stops naming (a reclaim swap: the rewritten
;     history names the tombstone's fresh handle instead) is RETIRED: the
;     host passes (fn-arf-retire-event HS) to the pins step, which stamps the
;     tagged handles with the current generation and advances it;
;   - every holder that can carry a handle across a release of the owner's
;     mutex (a checkpoint publication, a reclaim pass, a connection's
;     response in flight, a cold-read worker) PINNED the generation under the
;     mutex before it took the handle, from the state served then;
;   - the pins step's :release answers a retirement only when no live pin is
;     at or below its stamp (KEYSTONE fn-arpn-release-postdates-every-live-
;     pin), and the host hands what it answers to fn-arf-apply-released,
;     which forgets the tagged handles (and releases the staged pages the
;     same table carries as plain handles).
;
; Liveness is therefore CARRIED: one generation per holder, one stamp per
; retirement, one comparison with the oldest pin per release.  A forget costs
; one entry write; a release costs the pending retirements it walks.
;
; The liveness relation itself -- a released handle is named by no row and
; held by no reader, response plan or whole-arena lease -- is DEF-HOLDER's
; payload-handle instance (build/coordinator/lanedumps/def-holder.md section
; 4, instance 3: rows + generation + leases); this book owns what the
; release DOES and cites that theorem as its precondition.
; GEN: def-holder fn-handle-holds
;
; A LATE holder -- a read of a handle after its forget, by a holder that did
; not pin -- reads the EMPTY payload through no realizer and no descriptor
; (fn-arena-forget-payload; the concrete entry is :forgotten,
; books/payload-arena-extent.lisp): never a closed or reused file.

(in-package "ACL2")
(include-book "arena-reader-pins")
(include-book "payload-arena")
(include-book "held-record")

; -----------------------------------------------------------------------------
; 1. The retirement's items and what the release does with them.

; A forget item: (:forget H).  A plain natural is a staged page's handle
; (host/native/io.lisp fnn-log-reseat-fenced retires those in the same table).
(defun fn-arf-forget-item-p (item)
  (declare (xargs :guard t))
  (and (consp item)
       (eq (car item) :forget)
       (consp (cdr item))
       (natp (cadr item))
       (null (cddr item))))

; The handles HS tagged, in order.  Executes by a loop (the reclaimed
; handles of a pass are store data).
(defun fn-arf-tag-loop (hs rev)
  (declare (xargs :guard (true-listp rev)))
  (if (atom hs)
      (revappend rev nil)
    (fn-arf-tag-loop (cdr hs) (cons (list :forget (car hs)) rev))))

(defun fn-arf-tag (hs)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (if (atom hs)
                  nil
                (cons (list :forget (car hs)) (fn-arf-tag (cdr hs))))
       :exec (fn-arf-tag-loop hs nil)))

(defthm fn-arf-tag-loop-is-tag
  (equal (fn-arf-tag-loop hs rev)
         (revappend rev (fn-arf-tag hs))))

(verify-guards fn-arf-tag)

(defthm fn-arf-tag-true-listp
  (true-listp (fn-arf-tag hs))
  :rule-classes :type-prescription)

; The event the host passes to the pins step when the served state stops
; naming HS (host/native/owner.lisp fnn-owner-reclaim-pass, in the swap's
; quantum).
(defun fn-arf-retire-event (hs)
  (declare (xargs :guard t))
  (list :retire (fn-arf-tag hs)))

; The handles a list of items forgets (the specification's reading; nothing
; executes it).
(defun fn-arf-items-handles (items)
  (declare (xargs :guard t))
  (cond ((atom items) nil)
        ((fn-arf-forget-item-p (car items))
         (cons (cadr (car items)) (fn-arf-items-handles (cdr items))))
        (t (fn-arf-items-handles (cdr items)))))

(defthm fn-arf-items-handles-of-tag
  (implies (nat-listp hs)
           (equal (fn-arf-items-handles (fn-arf-tag hs)) hs)))

(defun fn-arf-pend-handles (pend)
  (declare (xargs :guard t))
  (if (atom pend)
      nil
    (append (fn-arf-items-handles (and (consp (car pend)) (cdr (car pend))))
            (fn-arf-pend-handles (cdr pend)))))

; What the host does with one released retirement's items, under the owner's
; mutex: a staged page is released, a tagged handle is forgotten.  One arena
; export per item.
(defun fn-arf-apply-items (items fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (atom items)
      fn-arena
    (let ((fn-arena (cond ((natp (car items))
                           (fn-arena-release (car items) fn-arena))
                          ((fn-arf-forget-item-p (car items))
                           (fn-arena-forget (cadr (car items)) fn-arena))
                          (t fn-arena))))
      (fn-arf-apply-items (cdr items) fn-arena))))

; The host's call (host/native/io.lisp fnn-arena-apply-due): REL the pins
; step's :release answer, ((S . ITEMS) ...).
(defun fn-arf-apply-released (rel fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (atom rel)
      fn-arena
    (let ((fn-arena (if (consp (car rel))
                        (fn-arf-apply-items (cdr (car rel)) fn-arena)
                      fn-arena)))
      (fn-arf-apply-released (cdr rel) fn-arena))))

(local (in-theory (disable fn-arena-payload-is-nth fn-arena-count-is-len
                           fn-arena-p-is-payload-listp)))

(local
 (defthm fn-arf-member-of-append
   (iff (member-equal k (append a b))
        (or (member-equal k a) (member-equal k b)))))

(local
 (defthm fn-arf-apply-items-keeps
   (implies (and (natp k) (not (member-equal k (fn-arf-items-handles items))))
            (equal (fn-arena-payload k (fn-arf-apply-items items fn-arena))
                   (fn-arena-payload k fn-arena)))
   :hints (("Goal" :induct (fn-arf-apply-items items fn-arena)))))

(local
 (defthm fn-arf-apply-items-empties
   (implies (and (natp k) (member-equal k (fn-arf-items-handles items)))
            (equal (fn-arena-payload k (fn-arf-apply-items items fn-arena))
                   nil))
   :hints (("Goal" :induct (fn-arf-apply-items items fn-arena)))))

(local
 (defthm fn-arf-apply-items-count
   (equal (fn-arena-count (fn-arf-apply-items items fn-arena))
          (fn-arena-count fn-arena))
   :hints (("Goal" :induct (fn-arf-apply-items items fn-arena)))))

(local
 (defthm fn-arf-apply-items-arena-p
   (implies (fn-arena-p fn-arena)
            (fn-arena-p (fn-arf-apply-items items fn-arena)))
   :hints (("Goal" :induct (fn-arf-apply-items items fn-arena)))))

(local (in-theory (disable fn-arf-apply-items fn-arf-forget-item-p)))

(local
 (defthm fn-arf-apply-released-keeps
   (implies (and (natp k) (not (member-equal k (fn-arf-pend-handles rel))))
            (equal (fn-arena-payload k (fn-arf-apply-released rel fn-arena))
                   (fn-arena-payload k fn-arena)))
   :hints (("Goal" :induct (fn-arf-apply-released rel fn-arena)))))

(local
 (defthm fn-arf-apply-released-empties
   (implies (and (natp k) (member-equal k (fn-arf-pend-handles rel)))
            (equal (fn-arena-payload k (fn-arf-apply-released rel fn-arena))
                   nil))
   :hints (("Goal" :induct (fn-arf-apply-released rel fn-arena)))))

(local
 (defthm fn-arf-apply-released-count
   (equal (fn-arena-count (fn-arf-apply-released rel fn-arena))
          (fn-arena-count fn-arena))
   :hints (("Goal" :induct (fn-arf-apply-released rel fn-arena)))))

(local
 (defthm fn-arf-apply-released-arena-p
   (implies (fn-arena-p fn-arena)
            (fn-arena-p (fn-arf-apply-released rel fn-arena)))
   :hints (("Goal" :induct (fn-arf-apply-released rel fn-arena)))))

; KEYSTONE (PRF-ARF-3).  The release empties exactly the tagged handles of
; what the pins step released: such a handle reads the empty payload, every
; other handle keeps its payload, the count is unchanged (no handle is
; reused) and an arena stays an arena.  Host subject: host/native/io.lisp
; fnn-arena-apply-due calls fn-arf-apply-released under the owner's mutex.
(defthm fn-arf-apply-released-payload
  (and (implies (and (natp k) (not (member-equal k (fn-arf-pend-handles rel))))
                (equal (fn-arena-payload k (fn-arf-apply-released rel fn-arena))
                       (fn-arena-payload k fn-arena)))
       (implies (and (natp k) (member-equal k (fn-arf-pend-handles rel)))
                (equal (fn-arena-payload k (fn-arf-apply-released rel fn-arena))
                       nil))
       (equal (fn-arena-count (fn-arf-apply-released rel fn-arena))
              (fn-arena-count fn-arena))
       (implies (fn-arena-p fn-arena)
                (fn-arena-p (fn-arf-apply-released rel fn-arena))))
  :hints (("Goal" :in-theory (disable fn-arf-apply-released))))

; -----------------------------------------------------------------------------
; 2. Which handles a rewrite of the history un-names.
;
; The reclaim pass holds the captured rows OLD and the rewritten, interned
; rows NEW, position for position (host/native/owner.lisp fnn-owner-reclaim-
; pass): a row the rewrite did not change is kept by pointer, a changed row
; is a record interned at a fresh handle (books/owner-reclaim-pass.lisp
; fn-orcp-intern-rows).  The handles to retire are the old handles of the
; changed positions: one walk of two lists the pass already holds, off the
; owner's mutex, a pointer comparison per unchanged row.


; The handle a row names: a held record's payload position, a retained
; statement's held record's; any other row names none.
(defun fn-arf-row-handle (row)
  (declare (xargs :guard t))
  (cond ((fn-held-p row)
         (and (natp (fn-record-payload row)) (fn-record-payload row)))
        ((fn-hstxa-p row)
         (and (natp (fn-record-payload (fn-hstxa-held row)))
              (fn-record-payload (fn-hstxa-held row))))
        (t nil)))

; The handles the rows name, in order (the specification's reading).
(defun fn-arf-rows-handles (rows)
  (declare (xargs :guard t))
  (cond ((atom rows) nil)
        ((fn-arf-row-handle (car rows))
         (cons (fn-arf-row-handle (car rows)) (fn-arf-rows-handles (cdr rows))))
        (t (fn-arf-rows-handles (cdr rows)))))

; The host's call: the old handles of the positions whose row changed.
; Executes by a loop (the history's rows are store data).
(defun fn-arf-changed-handles-loop (old new rev)
  (declare (xargs :guard (true-listp rev)))
  (cond ((or (atom old) (atom new)) (revappend rev nil))
        ((or (equal (car old) (car new))
             (not (fn-arf-row-handle (car old))))
         (fn-arf-changed-handles-loop (cdr old) (cdr new) rev))
        (t (fn-arf-changed-handles-loop (cdr old) (cdr new)
                                        (cons (fn-arf-row-handle (car old)) rev)))))

(defun fn-arf-changed-handles (old new)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (cond ((or (atom old) (atom new)) nil)
             ((or (equal (car old) (car new))
                  (not (fn-arf-row-handle (car old))))
              (fn-arf-changed-handles (cdr old) (cdr new)))
             (t (cons (fn-arf-row-handle (car old))
                      (fn-arf-changed-handles (cdr old) (cdr new)))))
       :exec (fn-arf-changed-handles-loop old new nil)))

(defthm fn-arf-changed-handles-loop-is-changed-handles
  (equal (fn-arf-changed-handles-loop old new rev)
         (revappend rev (fn-arf-changed-handles old new)))
  :hints (("Goal" :in-theory (disable fn-arf-row-handle))))

(verify-guards fn-arf-changed-handles
  :hints (("Goal" :in-theory (disable fn-arf-row-handle))))

; No element of XS is in YS.
(defun fn-arf-disjointp (xs ys)
  (declare (xargs :guard (true-listp ys)))
  (if (atom xs)
      t
    (and (not (member-equal (car xs) ys))
         (fn-arf-disjointp (cdr xs) ys))))

; NEW is a rewrite of OLD against the handles ALL: at every position the row
; is OLD's own, or it names no handle of ALL (a fresh handle, or none).
(defun fn-arf-rewrite-of-p (old new all)
  (declare (xargs :guard (true-listp all)))
  (if (atom new)
      t
    (and (or (and (consp old) (equal (car old) (car new)))
             (not (member-equal (fn-arf-row-handle (car new)) all)))
         (fn-arf-rewrite-of-p (and (consp old) (cdr old)) (cdr new) all))))

(local (in-theory (disable fn-arf-row-handle)))

(local
 (defthm fn-arf-changed-handles-are-old-handles
   (implies (member-equal c (fn-arf-changed-handles old new))
            (member-equal c (fn-arf-rows-handles old)))))

(local
 (defthm fn-arf-not-old-handle-is-not-changed
   (implies (not (member-equal c (fn-arf-rows-handles old)))
            (not (member-equal c (fn-arf-changed-handles old new))))))

(local
 (defthm fn-arf-rewrite-handle-is-old-or-fresh
   (implies (and (member-equal x (fn-arf-rows-handles new))
                 (fn-arf-rewrite-of-p old new all))
            (or (member-equal x (fn-arf-rows-handles old))
                (not (member-equal x all))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-arf-rewrite-of-p old new all)))))

(local
 (defthm fn-arf-disjointp-not-member
   (implies (and (fn-arf-disjointp xs ys) (not (member-equal y xs)))
            (fn-arf-disjointp xs (cons y ys)))))

(local
 (defthm fn-arf-rows-handles-non-nil
   (not (member-equal nil (fn-arf-rows-handles rows)))))

(local
 (defthm fn-arf-changed-disjoint-from-fresh
   (implies (and (subsetp-equal (fn-arf-rows-handles old) all)
                 (not (member-equal y all)))
            (not (member-equal y (fn-arf-changed-handles old new))))))

; KEYSTONE (PRF-ARF-4).  When the old rows' handles are pairwise distinct and
; NEW is a rewrite of OLD (every changed row names a handle the old history
; does not), no row of NEW names a handle the walk answers: the retired
; handles are exactly un-named.  Host subject: host/native/owner.lisp
; fnn-owner-reclaim-pass calls fn-arf-changed-handles over the captured and
; the interned rows.
(local
 (defthm fn-arf-changed-handles-are-unnamed-lemma
   (implies (and (no-duplicatesp-equal (fn-arf-rows-handles old))
                 (subsetp-equal (fn-arf-rows-handles old) all)
                 (fn-arf-rewrite-of-p old new all))
            (fn-arf-disjointp (fn-arf-changed-handles old new)
                              (fn-arf-rows-handles new)))
   :hints (("Goal" :induct (fn-arf-rewrite-of-p old new all))
           ("Subgoal *1/2" :use ((:instance fn-arf-rewrite-handle-is-old-or-fresh
                                            (x (fn-arf-row-handle (car old)))
                                            (old (cdr old)) (new (cdr new))))))))

(local
 (defthm fn-arf-subsetp-of-cons
   (implies (subsetp-equal x y) (subsetp-equal x (cons a y)))))

(local
 (defthm fn-arf-subsetp-reflexive
   (subsetp-equal x x)))

(defthm fn-arf-changed-handles-are-unnamed
  (implies (and (no-duplicatesp-equal (fn-arf-rows-handles old))
                (fn-arf-rewrite-of-p old new (fn-arf-rows-handles old)))
           (fn-arf-disjointp (fn-arf-changed-handles old new)
                             (fn-arf-rows-handles new)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-arf-changed-handles-are-unnamed-lemma
                            (all (fn-arf-rows-handles old))))
           :in-theory (disable fn-arf-changed-handles-are-unnamed-lemma))))
