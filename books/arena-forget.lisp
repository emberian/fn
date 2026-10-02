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
