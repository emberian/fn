; fn: pausing one peer's outbound feed without removing the peer.
;
; `peer feed NAME pause' and `peer feed NAME resume' (books/native-admin-peer.lisp
; `fn-native-admin-peer-extend-plan') let an operator contain a peer whose
; push misbehaves while its pull, its inbound admission and its queue stay:
; `peer remove' drops all of them.  The state is one configuration row of the
; peer's group, (NAME "outbound-paused" "" N), N 1 paused and 0 resumed, so the
; pause is a configuration event like every other peer change: durable,
; replayed at open, applied live.
;
; The deltas (`fn-fps-deltas') keep the slot single-valued without making it
; one of books/peer-carriage-rows.lisp's single-valued slots: they add the
; requested row and remove every other row of the slot the group holds, so
; the group never carries both a pause and a resume.
;
; Host callers: books/native-admin.lisp `fn-native-admin-plan-deltas-over'
; (host/native-admin-host.lisp, the live owner and the replayed store) builds
; `fn-fps-deltas' for a feed-pause plan; host/owner-host.lisp
; `fn-owner-feed-peers' answers `fn-fps-live-names' of the owner's feed table
; and configuration, which host/native/feed-service.lisp
; `fnn-feed-refresh-links' follows every worker cycle: a paused peer's link is
; closed and never dialled, and a resumed peer's link is dialled again.  The
; owner still enqueues for a paused peer (within its max-queue), so a resume
; delivers what was posted meanwhile.

(in-package "ACL2")
(include-book "peer-config")

(defconst *fn-fps-paused-slot* "outbound-paused")

(defun fn-fps-row (name pausep)
  (declare (xargs :guard t))
  (fn-cfg-row-make name *fn-fps-paused-slot* "" (if pausep 1 0)))

; Is ROW a row of the pause slot?
(defun fn-fps-slot-rowp (row)
  (declare (xargs :guard t))
  (equal (fn-cfg-row-b row) *fn-fps-paused-slot*))

(defun fn-fps-paused-in-rowsp (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (or (and (fn-fps-slot-rowp (car rows))
               (equal (fn-cfg-row-n (car rows)) 1))
          (fn-fps-paused-in-rowsp (cdr rows)))
    nil))

; NAME's outbound feed is paused in the peer table PEERS.
(defun fn-fps-pausedp (name peers)
  (declare (xargs :guard t))
  (fn-fps-paused-in-rowsp (fn-cfg-rows-with-key peers name)))

; The rows of the pause slot in ROWS other than ROW.
(defun fn-fps-other-slot-rows (rows row)
  (declare (xargs :guard t))
  (if (consp rows)
      (if (and (fn-fps-slot-rowp (car rows)) (not (equal (car rows) row)))
          (cons (car rows) (fn-fps-other-slot-rows (cdr rows) row))
        (fn-fps-other-slot-rows (cdr rows) row))
    nil))

; The configuration deltas that set NAME's pause to PAUSEP in PEERS, or nil
; when PEERS has no such peer (a pause never creates a peer).
(defun fn-fps-deltas (name pausep peers)
  (declare (xargs :guard t))
  (let* ((existing (fn-cfg-rows-with-key peers name))
         (row (fn-fps-row name pausep))
         (gone (fn-fps-other-slot-rows existing row)))
    (if (consp existing)
        (cons (fn-cfg-add-peer-rows name (list row))
              (if (consp gone) (list (fn-cfg-remove-peer-rows name gone)) nil))
      nil)))

; An admin plan's rows are a pause request: exactly one row of the slot.
(defun fn-fps-plan-rowsp (rows)
  (declare (xargs :guard t))
  (and (consp rows) (null (cdr rows)) (fn-fps-slot-rowp (car rows))))

(defun fn-fps-plan-pausep (rows)
  (declare (xargs :guard t))
  (and (consp rows) (equal (fn-cfg-row-n (car rows)) 1)))

; The outbound feeds the socket worker links: NAMES (the owner's feed table)
; without the paused ones.
(defun fn-fps-live-names (names peers)
  (declare (xargs :guard t))
  (if (consp names)
      (if (fn-fps-pausedp (car names) peers)
          (fn-fps-live-names (cdr names) peers)
        (cons (car names) (fn-fps-live-names (cdr names) peers)))
    nil))

; -----------------------------------------------------------------------------
; Properties

; KEYSTONE: the worker links exactly the unpaused feeds of the table.
(defthm fn-fps-live-names-are-the-unpaused-feeds
  (iff (member-equal n (fn-fps-live-names names peers))
       (and (member-equal n names)
            (not (fn-fps-pausedp n peers)))))

;; The row arithmetic the keystone below reads, local.
(local
 (defthm fn-fps-rows-with-key-of-keyed
   (implies (fn-cfg-rows-keyed-p rows k)
            (equal (fn-cfg-rows-with-key rows k) (true-list-fix rows)))
   :hints (("Goal" :in-theory (enable fn-cfg-rows-with-key
                                      fn-cfg-rows-keyed-p)))))

(local
 (defthm fn-fps-without-members-keyed
   (implies (fn-cfg-rows-keyed-p rows k)
            (fn-cfg-rows-keyed-p (fn-cfg-rows-without-members rows d) k))
   :hints (("Goal" :in-theory (enable fn-cfg-rows-keyed-p
                                      fn-cfg-rows-without-members)))))

(local
 (defthm fn-fps-rows-with-key-keyed
   (fn-cfg-rows-keyed-p (fn-cfg-rows-with-key rows k) k)
   :hints (("Goal" :in-theory (enable fn-cfg-rows-with-key
                                      fn-cfg-rows-keyed-p)))))

(local
 (defthm fn-fps-rows-with-key-of-append
   (equal (fn-cfg-rows-with-key (append a b) k)
          (append (fn-cfg-rows-with-key a k) (fn-cfg-rows-with-key b k)))
   :hints (("Goal" :in-theory (enable fn-cfg-rows-with-key)))))

(local
 (defthm fn-fps-rows-with-key-of-without-key
   (equal (fn-cfg-rows-with-key (fn-cfg-rows-without-key rows k) k) nil)
   :hints (("Goal" :in-theory (enable fn-cfg-rows-with-key
                                      fn-cfg-rows-without-key)))))

(local
 (defthm fn-fps-paused-in-rowsp-of-append
   (equal (fn-fps-paused-in-rowsp (append a b))
          (or (fn-fps-paused-in-rowsp a) (fn-fps-paused-in-rowsp b)))))

(local
 (defthm fn-fps-member-of-other-slot-rows
   (iff (member-equal x (fn-fps-other-slot-rows e row))
        (and (member-equal x e) (fn-fps-slot-rowp x) (not (equal x row))))))

(local
 (defthm fn-fps-no-pause-left
   (implies (subsetp-equal xs e)
            (not (fn-fps-paused-in-rowsp
                  (fn-cfg-rows-without-members
                   (fn-cfg-rows-without-members xs (list row))
                   (fn-fps-other-slot-rows e row)))))
   :hints (("Goal" :in-theory (enable fn-cfg-rows-without-members)))))

(local
 (defthm fn-fps-no-pause-when-nothing-gone
   (implies (and (subsetp-equal xs e)
                 (not (consp (fn-fps-other-slot-rows e row))))
            (not (fn-fps-paused-in-rowsp
                  (fn-cfg-rows-without-members xs (list row)))))
   :hints (("Goal" :in-theory (enable fn-cfg-rows-without-members)))))

(local
 (defthm fn-fps-subsetp-of-cons
   (implies (subsetp-equal x y) (subsetp-equal x (cons a y)))))

(local (defthm fn-fps-subsetp-refl (subsetp-equal x x)))

(local
 (defthm fn-fps-no-pause-when-nothing-gone-self
   (implies (not (consp (fn-fps-other-slot-rows e row)))
            (not (fn-fps-paused-in-rowsp
                  (fn-cfg-rows-without-members e (list row)))))
   :hints (("Goal" :use ((:instance fn-fps-no-pause-when-nothing-gone
                                    (xs e)))))))

(local
 (defthm fn-fps-no-pause-left-self
   (not (fn-fps-paused-in-rowsp
         (fn-cfg-rows-without-members
          (fn-cfg-rows-without-members e (list row))
          (fn-fps-other-slot-rows e row))))
   :hints (("Goal" :use ((:instance fn-fps-no-pause-left (xs e)))))))

(local
 (defthm fn-fps-row-survives
   (equal (fn-cfg-rows-without-members (list row)
                                       (fn-fps-other-slot-rows e row))
          (list row))
   :hints (("Goal" :in-theory (enable fn-cfg-rows-without-members)))))

(local
 (defthm fn-fps-without-members-of-append
   (equal (fn-cfg-rows-without-members (append a b) d)
          (append (fn-cfg-rows-without-members a d)
                  (fn-cfg-rows-without-members b d)))
   :hints (("Goal" :in-theory (enable fn-cfg-rows-without-members)))))

(local
 (defthm fn-fps-without-members-of-nil
   (equal (fn-cfg-rows-without-members nil d) nil)
   :hints (("Goal" :in-theory (enable fn-cfg-rows-without-members)))))

(local
 (defthm fn-fps-rows-with-key-of-nil
   (equal (fn-cfg-rows-with-key nil k) nil)
   :hints (("Goal" :in-theory (enable fn-cfg-rows-with-key)))))

(local
 (defthm fn-fps-rows-with-key-of-own-row
   (equal (fn-cfg-rows-with-key (list (fn-cfg-row-make name b c n)) name)
          (list (fn-cfg-row-make name b c n)))
   :hints (("Goal" :in-theory (enable fn-cfg-rows-with-key fn-cfg-row-a
                                      fn-cfg-row-make fn-cfg-ag-car)))))

(local
 (defthm fn-fps-paused-of-slot-row
   (equal (fn-fps-paused-in-rowsp
           (list (fn-cfg-row-make name "outbound-paused" "" n)))
          (equal n 1))
   :hints (("Goal" :in-theory (enable fn-cfg-row-make fn-cfg-row-b fn-cfg-row-n
                                      fn-cfg-ag-car fn-cfg-ag-cdr)))))

; KEYSTONE: the deltas a pause or resume publishes leave NAME's feed paused
; exactly when PAUSEP, for a peer the table holds (applied as the live owner
; and the replay apply them, `fn-cfg-apply').
(defthm fn-fps-deltas-set-the-pause
  (implies (consp (fn-cfg-rows-with-key (fn-cfg-peers v) name))
           (equal (fn-fps-pausedp
                   name
                   (fn-cfg-peers
                    (fn-cfg-apply v gen stamp
                                  (fn-fps-deltas name pausep (fn-cfg-peers v)))))
                  (if pausep t nil)))
  :hints (("Goal" :in-theory (e/d (fn-cfg-apply fn-cfg-apply-delta
                                   fn-cfg-add-peer-rows fn-cfg-remove-peer-rows)
                                  (fn-fps-paused-in-rowsp)))))

; A request for a peer the table does not hold publishes nothing.
(defthm fn-fps-deltas-of-an-absent-peer
  (implies (not (consp (fn-cfg-rows-with-key peers name)))
           (equal (fn-fps-deltas name pausep peers) nil)))

(in-theory (disable fn-fps-row fn-fps-pausedp fn-fps-deltas fn-fps-live-names))
