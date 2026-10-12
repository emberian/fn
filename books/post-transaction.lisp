; fn: the POST transaction machine (Builder P; RUNTIME-MODEL section 3 as ruled
; 2026-10-10: PAYLOAD_WRITING -> LOG_WRITING -> COMMITTING -> PUBLISHED, no payload
; barrier).  Packet draft 3: the start is a continuation (the head is read and
; accepted in quantum-sized windows on the zero-delay timer), the article is written
; from the poster's buffer unmoved, and the step first checks the state's shape
; against bounded per-field budgets, so the layer's obligations (charged, bounded
; requests and state) hold of every state.  The keystones P0-P6 are stated in the
; packet (build/post-runs/, the lane's scratch) and not yet proved, so this book is
; not in ACL2_BOOKS and certifies nothing of record.
;
; The owner, static slot 1 under contract v2.1, takes a poster's handed article
; buffer and writes one log entry from three spans: b1 (frame header, chain field,
; the record's prefix PRE) from an owner workspace, the article [0, len) from the
; poster's buffer unmoved, b3 (the record's suffix SUF and the trailer) from a
; second workspace; the record is PRE ++ article ++ SUF, the header edits being the
; block PRE carries before the head.  The padding is never written (the extent past
; the frontier reads zeros).  The three writes are L's fn-ptd one record write
; (books/post-transaction-durable.lisp); :posted only on the barrier's (:done).  The
; digest is BLAKE3 over 1024-octet windows on the zero-delay timer
; (books/blake3-tree.lisp's held state).  Geometry (unit fmax hmax) is the opened
; store's, never a constant (D27).
(in-package "ACL2")
(include-book "post-transaction-durable")
(include-book "runtime-contract-layer")
(include-book "blake3-tree")
(set-verify-guards-eagerness 0)

; -----------------------------------------------------------------------------
; Bounds and constants: properties of this code, none bounds data (D27).
(defconst *fn-ptx-k* 2)              ; posts waiting, at most
(defconst *fn-ptx-lfile* 2)          ; the log segment's file reference
(defconst *fn-ptx-wexp* 0)           ; digest window = 1024 * 2^wexp octets
(defconst *fn-ptx-window* 1024)
(defconst *fn-ptx-nw-max* 64)        ; digest windows per step at most (a quantum cap)
(defconst *fn-ptx-sufhead-max* 9)    ; the suffix's head (a CBOR uint), at most; b3's base
(defconst *fn-ptx-codes* '((:posted . 0) (:refused . 1) (:uncertain . 2) (:busy . 3)))
(defun fn-ptx-code (o)
  (declare (xargs :guard t)) (nfix (cdr (assoc-eq o *fn-ptx-codes*))))
(verify-guards fn-ptx-code)

; -----------------------------------------------------------------------------
; The acceptance, constrained and streaming (the seam with M's admission gate,
; settled 10-10 word for word): begun at the record's txid, fed the head's octets
; window by window, each feed answering the next state and a part of the record's
; suffix; ended with the article body's length, answering whether the article is
; accepted, the record's prefix PRE (the record fields before the article, the
; article's byte-string header, the injected header block), the Path insert INS and
; its offset IOFF in the article (D32: the agent is spliced in at the Path content),
; the suffix's head SUFHEAD (the group count, known only at the end) and its tail.
; record = PRE ++ article[0,IOFF) ++ INS ++ article[IOFF,len) ++ SUFHEAD ++ the
; parts ++ the tail.  The state and the outputs are bounded by constants of the
; gate's code: K = (fn-ptx-acc-out-max), M's (fn-adm-acc-out-max); SUFHEAD by the
; widest CBOR uint head; the state by the codec's group-name ceiling and naturals.
(encapsulate
  (((fn-ptx-acc-begin *) => *)
   ((fn-ptx-acc-feed * *) => (mv * *))
   ((fn-ptx-acc-feed-cost * *) => *)
   ((fn-ptx-acc-end * *) => (mv * * * * * *))
   ((fn-ptx-acc-max-state) => *)
   ((fn-ptx-acc-out-max) => *))
  (local (defun fn-ptx-acc-begin (txid) (declare (xargs :guard t) (ignore txid)) nil))
(local (verify-guards fn-ptx-acc-begin))
  (local (defun fn-ptx-acc-feed (a octets) (declare (xargs :guard t) (ignore a octets)) (mv nil nil)))
(local (verify-guards fn-ptx-acc-feed))
  (local (defun fn-ptx-acc-feed-cost (a octets) (declare (xargs :guard t) (ignore a octets)) 0))
(local (verify-guards fn-ptx-acc-feed-cost))
  (local (defun fn-ptx-acc-end (a blen) (declare (xargs :guard t) (ignore a blen)) (mv t nil nil 0 nil nil)))
(local (verify-guards fn-ptx-acc-end))
  (local (defun fn-ptx-acc-max-state ()
  (declare (xargs :guard t)) 1))
(local (verify-guards fn-ptx-acc-max-state))
  (local (defun fn-ptx-acc-out-max ()
  (declare (xargs :guard t)) 0))
(local (verify-guards fn-ptx-acc-out-max))
  (defthm fn-ptx-acc-max-state-natp (natp (fn-ptx-acc-max-state)) :rule-classes :type-prescription)
  (defthm fn-ptx-acc-out-max-natp (natp (fn-ptx-acc-out-max)) :rule-classes :type-prescription)
  (defthm fn-ptx-acc-begin-bounded (<= (fn-rtc-size (fn-ptx-acc-begin txid)) (fn-ptx-acc-max-state))
    :rule-classes :linear)
  (defthm fn-ptx-acc-feed-bounded (<= (fn-rtc-size (mv-nth 0 (fn-ptx-acc-feed a octets))) (fn-ptx-acc-max-state))
    :rule-classes :linear)
  ; the feed's work (the instance's def-cost bound): linear in the octets fed
  (defthm fn-ptx-acc-feed-cost-bounded
    (and (natp (fn-ptx-acc-feed-cost a octets))
         (<= (fn-ptx-acc-feed-cost a octets) (+ (* 4 (len octets)) (fn-ptx-acc-out-max))))
    :rule-classes nil)
  (defthm fn-ptx-acc-feed-shape
    (and (fn-cbor-octet-listp (mv-nth 1 (fn-ptx-acc-feed a octets)))
         (<= (len (mv-nth 1 (fn-ptx-acc-feed a octets))) (+ (* 2 (len octets)) (fn-ptx-acc-out-max))))
    :rule-classes nil)
  (defthm fn-ptx-acc-end-shape
    (mv-let (ok pre ins ioff sufhead suf) (fn-ptx-acc-end a blen)
      (declare (ignore ok))
      (and (fn-cbor-octet-listp pre) (fn-cbor-octet-listp ins) (natp ioff)
           (fn-cbor-octet-listp sufhead) (fn-cbor-octet-listp suf)
           (<= (len pre) (fn-ptx-acc-out-max)) (<= (len ins) (fn-ptx-acc-out-max))
           (<= (len sufhead) *fn-ptx-sufhead-max*) (<= (len suf) (fn-ptx-acc-out-max))))
    :rule-classes nil))

; -----------------------------------------------------------------------------
; State: (ph k cur q kd ext nxt b1 b3 hs committed evd geo acc).
;   cur  (fid finc bp len hoff txid ioff): the poster's slot, its handed buffer BP
;        holding the article at [0,len); HOFF the head's length once found (while
;        :reading, the position the head search has reached); the record's txid; IOFF
;        the Path insert's offset in the article (len when there is no insert)
;   q    waiting posts (fid finc bp len), at most *fn-ptx-k*
;   kd   the log kernel's projection (count last frontier next-txid acked): what
;        fn-ptd's actions read of fn-lgk, without COMMITTED's elements
;   ext nxt  fn-ptd's extent and the sealed extent
;   b1   owner workspace (h g l1 lins): [0,l1) = frame header ++ chain field ++ PRE,
;        [l1, l1+lins) = INS
;   b3   owner workspace (h g end start): [start,end) = SUF, then the trailer once the
;        digest is known (end then past it); while :reading, start is the base
;        *fn-ptx-sufhead-max* and end the suffix parts' running end
;   hs   the digest's held state (pos stack); after the last window (nmsg trailer pad)
;   evd  ghost: this transaction's completions (kind tag n), in order
;   geo  (unit fmax hmax), the opened store's
;   acc  the acceptance's state while :reading
(defun fn-ptx-mk (ph k cur q kd ext nxt b1 b3 hs committed evd geo acc)
  (declare (xargs :guard t))
  (list ph (nfix k) cur q kd (nfix ext) (nfix nxt) b1 b3 hs (and committed t) evd geo acc))
(verify-guards fn-ptx-mk)
(defun fn-ptx-ph (m)
  (declare (xargs :guard t)) (fn-rtc-get 0 m))
(verify-guards fn-ptx-ph)
(defun fn-ptx-k (m)
  (declare (xargs :guard t)) (nfix (fn-rtc-get 1 m)))
(verify-guards fn-ptx-k)
(defun fn-ptx-cur (m)
  (declare (xargs :guard t)) (fn-rtc-get 2 m))
(verify-guards fn-ptx-cur)
(defun fn-ptx-q (m)
  (declare (xargs :guard t)) (fn-rtc-get 3 m))
(verify-guards fn-ptx-q)
(defun fn-ptx-kd (m)
  (declare (xargs :guard t)) (fn-rtc-get 4 m))
(verify-guards fn-ptx-kd)
(defun fn-ptx-ext (m)
  (declare (xargs :guard t)) (nfix (fn-rtc-get 5 m)))
(verify-guards fn-ptx-ext)
(defun fn-ptx-nxt (m)
  (declare (xargs :guard t)) (nfix (fn-rtc-get 6 m)))
(verify-guards fn-ptx-nxt)
(defun fn-ptx-b1 (m)
  (declare (xargs :guard t)) (fn-rtc-get 7 m))
(verify-guards fn-ptx-b1)
(defun fn-ptx-b3 (m)
  (declare (xargs :guard t)) (fn-rtc-get 8 m))
(verify-guards fn-ptx-b3)
(defun fn-ptx-hs (m)
  (declare (xargs :guard t)) (fn-rtc-get 9 m))
(verify-guards fn-ptx-hs)
(defun fn-ptx-committedp (m)
  (declare (xargs :guard t)) (and (fn-rtc-get 10 m) t))
(verify-guards fn-ptx-committedp)
(defun fn-ptx-evd (m)
  (declare (xargs :guard t)) (fn-rtc-get 11 m))
(verify-guards fn-ptx-evd)
(defun fn-ptx-geo (m)
  (declare (xargs :guard t)) (fn-rtc-get 12 m))
(verify-guards fn-ptx-geo)
(defun fn-ptx-acc (m)
  (declare (xargs :guard t)) (fn-rtc-get 13 m))
(verify-guards fn-ptx-acc)
(defun fn-ptx-unit (m)
  (declare (xargs :guard t)) (max 1 (nfix (fn-rtc-get 0 (fn-ptx-geo m)))))
(verify-guards fn-ptx-unit)
(defun fn-ptx-fmax (m)
  (declare (xargs :guard t)) (nfix (fn-rtc-get 1 (fn-ptx-geo m))))
(verify-guards fn-ptx-fmax)
(defun fn-ptx-hmax (m)
  (declare (xargs :guard t)) (nfix (fn-rtc-get 2 (fn-ptx-geo m))))
(verify-guards fn-ptx-hmax)

; M with the named fields replaced (every other field read from M); the result
; is always a fresh fn-ptx-mk, so no field of M but the fourteen survives.
(defmacro fn-ptx-chg (m &key (ph 'nil ph-p) (k 'nil k-p) (cur 'nil cur-p) (q 'nil q-p) (kd 'nil kd-p)
                        (ext 'nil ext-p) (nxt 'nil nxt-p) (b1 'nil b1-p) (b3 'nil b3-p) (hs 'nil hs-p)
                        (committed 'nil committed-p) (evd 'nil evd-p) (geo 'nil geo-p) (acc 'nil acc-p))
  `(fn-ptx-mk ,(if ph-p ph `(fn-ptx-ph ,m)) ,(if k-p k `(fn-ptx-k ,m)) ,(if cur-p cur `(fn-ptx-cur ,m))
              ,(if q-p q `(fn-ptx-q ,m)) ,(if kd-p kd `(fn-ptx-kd ,m)) ,(if ext-p ext `(fn-ptx-ext ,m))
              ,(if nxt-p nxt `(fn-ptx-nxt ,m)) ,(if b1-p b1 `(fn-ptx-b1 ,m)) ,(if b3-p b3 `(fn-ptx-b3 ,m))
              ,(if hs-p hs `(fn-ptx-hs ,m)) ,(if committed-p committed `(fn-ptx-committedp ,m))
              ,(if evd-p evd `(fn-ptx-evd ,m)) ,(if geo-p geo `(fn-ptx-geo ,m)) ,(if acc-p acc `(fn-ptx-acc ,m))))

(defun fn-ptx-kd-mk (count last frontier txid acked)
  (declare (xargs :guard t)) (list (nfix count) last (nfix frontier) (nfix txid) (nfix acked)))
(verify-guards fn-ptx-kd-mk)
(defun fn-ptx-kd-count (kd)
  (declare (xargs :guard t)) (nfix (fn-rtc-get 0 kd)))
(verify-guards fn-ptx-kd-count)
(defun fn-ptx-kd-last (kd)
  (declare (xargs :guard t)) (fn-rtc-get 1 kd))
(verify-guards fn-ptx-kd-last)
(defun fn-ptx-kd-frontier (kd)
  (declare (xargs :guard t)) (nfix (fn-rtc-get 2 kd)))
(verify-guards fn-ptx-kd-frontier)
(defun fn-ptx-kd-txid (kd)
  (declare (xargs :guard t)) (nfix (fn-rtc-get 3 kd)))
(verify-guards fn-ptx-kd-txid)
(defun fn-ptx-kd-acked (kd)
  (declare (xargs :guard t)) (nfix (fn-rtc-get 4 kd)))
(verify-guards fn-ptx-kd-acked)

; The opened machine: idle over the open's kernel projection, at extent EXT.
(defun fn-ptx-opened (kd ext geo)
  (declare (xargs :guard t)) (fn-ptx-mk :idle 0 nil nil kd ext ext nil nil nil nil nil geo nil))
(verify-guards fn-ptx-opened)

; Before the store opens: the static slot's initial state (fn-rtc-m-static-init
; takes only the slot), refusing every post until the open's :opened event.
(defun fn-ptx-closed ()
  (declare (xargs :guard t)) (fn-ptx-mk :closed 0 nil nil nil 0 0 nil nil nil nil nil nil nil))
(verify-guards fn-ptx-closed)
; The open's data arrives once, as the completion of the :opened action fn-rtc-init
; arms for the static slot: (:opened (:done 0) J 1 DATA), DATA = (KD EXT GEO), read
; by fn-rtc-ev-opened-data (contract v2.2); a failed or cancelled :opened carries no
; DATA and leaves the machine :closed.

; The projection of a logical kernel (L's fn-lgk), for the P4 relation.
(defun fn-ptx-kd-of (ks)
  (fn-ptx-kd-mk (len (fn-lgk-committed ks)) (fn-lgk-last ks) (fn-lgk-frontier ks)
                (fn-lgk-next-txid ks) (fn-lgk-acked ks)))

(defun fn-ptx-cur-fid (c)
  (declare (xargs :guard t)) (fn-rtc-get 0 c))
(verify-guards fn-ptx-cur-fid)
(defun fn-ptx-cur-finc (c)
  (declare (xargs :guard t)) (fn-rtc-get 1 c))
(verify-guards fn-ptx-cur-finc)
(defun fn-ptx-cur-bp (c)
  (declare (xargs :guard t)) (nfix (fn-rtc-get 2 c)))
(verify-guards fn-ptx-cur-bp)
(defun fn-ptx-cur-len (c)
  (declare (xargs :guard t)) (nfix (fn-rtc-get 3 c)))
(verify-guards fn-ptx-cur-len)
(defun fn-ptx-cur-hoff (c)
  (declare (xargs :guard t)) (nfix (fn-rtc-get 4 c)))
(verify-guards fn-ptx-cur-hoff)
(defun fn-ptx-cur-txid (c)
  (declare (xargs :guard t)) (nfix (fn-rtc-get 5 c)))
(verify-guards fn-ptx-cur-txid)
(defun fn-ptx-cur-ioff (c)
  (declare (xargs :guard t)) (nfix (fn-rtc-get 6 c)))
(verify-guards fn-ptx-cur-ioff)
(defun fn-ptx-buf-h (b)
  (declare (xargs :guard t)) (nfix (fn-rtc-get 0 b)))
(verify-guards fn-ptx-buf-h)
(defun fn-ptx-buf-g (b)
  (declare (xargs :guard t)) (nfix (fn-rtc-get 1 b)))
(verify-guards fn-ptx-buf-g)
(defun fn-ptx-buf-len (b)
  (declare (xargs :guard t)) (nfix (fn-rtc-get 2 b)))
(verify-guards fn-ptx-buf-len)
(defun fn-ptx-buf-x (b)
  (declare (xargs :guard t)) (nfix (fn-rtc-get 3 b)))
(verify-guards fn-ptx-buf-x)

; -----------------------------------------------------------------------------
; The shape check.  (fn-ptx-size-rem X N) is N less X's size in words when that is
; at most N, else nil; it walks at most N words of X whatever X is.  A state is
; well formed when its phase is one of the machine's and each field fits its
; budget; the budgets cover every reachable state (keystone P0) with the digest's
; stack at most 64 entries deep (messages under 2^74 octets).
(defun fn-ptx-size-rem (x n)
  (declare (xargs :guard t :measure (acl2-count x)))
  (mbe :logic (cond ((zp n) nil)
        ((atom x) (- n 1))
        (t (let ((r (fn-ptx-size-rem (car x) (- n 1))))
             (and r (fn-ptx-size-rem (cdr x) r)))))
       :exec (cond ((zp (nfix n)) nil)
        ((atom x) (- n 1))
        (t (let ((r (fn-ptx-size-rem (car x) (- n 1))))
             (and r (fn-ptx-size-rem (cdr x) r)))))))
(verify-guards fn-ptx-size-rem)
(defconst *fn-ptx-phases*
  '(:closed :idle :reading :hashing :extending :extsyncing :payload-writing :log-writing :committing :fenced))
;                            ph k cur q  kd ext nxt b1 b3 hs   committed evd geo
(defconst *fn-ptx-budgets* '(1  1 15  21 75 1   1   9  9  4101 1         57  7))
(defun fn-ptx-fields-fit (m i bs)
  (declare (xargs :guard t :measure (len bs)))
  (if (consp bs)
      (and (fn-ptx-size-rem (fn-rtc-get i m) (nfix (car bs)))
           (fn-ptx-fields-fit m (+ 1 (nfix i)) (cdr bs)))
    t))
(verify-guards fn-ptx-fields-fit)
(defun fn-ptx-wfp (m)
  (declare (xargs :guard t))
  (and (member-eq (fn-ptx-ph m) *fn-ptx-phases*)
       (fn-ptx-fields-fit m 0 *fn-ptx-budgets*)
       (fn-ptx-size-rem (fn-ptx-acc m) (fn-ptx-acc-max-state))
       t))
(verify-guards fn-ptx-wfp)
; The check's charge: the words it may walk.
(defun fn-ptx-wf-cost ()
  (declare (xargs :guard t)) (+ 4298 (fn-ptx-acc-max-state)))
(verify-guards fn-ptx-wf-cost)
; A state that fails the check (none reachable) is replaced by this fenced one.
(defun fn-ptx-broken ()
  (declare (xargs :guard t)) (fn-ptx-mk :fenced 0 nil nil nil 0 0 nil nil nil nil nil nil nil))
(verify-guards fn-ptx-broken)

; -----------------------------------------------------------------------------
; Reading the view (the owner's own workspaces and :out leases only).
(defun fn-ptx-byte (h i id inc fn-rtc-st)
  (declare (xargs :guard t :stobjs fn-rtc-st))
  (nfix (fn-rtc-st-v-byte h i id inc fn-rtc-st)))
(verify-guards fn-ptx-byte)
(defun fn-ptx-range (h i n id inc fn-rtc-st)
  ; octets [i, i+n) of buffer h, as a list (statement level; the exec twin reads in place)
  (declare (xargs :guard t :stobjs fn-rtc-st :measure (nfix n)))
  (mbe :logic (if (zp n) nil
    (cons (fn-ptx-byte h i id inc fn-rtc-st)
          (fn-ptx-range h (+ 1 (nfix i)) (- n 1) id inc fn-rtc-st)))
       :exec (if (zp (nfix n)) nil
    (cons (fn-ptx-byte h i id inc fn-rtc-st)
          (fn-ptx-range h (+ 1 (nfix i)) (- n 1) id inc fn-rtc-st)))))
(verify-guards fn-ptx-range)
(defun fn-ptx-gen (h id inc fn-rtc-st)
  (declare (xargs :guard t :stobjs fn-rtc-st))
  (fn-rtc-st-v-gen h id inc fn-rtc-st))
(verify-guards fn-ptx-gen)
(defun fn-ptx-cap (h id inc fn-rtc-st)
  ; buffer H's capacity under the layer's configuration
  (declare (xargs :guard t :stobjs fn-rtc-st) (ignore id inc))
  (fn-rtc-buf-cap h (fn-rtc-st-config fn-rtc-st)))
(verify-guards fn-ptx-cap)

; The head's length: the least i in [I, LIM - 3) with CR LF CR LF at [i, i+4),
; plus 4; nil when there is none.
(defun fn-ptx-head-end (h i lim id inc fn-rtc-st)
  (declare (xargs :guard t :stobjs fn-rtc-st :measure (nfix (- (nfix lim) (nfix i)))))
  (let ((i (nfix i)))
    (if (< (+ i 3) (nfix lim))
        (if (and (equal (fn-ptx-byte h i id inc fn-rtc-st) 13) (equal (fn-ptx-byte h (+ i 1) id inc fn-rtc-st) 10)
                 (equal (fn-ptx-byte h (+ i 2) id inc fn-rtc-st) 13) (equal (fn-ptx-byte h (+ i 3) id inc fn-rtc-st) 10))
            (+ i 4)
          (fn-ptx-head-end h (+ i 1) lim id inc fn-rtc-st))
      nil)))
(verify-guards fn-ptx-head-end)

; The first free owner home buffer at or above I other than SKIP (home buffers of
; slot 1 are [0, qfixed)).
(defun fn-ptx-free (i skip id inc fn-rtc-st)
  (declare (xargs :guard t :stobjs fn-rtc-st
                  :measure (nfix (- (min (fn-rtc-nstatic-home (fn-rtc-st-config fn-rtc-st)) (fn-rtc-nbufs (fn-rtc-st-config fn-rtc-st))) (nfix i)))))
  (let ((i (nfix i)))
    (if (< i (min (fn-rtc-nstatic-home (fn-rtc-st-config fn-rtc-st)) (fn-rtc-nbufs (fn-rtc-st-config fn-rtc-st))))
        (if (and (not (equal i skip)) (equal (fn-rtc-st-v-owner i id inc fn-rtc-st) '(:free)))
            i
          (fn-ptx-free (+ 1 i) skip id inc fn-rtc-st))
      nil)))
(verify-guards fn-ptx-free)

; -----------------------------------------------------------------------------
; The entry's spans, in file order: b1's [0,l1) (frame header ++ chain field ++
; PRE), the article [0,ioff), b1's [l1, l1+lins) (INS), the article [ioff,len),
; b3's [start,end) (SUF, and the trailer once hashed); empty spans dropped.  Each
; span is (h off n).  The entry is written one pwrite per span from the buffer it
; lies in; the record moves nowhere.
(defun fn-ptx-span (h off n)
  (declare (xargs :guard t)) (mbe :logic (if (zp n) nil (list (list (nfix h) (nfix off) (nfix n))))
       :exec (if (zp (nfix n)) nil (list (list (nfix h) (nfix off) (nfix n))))))
(verify-guards fn-ptx-span)
(defun fn-ptx-spans (m)
  (declare (xargs :guard t))
  (let* ((b1 (fn-ptx-b1 m)) (b3 (fn-ptx-b3 m)) (cur (fn-ptx-cur m))
         (l1 (fn-ptx-buf-len b1)) (lins (fn-ptx-buf-x b1))
         (alen (fn-ptx-cur-len cur)) (ioff (min (fn-ptx-cur-ioff cur) alen)))
    (append (fn-ptx-span (fn-ptx-buf-h b1) 0 l1)
            (fn-ptx-span (fn-ptx-cur-bp cur) 0 ioff)
            (fn-ptx-span (fn-ptx-buf-h b1) l1 lins)
            (fn-ptx-span (fn-ptx-cur-bp cur) ioff (- alen ioff))
            (fn-ptx-span (fn-ptx-buf-h b3) (fn-ptx-buf-x b3) (- (fn-ptx-buf-len b3) (fn-ptx-buf-x b3))))))
(verify-guards fn-ptx-spans)
(defun fn-ptx-spans-len (spans)
  (declare (xargs :guard t))
  (if (consp spans) (+ (nfix (fn-rtc-get 2 (car spans))) (fn-ptx-spans-len (cdr spans))) 0))
(verify-guards fn-ptx-spans-len)

; Octet I of the message the spans make, and N octets from I, read through the view.
(defun fn-ptx-msg-byte (i spans id inc fn-rtc-st)
  (declare (xargs :guard t :stobjs fn-rtc-st :measure (len spans)))
  (if (consp spans)
      (let ((n (nfix (fn-rtc-get 2 (car spans)))))
        (if (< (nfix i) n)
            (fn-ptx-byte (fn-rtc-get 0 (car spans)) (+ (nfix (fn-rtc-get 1 (car spans))) (nfix i)) id inc fn-rtc-st)
          (fn-ptx-msg-byte (- (nfix i) n) (cdr spans) id inc fn-rtc-st)))
    0))
(verify-guards fn-ptx-msg-byte)
(defun fn-ptx-msg-range (i n spans id inc fn-rtc-st)
  (declare (xargs :guard t :stobjs fn-rtc-st :measure (nfix n)))
  (mbe :logic (if (zp n) nil
    (cons (fn-ptx-msg-byte i spans id inc fn-rtc-st)
          (fn-ptx-msg-range (+ 1 (nfix i)) (- n 1) spans id inc fn-rtc-st)))
       :exec (if (zp (nfix n)) nil
    (cons (fn-ptx-msg-byte i spans id inc fn-rtc-st)
          (fn-ptx-msg-range (+ 1 (nfix i)) (- n 1) spans id inc fn-rtc-st)))))
(verify-guards fn-ptx-msg-range)

; The digest's held state (pos stack) over a message of N octets: absorb up to
; NW windows; a window is pushed only when more than a window remains after it
; (fn-b3-window-outs' rule), the last one by the finish.
(defun fn-ptx-absorb (nw pos st n spans id inc fn-rtc-st)
  (declare (xargs :guard t :stobjs fn-rtc-st :measure (nfix nw)))
  (mbe :logic (let ((pos (nfix pos)) (n (nfix n)))
    (if (or (zp nw) (<= n (+ pos *fn-ptx-window*)))
        (mv pos st)
      (fn-ptx-absorb (- nw 1) (+ pos *fn-ptx-window*)
                     (fn-b3-cv-push *fn-b3-iv* 0 *fn-ptx-wexp*
                                    (fn-b3-node *fn-b3-iv*
                                                (fn-ptx-msg-range pos *fn-ptx-window* spans id inc fn-rtc-st)
                                                (floor pos 1024) 0)
                                    st)
                     n spans id inc fn-rtc-st)))
       :exec (let ((pos (nfix pos)) (n (nfix n)))
    (if (or (zp (nfix nw)) (<= n (+ pos *fn-ptx-window*)))
        (mv pos st)
      (fn-ptx-absorb (- nw 1) (+ pos *fn-ptx-window*)
                     (fn-b3-cv-push *fn-b3-iv* 0 *fn-ptx-wexp*
                                    (fn-b3-node *fn-b3-iv*
                                                (fn-ptx-msg-range pos *fn-ptx-window* spans id inc fn-rtc-st)
                                                (floor pos 1024) 0)
                                    st)
                     n spans id inc fn-rtc-st)))))
(verify-guards fn-ptx-absorb)
(defun fn-ptx-finish-digest (pos st n spans id inc fn-rtc-st)
  (declare (xargs :guard t :stobjs fn-rtc-st))
  (let ((pos (nfix pos)))
    (fn-b3-output-root
     (fn-b3-stack-fold *fn-b3-iv* 0
                       (fn-b3-cv-push *fn-b3-iv* 0 *fn-ptx-wexp*
                                      (fn-b3-node *fn-b3-iv*
                                                  (fn-ptx-msg-range pos (- (nfix n) pos) spans id inc fn-rtc-st)
                                                  (floor pos 1024) 0)
                                      st)))))
(verify-guards fn-ptx-finish-digest)

; -----------------------------------------------------------------------------
; Requests.
(defun fn-ptx-timer ()
  (declare (xargs :guard t)) (list :submit :timer nil (list 0)))
(verify-guards fn-ptx-timer)
(defun fn-ptx-pwrite (h g off n pos)
  (declare (xargs :guard t)) (list :submit :pwrite (list (nfix h) (nfix g) (nfix off) (nfix n)) (list *fn-ptx-lfile* (nfix pos))))
(verify-guards fn-ptx-pwrite)
(defun fn-ptx-fsync ()
  (declare (xargs :guard t)) (list :submit :fsync nil (list *fn-ptx-lfile*)))
(verify-guards fn-ptx-fsync)
; fn-ptd's extension as the unbuffered :extend kind (contract v2.2): FILE's extent
; from EXT to NXT; the layer accepts it only with naturals below 2^64 and EXT < NXT.
(defun fn-ptx-extend (ext nxt)
  (declare (xargs :guard t)) (list :submit :extend nil (list *fn-ptx-lfile* (nfix ext) (nfix nxt))))
(verify-guards fn-ptx-extend)

; The answer O to post P = (fid finc bp len ...): octet 0 of the poster's own
; buffer becomes the code, the whole buffer goes back by a hand.  The generation
; is the view's now (a lease's end advances it).
(defun fn-ptx-answer (p o id inc fn-rtc-st)
  (declare (xargs :guard t :stobjs fn-rtc-st))
  (let* ((h (fn-ptx-cur-bp p)) (g (fn-ptx-gen h id inc fn-rtc-st))
         (fl (max 1 (nfix (fn-rtc-st-v-fill h id inc fn-rtc-st)))))
    (list (list :write h g 0 (list (fn-ptx-code o)))
          (list :submit :hand (list h g 0 fl) (list (fn-ptx-cur-fid p) (fn-ptx-cur-finc p))))))
(verify-guards fn-ptx-answer)

; The frame header of an entry whose record is R octets long (kind 1, one record).
(defun fn-ptx-frame-header (rlen)
  (declare (xargs :guard t))
  (mbe :logic (fn-frame-header *fn-lg-magic* *fn-lg-version* *fn-lg-record-kind* (+ 32 (nfix rlen)))
       :exec (let* ((length (+ 32 (nfix rlen)))
                (q0 (floor length 256))
                (q1 (floor q0 256))
                (q2 (floor q1 256)))
           (append *fn-lg-magic*
                   (cons *fn-lg-version*
                         (cons *fn-lg-record-kind*
                               (list q2 (mod q1 256) (mod q0 256) (mod length 256))))))))
(verify-guards fn-ptx-frame-header
  :hints (("Goal" :in-theory (e/d (fn-frame-header fn-cbor-u32-bytes) (floor mod)))))
(defun fn-ptx-pad-len (elen unit)
  (declare (xargs :guard t)) (fn-lg-pad-len (nfix elen) unit))
(verify-guards fn-ptx-pad-len)

; Start post P = (fid finc bp len) over kernel projection KD: the head search and
; the acceptance begin on the zero-delay timer.  Constant work.  Q is the queue
; after P; COMMITTED is the step's commit flag, carried.
(defun fn-ptx-start (p q kd ext geo committed)
  (declare (xargs :guard t))
  (mv (fn-ptx-mk :reading 0
                 (list (fn-ptx-cur-fid p) (fn-ptx-cur-finc p) (fn-ptx-cur-bp p) (fn-ptx-cur-len p) 0 (fn-ptx-kd-txid kd)
                       (fn-ptx-cur-len p))
                 q kd ext ext nil nil nil committed nil geo (fn-ptx-acc-begin (fn-ptx-kd-txid kd)))
      (list (fn-ptx-timer))
      1))
(verify-guards fn-ptx-start)

; End the current transaction with outcome O: release b1 and b3, answer, then
; start the next waiting post unless FENCED (then every waiting post is refused).
(defun fn-ptx-release-bufs (m id inc fn-rtc-st)
  (declare (xargs :guard t :stobjs fn-rtc-st))
    ; at the view's generation: a pwrite's lease ending advances it
  (append (if (consp (fn-ptx-b1 m)) (list (list :release (fn-ptx-buf-h (fn-ptx-b1 m)) (fn-ptx-gen (fn-ptx-buf-h (fn-ptx-b1 m)) id inc fn-rtc-st))) nil)
          (if (consp (fn-ptx-b3 m)) (list (list :release (fn-ptx-buf-h (fn-ptx-b3 m)) (fn-ptx-gen (fn-ptx-buf-h (fn-ptx-b3 m)) id inc fn-rtc-st))) nil)))
(verify-guards fn-ptx-release-bufs)
(defun fn-ptx-refuse-all (q id inc fn-rtc-st)
  (declare (xargs :guard t :stobjs fn-rtc-st))
  (if (consp q)
      (append (fn-ptx-answer (car q) :refused id inc fn-rtc-st) (fn-ptx-refuse-all (cdr q) id inc fn-rtc-st))
    nil))
(verify-guards fn-ptx-refuse-all)
(defun fn-ptx-end (m o kd ext fenced committed id inc fn-rtc-st)
  ; (mv m reqs cost); KD and EXT the kernel projection and extent after this end
  (declare (xargs :guard t :stobjs fn-rtc-st))
  (let* ((cur (fn-ptx-cur m)) (q (fn-ptx-q m))
         (done (append (fn-ptx-release-bufs m id inc fn-rtc-st) (fn-ptx-answer cur o id inc fn-rtc-st))))
    (cond (fenced
           (mv (fn-ptx-mk :fenced 0 nil nil kd ext ext nil nil nil committed nil (fn-ptx-geo m) nil)
               (append done (fn-ptx-refuse-all q id inc fn-rtc-st)) 1))
          ((consp q)
           (mv-let (m2 r2 c2) (fn-ptx-start (car q) (cdr q) kd ext (fn-ptx-geo m) committed)
             (mv m2 (append done r2) (+ 1 c2))))
          (t (mv (fn-ptx-mk :idle 0 nil nil kd ext ext nil nil nil committed nil (fn-ptx-geo m) nil) done 1)))))
(verify-guards fn-ptx-end)

; The kernel projection after the barrier's :ok and the acknowledgement
; (fn-lgk-fence then fn-lgk-finish-one of a batch of one): one more committed
; record, the chain head the new trailer, the frontier past the entry.
(defun fn-ptx-kd-commit (kd trailer elen)
  (declare (xargs :guard t))
  (fn-ptx-kd-mk (+ 1 (fn-ptx-kd-count kd)) trailer (+ (fn-ptx-kd-frontier kd) (nfix elen))
                (+ 1 (fn-ptx-kd-txid kd))
                (+ 1 (fn-ptx-kd-acked kd))))
(verify-guards fn-ptx-kd-commit)

; The entry's geometry for the current transaction.
(defun fn-ptx-alen (m)
  (declare (xargs :guard t)) (fn-ptx-cur-len (fn-ptx-cur m)))
(verify-guards fn-ptx-alen)
(defun fn-ptx-nspans (m)
  (declare (xargs :guard t)) (len (fn-ptx-spans m)))
(verify-guards fn-ptx-nspans)
(defun fn-ptx-span-n (i m)
  (declare (xargs :guard t)) (nfix (fn-rtc-get 2 (fn-rtc-get i (fn-ptx-spans m)))))
(verify-guards fn-ptx-span-n)
(defun fn-ptx-nmsg (m)
  (declare (xargs :guard t)) (fn-ptx-spans-len (fn-ptx-spans m)))
(verify-guards fn-ptx-nmsg)     ; with the trailer once hashed
(defun fn-ptx-elen (m)
  (declare (xargs :guard t)) (+ (fn-ptx-nmsg m) (nfix (fn-rtc-get 2 (fn-ptx-hs m)))))
(verify-guards fn-ptx-elen)
; The pwrite of span I of the entry at frontier FRONT: from its buffer at the
; view's generation, to the entry's offset of the span.
(defun fn-ptx-span-pwrite (i m front id inc fn-rtc-st)
  (declare (xargs :guard t :stobjs fn-rtc-st))
  (let* ((spans (fn-ptx-spans m)) (sp (fn-rtc-get i spans)) (h (nfix (fn-rtc-get 0 sp))))
    (fn-ptx-pwrite h (fn-ptx-gen h id inc fn-rtc-st) (fn-rtc-get 1 sp) (fn-rtc-get 2 sp)
                   (+ (nfix front) (fn-ptx-spans-len (take (nfix i) spans))))))
(verify-guards fn-ptx-span-pwrite)

(defun fn-ptx-atom (x)
  (declare (xargs :guard t)) (if (consp x) nil x))
(verify-guards fn-ptx-atom)
(defun fn-ptx-summary (ev)
  (declare (xargs :guard t))
  (list (fn-ptx-atom (fn-rtc-get 0 ev)) (fn-ptx-atom (fn-rtc-get 0 (fn-rtc-get 1 ev)))
        (fn-ptx-atom (fn-rtc-get 1 (fn-rtc-get 1 ev)))))
(verify-guards fn-ptx-summary)
(defun fn-ptx-evd+ (m ev)
  (declare (xargs :guard t)) (append (true-list-fix (fn-ptx-evd m)) (list (fn-ptx-summary ev))))
(verify-guards fn-ptx-evd+)

; The reading step.  The first acquires the two workspaces (b1 empty, b3 at the
; base); each searches the head in [pos, pos + w + 3) and feeds the octets before
; the head's end (or the window) to the acceptance, appending its suffix part to
; b3; at the head's end it ends the acceptance, writes b1 = frame header ++ chain
; field ++ PRE ++ INS, the suffix's head just below the base and its tail after the
; parts, then hashes.  W is an eighth of the quantum (at least a window): the
; search is charged W + 3, the feed its cost (at most 4(W + 3) + K), the suffix
; part written at most 2(W + 3) + K octets, so the step fits Q + C.
(defun fn-ptx-read-w (q)
  (declare (xargs :guard t)) (max *fn-ptx-window* (floor (nfix q) 8)))
(verify-guards fn-ptx-read-w)
(defun fn-ptx-write-nz (h g off octets)
  (declare (xargs :guard t))
  ; the workspace write of OCTETS at OFF, none when empty
  (if (consp octets) (list (list :write (nfix h) (nfix g) (nfix off) octets)) nil))
(verify-guards fn-ptx-write-nz)
(defun fn-ptx-read (m q id inc fn-rtc-st)
  (declare (xargs :guard t :stobjs fn-rtc-st))
  (mbe :logic (let* ((cur (fn-ptx-cur m)) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m))
         (bp (fn-ptx-cur-bp cur)) (len (fn-ptx-cur-len cur)) (pos (fn-ptx-cur-hoff cur))
         (lim (min len (fn-ptx-hmax m)))
         (w (fn-ptx-read-w q))
         (m0 (fn-ptx-chg m :committed nil))
         (fresh (not (consp (fn-ptx-b1 m))))
         (h1 (if fresh (fn-ptx-free 0 nil id inc fn-rtc-st) (fn-ptx-buf-h (fn-ptx-b1 m))))
         (h3 (if fresh (fn-ptx-free 0 h1 id inc fn-rtc-st) (fn-ptx-buf-h (fn-ptx-b3 m))))
         (g1 (if fresh (+ 1 (fn-ptx-gen h1 id inc fn-rtc-st)) (fn-ptx-buf-g (fn-ptx-b1 m))))
         (g3 (if fresh (+ 1 (fn-ptx-gen h3 id inc fn-rtc-st)) (fn-ptx-buf-g (fn-ptx-b3 m))))
         (off (if fresh *fn-ptx-sufhead-max* (fn-ptx-buf-len (fn-ptx-b3 m))))
         ;; acquired, b3 is zeroed below its base (a write may not start past a buffer's
         ;; fill), so the suffix's head can be written just below the base at the end
         (acq (if fresh (list (list :acquire h1) (list :acquire h3)
                              (list :write h3 g3 0 (fn-bs-zeros *fn-ptx-sufhead-max*)))
                nil))
         (e (fn-ptx-head-end bp pos (min lim (+ pos w 3)) id inc fn-rtc-st))
         (cost0 (+ w 3 (* 3 (fn-ptx-acc-out-max)) 64)))
    (if (not (and h1 h3))
        ;; no workspaces: refused before any log action
        (mv-let (m2 r2 c2) (fn-ptx-end m0 :refused kd ext nil nil id inc fn-rtc-st)
          (mv m2 r2 (+ cost0 c2)))
      (let* ((m1 (fn-ptx-chg m0 :b1 (list h1 g1 0 0) :b3 (list h3 g3 off *fn-ptx-sufhead-max*)))
             ;; a refusal in this step: the end over the state without workspaces, which
             ;; are released here at the generation they were acquired or held at (no
             ;; lease has ended on them while reading)
             (mr (fn-ptx-chg m0 :b1 nil :b3 nil))
             (rel (list (list :release h1 g1) (list :release h3 g3)))
             (nfeed (if e (- e pos) (if (< (+ pos w 3) lim) w 0))))
        (mv-let (a sp) (fn-ptx-acc-feed (fn-ptx-acc m) (fn-ptx-range bp pos nfeed id inc fn-rtc-st))
          (let ((off2 (+ off (len sp)))
                (cost (+ cost0 (nfix (fn-ptx-acc-feed-cost (fn-ptx-acc m) (fn-ptx-range bp pos nfeed id inc fn-rtc-st))))))
            (cond
             ((not (<= (+ off2 32) (fn-ptx-cap h3 id inc fn-rtc-st)))
              ;; the suffix outgrows its workspace: refused before any log action
              (mv-let (m2 r2 c2) (fn-ptx-end mr :refused kd ext nil nil id inc fn-rtc-st)
                (mv m2 (append acq rel r2) (+ cost c2))))
             (e
              (mv-let (ok pre ins ioff sh st) (fn-ptx-acc-end a (- len e))
                (let* ((ioff (if (consp ins) (nfix ioff) len))
                       (start (- *fn-ptx-sufhead-max* (min (len sh) *fn-ptx-sufhead-max*)))
                       (end (+ off2 (len st)))
                       (rlen (+ (len pre) len (len ins) (- end start)))
                       (b1 (append (fn-ptx-frame-header rlen) (fn-ptx-kd-last kd) pre)))
                  (if (not (and ok (<= ioff len) (<= (+ 32 rlen) (fn-ptx-fmax m))
                                (<= (+ (len b1) (len ins)) (fn-ptx-cap h1 id inc fn-rtc-st))
                                (<= (+ end 32) (fn-ptx-cap h3 id inc fn-rtc-st))))
                      (mv-let (m2 r2 c2) (fn-ptx-end mr :refused kd ext nil nil id inc fn-rtc-st)
                        (mv m2 (append acq rel r2) (+ cost c2)))
                    (mv (fn-ptx-chg m1 :ph :hashing :k 0
                                    :cur (list (fn-ptx-cur-fid cur) (fn-ptx-cur-finc cur) bp len e (fn-ptx-cur-txid cur) ioff)
                                    :b1 (list h1 g1 (len b1) (len ins)) :b3 (list h3 g3 end start) :hs (list 0 nil) :acc nil)
                        (append acq (list (list :write h1 g1 0 (append b1 ins)))
                                (fn-ptx-write-nz h3 g3 start (take (- *fn-ptx-sufhead-max* start) sh))
                                (fn-ptx-write-nz h3 g3 off sp) (fn-ptx-write-nz h3 g3 off2 st)
                                (list (fn-ptx-timer)))
                        cost)))))
             ((< (+ pos w 3) lim)
              ;; no head end yet: the window fed, its suffix part written, continue
              (mv (fn-ptx-chg m1 :cur (list (fn-ptx-cur-fid cur) (fn-ptx-cur-finc cur) bp len (+ pos w) (fn-ptx-cur-txid cur) len)
                              :b3 (list h3 g3 off2 *fn-ptx-sufhead-max*) :acc a)
                  (append acq (fn-ptx-write-nz h3 g3 off sp) (list (fn-ptx-timer)))
                  cost))
             (t
              ;; no head within the head limit: refused before any log action
              (mv-let (m2 r2 c2) (fn-ptx-end mr :refused kd ext nil nil id inc fn-rtc-st)
                (mv m2 (append acq rel r2) (+ cost c2))))))))))
       :exec (let* ((cur (fn-ptx-cur m)) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m))
         (bp (fn-ptx-cur-bp cur)) (len (fn-ptx-cur-len cur)) (pos (fn-ptx-cur-hoff cur))
         (lim (min len (fn-ptx-hmax m)))
         (w (fn-ptx-read-w q))
         (m0 (fn-ptx-chg m :committed nil))
         (fresh (not (consp (fn-ptx-b1 m))))
         (h1 (if fresh (fn-ptx-free 0 nil id inc fn-rtc-st) (fn-ptx-buf-h (fn-ptx-b1 m))))
         (h3 (if fresh (fn-ptx-free 0 h1 id inc fn-rtc-st) (fn-ptx-buf-h (fn-ptx-b3 m))))
         (g1 (if fresh (+ 1 (fn-ptx-gen h1 id inc fn-rtc-st)) (fn-ptx-buf-g (fn-ptx-b1 m))))
         (g3 (if fresh (+ 1 (fn-ptx-gen h3 id inc fn-rtc-st)) (fn-ptx-buf-g (fn-ptx-b3 m))))
         (off (if fresh *fn-ptx-sufhead-max* (fn-ptx-buf-len (fn-ptx-b3 m))))
         ;; acquired, b3 is zeroed below its base (a write may not start past a buffer's
         ;; fill), so the suffix's head can be written just below the base at the end
         (acq (if fresh (list (list :acquire h1) (list :acquire h3)
                              (list :write h3 g3 0 (fn-bs-zeros *fn-ptx-sufhead-max*)))
                nil))
         (e (fn-ptx-head-end bp pos (min lim (+ pos w 3)) id inc fn-rtc-st))
         (cost0 (+ w 3 (* 3 (fn-ptx-acc-out-max)) 64)))
    (if (not (and h1 h3))
        ;; no workspaces: refused before any log action
        (mv-let (m2 r2 c2) (fn-ptx-end m0 :refused kd ext nil nil id inc fn-rtc-st)
          (mv m2 r2 (+ cost0 c2)))
      (let* ((m1 (fn-ptx-chg m0 :b1 (list h1 g1 0 0) :b3 (list h3 g3 off *fn-ptx-sufhead-max*)))
             ;; a refusal in this step: the end over the state without workspaces, which
             ;; are released here at the generation they were acquired or held at (no
             ;; lease has ended on them while reading)
             (mr (fn-ptx-chg m0 :b1 nil :b3 nil))
             (rel (list (list :release h1 g1) (list :release h3 g3)))
             (nfeed (if e (- e pos) (if (< (+ pos w 3) lim) w 0))))
        (mv-let (a sp) (fn-ptx-acc-feed (fn-ptx-acc m) (fn-ptx-range bp pos nfeed id inc fn-rtc-st))
          (let ((off2 (+ off (len sp)))
                (cost (+ cost0 (nfix (fn-ptx-acc-feed-cost (fn-ptx-acc m) (fn-ptx-range bp pos nfeed id inc fn-rtc-st))))))
            (cond
             ((not (<= (+ off2 32) (fn-ptx-cap h3 id inc fn-rtc-st)))
              ;; the suffix outgrows its workspace: refused before any log action
              (mv-let (m2 r2 c2) (fn-ptx-end mr :refused kd ext nil nil id inc fn-rtc-st)
                (mv m2 (append acq rel r2) (+ cost c2))))
             (e
              (mv-let (ok pre ins ioff sh st) (fn-ptx-acc-end a (- len e))
                (let* ((ioff (if (consp ins) (nfix ioff) len))
                       (start (- *fn-ptx-sufhead-max* (min (len sh) *fn-ptx-sufhead-max*)))
                       (end (+ off2 (len st)))
                       (rlen (+ (len pre) len (len ins) (- end start)))
                       (b1 (append (fn-ptx-frame-header rlen) (true-list-fix (fn-ptx-kd-last kd)) pre)))
                  (if (not (and ok (<= ioff len) (<= (+ 32 rlen) (fn-ptx-fmax m))
                                (<= (+ (len b1) (len ins)) (fn-ptx-cap h1 id inc fn-rtc-st))
                                (<= (+ end 32) (fn-ptx-cap h3 id inc fn-rtc-st))))
                      (mv-let (m2 r2 c2) (fn-ptx-end mr :refused kd ext nil nil id inc fn-rtc-st)
                        (mv m2 (append acq rel r2) (+ cost c2)))
                    (mv (fn-ptx-chg m1 :ph :hashing :k 0
                                    :cur (list (fn-ptx-cur-fid cur) (fn-ptx-cur-finc cur) bp len e (fn-ptx-cur-txid cur) ioff)
                                    :b1 (list h1 g1 (len b1) (len ins)) :b3 (list h3 g3 end start) :hs (list 0 nil) :acc nil)
                        (append acq (list (list :write h1 g1 0 (append b1 ins)))
                                (fn-ptx-write-nz h3 g3 start (take (- *fn-ptx-sufhead-max* start) sh))
                                (fn-ptx-write-nz h3 g3 off sp) (fn-ptx-write-nz h3 g3 off2 st)
                                (list (fn-ptx-timer)))
                        cost)))))
             ((< (+ pos w 3) lim)
              ;; no head end yet: the window fed, its suffix part written, continue
              (mv (fn-ptx-chg m1 :cur (list (fn-ptx-cur-fid cur) (fn-ptx-cur-finc cur) bp len (+ pos w) (fn-ptx-cur-txid cur) len)
                              :b3 (list h3 g3 off2 *fn-ptx-sufhead-max*) :acc a)
                  (append acq (fn-ptx-write-nz h3 g3 off sp) (list (fn-ptx-timer)))
                  cost))
             (t
              ;; no head within the head limit: refused before any log action
              (mv-let (m2 r2 c2) (fn-ptx-end mr :refused kd ext nil nil id inc fn-rtc-st)
                (mv m2 (append acq rel r2) (+ cost c2))))))))))))
(local (defthm fn-ptx-guard-append-fix
  (equal (append (true-list-fix x) y) (append x y))
  :hints (("Goal" :in-theory (enable binary-append true-list-fix)))))
(local (defthm fn-ptx-guard-head-end-natp
  (or (null (fn-ptx-head-end h i lim id inc st))
      (natp (fn-ptx-head-end h i lim id inc st)))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-ptx-head-end h i lim id inc st)
           :in-theory (e/d (fn-ptx-head-end) (fn-ptx-byte))))))
(local (defthm fn-ptx-guard-gen-natp
  (natp (fn-ptx-gen h id inc st))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-ptx-gen fn-rtc-st-v-gen fn-rtc-b-gen)))))
(local (defthm fn-ptx-guard-frame-header-listp
  (true-listp (fn-ptx-frame-header rlen))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (fn-ptx-frame-header fn-frame-header fn-cbor-u32-bytes)
                                  (floor mod))))))
(local (defthm fn-ptx-guard-feed-listp
  (true-listp (mv-nth 1 (fn-ptx-acc-feed a octets)))
  :hints (("Goal" :use fn-ptx-acc-feed-shape))))
(local (defthm fn-ptx-guard-end-listp
  (and (true-listp (mv-nth 1 (fn-ptx-acc-end a blen)))
       (true-listp (mv-nth 2 (fn-ptx-acc-end a blen)))
       (true-listp (mv-nth 4 (fn-ptx-acc-end a blen)))
       (true-listp (mv-nth 5 (fn-ptx-acc-end a blen))))
  :hints (("Goal" :use fn-ptx-acc-end-shape))))
(local (defthm fn-ptx-guard-end-cost-natp
  (natp (mv-nth 2 (fn-ptx-end m o kd ext fenced committed id inc st)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (fn-ptx-end fn-ptx-start)
                                  (fn-ptx-mk fn-ptx-answer fn-ptx-release-bufs
                                   fn-ptx-refuse-all fn-ptx-cur fn-ptx-q fn-ptx-geo
                                   fn-rtc-get))))))
(verify-guards fn-ptx-read
  :hints (("Goal" :in-theory (disable fn-ptx-end fn-ptx-mk fn-ptx-start
                                     fn-ptx-head-end fn-ptx-range fn-ptx-free fn-ptx-gen
                                     fn-ptx-frame-header fn-ptx-cap fn-rtc-get
                                     fn-ptx-ph fn-ptx-k fn-ptx-cur fn-ptx-q fn-ptx-kd
                                     fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs
                                     fn-ptx-committedp fn-ptx-evd fn-ptx-geo fn-ptx-acc
                                     fn-ptx-cur-fid fn-ptx-cur-finc fn-ptx-cur-bp
                                     fn-ptx-cur-len fn-ptx-cur-hoff fn-ptx-cur-txid
                                     fn-ptx-buf-h fn-ptx-buf-g fn-ptx-buf-len fn-ptx-buf-x
                                     fn-ptx-hmax fn-ptx-fmax fn-ptx-kd-last fn-ptx-read-w
                                     fn-ptx-write-nz fn-ptx-timer binary-append true-list-fix
                                     min max nfix mv-nth))))

; The hashing step: up to NW windows, then the trailer and fn-ptd's begin.
(defun fn-ptx-hash (m q id inc fn-rtc-st)
  (declare (xargs :guard t :stobjs fn-rtc-st))
  (let* ((kd (fn-ptx-kd m)) (ext (fn-ptx-ext m))
         (b3 (fn-ptx-b3 m)) (spans (fn-ptx-spans m))
         (nmsg (fn-ptx-spans-len spans)) (hs (fn-ptx-hs m))
         (nw (min *fn-ptx-nw-max* (max 1 (floor (nfix q) *fn-ptx-window*))))
         (m0 (fn-ptx-chg m :committed nil)))
    (mv-let (pos st)
      (fn-ptx-absorb nw (fn-rtc-get 0 hs) (fn-rtc-get 1 hs) nmsg spans id inc fn-rtc-st)
      (if (< (+ pos *fn-ptx-window*) nmsg)
          (mv (fn-ptx-chg m0 :hs (list pos st)) (list (fn-ptx-timer)) (* nw *fn-ptx-window*))
        ;; the last window: the trailer, then fn-ptd's begin.  The padding is not
        ;; written: the extent past the frontier reads zeros (fn-lgk-relp clause 2).
        (let* ((trailer (fn-ptx-finish-digest pos st nmsg spans id inc fn-rtc-st))
               (pad (fn-ptx-pad-len (+ nmsg 32) (fn-ptx-unit m)))
               (b3x (list (fn-ptx-buf-h b3) (fn-ptx-buf-g b3) (+ (fn-ptx-buf-len b3) 32) (fn-ptx-buf-x b3)))
               (elen (+ nmsg 32 pad))
               (front (fn-ptx-kd-frontier kd))
               (wr (list :write (fn-ptx-buf-h b3) (fn-ptx-buf-g b3) (fn-ptx-buf-len b3) trailer))
               (cost (+ (* nw *fn-ptx-window*) *fn-ptx-window* 32)))
          (if (fn-olr-extension-needed-p front elen ext (fn-ptx-unit m))
              (let ((nx (fn-olr-extension-target front elen ext (fn-ptx-unit m))))
                (if (<= (expt 2 64) nx)
                    ;; past the extent's bound (A's :extend takes naturals below 2^64,
                    ;; a larger request is refused with no completion): refused, no log action
                    (mv-let (m2 r2 c2) (fn-ptx-end m0 :refused kd ext nil nil id inc fn-rtc-st)
                      (mv m2 (cons wr r2) (+ cost c2)))
                (mv (fn-ptx-chg m0 :ph :extending :k 0 :nxt nx :b3 b3x :hs (list nmsg trailer pad) :evd nil)
                    (list wr (fn-ptx-extend ext nx)) cost)))
            (let ((m1 (fn-ptx-chg m0 :ph :payload-writing :k 0 :nxt ext :b3 b3x :hs (list nmsg trailer pad) :evd nil)))
              (mv m1 (list wr (fn-ptx-span-pwrite 0 m1 front id inc fn-rtc-st)) cost))))))))
(local (defthm fn-ptx-guard-absorb-pos-natp
  (natp (mv-nth 0 (fn-ptx-absorb nw pos st n spans id inc pool)))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-ptx-absorb nw pos st n spans id inc pool)
           :in-theory (e/d (fn-ptx-absorb)
                           (fn-b3-cv-push fn-b3-node fn-ptx-msg-range))))))
(verify-guards fn-ptx-hash
  :hints (("Goal" :in-theory (disable fn-ptx-end fn-ptx-mk fn-ptx-absorb
                                     fn-ptx-finish-digest fn-ptx-spans fn-ptx-spans-len
                                     fn-ptx-pad-len fn-ptx-unit fn-ptx-span-pwrite
                                     fn-ptx-ph fn-ptx-k fn-ptx-cur fn-ptx-q fn-ptx-kd
                                     fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs
                                     fn-ptx-committedp fn-ptx-evd fn-ptx-geo fn-ptx-acc
                                     fn-ptx-buf-h fn-ptx-buf-g fn-ptx-buf-len fn-ptx-buf-x
                                     fn-ptx-kd-frontier fn-rtc-get
                                     fn-olr-extension-needed-p fn-olr-extension-target
                                     min max floor nfix mv-nth))))

; The step on a well-formed state: (mv m2 requests cost).
(defun fn-ptx-step1 (m ev fn-rtc-st q)
  (declare (xargs :guard t :stobjs fn-rtc-st))
  (let* ((id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev))
         (kind (fn-rtc-get 0 ev)) (out (fn-rtc-get 1 ev)) (tag (fn-rtc-get 0 out)) (n (fn-rtc-get 1 out))
         (ph (fn-ptx-ph m)) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m)) (nxt (fn-ptx-nxt m))
         (m0 (fn-ptx-chg m :committed nil)))
    (cond
     ;; the store opened: the kernel projection, the extent and the geometry
     ((eq kind :opened)
      (if (and (eq ph :closed) (eq tag :done))
          ;; an open whose projection does not fit the budgets, or whose frame
          ;; bound exceeds the frame's u32 length field (*fn-frame-max-payload*: the log's
          ;; take admits no record past it), leaves the owner closed
          (let* ((d (fn-rtc-ev-opened-data ev))
                 (m1 (fn-ptx-opened (fn-rtc-get 0 d) (nfix (fn-rtc-get 1 d)) (fn-rtc-get 2 d))))
            (if (and (fn-ptx-wfp m1) (<= (fn-ptx-fmax m1) *fn-frame-max-payload*)
                     (equal (len (fn-ptx-kd-last (fn-ptx-kd m1))) 32))
                (mv m1 nil 1)
              (mv m0 nil 1)))
        (mv m0 nil 1)))
     ;; an article handed in: (:handed (:done 0) id inc fid finc (h g 0 len))
     ((eq kind :handed)
      (let* ((hd (fn-rtc-get 6 ev))
             (p (list (fn-ptx-atom (fn-rtc-get 4 ev)) (fn-ptx-atom (fn-rtc-get 5 ev)) (fn-rtc-h-buf hd) (fn-rtc-h-len hd))))
        (cond ((member-eq ph '(:fenced :closed)) (mv m0 (fn-ptx-answer p :refused id inc fn-rtc-st) 1))
              ((eq ph :idle) (fn-ptx-start p nil kd ext (fn-ptx-geo m) nil))
              ((< (len (fn-ptx-q m)) *fn-ptx-k*)
               (mv (fn-ptx-chg m0 :q (append (true-list-fix (fn-ptx-q m)) (list p))) nil 1))
              (t (mv m0 (fn-ptx-answer p :busy id inc fn-rtc-st) 1)))))
     ((and (eq ph :reading) (eq kind :timer)) (fn-ptx-read m q id inc fn-rtc-st))
     ((and (eq ph :hashing) (eq kind :timer)) (fn-ptx-hash m q id inc fn-rtc-st))
     ;; fn-ptd's extension (a failure refuses and fences: fn-ptd-complete's :extending arm)
     ((and (eq ph :extending) (eq kind :extend))
      (if (eq tag :done)
          (mv (fn-ptx-chg m0 :ph :extsyncing :evd (fn-ptx-evd+ m ev)) (list (fn-ptx-fsync)) 1)
        (fn-ptx-end m0 :refused kd ext t nil id inc fn-rtc-st)))
     ((and (eq ph :extsyncing) (eq kind :fsync))
      (if (eq tag :done)
          (let ((m1 (fn-ptx-chg m0 :ph :payload-writing :k 0 :evd (fn-ptx-evd+ m ev))))
            (mv m1 (list (fn-ptx-span-pwrite 0 m1 (fn-ptx-kd-frontier kd) id inc fn-rtc-st)) 1))
        (fn-ptx-end m0 :refused kd ext t nil id inc fn-rtc-st)))
     ;; the entry's writes, one per span (the last, b3's, the log-writing phase): any
     ;; outcome but the whole span is uncertain and fences
     ((and (eq ph :payload-writing) (eq kind :pwrite))
      (let ((k (fn-ptx-k m)) (front (fn-ptx-kd-frontier kd)))
        (cond ((not (and (eq tag :done) (equal n (fn-ptx-span-n k m))))
               (fn-ptx-end m0 :uncertain kd ext t nil id inc fn-rtc-st))
              (t
               (let ((m1 (fn-ptx-chg m0 :ph (if (< (+ k 2) (fn-ptx-nspans m)) :payload-writing :log-writing)
                                     :k (+ k 1) :evd (fn-ptx-evd+ m ev))))
                 (mv m1 (list (fn-ptx-span-pwrite (+ k 1) m1 front id inc fn-rtc-st)) 1))))))
     ((and (eq ph :log-writing) (eq kind :pwrite))
      (if (and (eq tag :done) (equal n (fn-ptx-span-n (fn-ptx-k m) m)))
          (mv (fn-ptx-chg m0 :ph :committing :evd (fn-ptx-evd+ m ev)) (list (fn-ptx-fsync)) 1)
        (fn-ptx-end m0 :uncertain kd ext t nil id inc fn-rtc-st)))
     ((and (eq ph :committing) (eq kind :fsync))
      (if (eq tag :done)
          ;; THE COMMIT POINT: the log barrier's completion
          (fn-ptx-end m0 :posted (fn-ptx-kd-commit kd (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-elen m)) nxt nil t
                      id inc fn-rtc-st)
        (fn-ptx-end m0 :uncertain kd ext t nil id inc fn-rtc-st)))
     ;; an answer's hand that came back (the poster gone): release the buffer
     ((eq kind :hand)
      (let ((hd (fn-rtc-get 4 ev)))
        (mv m0 (if (fn-rtc-handlep hd) (list (list :release (fn-rtc-h-buf hd) (fn-rtc-h-gen hd))) nil) 1)))
     (t (mv m0 nil 1)))))
(verify-guards fn-ptx-step1)

; The step: the shape check, then the machine.  (mv m2 requests cost).
(defun fn-ptx-step (m ev fn-rtc-st q)
  (declare (xargs :guard t :stobjs fn-rtc-st))
  (if (fn-ptx-wfp m)
      (mv-let (m2 reqs cost) (fn-ptx-step1 m ev fn-rtc-st q)
        (mv m2 reqs (+ (fn-ptx-wf-cost) (nfix cost))))
    (mv (fn-ptx-broken) nil (fn-ptx-wf-cost))))
(verify-guards fn-ptx-step)

; The layer's bounds for this machine: the charge's constant part (the shape
; check, a window's search slack and the trailer, the workspaces' writes), the
; requests one step may make (an end refusing a full queue), and the state's
; size (every field at its budget plus one step's growth: a post queued, a
; completion's summary, NW-MAX digest windows).
(defun fn-ptx-c ()
  (declare (xargs :guard t)) (+ (fn-ptx-wf-cost) (* 8 *fn-ptx-window*) 1024 (* 10 (fn-ptx-acc-out-max))))
(verify-guards fn-ptx-c)
(defun fn-ptx-max-reqs ()
  (declare (xargs :guard t)) 32)
(verify-guards fn-ptx-max-reqs)
(defun fn-ptx-max-state ()
  (declare (xargs :guard t)) (+ 8500 (fn-ptx-acc-max-state)))
(verify-guards fn-ptx-max-state)

; -----------------------------------------------------------------------------
; The keystones' predicates (packet draft 3).  Each keystone is a theorem over
; fn-ptx-step stated with these; the scratch sweeps evaluate their generated
; list twins (fn-ptxl-*) after every owner completion.

(defun fn-ptx-done-p (x kind n)
  (and (equal (fn-rtc-get 0 x) kind) (equal (fn-rtc-get 1 x) :done) (or (null n) (equal (fn-rtc-get 2 x) n))))

; The evidence a :posted answer rests on: [extend fsync], one pwrite per span of
; the entry, each :done and whole, in span order, then the barrier's fsync.
(defun fn-ptx-strip-ext (evd)
  (if (and (fn-ptx-done-p (fn-rtc-get 0 evd) :extend nil) (fn-ptx-done-p (fn-rtc-get 1 evd) :fsync nil))
      (cddr evd)
    evd))
(defun fn-ptx-spans-evd-p (evd spans)
  ; each completion :done and whole for the span at its index
  (if (consp evd)
      (and (consp spans)
           (fn-ptx-done-p (car evd) :pwrite (nfix (fn-rtc-get 2 (car spans))))
           (fn-ptx-spans-evd-p (cdr evd) (cdr spans)))
    t))
(defun fn-ptx-entry-evd-p (evd m nwrites)
  ; NWRITES completed entry writes, the first NWRITES spans' in order
  (and (true-listp evd) (equal (len evd) (nfix nwrites))
       (fn-ptx-spans-evd-p evd (fn-ptx-spans m))))
(defun fn-ptx-posted-evidence-p (evd m)
  (let ((e (fn-ptx-strip-ext evd)) (n (fn-ptx-nspans m)))
    (and (equal (len e) (+ 1 n))
         (fn-ptx-entry-evd-p (take n e) m n)
         (fn-ptx-done-p (fn-rtc-get n e) :fsync nil))))

; The digest's held stack over C windows: its entries' heights are C's set bits,
; lowest first, from height H; each entry (height out) at most 63 words.
(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm fn-ptx-floor-2-smaller
    (implies (and (integerp c) (< 0 c)) (and (natp (floor c 2)) (< (floor c 2) c)))
    :rule-classes nil))
(defun fn-ptx-stack-bits-p (st c h)
  (declare (xargs :measure (nfix c) :hints (("Goal" :use ((:instance fn-ptx-floor-2-smaller))))))
  (if (zp c)
      (null st)
    (if (oddp c)
        (and (consp st)
             (equal (nfix (fn-b3-nthx 0 (car st))) (nfix h))
             (<= (fn-rtc-size (car st)) 63)
             (fn-ptx-stack-bits-p (cdr st) (floor c 2) (+ 1 (nfix h))))
      (fn-ptx-stack-bits-p st (floor c 2) (+ 1 (nfix h))))))

; P0: the invariant.  Well formed; the frame bound within the frame's length field;
; the chain field 32 octets while open; the evidence is
; what the phase says (the extension's two completions first when there was
; one); while hashing, the held stack is the binary counter of the windows
; absorbed and the message is within the frame bound; the workspaces' shape and the
; trailer's length (d9: Sonnet 4's two counterexamples, a short trailer becoming the chain
; field at the commit and an empty b1 or inverted b3 leaving one span at :payload-writing); the shapes of the queue, the evidence, the
; current post and the trailer (d10: three more of Sonnet 4's, fields that fit their
; budgets as a whole but outgrow another field's budget when the step moves them).
; Shapes the step keeps (d10): a list of atoms; the waiting posts, each (fid finc bp len);
; the evidence's summaries, each (kind tag n).
(defun fn-ptx-atoms-p (x) (if (consp x) (and (atom (car x)) (fn-ptx-atoms-p (cdr x))) (null x)))
(defun fn-ptx-rows-p (x n)
  (if (consp x) (and (fn-ptx-atoms-p (car x)) (equal (len (car x)) n) (fn-ptx-rows-p (cdr x) n)) (null x)))
(defun fn-ptx-okp (m)
  (let* ((ph (fn-ptx-ph m)) (evd (fn-ptx-evd m)) (rest (fn-ptx-strip-ext evd))
         (hs (fn-ptx-hs m)) (pos (fn-rtc-get 0 hs))
         (nmsg (fn-ptx-nmsg m)) (k (fn-ptx-k m)) (n (fn-ptx-nspans m)))
    (and (fn-ptx-wfp m)
         (<= (fn-ptx-fmax m) *fn-frame-max-payload*)
         (or (member-eq ph '(:closed :fenced)) (equal (len (fn-ptx-kd-last (fn-ptx-kd m))) 32))
         (case ph
           ((:closed :idle :reading :hashing :extending :fenced) (null evd))
           (:extsyncing (and (true-listp evd) (equal (len evd) 1) (fn-ptx-done-p (car evd) :extend nil)))
           (:payload-writing (and (< (+ k 1) n) (fn-ptx-entry-evd-p rest m k)))
           (:log-writing (and (equal (+ k 1) n) (fn-ptx-entry-evd-p rest m k)))
           (:committing (fn-ptx-entry-evd-p rest m n))
           (otherwise nil))
         ;; the workspaces' shape: b3 holds the suffix's head below its base while reading;
         ;; b1 is not empty and b3 ends at or past its start while hashing; the entry has at
         ;; least b1's span and b3's while extending; the trailer is 32 octets once hashed
         (implies (and (equal ph :reading) (consp (fn-ptx-b1 m)))
                  (<= *fn-ptx-sufhead-max* (fn-ptx-buf-len (fn-ptx-b3 m))))
         (implies (equal ph :hashing)
                  (and (< 0 (fn-ptx-buf-len (fn-ptx-b1 m)))
                       (<= (fn-ptx-buf-x (fn-ptx-b3 m)) (fn-ptx-buf-len (fn-ptx-b3 m)))))
         (implies (member-eq ph '(:extending :extsyncing)) (<= 2 n))
         (implies (member-eq ph '(:extending :extsyncing :payload-writing :log-writing :committing))
                  (and (fn-ptx-atoms-p (fn-rtc-get 1 hs)) (equal (len (fn-rtc-get 1 hs)) 32)))
         (fn-ptx-rows-p (fn-ptx-q m) 4)
         (<= (len (fn-ptx-q m)) *fn-ptx-k*)
         (fn-ptx-rows-p evd 3)
         (implies (member-eq ph '(:reading :hashing :extending :extsyncing :payload-writing :log-writing :committing))
                  (and (fn-ptx-atoms-p (fn-ptx-cur m)) (equal (len (fn-ptx-cur m)) 7)))
         (implies (equal ph :hashing)
                  (and (natp pos) (equal (mod pos *fn-ptx-window*) 0) (< pos nmsg)
                       (<= nmsg (+ 10 (fn-ptx-fmax m)))
                       (fn-ptx-stack-bits-p (fn-rtc-get 1 hs) (floor pos *fn-ptx-window*) 0))))))

; The answers in a request list: a one-octet write at offset 0 of buffer h
; immediately followed by the :hand of that buffer (fn-ptx-answer's pair); a write
; not handed back (a workspace's) is no answer.  ((h code) ...).
(defun fn-ptx-codes-to (reqs)
  (if (consp reqs)
      (let ((r (car reqs)) (nx (cadr reqs)))
        (if (and (eq (fn-rtc-get 0 r) :write) (equal (fn-rtc-get 3 r) 0) (equal (len (fn-rtc-get 4 r)) 1)
                 (eq (fn-rtc-get 0 nx) :submit) (eq (fn-rtc-get 1 nx) :hand)
                 (equal (fn-rtc-get 0 (fn-rtc-get 2 nx)) (fn-rtc-get 1 r)))
            (cons (list (fn-rtc-get 1 r) (car (fn-rtc-get 4 r))) (fn-ptx-codes-to (cdr reqs)))
          (fn-ptx-codes-to (cdr reqs))))
    nil))
(defun fn-ptx-code-for (h codes) (cadr (assoc-equal h codes)))
(defun fn-ptx-cur-code (m reqs)
  (and (consp (fn-ptx-cur m)) (fn-ptx-code-for (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-codes-to reqs))))

; P1: the commit point is the log barrier's completion (no hypothesis).
(defun fn-ptx-p1 (m ev fn-rtc-st q)
  (declare (xargs :stobjs fn-rtc-st))
  (mv-let (m2 reqs c) (fn-ptx-step m ev fn-rtc-st q)
    (declare (ignore reqs c))
    (implies (and (not (fn-ptx-committedp m)) (fn-ptx-committedp m2))
             (and (equal (fn-ptx-ph m) :committing) (fn-rtc-fsync-done-p ev)))))

; P2: AckEligible => DurableCommitEvidence: the :posted code for the current post
; only with the whole entry's completions and then this barrier's, in order.
(defun fn-ptx-p2 (m ev fn-rtc-st q)
  (declare (xargs :stobjs fn-rtc-st))
  (mv-let (m2 reqs c) (fn-ptx-step m ev fn-rtc-st q)
    (declare (ignore m2 c))
    (implies (and (fn-ptx-okp m) (equal (fn-ptx-cur-code m reqs) 0))
             (fn-ptx-posted-evidence-p (append (fn-ptx-evd m) (list (fn-ptx-summary ev))) m))))

; P3: progress.  The work left, in steps: per post at most B (the reading at the
; head limit, the hashing at the frame bound, at most eight log actions: the
; extension, its barrier, five spans, the barrier); a completion of the kind the
; phase waits for lowers it.
(defun fn-ptx-post-bound (m)
  (+ 11 (ceiling (fn-ptx-hmax m) *fn-ptx-window*) (ceiling (+ 10 (fn-ptx-fmax m)) *fn-ptx-window*)))
(defun fn-ptx-rem (m)
  (let* ((ph (fn-ptx-ph m)) (nmsg (fn-ptx-nmsg m))
         (hashb (+ 10 (ceiling (+ 10 (fn-ptx-fmax m)) *fn-ptx-window*))))
    (case ph
      (:reading (+ hashb 1 (ceiling (nfix (- (min (fn-ptx-alen m) (fn-ptx-hmax m)) (fn-ptx-cur-hoff (fn-ptx-cur m))))
                                    *fn-ptx-window*)))
      (:hashing (+ 9 1 (ceiling (nfix (- nmsg (nfix (fn-rtc-get 0 (fn-ptx-hs m))))) *fn-ptx-window*)))
      (:extending 8) (:extsyncing 7) (:payload-writing (nfix (- (+ 1 (fn-ptx-nspans m)) (fn-ptx-k m))))
      (:log-writing 2) (:committing 1)
      (otherwise 0))))
(defun fn-ptx-measure (m) (+ (* (len (fn-ptx-q m)) (fn-ptx-post-bound m)) (fn-ptx-rem m)))
(defun fn-ptx-expected (m)
  (case (fn-ptx-ph m) ((:reading :hashing) :timer) (:extending :extend) (:extsyncing :fsync)
    ((:payload-writing :log-writing) :pwrite) (:committing :fsync) (otherwise nil)))
(defun fn-ptx-p3 (m ev fn-rtc-st q)
  (declare (xargs :stobjs fn-rtc-st))
  (mv-let (m2 reqs c) (fn-ptx-step m ev fn-rtc-st q)
    (declare (ignore reqs c))
    (implies (and (fn-ptx-okp m) (fn-ptx-expected m) (eq (fn-rtc-get 0 ev) (fn-ptx-expected m)))
             (< (fn-ptx-measure m2) (fn-ptx-measure m)))))

; P5: uncertainty is named: :uncertain only from the first entry write on, and
; the machine is then :fenced; :refused for the current post never from then on.
(defun fn-ptx-p5 (m ev fn-rtc-st q)
  (declare (xargs :stobjs fn-rtc-st))
  (mv-let (m2 reqs c) (fn-ptx-step m ev fn-rtc-st q)
    (declare (ignore c))
    (let ((code (fn-ptx-cur-code m reqs)))
      (and (implies (equal code 2) (and (member-eq (fn-ptx-ph m) '(:payload-writing :log-writing :committing))
                                        (equal (fn-ptx-ph m2) :fenced)))
           (implies (equal code 1) (not (member-eq (fn-ptx-ph m) '(:payload-writing :log-writing :committing))))))))

; -----------------------------------------------------------------------------
; Proofs (Sonnet 3, Sonnet 4)
; The layer's :reads-view lemma, bottom-up: every function of the step that takes
; the stobj reads it only through the view readers (fn-rtc-v-readers-of-view-state).
(defthm fn-ptx-byte-reads-view
  (equal (fn-ptx-byte h i id inc (fn-rtc-view-state id inc st)) (fn-ptx-byte h i id inc st))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-byte fn-rtc-v-readers-of-view-state)))))
(defthm fn-ptx-range-reads-view
  (equal (fn-ptx-range h i n id inc (fn-rtc-view-state id inc st)) (fn-ptx-range h i n id inc st)))
(defthm fn-ptx-gen-reads-view
  (equal (fn-ptx-gen h id inc (fn-rtc-view-state id inc st)) (fn-ptx-gen h id inc st)))
(defthm fn-ptx-cap-reads-view
  (equal (fn-ptx-cap h id inc (fn-rtc-view-state id inc st)) (fn-ptx-cap h id inc st)))
(defthm fn-ptx-head-end-reads-view
  (equal (fn-ptx-head-end h i lim id inc (fn-rtc-view-state id inc st)) (fn-ptx-head-end h i lim id inc st))
  :hints (("Goal" :in-theory (e/d ((:induction fn-ptx-head-end)) (fn-ptx-byte (:definition fn-ptx-head-end))) :induct (fn-ptx-head-end h i lim id inc st)
           :expand ((fn-ptx-head-end h i lim id inc (fn-rtc-view-state id inc st)) (fn-ptx-head-end h i lim id inc st)))))
(defthm fn-ptx-free-reads-view
  (equal (fn-ptx-free i skip id inc (fn-rtc-view-state id inc st)) (fn-ptx-free i skip id inc st))
  :hints (("Goal" :in-theory (disable fn-rtc-st-v-owner fn-rtc-st-config fn-rtc-nbufs))))
(defthm fn-ptx-msg-byte-reads-view
  (equal (fn-ptx-msg-byte i spans id inc (fn-rtc-view-state id inc st)) (fn-ptx-msg-byte i spans id inc st)))
(defthm fn-ptx-msg-range-reads-view
  (equal (fn-ptx-msg-range i n spans id inc (fn-rtc-view-state id inc st)) (fn-ptx-msg-range i n spans id inc st)))
(defthm fn-ptx-absorb-reads-view
  (equal (fn-ptx-absorb nw pos stk n spans id inc (fn-rtc-view-state id inc st)) (fn-ptx-absorb nw pos stk n spans id inc st)))
(defthm fn-ptx-finish-digest-reads-view
  (equal (fn-ptx-finish-digest pos stk n spans id inc (fn-rtc-view-state id inc st)) (fn-ptx-finish-digest pos stk n spans id inc st)))
(defthm fn-ptx-answer-reads-view
  (equal (fn-ptx-answer p o id inc (fn-rtc-view-state id inc st)) (fn-ptx-answer p o id inc st)))
(defthm fn-ptx-release-bufs-reads-view
  (equal (fn-ptx-release-bufs m id inc (fn-rtc-view-state id inc st)) (fn-ptx-release-bufs m id inc st)))
(defthm fn-ptx-refuse-all-reads-view
  (equal (fn-ptx-refuse-all q id inc (fn-rtc-view-state id inc st)) (fn-ptx-refuse-all q id inc st)))
(defthm fn-ptx-span-pwrite-reads-view
  (equal (fn-ptx-span-pwrite i m front id inc (fn-rtc-view-state id inc st)) (fn-ptx-span-pwrite i m front id inc st))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-span-pwrite fn-ptx-gen-reads-view)))))
(defthm fn-ptx-end-reads-view
  (equal (fn-ptx-end m o kd ext fenced committed id inc (fn-rtc-view-state id inc st)) (fn-ptx-end m o kd ext fenced committed id inc st))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
            '(fn-ptx-end fn-ptx-answer-reads-view fn-ptx-refuse-all-reads-view fn-ptx-release-bufs-reads-view)))))
(defthm fn-ptx-read-reads-view
  (equal (fn-ptx-read m q id inc (fn-rtc-view-state id inc st)) (fn-ptx-read m q id inc st))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
            '(fn-ptx-read fn-ptx-end-reads-view fn-ptx-head-end-reads-view fn-ptx-range-reads-view fn-ptx-free-reads-view
              fn-ptx-cap-reads-view fn-ptx-gen-reads-view)))))
(defthm fn-ptx-hash-reads-view
  (equal (fn-ptx-hash m q id inc (fn-rtc-view-state id inc st)) (fn-ptx-hash m q id inc st))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
            '(fn-ptx-hash fn-ptx-absorb-reads-view fn-ptx-finish-digest-reads-view fn-ptx-end-reads-view fn-ptx-span-pwrite-reads-view)))))
(defthm fn-ptx-step1-reads-view
  (equal (fn-ptx-step1 m ev (fn-rtc-view-state (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) st) q) (fn-ptx-step1 m ev st q))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
            '(fn-ptx-step1 fn-ptx-end-reads-view fn-ptx-read-reads-view fn-ptx-hash-reads-view fn-ptx-answer-reads-view
              fn-ptx-gen-reads-view fn-ptx-span-pwrite-reads-view)))))
(defthm fn-ptx-step-reads-view
  (equal (fn-ptx-step m ev (fn-rtc-view-state (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) st) q)
         (fn-ptx-step m ev st q))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
            '(fn-ptx-step fn-ptx-step1-reads-view)))))

(defthm fn-ptx-size-of-atom
  (implies (atom x) (equal (fn-rtc-size x) 1)))
(defthm fn-ptx-size-of-cons
  (equal (fn-rtc-size (cons a b)) (+ 1 (fn-rtc-size a) (fn-rtc-size b))))
(defthm fn-ptx-size-of-word-list
  (implies (fn-b3-word-listp xs) (equal (fn-rtc-size xs) (+ 1 (* 2 (len xs)))))
  :hints (("Goal" :in-theory (enable fn-b3-word-listp))))
(defthm fn-ptx-nthx-of-word-list
  (implies (fn-b3-word-listp xs) (atom (fn-b3-nthx n xs)))
  :hints (("Goal" :in-theory (enable fn-b3-word-listp fn-b3-nthx))))
(defthm fn-ptx-size-cv8
  (implies (fn-b3-word-listp cv) (equal (fn-rtc-size (fn-b3-cv8 cv)) 17))
  :hints (("Goal" :in-theory (enable fn-b3-cv8))))
(defthm fn-ptx-word-list-append
  (implies (and (fn-b3-word-listp a) (fn-b3-word-listp b)) (fn-b3-word-listp (append a b)))
  :hints (("Goal" :in-theory (enable fn-b3-word-listp))))
(defthm fn-ptx-iv-shape
  (and (fn-b3-word-listp *fn-b3-iv*) (equal (len *fn-b3-iv*) 8)))
(defthm fn-ptx-size-chunk
  (implies (and (fn-b3-word-listp cv) (atom counter))
           (equal (fn-rtc-size (fn-b3-chunk cv octets counter flags startp)) 59))
  :hints (("Goal" :in-theory (enable fn-b3-output) :induct (fn-b3-chunk cv octets counter flags startp))))
(defthm fn-ptx-size-node
  (implies (and (fn-b3-word-listp key) (equal (len key) 8) (atom counter))
           (equal (fn-rtc-size (fn-b3-node key octets counter flags)) 59))
  :hints (("Goal" :in-theory (e/d (fn-b3-output) (fn-b3-chunk)) :expand ((fn-b3-node key octets counter flags))
           :use ((:instance fn-b3-output-cv-shape (out (fn-b3-node key (fn-b3-firstn (* 1024 (fn-b3-left-chunks 1 (len octets))) octets) counter flags)))
                 (:instance fn-b3-output-cv-shape (out (fn-b3-node key (fn-b3-nthcdrx (* 1024 (fn-b3-left-chunks 1 (len octets))) octets) (+ (nfix counter) (fn-b3-left-chunks 1 (len octets))) flags)))))))
(defthm fn-ptx-size-parent-out
  (implies (and (fn-b3-word-listp key) (equal (len key) 8))
           (equal (fn-rtc-size (fn-b3-parent-out key lout rout flags)) 59))
  :hints (("Goal" :in-theory (e/d (fn-b3-parent-out fn-b3-output) nil)
           :use ((:instance fn-b3-output-cv-shape (out lout)) (:instance fn-b3-output-cv-shape (out rout))))))
(defthm fn-ptx-size-cv-push
  (implies (and (fn-b3-word-listp key) (equal (len key) 8) (<= (fn-rtc-size out) 59))
           (<= (fn-rtc-size (fn-b3-cv-push key flags h out st)) (+ 64 (fn-rtc-size st))))
  :hints (("Goal" :induct (fn-b3-cv-push key flags h out st))))
(defthm fn-ptx-size-push-node-c
  (implies (integerp c)
    (<= (fn-rtc-size (fn-b3-cv-push *fn-b3-iv* 0 w (fn-b3-node *fn-b3-iv* o c 0) st))
        (+ 64 (fn-rtc-size st))))
  :hints (("Goal" :use ((:instance fn-ptx-size-cv-push (key *fn-b3-iv*) (flags 0) (h w) (out (fn-b3-node *fn-b3-iv* o c 0)))
                        (:instance fn-ptx-size-node (key *fn-b3-iv*) (octets o) (counter c) (flags 0))
                        fn-ptx-iv-shape)
           :in-theory (disable fn-ptx-size-cv-push fn-ptx-size-node fn-b3-cv-push fn-b3-node)))
  :rule-classes :linear)
(defthm fn-ptx-absorb-st-size
  (<= (fn-rtc-size (mv-nth 1 (fn-ptx-absorb nw pos st n spans id inc fn-rtc-st)))
      (+ (* 64 (nfix nw)) (fn-rtc-size st)))
  :hints (("Goal" :induct (fn-ptx-absorb nw pos st n spans id inc fn-rtc-st)
           :in-theory (disable fn-b3-node fn-b3-cv-push fn-ptx-msg-range fn-ptx-size-cv-push fn-ptx-size-node))))
(defthm fn-ptx-finish-digest-shape
  (and (true-listp (fn-ptx-finish-digest pos st n spans id inc fn-rtc-st))
       (equal (len (fn-ptx-finish-digest pos st n spans id inc fn-rtc-st)) 32)
       (fn-b3-octet-listp (fn-ptx-finish-digest pos st n spans id inc fn-rtc-st)))
  :hints (("Goal" :in-theory (enable fn-ptx-finish-digest))))
(defthm fn-ptx-absorb-nat
  (implies (natp pos) (and (natp (mv-nth 0 (fn-ptx-absorb nw pos st n spans id inc fn-rtc-st)))
     (<= (mv-nth 0 (fn-ptx-absorb nw pos st n spans id inc fn-rtc-st)) (+ pos (* 1024 (nfix nw))))))
  :hints (("Goal" :induct (fn-ptx-absorb nw pos st n spans id inc fn-rtc-st)
           :in-theory (disable fn-b3-node fn-b3-cv-push fn-ptx-msg-range fn-ptx-size-cv-push fn-ptx-size-node))))
(defthm fn-ptx-size-rem-exact
  (implies (and (natp n) (fn-ptx-size-rem x n))
           (and (natp (fn-ptx-size-rem x n))
                (equal (fn-ptx-size-rem x n) (- n (fn-rtc-size x)))))
  :hints (("Goal" :induct (fn-ptx-size-rem x n))))
(defthm fn-ptx-size-rem-bound
  (implies (and (fn-ptx-size-rem x n) (natp n)) (<= (fn-rtc-size x) n))
  :rule-classes :linear
  :hints (("Goal" :use fn-ptx-size-rem-exact :in-theory (disable fn-ptx-size-rem-exact))))
(defthm fn-ptx-wfp-sizes
  (implies (fn-ptx-wfp m)
           (and (<= (fn-rtc-size (fn-ptx-ph m)) 1) (<= (fn-rtc-size (fn-rtc-get 1 m)) 1)
                (<= (fn-rtc-size (fn-ptx-cur m)) 15) (<= (fn-rtc-size (fn-ptx-q m)) 21)
                (<= (fn-rtc-size (fn-ptx-kd m)) 75) (<= (fn-rtc-size (fn-rtc-get 5 m)) 1)
                (<= (fn-rtc-size (fn-rtc-get 6 m)) 1) (<= (fn-rtc-size (fn-ptx-b1 m)) 9)
                (<= (fn-rtc-size (fn-ptx-b3 m)) 9) (<= (fn-rtc-size (fn-ptx-hs m)) 4101)
                (<= (fn-rtc-size (fn-rtc-get 10 m)) 1) (<= (fn-rtc-size (fn-ptx-evd m)) 57)
                (<= (fn-rtc-size (fn-ptx-geo m)) 7) (<= (fn-rtc-size (fn-ptx-acc m)) (fn-ptx-acc-max-state))))
  :hints (("Goal" :in-theory (enable fn-ptx-wfp fn-ptx-fields-fit) :do-not-induct t)))
(defthm fn-ptx-size-get
  (<= (fn-rtc-size (fn-rtc-get i x)) (fn-rtc-size x))
  :rule-classes :linear)
(defthm fn-ptx-size-append
  (<= (fn-rtc-size (append a b)) (+ (fn-rtc-size a) (fn-rtc-size b)))
  :rule-classes :linear)
(defthm fn-ptx-size-tlf
  (<= (fn-rtc-size (true-list-fix a)) (fn-rtc-size a))
  :rule-classes :linear)
(defthm fn-ptx-size-pos
  (<= 1 (fn-rtc-size x))
  :rule-classes :linear)
(defthm fn-ptx-mk-size
  (equal (fn-rtc-size (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc))
         (+ 15 (fn-rtc-size ph) 1 (fn-rtc-size cur) (fn-rtc-size q) (fn-rtc-size kd) 1 1
            (fn-rtc-size b1) (fn-rtc-size b3) (fn-rtc-size hs) 1 (fn-rtc-size evd) (fn-rtc-size geo) (fn-rtc-size acc)))
  :hints (("Goal" :in-theory (enable fn-ptx-mk))))
(defthm fn-ptx-size-len
  (<= (+ 1 (* 2 (len x))) (fn-rtc-size x))
  :rule-classes :linear)
(defthm fn-ptx-start-facts
  (implies (and (<= (+ (fn-rtc-size p) (fn-rtc-size q)) 21) (<= (fn-rtc-size kd) kb) (<= (fn-rtc-size geo) 7))
           (and (equal (mv-nth 2 (fn-ptx-start p q kd ext geo committed)) 1)
                (equal (fn-rtc-reqs-octets (mv-nth 1 (fn-ptx-start p q kd ext geo committed))) 0)
                (equal (len (mv-nth 1 (fn-ptx-start p q kd ext geo committed))) 1)
                (<= (fn-rtc-size (mv-nth 0 (fn-ptx-start p q kd ext geo committed)))
                    (+ kb 100 (fn-ptx-acc-max-state)))))
  :hints (("Goal" :in-theory (e/d (fn-ptx-start fn-ptx-cur-fid fn-ptx-cur-finc fn-ptx-cur-bp fn-ptx-cur-len fn-ptx-timer fn-rtc-reqs-octets) (fn-ptx-mk)))))
(defthm fn-ptx-answer-facts
  (and (equal (len (fn-ptx-answer p o id inc st)) 2)
       (equal (fn-rtc-reqs-octets (fn-ptx-answer p o id inc st)) 1))
  :hints (("Goal" :in-theory (enable fn-ptx-answer fn-rtc-reqs-octets))))
(defthm fn-ptx-release-bufs-facts
  (and (<= (len (fn-ptx-release-bufs m id inc st)) 2)
       (equal (fn-rtc-reqs-octets (fn-ptx-release-bufs m id inc st)) 0))
  :hints (("Goal" :in-theory (enable fn-ptx-release-bufs fn-rtc-reqs-octets))))
(defthm fn-ptx-refuse-all-facts
  (and (equal (len (fn-ptx-refuse-all q id inc st)) (* 2 (len q)))
       (equal (fn-rtc-reqs-octets (fn-ptx-refuse-all q id inc st)) (len q)))
  :hints (("Goal" :in-theory (enable fn-rtc-reqs-octets))))
(defthm fn-ptx-reqs-octets-append
  (equal (fn-rtc-reqs-octets (append a b)) (+ (fn-rtc-reqs-octets a) (fn-rtc-reqs-octets b)))
  :hints (("Goal" :in-theory (enable fn-rtc-reqs-octets))))
(defthm fn-ptx-start-uncond
  (and (equal (mv-nth 2 (fn-ptx-start p q kd ext geo committed)) 1)
       (equal (fn-rtc-reqs-octets (mv-nth 1 (fn-ptx-start p q kd ext geo committed))) 0)
       (equal (len (mv-nth 1 (fn-ptx-start p q kd ext geo committed))) 1))
  :hints (("Goal" :in-theory (enable fn-ptx-start fn-ptx-timer fn-rtc-reqs-octets))))
(defthm fn-ptx-len-append
  (equal (len (append a b)) (+ (len a) (len b))))
(defthm fn-ptx-done-facts
  (and (<= (len (append (fn-ptx-release-bufs m id inc st) (fn-ptx-answer cur o id inc st))) 4)
       (equal (fn-rtc-reqs-octets (append (fn-ptx-release-bufs m id inc st) (fn-ptx-answer cur o id inc st))) 1))
  :hints (("Goal" :use ((:instance fn-ptx-release-bufs-facts) (:instance fn-ptx-answer-facts (p cur)))
           :in-theory (disable fn-ptx-release-bufs fn-ptx-answer fn-ptx-release-bufs-facts fn-ptx-answer-facts))))
(defthm fn-ptx-len-q-bound
  (implies (<= (fn-rtc-size q) 21) (<= (len q) 10))
  :rule-classes :linear
  :hints (("Goal" :use (:instance fn-ptx-size-len (x q)) :in-theory (disable fn-ptx-size-len))))
(defthm fn-ptx-end-cost
  (and (natp (mv-nth 2 (fn-ptx-end m o kd ext fenced committed id inc st)))
       (<= (mv-nth 2 (fn-ptx-end m o kd ext fenced committed id inc st)) 2))
  :hints (("Goal" :in-theory (e/d (fn-ptx-end) (fn-ptx-mk fn-ptx-start fn-ptx-answer fn-ptx-release-bufs fn-ptx-refuse-all)))))
(defthm fn-ptx-end-octets
  (implies (<= (fn-rtc-size (fn-ptx-q m)) 21)
           (<= (fn-rtc-reqs-octets (mv-nth 1 (fn-ptx-end m o kd ext fenced committed id inc st))) 11))
  :hints (("Goal" :in-theory (e/d (fn-ptx-end) (fn-ptx-mk fn-ptx-start fn-ptx-answer fn-ptx-release-bufs fn-ptx-refuse-all fn-ptx-done-facts))
           :use ((:instance fn-ptx-len-q-bound (q (fn-ptx-q m)))
                 (:instance fn-ptx-start-uncond (p (car (fn-ptx-q m))) (q (cdr (fn-ptx-q m))) (geo (fn-ptx-geo m))))
           :do-not-induct t)))
(defthm fn-ptx-release-bufs-len
  (<= (len (fn-ptx-release-bufs m id inc st)) 2)
  :rule-classes :linear
  :hints (("Goal" :use fn-ptx-release-bufs-facts :in-theory (disable fn-ptx-release-bufs-facts))))
(defthm fn-ptx-end-len
  (implies (<= (fn-rtc-size (fn-ptx-q m)) 21)
           (<= (len (mv-nth 1 (fn-ptx-end m o kd ext fenced committed id inc st))) 24))
  :hints (("Goal" :in-theory (e/d (fn-ptx-end) (fn-ptx-mk fn-ptx-start fn-ptx-answer fn-ptx-release-bufs fn-ptx-refuse-all fn-ptx-done-facts))
           :use ((:instance fn-ptx-len-q-bound (q (fn-ptx-q m)))
                 (:instance fn-ptx-start-uncond (p (car (fn-ptx-q m))) (q (cdr (fn-ptx-q m))) (geo (fn-ptx-geo m))))
           :do-not-induct t)))
(defthm fn-ptx-end-size
  (implies (and (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-geo m)) 7) (<= (fn-rtc-size kd) kb))
           (<= (fn-rtc-size (mv-nth 0 (fn-ptx-end m o kd ext fenced committed id inc st))) (+ kb 200 (fn-ptx-acc-max-state))))
  :hints (("Goal" :in-theory (e/d (fn-ptx-end) (fn-ptx-mk fn-ptx-start fn-ptx-start-facts fn-ptx-answer fn-ptx-release-bufs fn-ptx-refuse-all fn-ptx-done-facts))
           :use ((:instance fn-ptx-start-facts (p (car (fn-ptx-q m))) (q (cdr (fn-ptx-q m))) (geo (fn-ptx-geo m))))
           :do-not-induct t)))
(defthm fn-ptx-frame-header-len
  (equal (len (fn-ptx-frame-header rlen)) 10)
  :hints (("Goal" :in-theory (enable fn-ptx-frame-header fn-frame-header))))
(defthm fn-ptx-len-kd-last
  (implies (<= (fn-rtc-size kd) 75) (<= (len (fn-rtc-get 1 kd)) 37))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-ptx-size-len (x (fn-rtc-get 1 kd))) (:instance fn-ptx-size-get (i 1) (x kd)))
           :in-theory (disable fn-ptx-size-len fn-ptx-size-get))))
(defthm fn-ptx-accessors-of-mk
  (and (equal (fn-ptx-ph (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc)) ph)
       (equal (fn-ptx-k (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc)) (nfix k))
       (equal (fn-ptx-cur (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc)) cur)
       (equal (fn-ptx-q (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc)) q)
       (equal (fn-ptx-kd (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc)) kd)
       (equal (fn-ptx-ext (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc)) (nfix ext))
       (equal (fn-ptx-nxt (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc)) (nfix nxt))
       (equal (fn-ptx-b1 (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc)) b1)
       (equal (fn-ptx-b3 (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc)) b3)
       (equal (fn-ptx-hs (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc)) hs)
       (equal (fn-ptx-committedp (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc)) (and committed t))
       (equal (fn-ptx-evd (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc)) evd)
       (equal (fn-ptx-geo (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc)) geo)
       (equal (fn-ptx-acc (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc)) acc))
  :hints (("Goal" :in-theory (enable fn-ptx-mk fn-ptx-ph fn-ptx-k fn-ptx-cur fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs
                                     fn-ptx-committedp fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-rtc-get))))

(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm fn-ptx-head-end-bound
    (implies (fn-ptx-head-end h i lim id inc st)
             (and (<= (fn-ptx-head-end h i lim id inc st) (nfix lim))
                  (< (nfix i) (fn-ptx-head-end h i lim id inc st))
                  (integerp (fn-ptx-head-end h i lim id inc st))))
    :rule-classes nil
    :hints (("Goal" :induct (fn-ptx-head-end h i lim id inc st)
             :expand ((fn-ptx-head-end h i lim id inc st))
             :in-theory (e/d ((:induction fn-ptx-head-end)) (fn-ptx-byte (:definition fn-ptx-head-end)))))))
(defthm fn-ptx-head-end-le
  (implies (fn-ptx-head-end h i lim id inc st)
           (<= (fn-ptx-head-end h i lim id inc st) (nfix lim)))
  :rule-classes :linear
  :hints (("Goal" :use fn-ptx-head-end-bound)))
(defthm fn-ptx-head-end-gt
  (implies (fn-ptx-head-end h i lim id inc st)
           (< (nfix i) (fn-ptx-head-end h i lim id inc st)))
  :rule-classes :linear
  :hints (("Goal" :use fn-ptx-head-end-bound)))
(defthm fn-ptx-head-end-int
  (implies (fn-ptx-head-end h i lim id inc st)
           (integerp (fn-ptx-head-end h i lim id inc st)))
  :hints (("Goal" :use fn-ptx-head-end-bound)))

(defthm fn-ptx-range-len
  (equal (len (fn-ptx-range h i n id inc st)) (nfix n)))
(defthm fn-ptx-msg-range-len
  (equal (len (fn-ptx-msg-range i n spans id inc st)) (nfix n)))
(defthm fn-ptx-write-nz-octets
  (and (equal (fn-rtc-reqs-octets (fn-ptx-write-nz h g off octets)) (len octets))
       (<= (len (fn-ptx-write-nz h g off octets)) 1))
  :hints (("Goal" :in-theory (enable fn-ptx-write-nz fn-rtc-reqs-octets))))
(defthm fn-ptx-len-take-le
  (<= (len (take n x)) (nfix n))
  :rule-classes :linear)
(defthm fn-ptx-zeros-len
  (equal (len (fn-bs-zeros n)) (nfix n)))

(defthm fn-ptx-acc-end-lens
  (and (<= (len (mv-nth 1 (fn-ptx-acc-end a blen))) (fn-ptx-acc-out-max))
       (<= (len (mv-nth 2 (fn-ptx-acc-end a blen))) (fn-ptx-acc-out-max))
       (<= (len (mv-nth 4 (fn-ptx-acc-end a blen))) *fn-ptx-sufhead-max*)
       (<= (len (mv-nth 5 (fn-ptx-acc-end a blen))) (fn-ptx-acc-out-max)))
  :rule-classes :linear
  :hints (("Goal" :use fn-ptx-acc-end-shape)))
(defthm fn-ptx-acc-end-ioff-natp
  (natp (mv-nth 3 (fn-ptx-acc-end a blen)))
  :rule-classes :type-prescription
  :hints (("Goal" :use fn-ptx-acc-end-shape)))
(defthm fn-ptx-acc-feed-len
  (<= (len (mv-nth 1 (fn-ptx-acc-feed a octets))) (+ (* 2 (len octets)) (fn-ptx-acc-out-max)))
  :rule-classes :linear
  :hints (("Goal" :use fn-ptx-acc-feed-shape)))
(defthm fn-ptx-acc-feed-cost-natp
  (natp (fn-ptx-acc-feed-cost a octets))
  :rule-classes :type-prescription
  :hints (("Goal" :use fn-ptx-acc-feed-cost-bounded)))
(defthm fn-ptx-acc-feed-cost-le
  (<= (fn-ptx-acc-feed-cost a octets) (+ (* 4 (len octets)) (fn-ptx-acc-out-max)))
  :rule-classes :linear
  :hints (("Goal" :use fn-ptx-acc-feed-cost-bounded)))

(defthm fn-ptx-end-size-lin
  (implies (and (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-geo m)) 7) (<= (fn-rtc-size kd) 4111))
           (<= (fn-rtc-size (mv-nth 0 (fn-ptx-end m o kd ext fenced committed id inc st))) (+ 4311 (fn-ptx-acc-max-state))))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-ptx-end-size (kb 4111))) :in-theory (disable fn-ptx-end fn-ptx-end-size))))
(defthm fn-ptx-start-size-lin
  (implies (and (<= (+ (fn-rtc-size p) (fn-rtc-size q)) 21) (<= (fn-rtc-size kd) 4111) (<= (fn-rtc-size geo) 7))
           (<= (fn-rtc-size (mv-nth 0 (fn-ptx-start p q kd ext geo committed))) (+ 4211 (fn-ptx-acc-max-state))))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-ptx-start-facts (kb 4111))) :in-theory (disable fn-ptx-start fn-ptx-start-facts))))
(defthm fn-ptx-kd-commit-size
  (<= (fn-rtc-size (fn-ptx-kd-commit kd trailer elen)) (+ 10 (fn-rtc-size trailer)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-ptx-kd-commit fn-ptx-kd-mk fn-ptx-kd-count fn-ptx-kd-frontier fn-ptx-kd-txid fn-ptx-kd-acked fn-rtc-get))))
(defthm fn-ptx-end-cost-natp
  (natp (mv-nth 2 (fn-ptx-end m o kd ext fenced committed id inc st)))
  :rule-classes :type-prescription
  :hints (("Goal" :use fn-ptx-end-cost :in-theory (disable fn-ptx-end fn-ptx-end-cost))))
(defthm fn-ptx-end-cost-lin
  (<= (mv-nth 2 (fn-ptx-end m o kd ext fenced committed id inc st)) 2)
  :rule-classes :linear
  :hints (("Goal" :use fn-ptx-end-cost :in-theory (disable fn-ptx-end fn-ptx-end-cost))))
(defthm fn-ptx-end-octets-lin
  (implies (<= (fn-rtc-size (fn-ptx-q m)) 21)
           (<= (fn-rtc-reqs-octets (mv-nth 1 (fn-ptx-end m o kd ext fenced committed id inc st))) 11))
  :rule-classes :linear
  :hints (("Goal" :use fn-ptx-end-octets :in-theory (disable fn-ptx-end fn-ptx-end-octets))))
(defthm fn-ptx-end-len-lin
  (implies (<= (fn-rtc-size (fn-ptx-q m)) 21)
           (<= (len (mv-nth 1 (fn-ptx-end m o kd ext fenced committed id inc st))) 24))
  :rule-classes :linear
  :hints (("Goal" :use fn-ptx-end-len :in-theory (disable fn-ptx-end fn-ptx-end-len))))

(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm fn-ptx-times-neg (and (equal (* 4 (- x)) (* -4 x)) (equal (* 2 (- x)) (* -2 x)))))

(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm fn-ptx-read-w-ge
    (<= 1024 (fn-ptx-read-w q))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable fn-ptx-read-w))))
  (defthm fn-ptx-read-w-le
    (implies (natp q) (<= (* 8 (fn-ptx-read-w q)) (+ q 8192)))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable fn-ptx-read-w) :cases ((< (floor (nfix q) 8) 1024)))))
  (defthm fn-ptx-read-w-int
    (natp (fn-ptx-read-w q))
    :rule-classes :type-prescription
    :hints (("Goal" :in-theory (enable fn-ptx-read-w)))))

(defthm fn-ptx-min-le
  (and (<= (min a b) a) (<= (min a b) b))
  :rule-classes :linear)
(defthm fn-ptx-min-ge
  (implies (and (<= c a) (<= c b)) (<= c (min a b)))
  :rule-classes :linear)
(defthm fn-ptx-min-natp
  (implies (and (natp a) (natp b)) (natp (min a b)))
  :rule-classes :type-prescription)

(defthm fn-ptx-feed-cost-range-le
  (<= (fn-ptx-acc-feed-cost a (fn-ptx-range h i n id inc st)) (+ (* 4 (nfix n)) (fn-ptx-acc-out-max)))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-ptx-acc-feed-cost-le (octets (fn-ptx-range h i n id inc st))))
           :in-theory (disable fn-ptx-acc-feed-cost-le))))
(defthm fn-ptx-feed-len-range-le
  (<= (len (mv-nth 1 (fn-ptx-acc-feed a (fn-ptx-range h i n id inc st)))) (+ (* 2 (nfix n)) (fn-ptx-acc-out-max)))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-ptx-acc-feed-len (octets (fn-ptx-range h i n id inc st))))
           :in-theory (disable fn-ptx-acc-feed-len))))
(defthm fn-ptx-feed-cost-head-le
  (implies (and (natp pos) (natp lim) (fn-ptx-head-end h pos lim id inc st))
           (<= (fn-ptx-acc-feed-cost a (fn-ptx-range h pos (+ (- pos) (fn-ptx-head-end h pos lim id inc st)) id inc st))
               (+ (* 4 lim) (* -4 pos) (fn-ptx-acc-out-max))))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-ptx-feed-cost-range-le (h h) (i pos) (n (+ (- pos) (fn-ptx-head-end h pos lim id inc st))))
                        (:instance fn-ptx-head-end-le (i pos)))
           :in-theory (disable fn-ptx-feed-cost-range-le fn-ptx-head-end-le fn-ptx-range fn-ptx-head-end))))
(defthm fn-ptx-feed-len-head-le
  (implies (and (natp pos) (natp lim) (fn-ptx-head-end h pos lim id inc st))
           (<= (len (mv-nth 1 (fn-ptx-acc-feed a (fn-ptx-range h pos (+ (- pos) (fn-ptx-head-end h pos lim id inc st)) id inc st))))
               (+ (* 2 lim) (* -2 pos) (fn-ptx-acc-out-max))))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-ptx-feed-len-range-le (h h) (i pos) (n (+ (- pos) (fn-ptx-head-end h pos lim id inc st))))
                        (:instance fn-ptx-head-end-le (i pos)))
           :in-theory (disable fn-ptx-feed-len-range-le fn-ptx-head-end-le fn-ptx-range fn-ptx-head-end))))

(defthm fn-ptx-read-charge
  (implies (and (natp q) (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-kd m)) 75))
           (and (natp (mv-nth 2 (fn-ptx-read m q id inc st)))
                (<= (+ (mv-nth 2 (fn-ptx-read m q id inc st)) (fn-rtc-reqs-octets (mv-nth 1 (fn-ptx-read m q id inc st))))
                    (+ q 9216 (* 10 (fn-ptx-acc-out-max))))))
  :hints (("Goal" :in-theory (e/d (fn-ptx-read fn-ptx-kd-last) (fn-ptx-read-w min mv-nth fn-ptx-buf-h fn-ptx-buf-g fn-ptx-buf-len fn-ptx-buf-x fn-ptx-write-nz fn-bs-zeros take fn-ptx-mk fn-ptx-end fn-ptx-free fn-ptx-head-end fn-ptx-range fn-ptx-cap fn-ptx-gen
                                                 fn-ptx-frame-header fn-ptx-end-octets fn-ptx-end-cost fn-ptx-timer fn-ptx-committedp fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-rtc-get fn-ptx-hmax fn-ptx-fmax fn-ptx-unit fn-ptx-cur-fid fn-ptx-cur-finc fn-ptx-cur-bp fn-ptx-cur-len fn-ptx-cur-hoff fn-ptx-cur-txid fn-ptx-cur-ioff fn-ptx-kd-txid))
           :do-not-induct t)))

(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm fn-ptx-nw-natp
    (natp (min 64 (max 1 (floor (nfix q) 1024))))
    :rule-classes :type-prescription)
  (defthm fn-ptx-nw-le
    (implies (natp q)
             (<= (* 1024 (min 64 (max 1 (floor q 1024)))) (+ q 1024)))
    :rule-classes :linear
    :hints (("Goal" :cases ((< q 1024))))))
(defthm fn-ptx-submit-heads
  (and (equal (fn-rtc-get 0 (fn-ptx-timer)) :submit)
       (equal (fn-rtc-get 0 (fn-ptx-fsync)) :submit)
       (equal (fn-rtc-get 0 (fn-ptx-pwrite h g off n pos)) :submit)
       (equal (fn-rtc-get 0 (fn-ptx-extend ext nxt)) :submit))
  :hints (("Goal" :in-theory (enable fn-ptx-timer fn-ptx-fsync fn-ptx-pwrite fn-ptx-extend fn-rtc-get))))
(defthm fn-ptx-span-pwrite-head
  (equal (fn-rtc-get 0 (fn-ptx-span-pwrite i m front id inc st)) :submit)
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                             '(fn-ptx-span-pwrite fn-ptx-submit-heads)))))
(defthm fn-ptx-hash-charge
  (implies (and (natp q) (<= (fn-rtc-size (fn-ptx-q m)) 21))
           (<= (+ (mv-nth 2 (fn-ptx-hash m q id inc st)) (fn-rtc-reqs-octets (mv-nth 1 (fn-ptx-hash m q id inc st))))
               (+ q 9216 (* 10 (fn-ptx-acc-out-max)))))
  :hints (("Goal" :in-theory (e/d (fn-ptx-hash) (fn-ptx-end fn-ptx-mk fn-ptx-absorb fn-ptx-finish-digest fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-rtc-get fn-ptx-committedp
                                                   fn-ptx-unit fn-ptx-buf-h fn-ptx-buf-g fn-ptx-buf-len fn-ptx-buf-x fn-ptx-spans fn-ptx-spans-len min max floor fn-olr-extension-needed-p fn-olr-extension-target fn-ptx-pad-len fn-ptx-kd-frontier fn-ptx-span-pwrite mv-nth fn-ptx-timer fn-ptx-extend fn-ptx-pwrite fn-ptx-fsync))
           :do-not-induct t)))

(defthm fn-ptx-hash-cost-natp
  (natp (mv-nth 2 (fn-ptx-hash m q id inc st)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (fn-ptx-hash) (fn-ptx-end fn-ptx-mk fn-ptx-absorb fn-ptx-finish-digest fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-rtc-get fn-ptx-committedp
                                                   fn-ptx-unit fn-ptx-spans fn-ptx-spans-len min max floor fn-olr-extension-needed-p fn-olr-extension-target fn-ptx-pad-len fn-ptx-kd-frontier fn-ptx-span-pwrite mv-nth fn-ptx-timer fn-ptx-extend fn-ptx-pwrite fn-ptx-fsync))
           :do-not-induct t)))

(defthm fn-ptx-write-nz-len
  (<= (len (fn-ptx-write-nz h g off octets)) 1)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-ptx-write-nz))))
(defthm fn-ptx-read-len
  (implies (<= (fn-rtc-size (fn-ptx-q m)) 21)
           (<= (len (mv-nth 1 (fn-ptx-read m q id inc st))) 29))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (fn-ptx-read) (fn-ptx-read-w fn-ptx-mk fn-ptx-end fn-ptx-free fn-ptx-head-end fn-ptx-range fn-ptx-cap fn-ptx-gen min mv-nth
                                                 fn-ptx-frame-header fn-ptx-timer fn-ptx-committedp fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-rtc-get fn-ptx-hmax fn-ptx-fmax fn-ptx-unit fn-ptx-cur-fid fn-ptx-cur-finc fn-ptx-cur-bp fn-ptx-cur-len fn-ptx-cur-hoff fn-ptx-cur-txid fn-ptx-cur-ioff fn-ptx-kd-txid fn-ptx-buf-h fn-ptx-buf-g fn-ptx-buf-len fn-ptx-buf-x fn-ptx-write-nz fn-bs-zeros take))
           :do-not-induct t)))
(defthm fn-ptx-hash-len
  (implies (<= (fn-rtc-size (fn-ptx-q m)) 21)
           (<= (len (mv-nth 1 (fn-ptx-hash m q id inc st))) 25))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (fn-ptx-hash) (fn-ptx-buf-h fn-ptx-buf-g fn-ptx-buf-len fn-ptx-buf-x fn-ptx-end fn-ptx-mk fn-ptx-absorb fn-ptx-finish-digest fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-rtc-get fn-ptx-committedp
                                                   fn-ptx-unit fn-ptx-spans fn-ptx-spans-len min max floor fn-olr-extension-needed-p fn-olr-extension-target fn-ptx-pad-len fn-ptx-kd-frontier fn-ptx-span-pwrite mv-nth fn-ptx-timer fn-ptx-extend fn-ptx-pwrite fn-ptx-fsync))
           :do-not-induct t)))

(defthm fn-ptx-absorb-pos-natp
  (natp (mv-nth 0 (fn-ptx-absorb nw pos st n spans id inc fn-rtc-st)))
  :hints (("Goal" :induct (fn-ptx-absorb nw pos st n spans id inc fn-rtc-st)
           :in-theory (disable fn-b3-node fn-b3-cv-push fn-ptx-msg-range)))
  :rule-classes :type-prescription)
(defthm fn-ptx-absorb-pos-natp-car
  (natp (car (fn-ptx-absorb nw pos st n spans id inc fn-rtc-st)))
  :hints (("Goal" :use fn-ptx-absorb-pos-natp :in-theory (disable fn-ptx-absorb-pos-natp)))
  :rule-classes :type-prescription)
(defthm fn-ptx-size-of-octet-list
  (implies (fn-b3-octet-listp xs) (equal (fn-rtc-size xs) (+ 1 (* 2 (len xs)))))
  :hints (("Goal" :in-theory (enable fn-b3-octet-listp))))
(defthm fn-ptx-finish-digest-size
  (equal (fn-rtc-size (fn-ptx-finish-digest pos st n spans id inc fn-rtc-st)) 65)
  :hints (("Goal" :use fn-ptx-finish-digest-shape :in-theory (disable fn-ptx-finish-digest-shape fn-ptx-finish-digest))))

(defthm fn-ptx-absorb-st-size-nat
  (implies (natp nw)
           (<= (fn-rtc-size (mv-nth 1 (fn-ptx-absorb nw pos st n spans id inc fn-rtc-st)))
               (+ (* 64 nw) (fn-rtc-size st))))
  :rule-classes :linear
  :hints (("Goal" :use fn-ptx-absorb-st-size :in-theory (disable fn-ptx-absorb fn-ptx-absorb-st-size))))

(defthm fn-ptx-cur-parts-size
  (and (<= (fn-rtc-size (fn-ptx-cur-fid c)) (fn-rtc-size c))
       (<= (fn-rtc-size (fn-ptx-cur-finc c)) (fn-rtc-size c))
       (<= (fn-rtc-size (fn-ptx-kd-last c)) (fn-rtc-size c)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-ptx-cur-fid fn-ptx-cur-finc fn-ptx-kd-last))))
(defthm fn-ptx-read-size
  (implies (and (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-geo m)) 7) (<= (fn-rtc-size (fn-ptx-kd m)) 75)
                (<= (fn-rtc-size (fn-ptx-cur m)) 15) (<= (fn-rtc-size (fn-ptx-acc m)) (fn-ptx-acc-max-state))
                (<= (fn-rtc-size (fn-ptx-b1 m)) 9) (<= (fn-rtc-size (fn-ptx-b3 m)) 9) (<= (fn-rtc-size (fn-ptx-hs m)) 4101)
                (<= (fn-rtc-size (fn-ptx-evd m)) 57) (<= (fn-rtc-size (fn-ptx-ph m)) 1))
           (<= (fn-rtc-size (mv-nth 0 (fn-ptx-read m q id inc st))) (+ 8000 (fn-ptx-acc-max-state))))
  :hints (("Goal" :in-theory (e/d (fn-ptx-read) (fn-ptx-read-w fn-ptx-mk fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-ptx-end fn-ptx-free fn-ptx-head-end fn-ptx-range fn-ptx-cap fn-ptx-gen min mv-nth
                                                 fn-ptx-frame-header fn-ptx-timer fn-ptx-committedp fn-rtc-get fn-ptx-hmax fn-ptx-fmax fn-ptx-unit fn-ptx-cur-fid fn-ptx-cur-finc fn-ptx-cur-bp fn-ptx-cur-len fn-ptx-cur-hoff fn-ptx-cur-txid fn-ptx-cur-ioff fn-ptx-kd-txid fn-ptx-buf-h fn-ptx-buf-g fn-ptx-buf-len fn-ptx-buf-x fn-ptx-write-nz fn-bs-zeros take
                                                 fn-ptx-size-len fn-ptx-size-append fn-ptx-size-tlf fn-ptx-len-kd-last fn-ptx-size-pos))
           :use ((:instance fn-ptx-end-size (m (fn-ptx-chg m :committed nil)) (o :refused) (kb 75) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m)) (fenced nil) (committed nil))
                 (:instance fn-ptx-end-size (m (fn-ptx-chg m :committed nil :b1 nil :b3 nil)) (o :refused) (kb 75) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m)) (fenced nil) (committed nil)))
           :do-not-induct t)))

(defthm fn-ptx-hash-size
  (implies (and (natp q) (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-geo m)) 7) (<= (fn-rtc-size (fn-ptx-kd m)) 75)
                (<= (fn-rtc-size (fn-ptx-cur m)) 15) (<= (fn-rtc-size (fn-ptx-acc m)) (fn-ptx-acc-max-state))
                (<= (fn-rtc-size (fn-ptx-b1 m)) 9) (<= (fn-rtc-size (fn-ptx-b3 m)) 9) (<= (fn-rtc-size (fn-ptx-hs m)) 4101)
                (<= (fn-rtc-size (fn-ptx-evd m)) 57) (<= (fn-rtc-size (fn-ptx-ph m)) 1))
           (<= (fn-rtc-size (mv-nth 0 (fn-ptx-hash m q id inc st))) (+ 8500 (fn-ptx-acc-max-state))))
  :hints (("Goal" :in-theory (e/d (fn-ptx-hash) (fn-ptx-buf-h fn-ptx-buf-g fn-ptx-buf-len fn-ptx-buf-x fn-ptx-end fn-ptx-mk fn-ptx-absorb fn-ptx-finish-digest fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-rtc-get fn-ptx-committedp
                                                   fn-ptx-unit fn-ptx-spans fn-ptx-spans-len min max floor fn-olr-extension-needed-p fn-olr-extension-target fn-ptx-pad-len fn-ptx-kd-frontier fn-ptx-span-pwrite mv-nth fn-ptx-timer fn-ptx-extend fn-ptx-pwrite fn-ptx-fsync))
           :use ((:instance fn-ptx-end-size (m (fn-ptx-chg m :committed nil)) (o :refused) (kb 75) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m)) (fenced nil) (committed nil)))
           :do-not-induct t)))

(defthm fn-ptx-read-charge-lin
  (implies (and (natp q) (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-kd m)) 75))
           (<= (+ (mv-nth 2 (fn-ptx-read m q id inc st)) (fn-rtc-reqs-octets (mv-nth 1 (fn-ptx-read m q id inc st))))
               (+ q 9216 (* 10 (fn-ptx-acc-out-max)))))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-ptx-read-charge)) :in-theory (disable fn-ptx-read fn-ptx-read-charge))))
(defthm fn-ptx-read-cost-natp
  (implies (and (natp q) (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-kd m)) 75))
           (natp (mv-nth 2 (fn-ptx-read m q id inc st))))
  :rule-classes :type-prescription
  :hints (("Goal" :use ((:instance fn-ptx-read-charge)) :in-theory (disable fn-ptx-read fn-ptx-read-charge))))
(defthm fn-ptx-hash-charge-lin
  (implies (and (natp q) (<= (fn-rtc-size (fn-ptx-q m)) 21))
           (<= (+ (mv-nth 2 (fn-ptx-hash m q id inc st)) (fn-rtc-reqs-octets (mv-nth 1 (fn-ptx-hash m q id inc st))))
               (+ q 9216 (* 10 (fn-ptx-acc-out-max)))))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-ptx-hash-charge)) :in-theory (disable fn-ptx-hash fn-ptx-hash-charge))))
(defthm fn-ptx-read-size-lin
  (implies (and (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-geo m)) 7) (<= (fn-rtc-size (fn-ptx-kd m)) 75)
                (<= (fn-rtc-size (fn-ptx-cur m)) 15) (<= (fn-rtc-size (fn-ptx-acc m)) (fn-ptx-acc-max-state))
                (<= (fn-rtc-size (fn-ptx-b1 m)) 9) (<= (fn-rtc-size (fn-ptx-b3 m)) 9) (<= (fn-rtc-size (fn-ptx-hs m)) 4101)
                (<= (fn-rtc-size (fn-ptx-evd m)) 57) (<= (fn-rtc-size (fn-ptx-ph m)) 1))
           (<= (fn-rtc-size (mv-nth 0 (fn-ptx-read m q id inc st))) (+ 8000 (fn-ptx-acc-max-state))))
  :rule-classes :linear
  :hints (("Goal" :use fn-ptx-read-size :in-theory (disable fn-ptx-read fn-ptx-read-size))))
(defthm fn-ptx-hash-size-lin
  (implies (and (natp q) (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-geo m)) 7) (<= (fn-rtc-size (fn-ptx-kd m)) 75)
                (<= (fn-rtc-size (fn-ptx-cur m)) 15) (<= (fn-rtc-size (fn-ptx-acc m)) (fn-ptx-acc-max-state))
                (<= (fn-rtc-size (fn-ptx-b1 m)) 9) (<= (fn-rtc-size (fn-ptx-b3 m)) 9) (<= (fn-rtc-size (fn-ptx-hs m)) 4101)
                (<= (fn-rtc-size (fn-ptx-evd m)) 57) (<= (fn-rtc-size (fn-ptx-ph m)) 1))
           (<= (fn-rtc-size (mv-nth 0 (fn-ptx-hash m q id inc st))) (+ 8500 (fn-ptx-acc-max-state))))
  :rule-classes :linear
  :hints (("Goal" :use fn-ptx-hash-size :in-theory (disable fn-ptx-hash fn-ptx-hash-size))))
(defthm fn-ptx-read-size-car
  (implies (and (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-geo m)) 7) (<= (fn-rtc-size (fn-ptx-kd m)) 75)
                (<= (fn-rtc-size (fn-ptx-cur m)) 15) (<= (fn-rtc-size (fn-ptx-acc m)) (fn-ptx-acc-max-state))
                (<= (fn-rtc-size (fn-ptx-b1 m)) 9) (<= (fn-rtc-size (fn-ptx-b3 m)) 9) (<= (fn-rtc-size (fn-ptx-hs m)) 4101)
                (<= (fn-rtc-size (fn-ptx-evd m)) 57) (<= (fn-rtc-size (fn-ptx-ph m)) 1))
           (<= (fn-rtc-size (car (fn-ptx-read m q id inc st))) (+ 8000 (fn-ptx-acc-max-state))))
  :rule-classes :linear
  :hints (("Goal" :use fn-ptx-read-size-lin :in-theory (disable fn-ptx-read fn-ptx-read-size-lin))))
(defthm fn-ptx-hash-size-car
  (implies (and (natp q) (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-geo m)) 7) (<= (fn-rtc-size (fn-ptx-kd m)) 75)
                (<= (fn-rtc-size (fn-ptx-cur m)) 15) (<= (fn-rtc-size (fn-ptx-acc m)) (fn-ptx-acc-max-state))
                (<= (fn-rtc-size (fn-ptx-b1 m)) 9) (<= (fn-rtc-size (fn-ptx-b3 m)) 9) (<= (fn-rtc-size (fn-ptx-hs m)) 4101)
                (<= (fn-rtc-size (fn-ptx-evd m)) 57) (<= (fn-rtc-size (fn-ptx-ph m)) 1))
           (<= (fn-rtc-size (car (fn-ptx-hash m q id inc st))) (+ 8500 (fn-ptx-acc-max-state))))
  :rule-classes :linear
  :hints (("Goal" :use fn-ptx-hash-size-lin :in-theory (disable fn-ptx-hash fn-ptx-hash-size-lin))))

(defthm fn-ptx-step1-cost-natp
  (implies (and (natp q) (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-kd m)) 75))
           (natp (mv-nth 2 (fn-ptx-step1 m ev st q))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1) (fn-ptx-mk fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-ptx-committedp
fn-ptx-end fn-ptx-read fn-ptx-hash fn-ptx-start fn-ptx-answer fn-rtc-get fn-ptx-opened fn-ptx-wfp fn-ptx-evd+ fn-ptx-summary fn-ptx-kd-commit
fn-ptx-elen fn-ptx-nmsg fn-ptx-nspans fn-ptx-span-n fn-ptx-spans fn-ptx-spans-len fn-ptx-buf-len fn-ptx-gen fn-ptx-kd-frontier fn-ptx-pwrite fn-ptx-fsync fn-ptx-extend fn-ptx-atom fn-ptx-span-pwrite mv-nth fn-ptx-release-bufs))
           :do-not-induct t)))
(defthm fn-ptx-step1-charge
  (implies (and (natp q) (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-kd m)) 75))
           (<= (+ (mv-nth 2 (fn-ptx-step1 m ev st q)) (fn-rtc-reqs-octets (mv-nth 1 (fn-ptx-step1 m ev st q))))
               (+ q 9216 (* 10 (fn-ptx-acc-out-max)))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1) (fn-ptx-mk fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-ptx-committedp
fn-ptx-end fn-ptx-read fn-ptx-hash fn-ptx-start fn-ptx-answer fn-rtc-get fn-ptx-opened fn-ptx-wfp fn-ptx-evd+ fn-ptx-summary fn-ptx-kd-commit
fn-ptx-elen fn-ptx-nmsg fn-ptx-nspans fn-ptx-span-n fn-ptx-spans fn-ptx-spans-len fn-ptx-buf-len fn-ptx-gen fn-ptx-kd-frontier fn-ptx-pwrite fn-ptx-fsync fn-ptx-extend fn-ptx-atom fn-ptx-span-pwrite mv-nth fn-ptx-release-bufs))
           :do-not-induct t)))
(defthm fn-ptx-step1-len
  (implies (and (<= (fn-rtc-size (fn-ptx-q m)) 21))
           (<= (len (mv-nth 1 (fn-ptx-step1 m ev st q))) 29))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1) (fn-ptx-mk fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-ptx-committedp
fn-ptx-end fn-ptx-read fn-ptx-hash fn-ptx-start fn-ptx-answer fn-rtc-get fn-ptx-opened fn-ptx-wfp fn-ptx-evd+ fn-ptx-summary fn-ptx-kd-commit
fn-ptx-elen fn-ptx-nmsg fn-ptx-nspans fn-ptx-span-n fn-ptx-spans fn-ptx-spans-len fn-ptx-buf-len fn-ptx-gen fn-ptx-kd-frontier fn-ptx-pwrite fn-ptx-fsync fn-ptx-extend fn-ptx-atom fn-ptx-span-pwrite mv-nth fn-ptx-release-bufs))
           :do-not-induct t)))

(defthm fn-ptx-opened-size
  (implies (fn-ptx-wfp (fn-ptx-opened kd ext geo))
           (<= (fn-rtc-size (fn-ptx-opened kd ext geo)) (+ 4300 (fn-ptx-acc-max-state))))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-ptx-wfp-sizes (m (fn-ptx-opened kd ext geo))))
           :in-theory (e/d (fn-ptx-opened) (fn-ptx-wfp fn-ptx-wfp-sizes fn-ptx-mk fn-ptx-ph fn-ptx-k fn-ptx-cur fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-committedp fn-rtc-get)))))
(defthm fn-ptx-end-size-car
  (implies (and (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-geo m)) 7) (<= (fn-rtc-size kd) 4111))
           (<= (fn-rtc-size (car (fn-ptx-end m o kd ext fenced committed id inc st))) (+ 4311 (fn-ptx-acc-max-state))))
  :rule-classes :linear
  :hints (("Goal" :use fn-ptx-end-size-lin :in-theory (disable fn-ptx-end fn-ptx-end-size-lin))))
(defthm fn-ptx-start-size-car
  (implies (and (<= (+ (fn-rtc-size p) (fn-rtc-size q)) 21) (<= (fn-rtc-size kd) 4111) (<= (fn-rtc-size geo) 7))
           (<= (fn-rtc-size (car (fn-ptx-start p q kd ext geo committed))) (+ 4211 (fn-ptx-acc-max-state))))
  :rule-classes :linear
  :hints (("Goal" :use fn-ptx-start-size-lin :in-theory (disable fn-ptx-start fn-ptx-start-size-lin))))
(defthm fn-ptx-evd+-size
  (<= (fn-rtc-size (fn-ptx-evd+ m ev)) (+ 9 (fn-rtc-size (fn-ptx-evd m))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-ptx-evd+ fn-ptx-summary fn-ptx-atom))))
(defthm fn-ptx-step1-size-opened
  (implies (and (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-geo m)) 7) (<= (fn-rtc-size (fn-ptx-kd m)) 75)
                (<= (fn-rtc-size (fn-ptx-cur m)) 15) (<= (fn-rtc-size (fn-ptx-acc m)) (fn-ptx-acc-max-state))
                (<= (fn-rtc-size (fn-ptx-b1 m)) 9) (<= (fn-rtc-size (fn-ptx-b3 m)) 9) (<= (fn-rtc-size (fn-ptx-hs m)) 4101)
                (<= (fn-rtc-size (fn-ptx-evd m)) 57) (<= (fn-rtc-size (fn-ptx-ph m)) 1) (natp q) (equal (fn-rtc-get 0 ev) :opened))
           (<= (fn-rtc-size (car (fn-ptx-step1 m ev st q))) (+ 8500 (fn-ptx-acc-max-state))))
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1) (fn-ptx-mk fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-ptx-committedp
                                                   fn-ptx-end fn-ptx-read fn-ptx-hash fn-ptx-start fn-ptx-answer fn-rtc-get fn-ptx-opened fn-ptx-wfp fn-ptx-evd+ fn-ptx-summary fn-ptx-kd-commit
                                                   fn-ptx-elen fn-ptx-nmsg fn-ptx-nspans fn-ptx-span-n fn-ptx-spans fn-ptx-spans-len fn-ptx-buf-len fn-ptx-span-pwrite mv-nth fn-ptx-release-bufs fn-ptx-gen fn-ptx-kd-frontier fn-ptx-pwrite fn-ptx-fsync fn-ptx-extend fn-ptx-atom))
           :do-not-induct t)))
(defthm fn-ptx-atom-size
  (equal (fn-rtc-size (fn-ptx-atom x)) 1)
  :hints (("Goal" :in-theory (enable fn-ptx-atom))))
(defthm fn-ptx-step1-size-handed
  (implies (and (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-geo m)) 7) (<= (fn-rtc-size (fn-ptx-kd m)) 75)
                (<= (fn-rtc-size (fn-ptx-cur m)) 15) (<= (fn-rtc-size (fn-ptx-acc m)) (fn-ptx-acc-max-state))
                (<= (fn-rtc-size (fn-ptx-b1 m)) 9) (<= (fn-rtc-size (fn-ptx-b3 m)) 9) (<= (fn-rtc-size (fn-ptx-hs m)) 4101)
                (<= (fn-rtc-size (fn-ptx-evd m)) 57) (<= (fn-rtc-size (fn-ptx-ph m)) 1) (natp q) (equal (fn-rtc-get 0 ev) :handed))
           (<= (fn-rtc-size (car (fn-ptx-step1 m ev st q))) (+ 8500 (fn-ptx-acc-max-state))))
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1) (fn-ptx-mk fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-ptx-committedp
                                                   fn-ptx-end fn-ptx-read fn-ptx-hash fn-ptx-start fn-ptx-answer fn-rtc-get fn-ptx-opened fn-ptx-wfp fn-ptx-evd+ fn-ptx-summary fn-ptx-kd-commit
                                                   fn-ptx-elen fn-ptx-nmsg fn-ptx-nspans fn-ptx-span-n fn-ptx-spans fn-ptx-spans-len fn-ptx-buf-len fn-ptx-span-pwrite mv-nth fn-ptx-release-bufs fn-ptx-gen fn-ptx-kd-frontier fn-ptx-pwrite fn-ptx-fsync fn-ptx-extend fn-ptx-atom))
           :do-not-induct t)))
(defthm fn-ptx-step1-size-timer
  (implies (and (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-geo m)) 7) (<= (fn-rtc-size (fn-ptx-kd m)) 75)
                (<= (fn-rtc-size (fn-ptx-cur m)) 15) (<= (fn-rtc-size (fn-ptx-acc m)) (fn-ptx-acc-max-state))
                (<= (fn-rtc-size (fn-ptx-b1 m)) 9) (<= (fn-rtc-size (fn-ptx-b3 m)) 9) (<= (fn-rtc-size (fn-ptx-hs m)) 4101)
                (<= (fn-rtc-size (fn-ptx-evd m)) 57) (<= (fn-rtc-size (fn-ptx-ph m)) 1) (natp q) (equal (fn-rtc-get 0 ev) :timer))
           (<= (fn-rtc-size (car (fn-ptx-step1 m ev st q))) (+ 8500 (fn-ptx-acc-max-state))))
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1) (fn-ptx-mk fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-ptx-committedp
                                                   fn-ptx-end fn-ptx-read fn-ptx-hash fn-ptx-start fn-ptx-answer fn-rtc-get fn-ptx-opened fn-ptx-wfp fn-ptx-evd+ fn-ptx-summary fn-ptx-kd-commit
                                                   fn-ptx-elen fn-ptx-nmsg fn-ptx-nspans fn-ptx-span-n fn-ptx-spans fn-ptx-spans-len fn-ptx-buf-len fn-ptx-span-pwrite mv-nth fn-ptx-release-bufs fn-ptx-gen fn-ptx-kd-frontier fn-ptx-pwrite fn-ptx-fsync fn-ptx-extend fn-ptx-atom))
           :do-not-induct t)))
(defthm fn-ptx-step1-size-extend
  (implies (and (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-geo m)) 7) (<= (fn-rtc-size (fn-ptx-kd m)) 75)
                (<= (fn-rtc-size (fn-ptx-cur m)) 15) (<= (fn-rtc-size (fn-ptx-acc m)) (fn-ptx-acc-max-state))
                (<= (fn-rtc-size (fn-ptx-b1 m)) 9) (<= (fn-rtc-size (fn-ptx-b3 m)) 9) (<= (fn-rtc-size (fn-ptx-hs m)) 4101)
                (<= (fn-rtc-size (fn-ptx-evd m)) 57) (<= (fn-rtc-size (fn-ptx-ph m)) 1) (natp q) (equal (fn-rtc-get 0 ev) :extend))
           (<= (fn-rtc-size (car (fn-ptx-step1 m ev st q))) (+ 8500 (fn-ptx-acc-max-state))))
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1) (fn-ptx-mk fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-ptx-committedp
                                                   fn-ptx-end fn-ptx-read fn-ptx-hash fn-ptx-start fn-ptx-answer fn-rtc-get fn-ptx-opened fn-ptx-wfp fn-ptx-evd+ fn-ptx-summary fn-ptx-kd-commit
                                                   fn-ptx-elen fn-ptx-nmsg fn-ptx-nspans fn-ptx-span-n fn-ptx-spans fn-ptx-spans-len fn-ptx-buf-len fn-ptx-span-pwrite mv-nth fn-ptx-release-bufs fn-ptx-gen fn-ptx-kd-frontier fn-ptx-pwrite fn-ptx-fsync fn-ptx-extend fn-ptx-atom))
           :do-not-induct t)))
(defthm fn-ptx-step1-size-fsync
  (implies (and (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-geo m)) 7) (<= (fn-rtc-size (fn-ptx-kd m)) 75)
                (<= (fn-rtc-size (fn-ptx-cur m)) 15) (<= (fn-rtc-size (fn-ptx-acc m)) (fn-ptx-acc-max-state))
                (<= (fn-rtc-size (fn-ptx-b1 m)) 9) (<= (fn-rtc-size (fn-ptx-b3 m)) 9) (<= (fn-rtc-size (fn-ptx-hs m)) 4101)
                (<= (fn-rtc-size (fn-ptx-evd m)) 57) (<= (fn-rtc-size (fn-ptx-ph m)) 1) (natp q) (equal (fn-rtc-get 0 ev) :fsync))
           (<= (fn-rtc-size (car (fn-ptx-step1 m ev st q))) (+ 8500 (fn-ptx-acc-max-state))))
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1) (fn-ptx-mk fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-ptx-committedp
                                                   fn-ptx-end fn-ptx-read fn-ptx-hash fn-ptx-start fn-ptx-answer fn-rtc-get fn-ptx-opened fn-ptx-wfp fn-ptx-evd+ fn-ptx-summary fn-ptx-kd-commit
                                                   fn-ptx-elen fn-ptx-nmsg fn-ptx-nspans fn-ptx-span-n fn-ptx-spans fn-ptx-spans-len fn-ptx-buf-len fn-ptx-span-pwrite mv-nth fn-ptx-release-bufs fn-ptx-gen fn-ptx-kd-frontier fn-ptx-pwrite fn-ptx-fsync fn-ptx-extend fn-ptx-atom))
           :do-not-induct t)))
(defthm fn-ptx-step1-size-pwrite
  (implies (and (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-geo m)) 7) (<= (fn-rtc-size (fn-ptx-kd m)) 75)
                (<= (fn-rtc-size (fn-ptx-cur m)) 15) (<= (fn-rtc-size (fn-ptx-acc m)) (fn-ptx-acc-max-state))
                (<= (fn-rtc-size (fn-ptx-b1 m)) 9) (<= (fn-rtc-size (fn-ptx-b3 m)) 9) (<= (fn-rtc-size (fn-ptx-hs m)) 4101)
                (<= (fn-rtc-size (fn-ptx-evd m)) 57) (<= (fn-rtc-size (fn-ptx-ph m)) 1) (natp q) (equal (fn-rtc-get 0 ev) :pwrite))
           (<= (fn-rtc-size (car (fn-ptx-step1 m ev st q))) (+ 8500 (fn-ptx-acc-max-state))))
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1) (fn-ptx-mk fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-ptx-committedp
                                                   fn-ptx-end fn-ptx-read fn-ptx-hash fn-ptx-start fn-ptx-answer fn-rtc-get fn-ptx-opened fn-ptx-wfp fn-ptx-evd+ fn-ptx-summary fn-ptx-kd-commit
                                                   fn-ptx-elen fn-ptx-nmsg fn-ptx-nspans fn-ptx-span-n fn-ptx-spans fn-ptx-spans-len fn-ptx-buf-len fn-ptx-span-pwrite mv-nth fn-ptx-release-bufs fn-ptx-gen fn-ptx-kd-frontier fn-ptx-pwrite fn-ptx-fsync fn-ptx-extend fn-ptx-atom))
           :do-not-induct t)))
(defthm fn-ptx-step1-size-hand
  (implies (and (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-geo m)) 7) (<= (fn-rtc-size (fn-ptx-kd m)) 75)
                (<= (fn-rtc-size (fn-ptx-cur m)) 15) (<= (fn-rtc-size (fn-ptx-acc m)) (fn-ptx-acc-max-state))
                (<= (fn-rtc-size (fn-ptx-b1 m)) 9) (<= (fn-rtc-size (fn-ptx-b3 m)) 9) (<= (fn-rtc-size (fn-ptx-hs m)) 4101)
                (<= (fn-rtc-size (fn-ptx-evd m)) 57) (<= (fn-rtc-size (fn-ptx-ph m)) 1) (natp q) (equal (fn-rtc-get 0 ev) :hand))
           (<= (fn-rtc-size (car (fn-ptx-step1 m ev st q))) (+ 8500 (fn-ptx-acc-max-state))))
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1) (fn-ptx-mk fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-ptx-committedp
                                                   fn-ptx-end fn-ptx-read fn-ptx-hash fn-ptx-start fn-ptx-answer fn-rtc-get fn-ptx-opened fn-ptx-wfp fn-ptx-evd+ fn-ptx-summary fn-ptx-kd-commit
                                                   fn-ptx-elen fn-ptx-nmsg fn-ptx-nspans fn-ptx-span-n fn-ptx-spans fn-ptx-spans-len fn-ptx-buf-len fn-ptx-span-pwrite mv-nth fn-ptx-release-bufs fn-ptx-gen fn-ptx-kd-frontier fn-ptx-pwrite fn-ptx-fsync fn-ptx-extend fn-ptx-atom))
           :do-not-induct t)))
(defthm fn-ptx-step1-size-other
  (implies (and (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-geo m)) 7) (<= (fn-rtc-size (fn-ptx-kd m)) 75)
                (<= (fn-rtc-size (fn-ptx-cur m)) 15) (<= (fn-rtc-size (fn-ptx-acc m)) (fn-ptx-acc-max-state))
                (<= (fn-rtc-size (fn-ptx-b1 m)) 9) (<= (fn-rtc-size (fn-ptx-b3 m)) 9) (<= (fn-rtc-size (fn-ptx-hs m)) 4101)
                (<= (fn-rtc-size (fn-ptx-evd m)) 57) (<= (fn-rtc-size (fn-ptx-ph m)) 1) (natp q) (not (member-equal (fn-rtc-get 0 ev) '(:opened :handed :timer :extend :fsync :pwrite :hand))))
           (<= (fn-rtc-size (car (fn-ptx-step1 m ev st q))) (+ 8500 (fn-ptx-acc-max-state))))
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1) (fn-ptx-mk fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-ptx-committedp
                                                   fn-ptx-end fn-ptx-read fn-ptx-hash fn-ptx-start fn-ptx-answer fn-rtc-get fn-ptx-opened fn-ptx-wfp fn-ptx-evd+ fn-ptx-summary fn-ptx-kd-commit
                                                   fn-ptx-elen fn-ptx-nmsg fn-ptx-nspans fn-ptx-span-n fn-ptx-spans fn-ptx-spans-len fn-ptx-buf-len fn-ptx-span-pwrite mv-nth fn-ptx-release-bufs fn-ptx-gen fn-ptx-kd-frontier fn-ptx-pwrite fn-ptx-fsync fn-ptx-extend fn-ptx-atom))
           :do-not-induct t)))
(defthm fn-ptx-step1-size
  (implies (and (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-geo m)) 7) (<= (fn-rtc-size (fn-ptx-kd m)) 75)
                (<= (fn-rtc-size (fn-ptx-cur m)) 15) (<= (fn-rtc-size (fn-ptx-acc m)) (fn-ptx-acc-max-state))
                (<= (fn-rtc-size (fn-ptx-b1 m)) 9) (<= (fn-rtc-size (fn-ptx-b3 m)) 9) (<= (fn-rtc-size (fn-ptx-hs m)) 4101)
                (<= (fn-rtc-size (fn-ptx-evd m)) 57) (<= (fn-rtc-size (fn-ptx-ph m)) 1) (natp q))
           (<= (fn-rtc-size (car (fn-ptx-step1 m ev st q))) (+ 8500 (fn-ptx-acc-max-state))))
  :hints (("Goal" :in-theory (disable fn-ptx-step1 fn-rtc-get fn-ptx-q fn-ptx-geo fn-ptx-kd fn-ptx-cur fn-ptx-acc fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-ph)
           :do-not-induct t :use (fn-ptx-step1-size-opened fn-ptx-step1-size-handed fn-ptx-step1-size-timer fn-ptx-step1-size-extend
                 fn-ptx-step1-size-fsync fn-ptx-step1-size-pwrite fn-ptx-step1-size-hand fn-ptx-step1-size-other))))
(defthm fn-ptx-step1-size-lin
  (implies (and (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-geo m)) 7) (<= (fn-rtc-size (fn-ptx-kd m)) 75)
                (<= (fn-rtc-size (fn-ptx-cur m)) 15) (<= (fn-rtc-size (fn-ptx-acc m)) (fn-ptx-acc-max-state))
                (<= (fn-rtc-size (fn-ptx-b1 m)) 9) (<= (fn-rtc-size (fn-ptx-b3 m)) 9) (<= (fn-rtc-size (fn-ptx-hs m)) 4101)
                (<= (fn-rtc-size (fn-ptx-evd m)) 57) (<= (fn-rtc-size (fn-ptx-ph m)) 1) (natp q))
           (<= (fn-rtc-size (car (fn-ptx-step1 m ev st q))) (+ 8500 (fn-ptx-acc-max-state))))
  :rule-classes :linear
  :hints (("Goal" :use fn-ptx-step1-size :in-theory (disable fn-ptx-step1 fn-ptx-step1-size))))

(defthm fn-ptx-step-facts
  (implies (natp q)
           (and (natp (mv-nth 2 (fn-ptx-step m ev st q)))
                (<= (+ (mv-nth 2 (fn-ptx-step m ev st q)) (fn-rtc-reqs-octets (mv-nth 1 (fn-ptx-step m ev st q))))
                    (+ q (fn-ptx-c)))
                (<= (len (mv-nth 1 (fn-ptx-step m ev st q))) (fn-ptx-max-reqs))
                (<= (fn-rtc-size (mv-nth 0 (fn-ptx-step m ev st q))) (fn-ptx-max-state))))
  :hints (("Goal" :in-theory (e/d (fn-ptx-step fn-ptx-wf-cost fn-ptx-c fn-ptx-max-reqs fn-ptx-max-state) (fn-ptx-step1 fn-ptx-wfp fn-ptx-wfp-sizes fn-ptx-broken fn-ptx-q fn-ptx-geo fn-ptx-kd fn-ptx-cur fn-ptx-acc fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-ph))
           :use ((:instance fn-ptx-wfp-sizes))
           :do-not-induct t)))


(defthm fn-ptx-nfix-nfix (equal (nfix (nfix q)) (nfix q)))
(defthm fn-ptx-read-w-nfix
  (equal (fn-ptx-read-w (nfix q)) (fn-ptx-read-w q))
  :hints (("Goal" :in-theory (enable fn-ptx-read-w))))
(defthm fn-ptx-read-nfix-q
  (equal (fn-ptx-read m q id inc st) (fn-ptx-read m (nfix q) id inc st))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-nfix-nfix fn-ptx-read-w-nfix))
           :expand ((fn-ptx-read m q id inc st) (fn-ptx-read m (nfix q) id inc st)))))
(defthm fn-ptx-hash-nfix-q
  (equal (fn-ptx-hash m q id inc st) (fn-ptx-hash m (nfix q) id inc st))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-nfix-nfix))
           :expand ((fn-ptx-hash m q id inc st) (fn-ptx-hash m (nfix q) id inc st)))))
(defthm fn-ptx-step1-nfix-q
  (equal (fn-ptx-step1 m ev st q) (fn-ptx-step1 m ev st (nfix q)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-nfix-nfix))
           :expand ((fn-ptx-step1 m ev st q) (fn-ptx-step1 m ev st (nfix q)))
           :use ((:instance fn-ptx-read-nfix-q (id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev)))
                 (:instance fn-ptx-hash-nfix-q (id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev)))))))
(defthm fn-ptx-step-nfix-q
  (equal (fn-ptx-step m ev st q) (fn-ptx-step m ev st (nfix q)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ptx-step) (fn-ptx-step1 fn-ptx-wfp fn-ptx-broken fn-ptx-wf-cost))
           :use ((:instance fn-ptx-step1-nfix-q)))))
(defthm fn-ptx-step-requests-bounded
  (<= (len (mv-nth 1 (fn-ptx-step m ev st q))) (fn-ptx-max-reqs))
  :hints (("Goal" :in-theory (disable fn-ptx-step fn-ptx-step-facts fn-ptx-max-reqs)
           :use ((:instance fn-ptx-step-facts (q (nfix q))) fn-ptx-step-nfix-q))))
(defthm fn-ptx-step-state-bounded
  (<= (fn-rtc-size (mv-nth 0 (fn-ptx-step m ev st q))) (fn-ptx-max-state))
  :hints (("Goal" :in-theory (disable fn-ptx-step fn-ptx-step-facts fn-ptx-max-state)
           :use ((:instance fn-ptx-step-facts (q (nfix q))) fn-ptx-step-nfix-q))))

(defthm fn-ptx-start-committed
  (equal (fn-ptx-committedp (car (fn-ptx-start p q kd ext geo committed))) (and committed t))
  :hints (("Goal" :in-theory (e/d (fn-ptx-start) (fn-ptx-mk fn-ptx-committedp)))))
(defthm fn-ptx-end-committed
  (equal (fn-ptx-committedp (car (fn-ptx-end m o kd ext fenced committed id inc st))) (and committed t))
  :hints (("Goal" :in-theory (e/d (fn-ptx-end) (fn-ptx-mk fn-ptx-committedp fn-ptx-start fn-ptx-answer fn-ptx-release-bufs fn-ptx-refuse-all)))))

(defthm fn-ptx-end-committed-mv
  (equal (fn-ptx-committedp (mv-nth 0 (fn-ptx-end m o kd ext fenced committed id inc st))) (and committed t))
  :hints (("Goal" :use fn-ptx-end-committed :in-theory (disable fn-ptx-end-committed fn-ptx-end fn-ptx-committedp))))
(defthm fn-ptx-start-committed-mv
  (equal (fn-ptx-committedp (mv-nth 0 (fn-ptx-start p q kd ext geo committed))) (and committed t))
  :hints (("Goal" :use fn-ptx-start-committed :in-theory (disable fn-ptx-start-committed fn-ptx-start fn-ptx-committedp))))
(defthm fn-ptx-read-uncommitted
  (not (fn-ptx-committedp (car (fn-ptx-read m q id inc st))))
  :hints (("Goal" :in-theory (e/d (fn-ptx-read) (fn-ptx-read-w fn-ptx-mk fn-ptx-committedp fn-ptx-end fn-ptx-start fn-ptx-free fn-ptx-head-end fn-ptx-range fn-ptx-cap fn-ptx-gen fn-ptx-frame-header min mv-nth
                                                 fn-ptx-write-nz fn-bs-zeros take fn-ptx-timer fn-ptx-buf-h fn-ptx-buf-g fn-ptx-buf-len fn-ptx-buf-x
                                                 fn-rtc-get fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur
                                                 fn-ptx-hmax fn-ptx-fmax fn-ptx-cur-bp fn-ptx-cur-len fn-ptx-cur-hoff fn-ptx-cur-fid fn-ptx-cur-finc fn-ptx-cur-txid fn-ptx-cur-ioff fn-ptx-kd-last))
           :do-not-induct t)))

(defthm fn-ptx-hash-uncommitted
  (not (fn-ptx-committedp (car (fn-ptx-hash m q id inc st))))
  :hints (("Goal" :in-theory (e/d (fn-ptx-hash) (fn-ptx-end fn-ptx-mk fn-ptx-absorb fn-ptx-finish-digest fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-rtc-get fn-ptx-committedp
                                                 fn-ptx-unit fn-ptx-buf-h fn-ptx-buf-g fn-ptx-buf-len fn-ptx-spans fn-ptx-spans-len fn-ptx-span-pwrite min max floor fn-olr-extension-needed-p fn-olr-extension-target fn-ptx-pad-len fn-ptx-kd-frontier fn-ptx-timer fn-ptx-extend fn-ptx-pwrite fn-ptx-fsync))
           :do-not-induct t)))

(defthm fn-ptx-opened-uncommitted
  (not (fn-ptx-committedp (fn-ptx-opened kd ext geo)))
  :hints (("Goal" :in-theory (e/d (fn-ptx-opened) (fn-ptx-mk fn-ptx-committedp)))))
(defthm fn-ptx-step1-committed
  (implies (fn-ptx-committedp (car (fn-ptx-step1 m ev st q)))
           (and (equal (fn-ptx-ph m) :committing) (fn-rtc-fsync-done-p ev)))
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1 fn-rtc-fsync-done-p) (fn-ptx-mk fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-ptx-committedp
                                                   fn-ptx-read fn-ptx-hash fn-ptx-opened fn-ptx-wfp fn-ptx-evd+ fn-ptx-kd-commit fn-ptx-answer fn-ptx-start fn-ptx-end fn-rtc-get
                                                   fn-ptx-elen fn-ptx-nmsg fn-ptx-nspans fn-ptx-span-n fn-ptx-spans fn-ptx-spans-len fn-ptx-buf-len fn-ptx-span-pwrite mv-nth fn-ptx-release-bufs fn-ptx-gen fn-ptx-kd-frontier fn-ptx-pwrite fn-ptx-fsync fn-ptx-extend fn-ptx-atom fn-ptx-summary))
           :do-not-induct t)))
(defthm fn-ptx-commits-only-on-fsync-done
  (implies (and (not (fn-ptx-committedp m)) (fn-ptx-committedp (mv-nth 0 (fn-ptx-step m ev st q))))
           (fn-rtc-fsync-done-p ev))
  :hints (("Goal" :in-theory (e/d (fn-ptx-step) (fn-ptx-step1 fn-ptx-wfp fn-ptx-committedp fn-ptx-broken))
           :use ((:instance fn-ptx-step1-committed)) :do-not-induct t)))
(defthm fn-ptx-commit-is-the-barrier-completion
  (fn-ptx-p1 m ev st q)
  :hints (("Goal" :in-theory (e/d (fn-ptx-p1 fn-ptx-step) (fn-ptx-step1 fn-ptx-wfp fn-ptx-committedp fn-ptx-broken))
           :use ((:instance fn-ptx-step1-committed)) :do-not-induct t)))

(defthm fn-ptx-codes-to-nonwrite
  (implies (not (equal (fn-rtc-get 0 r) :write))
           (equal (fn-ptx-codes-to (cons r x)) (fn-ptx-codes-to x)))
  :hints (("Goal" :in-theory (enable fn-ptx-codes-to))))
(defthm fn-ptx-codes-to-answer
  (equal (fn-ptx-codes-to (append (fn-ptx-answer p o id inc st) rest))
         (cons (list (fn-ptx-cur-bp p) (fn-ptx-code o)) (fn-ptx-codes-to rest)))
  :hints (("Goal" :in-theory (e/d (fn-ptx-answer fn-ptx-codes-to) (fn-ptx-code fn-ptx-cur-bp fn-ptx-gen)))))
(defthm fn-ptx-codes-to-release-bufs
  (equal (fn-ptx-codes-to (append (fn-ptx-release-bufs m id inc st) rest)) (fn-ptx-codes-to rest))
  :hints (("Goal" :in-theory (e/d (fn-ptx-release-bufs) (fn-ptx-codes-to fn-ptx-gen)))))
(defthm fn-ptx-code-for-cons
  (equal (fn-ptx-code-for h (cons (list h2 c) rest))
         (if (equal h h2) c (fn-ptx-code-for h rest)))
  :hints (("Goal" :in-theory (enable fn-ptx-code-for))))
(defthm fn-ptx-codes-to-answer-alone
  (equal (fn-ptx-codes-to (fn-ptx-answer p o id inc st))
         (list (list (fn-ptx-cur-bp p) (fn-ptx-code o))))
  :hints (("Goal" :use ((:instance fn-ptx-codes-to-answer (rest nil)))
           :in-theory (e/d (fn-ptx-codes-to) (fn-ptx-codes-to-answer fn-ptx-answer fn-ptx-code fn-ptx-cur-bp)))))
(defthm fn-ptx-codes-to-release-bufs-alone
  (equal (fn-ptx-codes-to (fn-ptx-release-bufs m id inc st)) nil)
  :hints (("Goal" :use ((:instance fn-ptx-codes-to-release-bufs (rest nil)))
           :in-theory (e/d (fn-ptx-codes-to) (fn-ptx-codes-to-release-bufs fn-ptx-release-bufs)))))
(defthm fn-ptx-end-cur-code
  (implies (equal (fn-ptx-cur m0) (fn-ptx-cur m))
           (equal (fn-ptx-cur-code m (mv-nth 1 (fn-ptx-end m0 o kd ext fenced committed id inc st)))
                  (if (consp (fn-ptx-cur m)) (fn-ptx-code o) nil)))
  :hints (("Goal" :in-theory (e/d (fn-ptx-end fn-ptx-cur-code) (fn-ptx-mk fn-ptx-start fn-ptx-answer fn-ptx-release-bufs fn-ptx-refuse-all fn-ptx-code fn-ptx-cur fn-ptx-cur-bp fn-ptx-codes-to fn-ptx-code-for))
           :do-not-induct t)))
(defthm fn-ptx-end-fenced-ph
  (equal (fn-ptx-ph (mv-nth 0 (fn-ptx-end m o kd ext t committed id inc st))) :fenced)
  :hints (("Goal" :in-theory (e/d (fn-ptx-end) (fn-ptx-mk fn-ptx-ph fn-ptx-start fn-ptx-answer fn-ptx-release-bufs fn-ptx-refuse-all)))))
(defthm fn-ptx-end-fenced-ph-car
  (equal (fn-ptx-ph (car (fn-ptx-end m o kd ext t committed id inc st))) :fenced)
  :hints (("Goal" :use fn-ptx-end-fenced-ph :in-theory (disable fn-ptx-end-fenced-ph fn-ptx-end fn-ptx-ph))))
(defthm fn-ptx-cur-code-of-no-codes
  (implies (null (fn-ptx-codes-to reqs)) (null (fn-ptx-cur-code m reqs)))
  :hints (("Goal" :in-theory (enable fn-ptx-cur-code fn-ptx-code-for))))
(defthm fn-ptx-codes-to-read-start2
  (equal (fn-ptx-codes-to (list* (list :acquire a) (list :write b c 0 d) (list :acquire e) (list :write f g 0 h) '((:submit :timer nil (0)))))
         nil)
  :hints (("Goal" :in-theory (enable fn-ptx-codes-to fn-rtc-get))))
(defthm fn-ptx-cur-code-read-start
  (equal (fn-ptx-cur-code m (list* (list :acquire a) (list :write b c 0 d) (list :acquire e) (list :write f g 0 h) '((:submit :timer nil (0))))) nil))
(defthm fn-ptx-cur-code-timer
  (equal (fn-ptx-cur-code m '((:submit :timer nil (0)))) nil))
(defthm fn-ptx-cur-code-nil
  (null (fn-ptx-cur-code m nil))
  :hints (("Goal" :in-theory (enable fn-ptx-cur-code fn-ptx-codes-to fn-ptx-code-for))))
(defthm fn-ptx-cur-code-single-nonwrite
  (implies (not (equal (fn-rtc-get 0 r) :write))
           (null (fn-ptx-cur-code m (list r))))
  :hints (("Goal" :in-theory (enable fn-ptx-cur-code fn-ptx-codes-to fn-ptx-code-for))))
(defthm fn-ptx-cur-code-answer-alone
  (equal (fn-ptx-cur-code m (fn-ptx-answer p o id inc st))
         (and (consp (fn-ptx-cur m))
              (if (equal (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-bp p)) (fn-ptx-code o) nil)))
  :hints (("Goal" :in-theory (e/d (fn-ptx-cur-code) (fn-ptx-answer fn-ptx-code fn-ptx-cur-bp fn-ptx-cur)))))
(defthm fn-ptx-cur-code-nil-012
  (and (not (equal (fn-ptx-cur-code m nil) 0)) (not (equal (fn-ptx-cur-code m nil) 1)) (not (equal (fn-ptx-cur-code m nil) 2)))
  :hints (("Goal" :in-theory (enable fn-ptx-cur-code fn-ptx-codes-to fn-ptx-code-for))))
(defthm fn-ptx-cur-code-single-nonwrite-012
  (implies (not (equal (fn-rtc-get 0 r) :write))
           (and (not (equal (fn-ptx-cur-code m (list r)) 0)) (not (equal (fn-ptx-cur-code m (list r)) 1)) (not (equal (fn-ptx-cur-code m (list r)) 2))))
  :hints (("Goal" :use fn-ptx-cur-code-single-nonwrite :in-theory (disable fn-ptx-cur-code-single-nonwrite fn-ptx-cur-code))))
(defthm fn-ptx-start-reqs
  (equal (mv-nth 1 (fn-ptx-start p q kd ext geo committed)) '((:submit :timer nil (0))))
  :hints (("Goal" :in-theory (enable fn-ptx-start fn-ptx-timer))))
(defthm fn-ptx-step1-code-facts-opened
  (implies (equal (fn-rtc-get 0 ev) :opened)
    (let* ((r (fn-ptx-step1 m ev st q))
         (cc (fn-ptx-cur-code m (mv-nth 1 r)))
         (ph (fn-ptx-ph m)))
    (and (implies (equal cc 2)
                  (and (member-eq ph '(:payload-writing :log-writing :committing))
                       (equal (fn-ptx-ph (mv-nth 0 r)) :fenced)))
         (implies (equal cc 1) (not (member-eq ph '(:payload-writing :log-writing :committing))))
         (implies (equal cc 0)
                  (and (equal ph :committing) (equal (fn-rtc-get 0 ev) :fsync)
                       (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1 fn-ptx-fsync fn-ptx-timer fn-ptx-pwrite fn-ptx-extend)
                                  (fn-ptx-mk fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-ptx-committedp
                                   fn-ptx-end fn-ptx-start fn-ptx-answer fn-ptx-cur-code fn-ptx-opened fn-ptx-wfp fn-ptx-evd+ fn-ptx-kd-commit
                                   fn-ptx-elen fn-ptx-nmsg fn-ptx-nspans fn-ptx-span-n fn-ptx-spans fn-ptx-spans-len fn-ptx-buf-len fn-ptx-span-pwrite mv-nth fn-ptx-release-bufs fn-ptx-gen fn-ptx-kd-frontier fn-ptx-atom fn-ptx-summary
                                   fn-ptx-read fn-ptx-hash fn-ptx-cur-bp fn-ptx-code))
           :do-not-induct t)))
(defthm fn-ptx-step1-code-facts-handed
  (implies (equal (fn-rtc-get 0 ev) :handed)
    (let* ((r (fn-ptx-step1 m ev st q))
         (cc (fn-ptx-cur-code m (mv-nth 1 r)))
         (ph (fn-ptx-ph m)))
    (and (implies (equal cc 2)
                  (and (member-eq ph '(:payload-writing :log-writing :committing))
                       (equal (fn-ptx-ph (mv-nth 0 r)) :fenced)))
         (implies (equal cc 1) (not (member-eq ph '(:payload-writing :log-writing :committing))))
         (implies (equal cc 0)
                  (and (equal ph :committing) (equal (fn-rtc-get 0 ev) :fsync)
                       (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1 fn-ptx-fsync fn-ptx-timer fn-ptx-pwrite fn-ptx-extend)
                                  (fn-ptx-mk fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-ptx-committedp
                                   fn-ptx-end fn-ptx-start fn-ptx-answer fn-ptx-cur-code fn-ptx-opened fn-ptx-wfp fn-ptx-evd+ fn-ptx-kd-commit
                                   fn-ptx-elen fn-ptx-nmsg fn-ptx-nspans fn-ptx-span-n fn-ptx-spans fn-ptx-spans-len fn-ptx-buf-len fn-ptx-span-pwrite mv-nth fn-ptx-release-bufs fn-ptx-gen fn-ptx-kd-frontier fn-ptx-atom fn-ptx-summary
                                   fn-ptx-read fn-ptx-hash fn-ptx-cur-bp fn-ptx-code))
           :do-not-induct t)))
(defthm fn-ptx-step1-code-facts-extend
  (implies (equal (fn-rtc-get 0 ev) :extend)
    (let* ((r (fn-ptx-step1 m ev st q))
         (cc (fn-ptx-cur-code m (mv-nth 1 r)))
         (ph (fn-ptx-ph m)))
    (and (implies (equal cc 2)
                  (and (member-eq ph '(:payload-writing :log-writing :committing))
                       (equal (fn-ptx-ph (mv-nth 0 r)) :fenced)))
         (implies (equal cc 1) (not (member-eq ph '(:payload-writing :log-writing :committing))))
         (implies (equal cc 0)
                  (and (equal ph :committing) (equal (fn-rtc-get 0 ev) :fsync)
                       (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1 fn-ptx-fsync fn-ptx-timer fn-ptx-pwrite fn-ptx-extend)
                                  (fn-ptx-mk fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-ptx-committedp
                                   fn-ptx-end fn-ptx-start fn-ptx-answer fn-ptx-cur-code fn-ptx-opened fn-ptx-wfp fn-ptx-evd+ fn-ptx-kd-commit
                                   fn-ptx-elen fn-ptx-nmsg fn-ptx-nspans fn-ptx-span-n fn-ptx-spans fn-ptx-spans-len fn-ptx-buf-len fn-ptx-span-pwrite mv-nth fn-ptx-release-bufs fn-ptx-gen fn-ptx-kd-frontier fn-ptx-atom fn-ptx-summary
                                   fn-ptx-read fn-ptx-hash fn-ptx-cur-bp fn-ptx-code))
           :do-not-induct t)))
(defthm fn-ptx-step1-code-facts-fsync
  (implies (equal (fn-rtc-get 0 ev) :fsync)
    (let* ((r (fn-ptx-step1 m ev st q))
         (cc (fn-ptx-cur-code m (mv-nth 1 r)))
         (ph (fn-ptx-ph m)))
    (and (implies (equal cc 2)
                  (and (member-eq ph '(:payload-writing :log-writing :committing))
                       (equal (fn-ptx-ph (mv-nth 0 r)) :fenced)))
         (implies (equal cc 1) (not (member-eq ph '(:payload-writing :log-writing :committing))))
         (implies (equal cc 0)
                  (and (equal ph :committing) (equal (fn-rtc-get 0 ev) :fsync)
                       (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1 fn-ptx-fsync fn-ptx-timer fn-ptx-pwrite fn-ptx-extend)
                                  (fn-ptx-mk fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-ptx-committedp
                                   fn-ptx-end fn-ptx-start fn-ptx-answer fn-ptx-cur-code fn-ptx-opened fn-ptx-wfp fn-ptx-evd+ fn-ptx-kd-commit
                                   fn-ptx-elen fn-ptx-nmsg fn-ptx-nspans fn-ptx-span-n fn-ptx-spans fn-ptx-spans-len fn-ptx-buf-len fn-ptx-span-pwrite mv-nth fn-ptx-release-bufs fn-ptx-gen fn-ptx-kd-frontier fn-ptx-atom fn-ptx-summary
                                   fn-ptx-read fn-ptx-hash fn-ptx-cur-bp fn-ptx-code))
           :do-not-induct t)))
(defthm fn-ptx-step1-code-facts-pwrite
  (implies (equal (fn-rtc-get 0 ev) :pwrite)
    (let* ((r (fn-ptx-step1 m ev st q))
         (cc (fn-ptx-cur-code m (mv-nth 1 r)))
         (ph (fn-ptx-ph m)))
    (and (implies (equal cc 2)
                  (and (member-eq ph '(:payload-writing :log-writing :committing))
                       (equal (fn-ptx-ph (mv-nth 0 r)) :fenced)))
         (implies (equal cc 1) (not (member-eq ph '(:payload-writing :log-writing :committing))))
         (implies (equal cc 0)
                  (and (equal ph :committing) (equal (fn-rtc-get 0 ev) :fsync)
                       (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1 fn-ptx-fsync fn-ptx-timer fn-ptx-pwrite fn-ptx-extend)
                                  (fn-ptx-mk fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-ptx-committedp
                                   fn-ptx-end fn-ptx-start fn-ptx-answer fn-ptx-cur-code fn-ptx-opened fn-ptx-wfp fn-ptx-evd+ fn-ptx-kd-commit
                                   fn-ptx-elen fn-ptx-nmsg fn-ptx-nspans fn-ptx-span-n fn-ptx-spans fn-ptx-spans-len fn-ptx-buf-len fn-ptx-span-pwrite mv-nth fn-ptx-release-bufs fn-ptx-gen fn-ptx-kd-frontier fn-ptx-atom fn-ptx-summary
                                   fn-ptx-read fn-ptx-hash fn-ptx-cur-bp fn-ptx-code))
           :do-not-induct t)))
(defthm fn-ptx-step1-code-facts-hand
  (implies (equal (fn-rtc-get 0 ev) :hand)
    (let* ((r (fn-ptx-step1 m ev st q))
         (cc (fn-ptx-cur-code m (mv-nth 1 r)))
         (ph (fn-ptx-ph m)))
    (and (implies (equal cc 2)
                  (and (member-eq ph '(:payload-writing :log-writing :committing))
                       (equal (fn-ptx-ph (mv-nth 0 r)) :fenced)))
         (implies (equal cc 1) (not (member-eq ph '(:payload-writing :log-writing :committing))))
         (implies (equal cc 0)
                  (and (equal ph :committing) (equal (fn-rtc-get 0 ev) :fsync)
                       (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1 fn-ptx-fsync fn-ptx-timer fn-ptx-pwrite fn-ptx-extend)
                                  (fn-ptx-mk fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-ptx-committedp
                                   fn-ptx-end fn-ptx-start fn-ptx-answer fn-ptx-cur-code fn-ptx-opened fn-ptx-wfp fn-ptx-evd+ fn-ptx-kd-commit
                                   fn-ptx-elen fn-ptx-nmsg fn-ptx-nspans fn-ptx-span-n fn-ptx-spans fn-ptx-spans-len fn-ptx-buf-len fn-ptx-span-pwrite mv-nth fn-ptx-release-bufs fn-ptx-gen fn-ptx-kd-frontier fn-ptx-atom fn-ptx-summary
                                   fn-ptx-read fn-ptx-hash fn-ptx-cur-bp fn-ptx-code))
           :do-not-induct t)))
(defthm fn-ptx-step1-code-facts-other
  (implies (not (member-equal (fn-rtc-get 0 ev) '(:opened :handed :timer :extend :fsync :pwrite :hand)))
    (let* ((r (fn-ptx-step1 m ev st q))
         (cc (fn-ptx-cur-code m (mv-nth 1 r)))
         (ph (fn-ptx-ph m)))
    (and (implies (equal cc 2)
                  (and (member-eq ph '(:payload-writing :log-writing :committing))
                       (equal (fn-ptx-ph (mv-nth 0 r)) :fenced)))
         (implies (equal cc 1) (not (member-eq ph '(:payload-writing :log-writing :committing))))
         (implies (equal cc 0)
                  (and (equal ph :committing) (equal (fn-rtc-get 0 ev) :fsync)
                       (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1 fn-ptx-fsync fn-ptx-timer fn-ptx-pwrite fn-ptx-extend)
                                  (fn-ptx-mk fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-ptx-committedp
                                   fn-ptx-end fn-ptx-start fn-ptx-answer fn-ptx-cur-code fn-ptx-opened fn-ptx-wfp fn-ptx-evd+ fn-ptx-kd-commit
                                   fn-ptx-elen fn-ptx-nmsg fn-ptx-nspans fn-ptx-span-n fn-ptx-spans fn-ptx-spans-len fn-ptx-buf-len fn-ptx-span-pwrite mv-nth fn-ptx-release-bufs fn-ptx-gen fn-ptx-kd-frontier fn-ptx-atom fn-ptx-summary
                                   fn-ptx-read fn-ptx-hash fn-ptx-cur-bp fn-ptx-code))
           :do-not-induct t)))

(defun fn-ptx-submit-hand-p (r)
  (and (equal (fn-rtc-get 0 r) :submit) (equal (fn-rtc-get 1 r) :hand)))
(defun fn-ptx-no-hand-p (reqs)
  (if (consp reqs)
      (and (not (fn-ptx-submit-hand-p (car reqs)))
           (fn-ptx-no-hand-p (cdr reqs)))
    t))
(defthm fn-ptx-no-hand-p-append
  (equal (fn-ptx-no-hand-p (append a b)) (and (fn-ptx-no-hand-p a) (fn-ptx-no-hand-p b)))
  :hints (("Goal" :in-theory (enable fn-ptx-no-hand-p))))
(defthm fn-ptx-no-hand-p-cons
  (equal (fn-ptx-no-hand-p (cons r x))
         (and (not (fn-ptx-submit-hand-p r)) (fn-ptx-no-hand-p x)))
  :hints (("Goal" :in-theory (enable fn-ptx-no-hand-p))))
(defthm fn-ptx-no-hand-p-nil (fn-ptx-no-hand-p nil)
  :hints (("Goal" :in-theory (enable fn-ptx-no-hand-p))))
(defthm fn-ptx-no-hand-p-write-nz
  (fn-ptx-no-hand-p (fn-ptx-write-nz h g off octets))
  :hints (("Goal" :in-theory (enable fn-ptx-write-nz fn-ptx-submit-hand-p fn-rtc-get))))
(defthm fn-ptx-codes-to-no-hand
  (implies (fn-ptx-no-hand-p x) (equal (fn-ptx-codes-to x) nil))
  :hints (("Goal" :in-theory (enable fn-ptx-codes-to fn-ptx-no-hand-p))))

(defthm fn-ptx-codes-to-cons-skip
  (implies (not (fn-ptx-submit-hand-p (car l)))
           (equal (fn-ptx-codes-to (cons r l)) (fn-ptx-codes-to l)))
  :hints (("Goal" :in-theory (enable fn-ptx-codes-to fn-ptx-submit-hand-p))))
(defthm fn-ptx-no-hand-p-car
  (implies (and (fn-ptx-no-hand-p w) (consp w)) (not (fn-ptx-submit-hand-p (car w))))
  :hints (("Goal" :in-theory (enable fn-ptx-no-hand-p))))
(defthm fn-ptx-car-append-nohand
  (implies (and (fn-ptx-no-hand-p w) (not (fn-ptx-submit-hand-p x)))
           (not (fn-ptx-submit-hand-p (car (append w (cons x tail))))))
  :hints (("Goal" :in-theory (enable fn-ptx-no-hand-p))))
(defthm fn-ptx-codes-to-append-nohand
  (implies (and (fn-ptx-no-hand-p w) (not (fn-ptx-submit-hand-p x)))
           (equal (fn-ptx-codes-to (append w (cons x tail))) (fn-ptx-codes-to (cons x tail))))
  :hints (("Goal" :induct (fn-ptx-no-hand-p w)
           :in-theory (e/d (fn-ptx-no-hand-p) (fn-ptx-codes-to fn-ptx-submit-hand-p fn-ptx-codes-to-cons-skip)))
          ("Subgoal *1/1" :use ((:instance fn-ptx-codes-to-cons-skip (r (car w)) (l (append (cdr w) (cons x tail)))) (:instance fn-ptx-car-append-nohand (w (cdr w)))))))

(defthm fn-ptx-no-hand-p-release-bufs
  (fn-ptx-no-hand-p (fn-ptx-release-bufs m id inc st))
  :hints (("Goal" :in-theory (enable fn-ptx-release-bufs fn-ptx-no-hand-p fn-ptx-submit-hand-p fn-rtc-get))))
(defthm fn-ptx-answer-shape
  (and (consp (fn-ptx-answer p o id inc st))
       (equal (fn-rtc-get 0 (car (fn-ptx-answer p o id inc st))) :write)
       (not (fn-ptx-submit-hand-p (car (fn-ptx-answer p o id inc st)))))
  :hints (("Goal" :in-theory (enable fn-ptx-answer fn-ptx-submit-hand-p fn-rtc-get))))
(defthm fn-ptx-car-append-gen
  (implies (and (fn-ptx-no-hand-p a) (not (fn-ptx-submit-hand-p (car b))))
           (not (fn-ptx-submit-hand-p (car (append a b)))))
  :hints (("Goal" :in-theory (enable fn-ptx-no-hand-p))))
(defthm fn-ptx-done-car
  (and (consp (append (fn-ptx-release-bufs m id inc st) (fn-ptx-answer p o id inc st)))
       (not (fn-ptx-submit-hand-p (car (append (fn-ptx-release-bufs m id inc st) (fn-ptx-answer p o id inc st))))))
  :hints (("Goal" :use ((:instance fn-ptx-car-append-gen (a (fn-ptx-release-bufs m id inc st)) (b (fn-ptx-answer p o id inc st))))
           :in-theory (disable fn-ptx-car-append-gen fn-ptx-release-bufs fn-ptx-answer fn-ptx-submit-hand-p))))

(defthm fn-ptx-car-append-consp
  (implies (consp a) (equal (car (append a x)) (car a))))
(defthm fn-ptx-answer-car-append
  (not (fn-ptx-submit-hand-p (car (append (fn-ptx-answer p o id inc st) x))))
  :hints (("Goal" :use (fn-ptx-answer-shape (:instance fn-ptx-car-append-consp (a (fn-ptx-answer p o id inc st)))) :in-theory (disable fn-ptx-car-append-consp fn-ptx-answer-shape fn-ptx-answer fn-ptx-submit-hand-p))))
(defthm fn-ptx-done-car-append
  (not (fn-ptx-submit-hand-p (car (append (append (fn-ptx-release-bufs m id inc st) (fn-ptx-answer p o id inc st)) x))))
  :hints (("Goal" :use ((:instance fn-ptx-car-append-gen (a (fn-ptx-release-bufs m id inc st)) (b (append (fn-ptx-answer p o id inc st) x))) (:instance fn-ptx-answer-car-append))
           :in-theory (disable fn-ptx-done-car fn-ptx-car-append-gen fn-ptx-answer-car-append fn-ptx-release-bufs fn-ptx-answer fn-ptx-submit-hand-p))))
(defthm fn-ptx-end-car-not-hand
  (not (fn-ptx-submit-hand-p (car (mv-nth 1 (fn-ptx-end m o kd ext fenced committed id inc st)))))
  :hints (("Goal" :in-theory (e/d (fn-ptx-end) (fn-ptx-mk fn-ptx-start fn-ptx-answer fn-ptx-release-bufs fn-ptx-refuse-all fn-ptx-submit-hand-p fn-ptx-done-car fn-ptx-done-car-append))
           :use ((:instance fn-ptx-done-car-append (p (fn-ptx-cur m)) (x nil))) :do-not-induct t)))

(defthm fn-ptx-cur-code-cons-skip
  (implies (not (fn-ptx-submit-hand-p (car l)))
           (equal (fn-ptx-cur-code m (cons r l)) (fn-ptx-cur-code m l)))
  :hints (("Goal" :in-theory (e/d (fn-ptx-cur-code) (fn-ptx-codes-to fn-ptx-submit-hand-p)))))
(defthm fn-ptx-cur-code-no-hand-eq
  (implies (fn-ptx-no-hand-p x) (equal (fn-ptx-cur-code m x) nil))
  :hints (("Goal" :use fn-ptx-codes-to-no-hand
           :in-theory (e/d (fn-ptx-cur-code fn-ptx-code-for) (fn-ptx-codes-to fn-ptx-codes-to-no-hand fn-ptx-no-hand-p)))))
(defthm fn-ptx-cur-code-nil-eq
  (equal (fn-ptx-cur-code m nil) nil)
  :hints (("Goal" :in-theory (enable fn-ptx-cur-code fn-ptx-codes-to fn-ptx-code-for))))
(defthm fn-ptx-cur-code-append-nohand
  (implies (and (fn-ptx-no-hand-p w) (not (fn-ptx-submit-hand-p x)))
           (equal (fn-ptx-cur-code m (append w (cons x tail))) (fn-ptx-cur-code m (cons x tail))))
  :hints (("Goal" :in-theory (e/d (fn-ptx-cur-code) (fn-ptx-codes-to fn-ptx-submit-hand-p fn-ptx-no-hand-p)))))
(defthm fn-ptx-pwrite-kind
  (equal (fn-rtc-get 1 (fn-ptx-pwrite h g off n pos)) :pwrite)
  :hints (("Goal" :in-theory (enable fn-ptx-pwrite fn-rtc-get))))
(defthm fn-ptx-span-pwrite-kind
  (equal (fn-rtc-get 1 (fn-ptx-span-pwrite i m front id inc st)) :pwrite)
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-span-pwrite fn-ptx-pwrite-kind)))))

(defthm fn-ptx-timer-nohand (not (fn-ptx-submit-hand-p (fn-ptx-timer))))
(defthm fn-ptx-fsync-nohand (not (fn-ptx-submit-hand-p (fn-ptx-fsync))))
(defthm fn-ptx-extend-nohand (not (fn-ptx-submit-hand-p (fn-ptx-extend ext nxt)))
  :hints (("Goal" :in-theory (enable fn-ptx-submit-hand-p fn-ptx-extend fn-rtc-get))))
(defthm fn-ptx-span-pwrite-nohand (not (fn-ptx-submit-hand-p (fn-ptx-span-pwrite i m front id inc st)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn-ptx-submit-hand-p fn-ptx-span-pwrite-kind fn-ptx-span-pwrite-head (:executable-counterpart equal) (:executable-counterpart not))))))

(defthm fn-ptx-hash-cur-code
  (let ((cc (fn-ptx-cur-code m (mv-nth 1 (fn-ptx-hash m q id inc st)))))
    (or (null cc) (equal cc 1)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ptx-hash) (fn-ptx-end fn-ptx-mk fn-ptx-absorb fn-ptx-finish-digest fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-rtc-get fn-ptx-committedp
                                   fn-ptx-unit fn-ptx-buf-h fn-ptx-buf-g fn-ptx-buf-len fn-ptx-spans fn-ptx-spans-len fn-ptx-span-pwrite min max floor fn-olr-extension-needed-p fn-olr-extension-target fn-ptx-pad-len fn-ptx-kd-frontier fn-ptx-timer fn-ptx-extend fn-ptx-pwrite fn-ptx-fsync
                                   fn-ptx-cur-code fn-ptx-submit-hand-p mv-nth))
           :use ((:instance fn-ptx-cur-code-nil) (:instance fn-ptx-end-cur-code (m0 (fn-ptx-chg m :committed nil)) (o :refused) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m)) (fenced nil) (committed nil)))
           :do-not-induct t)))

(defthm fn-ptx-request-kinds-nohand
  (and (not (fn-ptx-submit-hand-p (list :release a b)))
       (not (fn-ptx-submit-hand-p (list :acquire a)))
       (not (fn-ptx-submit-hand-p (list :write a b c d))))
  :hints (("Goal" :in-theory (enable fn-ptx-submit-hand-p fn-rtc-get))))
(defthm fn-ptx-read-cur-code
  (let ((cc (fn-ptx-cur-code m (mv-nth 1 (fn-ptx-read m q id inc st)))))
    (or (null cc) (equal cc 1)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ptx-read) (fn-ptx-end fn-ptx-read-w fn-ptx-mk fn-ptx-free fn-ptx-head-end fn-ptx-range fn-ptx-cap fn-ptx-gen min mv-nth
                                                 fn-ptx-frame-header fn-ptx-timer fn-ptx-committedp fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-rtc-get fn-ptx-hmax fn-ptx-fmax fn-ptx-unit fn-ptx-cur-fid fn-ptx-cur-finc fn-ptx-cur-bp fn-ptx-cur-len fn-ptx-cur-hoff fn-ptx-cur-txid fn-ptx-cur-ioff fn-ptx-kd-txid fn-ptx-buf-h fn-ptx-buf-g fn-ptx-buf-len fn-ptx-buf-x fn-ptx-write-nz fn-bs-zeros take fn-ptx-kd-last
                                                 fn-ptx-cur-code))
           :use ((:instance fn-ptx-end-cur-code (m0 (fn-ptx-chg m :committed nil)) (o :refused) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m)) (fenced nil) (committed nil))
                 (:instance fn-ptx-end-cur-code (m0 (fn-ptx-chg m :committed nil :b1 nil :b3 nil)) (o :refused) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m)) (fenced nil) (committed nil)))
           :do-not-induct t)))

(defthm fn-ptx-step1-code-facts-timer
  (implies (equal (fn-rtc-get 0 ev) :timer)
    (let* ((r (fn-ptx-step1 m ev st q))
         (cc (fn-ptx-cur-code m (mv-nth 1 r)))
         (ph (fn-ptx-ph m)))
    (and (implies (equal cc 2)
                  (and (member-eq ph '(:payload-writing :log-writing :committing))
                       (equal (fn-ptx-ph (mv-nth 0 r)) :fenced)))
         (implies (equal cc 1) (not (member-eq ph '(:payload-writing :log-writing :committing))))
         (implies (equal cc 0)
                  (and (equal ph :committing) (equal (fn-rtc-get 0 ev) :fsync)
                       (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1 fn-ptx-fsync fn-ptx-timer fn-ptx-pwrite fn-ptx-extend)
                                  (fn-ptx-mk fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-ptx-committedp
                                   fn-ptx-end fn-ptx-start fn-ptx-answer fn-ptx-cur-code fn-ptx-opened fn-ptx-wfp fn-ptx-evd+ fn-ptx-kd-commit
                                   fn-ptx-elen fn-ptx-nmsg fn-ptx-nspans fn-ptx-span-n fn-ptx-spans fn-ptx-spans-len fn-ptx-buf-len fn-ptx-span-pwrite mv-nth fn-ptx-release-bufs fn-ptx-gen fn-ptx-kd-frontier fn-ptx-atom fn-ptx-summary
                                   fn-ptx-read fn-ptx-hash fn-ptx-cur-bp fn-ptx-code))
           :use ((:instance fn-ptx-read-cur-code (id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev))) (:instance fn-ptx-hash-cur-code (id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev))))
           :do-not-induct t)))
(defthm fn-ptx-step1-code-facts
  (let* ((r (fn-ptx-step1 m ev st q))
         (cc (fn-ptx-cur-code m (mv-nth 1 r)))
         (ph (fn-ptx-ph m)))
    (and (implies (equal cc 2)
                  (and (member-eq ph '(:payload-writing :log-writing :committing))
                       (equal (fn-ptx-ph (mv-nth 0 r)) :fenced)))
         (implies (equal cc 1) (not (member-eq ph '(:payload-writing :log-writing :committing))))
         (implies (equal cc 0)
                  (and (equal ph :committing) (equal (fn-rtc-get 0 ev) :fsync)
                       (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-ptx-step1 fn-ptx-cur-code fn-rtc-get fn-ptx-ph)
           :do-not-induct t
           :use (fn-ptx-step1-code-facts-opened fn-ptx-step1-code-facts-handed fn-ptx-step1-code-facts-timer fn-ptx-step1-code-facts-extend fn-ptx-step1-code-facts-fsync fn-ptx-step1-code-facts-pwrite fn-ptx-step1-code-facts-hand fn-ptx-step1-code-facts-other))))
(defthm fn-ptx-uncertain-only-after-the-first-entry-write
  (fn-ptx-p5 m ev st q)
  :hints (("Goal" :in-theory (e/d (fn-ptx-p5 fn-ptx-step) (fn-ptx-step1 fn-ptx-wfp fn-ptx-cur-code fn-ptx-broken fn-ptx-ph fn-ptx-wf-cost))
           :use ((:instance fn-ptx-step1-code-facts))
           :do-not-induct t)))

(defthm fn-ptx-strip-ext-append-a
  (equal (fn-ptx-strip-ext (append (list* a b r) (list s)))
         (if (and (fn-ptx-done-p a :extend nil) (fn-ptx-done-p b :fsync nil))
             (append r (list s))
           (list* a b (append r (list s)))))
  :hints (("Goal" :in-theory (e/d (fn-ptx-strip-ext fn-rtc-get) (fn-ptx-done-p)))))
(defthm fn-ptx-summary-done
  (implies (and (equal (fn-rtc-get 0 ev) :fsync) (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done))
           (fn-ptx-done-p (fn-ptx-summary ev) :fsync nil))
  :hints (("Goal" :in-theory (enable fn-ptx-summary fn-ptx-done-p fn-ptx-atom fn-rtc-get))))
(defthm fn-ptx-strip-ext-append
  (implies (and (consp evd) (consp (cdr evd)))
           (equal (fn-ptx-strip-ext (append evd (list s)))
                  (append (fn-ptx-strip-ext evd) (list s))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-get) (fn-ptx-done-p fn-ptx-strip-ext-append-a))
           :expand ((append evd (list s)) (append (cdr evd) (list s)) (fn-ptx-strip-ext evd))
           :use ((:instance fn-ptx-strip-ext-append-a (a (car evd)) (b (cadr evd)) (r (cddr evd)))))))
(defthm fn-ptx-strip-ext-single
  (implies (and (consp evd) (atom (cdr evd)))
           (equal (fn-ptx-strip-ext evd) evd))
  :hints (("Goal" :in-theory (enable fn-ptx-strip-ext fn-ptx-done-p fn-rtc-get))))
(defthm fn-ptx-strip-ext-append-single
  (implies (and (consp evd) (atom (cdr evd)) (not (fn-ptx-done-p (car evd) :extend nil)))
           (equal (fn-ptx-strip-ext (append evd (list s))) (append evd (list s))))
  :hints (("Goal" :in-theory (enable fn-ptx-strip-ext fn-rtc-get))))
(defthm fn-ptx-strip-ext-append-nil
  (equal (fn-ptx-strip-ext (list s)) (list s))
  :hints (("Goal" :in-theory (enable fn-ptx-strip-ext fn-ptx-done-p fn-rtc-get))))
(defthm fn-ptx-spans-evd-p-first-not-extend
  (implies (and (consp evd) (fn-ptx-spans-evd-p evd spans))
           (not (fn-ptx-done-p (car evd) :extend nil)))
  :hints (("Goal" :in-theory (enable fn-ptx-spans-evd-p fn-ptx-done-p fn-rtc-get))))
(defthm fn-ptx-take-append-last-len
  (implies (true-listp r)
           (and (equal (take (len r) (append r (list s))) r)
                (equal (fn-rtc-get (len r) (append r (list s))) s)))
  :hints (("Goal" :in-theory (enable take fn-rtc-get) :induct (len r))))
(defthm fn-ptx-take-append-last
  (implies (and (true-listp r) (equal (len r) n))
           (and (equal (take n (append r (list s))) r)
                (equal (fn-rtc-get n (append r (list s))) s)
                (equal (len (append r (list s))) (+ 1 n))))
  :hints (("Goal" :use fn-ptx-take-append-last-len :in-theory (disable fn-ptx-take-append-last-len take fn-rtc-get))))

(defthm fn-ptx-okp-committing
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :committing))
           (and (true-listp (fn-ptx-strip-ext (fn-ptx-evd m)))
                (equal (len (fn-ptx-strip-ext (fn-ptx-evd m))) (fn-ptx-nspans m))
                (fn-ptx-spans-evd-p (fn-ptx-strip-ext (fn-ptx-evd m)) (fn-ptx-spans m))))
  :hints (("Goal" :in-theory (e/d (fn-ptx-okp fn-ptx-entry-evd-p) (fn-ptx-wfp fn-ptx-stack-bits-p fn-ptx-strip-ext fn-ptx-spans-evd-p fn-ptx-spans fn-ptx-nspans fn-ptx-nmsg fn-ptx-evd fn-ptx-ph fn-ptx-hs fn-ptx-k fn-ptx-fmax)))))
(defthm fn-ptx-strip-ext-append-ok
  (implies (and (true-listp (fn-ptx-strip-ext evd))
                (fn-ptx-spans-evd-p (fn-ptx-strip-ext evd) spans))
           (equal (fn-ptx-strip-ext (append evd (list s)))
                  (append (fn-ptx-strip-ext evd) (list s))))
  :hints (("Goal" :cases ((not (consp evd)) (and (consp evd) (consp (cdr evd))) (and (consp evd) (atom (cdr evd)))))
          ("Subgoal 3" :in-theory (enable fn-ptx-strip-ext))
          ("Subgoal 1" :use ((:instance fn-ptx-strip-ext-single)
                              (:instance fn-ptx-spans-evd-p-first-not-extend (evd (fn-ptx-strip-ext evd)))
                              (:instance fn-ptx-strip-ext-append-single))
           :in-theory (disable fn-ptx-strip-ext-single fn-ptx-spans-evd-p-first-not-extend fn-ptx-strip-ext-append-single))
          ("Subgoal 2" :use fn-ptx-strip-ext-append :in-theory (disable fn-ptx-strip-ext-append))))
(defthm fn-ptx-posted-evidence-of-commit
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :committing) (fn-ptx-done-p s :fsync nil))
           (fn-ptx-posted-evidence-p (append (fn-ptx-evd m) (list s)) m))
  :hints (("Goal" :in-theory (e/d (fn-ptx-posted-evidence-p fn-ptx-entry-evd-p) (fn-ptx-okp fn-ptx-strip-ext fn-ptx-done-p fn-ptx-spans-evd-p fn-ptx-spans fn-ptx-nspans fn-ptx-evd fn-ptx-ph fn-ptx-take-append-last fn-ptx-okp-committing fn-ptx-strip-ext-append-ok))
           :use (fn-ptx-okp-committing
                 (:instance fn-ptx-strip-ext-append-ok (evd (fn-ptx-evd m)) (spans (fn-ptx-spans m)))
                 (:instance fn-ptx-take-append-last (r (fn-ptx-strip-ext (fn-ptx-evd m))) (n (fn-ptx-nspans m))))
           :do-not-induct t)))
(defthm fn-ptx-posted-has-durable-commit-evidence
  (fn-ptx-p2 m ev st q)
  :hints (("Goal" :in-theory (e/d (fn-ptx-p2 fn-ptx-step) (fn-ptx-step1 fn-ptx-wfp fn-ptx-cur-code fn-ptx-broken fn-ptx-ph fn-ptx-wf-cost fn-ptx-okp fn-ptx-posted-evidence-p fn-ptx-summary fn-ptx-evd))
           :use ((:instance fn-ptx-step1-code-facts)
                 (:instance fn-ptx-summary-done)
                 (:instance fn-ptx-posted-evidence-of-commit (s (fn-ptx-summary ev))))
           :do-not-induct t)))

(defthm fn-ptx-acc-max-state-pos
  (<= 1 (fn-ptx-acc-max-state))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-ptx-acc-begin-bounded (txid 0) )
                        (:instance fn-ptx-size-pos (x (fn-ptx-acc-begin 0))))
           :in-theory (disable fn-ptx-acc-begin-bounded fn-ptx-size-pos))))
(defthm fn-ptx-closed-is-ok
  (fn-ptx-okp (fn-ptx-closed))
  :hints (("Goal" :in-theory (e/d (fn-ptx-okp fn-ptx-closed fn-ptx-wfp fn-ptx-fields-fit fn-ptx-size-rem) (fn-ptx-stack-bits-p))
           :use fn-ptx-acc-max-state-pos)))


; -----------------------------------------------------------------------------
; P0 (Sonnet 4): fn-ptx-step-keeps-ok.  The invariant's introduction/elimination,
; the binary counter of the digest stack, and one lemma per arm of the step.
;; binary counter
(defthm fn-ptx-stack-bits-height-ge
  (implies (and (fn-ptx-stack-bits-p st c h) (consp st))
           (<= (nfix h) (nfix (fn-b3-nthx 0 (car st)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-ptx-stack-bits-p st c h))))
(defun fn-ptx-cvp-ind (c h out st)
  (declare (xargs :measure (nfix c) :hints (("Goal" :use ((:instance fn-ptx-floor-2-smaller))))))
  (if (zp c) (list h out st)
    (if (oddp c)
        (fn-ptx-cvp-ind (floor c 2) (+ 1 (nfix h)) (fn-b3-parent-out *fn-b3-iv* (fn-b3-nthx 1 (car st)) out 0) (cdr st))
      (list h out st))))
(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm fn-ptx-c-odd-succ
    (implies (and (natp c) (oddp c))
             (and (not (oddp (+ 1 c))) (equal (floor (+ 1 c) 2) (+ 1 (floor c 2))) (< 0 (+ 1 c))))
    :rule-classes nil)
  (defthm fn-ptx-c-even-succ
    (implies (and (natp c) (not (oddp c)))
             (and (oddp (+ 1 c)) (equal (floor (+ 1 c) 2) (floor c 2))))
    :rule-classes nil))
(defthm fn-ptx-bits-odd
  (implies (and (natp c) (oddp c))
           (equal (fn-ptx-stack-bits-p st c h)
                  (and (consp st) (equal (nfix (fn-b3-nthx 0 (car st))) (nfix h)) (<= (fn-rtc-size (car st)) 63)
                       (fn-ptx-stack-bits-p (cdr st) (floor c 2) (+ 1 (nfix h))))))
  :hints (("Goal" :expand ((fn-ptx-stack-bits-p st c h)))))
(defthm fn-ptx-bits-even
  (implies (and (natp c) (< 0 c) (not (oddp c)))
           (equal (fn-ptx-stack-bits-p st c h) (fn-ptx-stack-bits-p st (floor c 2) (+ 1 (nfix h)))))
  :hints (("Goal" :expand ((fn-ptx-stack-bits-p st c h)))))
(defthm fn-ptx-bits-zero
  (equal (fn-ptx-stack-bits-p st 0 h) (null st))
  :hints (("Goal" :expand ((fn-ptx-stack-bits-p st 0 h)))))
(defthm fn-ptx-cv-push-even
  (implies (and (fn-ptx-stack-bits-p st c h) (natp c) (natp h) (not (oddp c)))
           (equal (fn-b3-cv-push *fn-b3-iv* 0 h out st) (cons (list h out) st)))
  :hints (("Goal" :cases ((equal c 0) (consp st))
           :in-theory (disable fn-ptx-stack-bits-p fn-b3-cv-push)
           :use ((:instance fn-ptx-bits-even) (:instance fn-ptx-stack-bits-height-ge (c (floor c 2)) (h (+ 1 h)))))
          ("Subgoal 3" :expand ((fn-b3-cv-push *fn-b3-iv* 0 h out st)))
          ("Subgoal 2" :expand ((fn-b3-cv-push *fn-b3-iv* 0 h out st)))
          ("Subgoal 1" :expand ((fn-b3-cv-push *fn-b3-iv* 0 h out st)))))
(defthm fn-ptx-cv-push-merge
  (implies (and (consp st) (equal (nfix (fn-b3-nthx 0 (car st))) (nfix h)))
           (equal (fn-b3-cv-push *fn-b3-iv* 0 h out st)
                  (fn-b3-cv-push *fn-b3-iv* 0 (+ 1 (nfix h)) (fn-b3-parent-out *fn-b3-iv* (fn-b3-nthx 1 (car st)) out 0) (cdr st))))
  :hints (("Goal" :in-theory (disable fn-b3-parent-out) :expand ((fn-b3-cv-push *fn-b3-iv* 0 h out st)))))
(defthm fn-ptx-oddp-succ-odd (implies (and (natp c) (oddp c)) (equal (oddp (+ 1 c)) nil))
  :hints (("Goal" :use fn-ptx-c-odd-succ)))
(defthm fn-ptx-floor-succ-odd (implies (and (natp c) (oddp c)) (equal (floor (+ 1 c) 2) (+ 1 (floor c 2))))
  :hints (("Goal" :use fn-ptx-c-odd-succ)))
(defthm fn-ptx-oddp-succ-even (implies (and (natp c) (not (oddp c))) (equal (oddp (+ 1 c)) t))
  :hints (("Goal" :use fn-ptx-c-even-succ)))
(defthm fn-ptx-floor-succ-even (implies (and (natp c) (not (oddp c))) (equal (floor (+ 1 c) 2) (floor c 2)))
  :hints (("Goal" :use fn-ptx-c-even-succ)))
(defthm fn-ptx-stack-bits-cv-push
  (implies (and (fn-ptx-stack-bits-p st c h) (natp c) (natp h)
                (<= (fn-rtc-size out) 59))
           (fn-ptx-stack-bits-p (fn-b3-cv-push *fn-b3-iv* 0 h out st) (+ 1 c) h))
  :hints (("Goal" :induct (fn-ptx-cvp-ind c h out st)
           :do-not '(eliminate-destructors generalize)
           :in-theory (disable fn-ptx-stack-bits-p fn-b3-cv-push fn-b3-parent-out fn-ptx-size-parent-out
                               fn-ptx-bits-odd fn-ptx-bits-even oddp evenp floor))
          ("Subgoal *1/3" :use ((:instance fn-ptx-bits-even (c (+ 1 c)) (st (fn-b3-cv-push *fn-b3-iv* 0 h out st)))
                                (:instance fn-ptx-cv-push-even)
                                (:instance fn-ptx-bits-odd (c (+ 1 c)) (st (cons (list h out) st))) (:instance fn-ptx-bits-even)))
          ("Subgoal *1/1" :use ((:instance fn-ptx-bits-odd (c 1) (st (list (list h out)))) (:instance fn-ptx-bits-zero (st nil) (h (+ 1 h)))))
          ("Subgoal *1/2" :use ((:instance fn-ptx-bits-odd)
                                (:instance fn-ptx-bits-even (c (+ 1 c)) (st (fn-b3-cv-push *fn-b3-iv* 0 h out st)))
                                (:instance fn-ptx-size-parent-out (key *fn-b3-iv*) (lout (fn-b3-nthx 1 (car st))) (rout out) (flags 0))))))
(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm fn-ptx-floor-1024-succ
    (implies (natp pos) (equal (floor (+ 1024 pos) 1024) (+ 1 (floor pos 1024)))))
  (defthm fn-ptx-mod-1024-succ
    (implies (natp pos) (equal (mod (+ 1024 pos) 1024) (mod pos 1024))))
  (defthm fn-ptx-floor-1024-natp
    (implies (natp pos) (natp (floor pos 1024)))
    :rule-classes :type-prescription))
(defthm fn-ptx-absorb-bits
  (implies (and (natp pos) (equal (mod pos 1024) 0)
                (fn-ptx-stack-bits-p st (floor pos 1024) 0))
           (and (natp (mv-nth 0 (fn-ptx-absorb nw pos st n spans id inc fn-rtc-st)))
                (equal (mod (mv-nth 0 (fn-ptx-absorb nw pos st n spans id inc fn-rtc-st)) 1024) 0)
                (fn-ptx-stack-bits-p (mv-nth 1 (fn-ptx-absorb nw pos st n spans id inc fn-rtc-st))
                                     (floor (mv-nth 0 (fn-ptx-absorb nw pos st n spans id inc fn-rtc-st)) 1024) 0)))
  :hints (("Goal" :induct (fn-ptx-absorb nw pos st n spans id inc fn-rtc-st)
           :in-theory (disable fn-ptx-stack-bits-p fn-b3-cv-push fn-b3-node fn-ptx-msg-range fn-ptx-size-node floor mod)
           :expand ((fn-ptx-absorb nw pos st n spans id inc fn-rtc-st)))
          ("Subgoal *1/2" :use ((:instance fn-ptx-stack-bits-cv-push (c (floor pos 1024)) (h 0)
                                           (out (fn-b3-node *fn-b3-iv* (fn-ptx-msg-range pos 1024 spans id inc fn-rtc-st) (floor pos 1024) 0)))
                                (:instance fn-ptx-size-node (key *fn-b3-iv*) (octets (fn-ptx-msg-range pos 1024 spans id inc fn-rtc-st))
                                           (counter (floor pos 1024)) (flags 0))
                                fn-ptx-iv-shape))))
(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm fn-ptx-floor-2-expt
    (implies (and (natp c) (< 0 c) (natp j) (< c (expt 2 j)))
             (and (< 0 j) (< (floor c 2) (expt 2 (- j 1)))))
    :rule-classes nil))
(defun fn-ptx-sz-ind (st c h j)
  (declare (xargs :measure (nfix c) :hints (("Goal" :use ((:instance fn-ptx-floor-2-smaller))))))
  (if (zp c) (list st h j)
    (fn-ptx-sz-ind (if (oddp c) (cdr st) st) (floor c 2) (+ 1 (nfix h)) (nfix (- (nfix j) 1)))))
(defthm fn-ptx-stack-bits-size
  (implies (and (fn-ptx-stack-bits-p st c h) (natp c) (natp j) (< c (expt 2 j)))
           (<= (fn-rtc-size st) (+ 1 (* 64 j))))
  :hints (("Goal" :induct (fn-ptx-sz-ind st c h j)
           :in-theory (disable fn-ptx-stack-bits-p fn-ptx-bits-odd fn-ptx-bits-even oddp evenp floor expt))
          ("Subgoal *1/2" :cases ((oddp c))
           :use ((:instance fn-ptx-bits-odd) (:instance fn-ptx-bits-even) (:instance fn-ptx-floor-2-expt)))
          ("Subgoal *1/1" :use ((:instance fn-ptx-bits-zero)))))
(defthm fn-ptx-size-rem-intro
  (implies (and (natp n) (<= (fn-rtc-size x) n))
           (fn-ptx-size-rem x n))
  :hints (("Goal" :induct (fn-ptx-size-rem x n)
           :in-theory (disable fn-ptx-size-rem-exact fn-ptx-size-rem-bound))
          ("Subgoal *1/3" :use ((:instance fn-ptx-size-rem-exact (x (car x)) (n (- n 1))) (:instance fn-ptx-size-pos (x (car x))) (:instance fn-ptx-size-pos (x (cdr x))))
           :in-theory (disable fn-ptx-size-rem-bound))))
(defthm fn-ptx-wfp-intro
  (implies (and (member-eq (fn-ptx-ph m) *fn-ptx-phases*)
                (<= (fn-rtc-size (fn-rtc-get 0 m)) 1) (<= (fn-rtc-size (fn-rtc-get 1 m)) 1)
                (<= (fn-rtc-size (fn-rtc-get 2 m)) 15) (<= (fn-rtc-size (fn-rtc-get 3 m)) 21)
                (<= (fn-rtc-size (fn-rtc-get 4 m)) 75) (<= (fn-rtc-size (fn-rtc-get 5 m)) 1)
                (<= (fn-rtc-size (fn-rtc-get 6 m)) 1) (<= (fn-rtc-size (fn-rtc-get 7 m)) 9)
                (<= (fn-rtc-size (fn-rtc-get 8 m)) 9) (<= (fn-rtc-size (fn-rtc-get 9 m)) 4101)
                (<= (fn-rtc-size (fn-rtc-get 10 m)) 1) (<= (fn-rtc-size (fn-rtc-get 11 m)) 57)
                (<= (fn-rtc-size (fn-rtc-get 12 m)) 7)
                (<= (fn-rtc-size (fn-ptx-acc m)) (fn-ptx-acc-max-state)))
           (fn-ptx-wfp m))
  :hints (("Goal" :in-theory (e/d (fn-ptx-wfp fn-ptx-fields-fit) (fn-ptx-size-rem fn-rtc-get fn-rtc-size)))))
(defun fn-ptx-spans-g (b1 b3 cur)
  (let* ((l1 (fn-ptx-buf-len b1)) (lins (fn-ptx-buf-x b1))
         (alen (fn-ptx-cur-len cur)) (ioff (min (fn-ptx-cur-ioff cur) alen)))
    (append (fn-ptx-span (fn-ptx-buf-h b1) 0 l1)
            (fn-ptx-span (fn-ptx-cur-bp cur) 0 ioff)
            (fn-ptx-span (fn-ptx-buf-h b1) l1 lins)
            (fn-ptx-span (fn-ptx-cur-bp cur) ioff (- alen ioff))
            (fn-ptx-span (fn-ptx-buf-h b3) (fn-ptx-buf-x b3) (- (fn-ptx-buf-len b3) (fn-ptx-buf-x b3))))))
(defthm fn-ptx-spans-is-g
  (equal (fn-ptx-spans m) (fn-ptx-spans-g (fn-ptx-b1 m) (fn-ptx-b3 m) (fn-ptx-cur m)))
  :hints (("Goal" :in-theory (enable fn-ptx-spans fn-ptx-spans-g))))
(in-theory (disable fn-ptx-spans-is-g))
(defthm fn-ptx-spans-of-mk
  (equal (fn-ptx-spans (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc))
         (fn-ptx-spans-g b1 b3 cur))
  :hints (("Goal" :in-theory (e/d (fn-ptx-spans-is-g fn-ptx-accessors-of-mk) (fn-ptx-mk fn-ptx-spans-g)))))
(defthm fn-ptx-nspans-of-mk
  (equal (fn-ptx-nspans (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc))
         (len (fn-ptx-spans-g b1 b3 cur)))
  :hints (("Goal" :in-theory (e/d (fn-ptx-nspans) (fn-ptx-mk)))))
(defthm fn-ptx-nmsg-of-mk
  (equal (fn-ptx-nmsg (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc))
         (fn-ptx-spans-len (fn-ptx-spans-g b1 b3 cur)))
  :hints (("Goal" :in-theory (e/d (fn-ptx-nmsg) (fn-ptx-mk)))))
(defthm fn-ptx-get-of-mk
  (and (equal (fn-rtc-get 0 (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc)) ph)
       (equal (fn-rtc-get 1 (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc)) (nfix k))
       (equal (fn-rtc-get 2 (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc)) cur)
       (equal (fn-rtc-get 3 (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc)) q)
       (equal (fn-rtc-get 4 (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc)) kd)
       (equal (fn-rtc-get 5 (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc)) (nfix ext))
       (equal (fn-rtc-get 6 (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc)) (nfix nxt))
       (equal (fn-rtc-get 7 (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc)) b1)
       (equal (fn-rtc-get 8 (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc)) b3)
       (equal (fn-rtc-get 9 (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc)) hs)
       (equal (fn-rtc-get 10 (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc)) (and committed t))
       (equal (fn-rtc-get 11 (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc)) evd)
       (equal (fn-rtc-get 12 (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc)) geo)
       (equal (fn-rtc-get 13 (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc)) acc))
  :hints (("Goal" :in-theory (enable fn-ptx-mk fn-rtc-get))))
(defthm fn-ptx-nspans-is-g
  (equal (fn-ptx-nspans m) (len (fn-ptx-spans-g (fn-ptx-b1 m) (fn-ptx-b3 m) (fn-ptx-cur m))))
  :hints (("Goal" :in-theory (enable fn-ptx-nspans fn-ptx-spans-is-g))))
(defthm fn-ptx-nmsg-is-g
  (equal (fn-ptx-nmsg m) (fn-ptx-spans-len (fn-ptx-spans-g (fn-ptx-b1 m) (fn-ptx-b3 m) (fn-ptx-cur m))))
  :hints (("Goal" :in-theory (enable fn-ptx-nmsg fn-ptx-spans-is-g))))
(defthm fn-ptx-entry-evd-is-g
  (equal (fn-ptx-entry-evd-p evd m nw)
         (and (true-listp evd) (equal (len evd) (nfix nw))
              (fn-ptx-spans-evd-p evd (fn-ptx-spans-g (fn-ptx-b1 m) (fn-ptx-b3 m) (fn-ptx-cur m)))))
  :hints (("Goal" :in-theory (enable fn-ptx-entry-evd-p fn-ptx-spans-is-g))))
(in-theory (disable fn-ptx-nspans-is-g fn-ptx-nmsg-is-g fn-ptx-entry-evd-is-g))
(defthm fn-ptx-wfp-phase
  (implies (fn-ptx-wfp m) (member-eq (fn-ptx-ph m) *fn-ptx-phases*))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-wfp)))))
(defthm fn-ptx-wfp-m0
  (implies (fn-ptx-wfp m) (fn-ptx-wfp (fn-ptx-chg m :committed nil)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-get-of-mk fn-ptx-ph fn-ptx-acc fn-ptx-committedp fn-ptx-k fn-ptx-cur fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo
                          (:executable-counterpart nfix) nfix fn-ptx-size-of-atom))
           :use ((:instance fn-ptx-wfp-sizes) (:instance fn-ptx-wfp-phase) (:instance fn-ptx-wfp-intro (m (fn-ptx-chg m :committed nil))))
           :do-not-induct t)))
(defthm fn-ptx-okp-intro
  (implies (and (fn-ptx-wfp m)
                (<= (fn-ptx-fmax m) *fn-frame-max-payload*)
                (or (member-eq (fn-ptx-ph m) '(:closed :fenced)) (equal (len (fn-ptx-kd-last (fn-ptx-kd m))) 32))
                (case (fn-ptx-ph m)
                  ((:closed :idle :reading :hashing :extending :fenced) (null (fn-ptx-evd m)))
                  (:extsyncing (and (true-listp (fn-ptx-evd m)) (equal (len (fn-ptx-evd m)) 1) (fn-ptx-done-p (car (fn-ptx-evd m)) :extend nil)))
                  (:payload-writing (and (< (+ (fn-ptx-k m) 1) (fn-ptx-nspans m)) (fn-ptx-entry-evd-p (fn-ptx-strip-ext (fn-ptx-evd m)) m (fn-ptx-k m))))
                  (:log-writing (and (equal (+ (fn-ptx-k m) 1) (fn-ptx-nspans m)) (fn-ptx-entry-evd-p (fn-ptx-strip-ext (fn-ptx-evd m)) m (fn-ptx-k m))))
                  (:committing (fn-ptx-entry-evd-p (fn-ptx-strip-ext (fn-ptx-evd m)) m (fn-ptx-nspans m)))
                  (otherwise nil))
                (implies (and (equal (fn-ptx-ph m) :reading) (consp (fn-ptx-b1 m)))
                         (<= *fn-ptx-sufhead-max* (fn-ptx-buf-len (fn-ptx-b3 m))))
                (implies (equal (fn-ptx-ph m) :hashing)
                         (and (< 0 (fn-ptx-buf-len (fn-ptx-b1 m)))
                              (<= (fn-ptx-buf-x (fn-ptx-b3 m)) (fn-ptx-buf-len (fn-ptx-b3 m)))))
                (implies (member-eq (fn-ptx-ph m) '(:extending :extsyncing)) (<= 2 (fn-ptx-nspans m)))
                (implies (member-eq (fn-ptx-ph m) '(:extending :extsyncing :payload-writing :log-writing :committing))
                         (and (fn-ptx-atoms-p (fn-rtc-get 1 (fn-ptx-hs m))) (equal (len (fn-rtc-get 1 (fn-ptx-hs m))) 32)))
                (fn-ptx-rows-p (fn-ptx-q m) 4)
                (<= (len (fn-ptx-q m)) *fn-ptx-k*)
                (fn-ptx-rows-p (fn-ptx-evd m) 3)
                (implies (member-eq (fn-ptx-ph m) '(:reading :hashing :extending :extsyncing :payload-writing :log-writing :committing))
                         (and (fn-ptx-atoms-p (fn-ptx-cur m)) (equal (len (fn-ptx-cur m)) 7)))
                (implies (equal (fn-ptx-ph m) :hashing)
                         (and (natp (fn-rtc-get 0 (fn-ptx-hs m)))
                              (equal (mod (fn-rtc-get 0 (fn-ptx-hs m)) *fn-ptx-window*) 0)
                              (< (fn-rtc-get 0 (fn-ptx-hs m)) (fn-ptx-nmsg m))
                              (<= (fn-ptx-nmsg m) (+ 10 (fn-ptx-fmax m)))
                              (fn-ptx-stack-bits-p (fn-rtc-get 1 (fn-ptx-hs m)) (floor (fn-rtc-get 0 (fn-ptx-hs m)) *fn-ptx-window*) 0))))
           (fn-ptx-okp m))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-okp)))))
(defthm fn-ptx-okp-elim
  (implies (fn-ptx-okp m)
           (and (fn-ptx-wfp m)
                (<= (fn-ptx-fmax m) *fn-frame-max-payload*)
                (or (member-eq (fn-ptx-ph m) '(:closed :fenced)) (equal (len (fn-ptx-kd-last (fn-ptx-kd m))) 32))
                (case (fn-ptx-ph m)
                  ((:closed :idle :reading :hashing :extending :fenced) (null (fn-ptx-evd m)))
                  (:extsyncing (and (true-listp (fn-ptx-evd m)) (equal (len (fn-ptx-evd m)) 1) (fn-ptx-done-p (car (fn-ptx-evd m)) :extend nil)))
                  (:payload-writing (and (< (+ (fn-ptx-k m) 1) (fn-ptx-nspans m)) (fn-ptx-entry-evd-p (fn-ptx-strip-ext (fn-ptx-evd m)) m (fn-ptx-k m))))
                  (:log-writing (and (equal (+ (fn-ptx-k m) 1) (fn-ptx-nspans m)) (fn-ptx-entry-evd-p (fn-ptx-strip-ext (fn-ptx-evd m)) m (fn-ptx-k m))))
                  (:committing (fn-ptx-entry-evd-p (fn-ptx-strip-ext (fn-ptx-evd m)) m (fn-ptx-nspans m)))
                  (otherwise nil))
                (implies (and (equal (fn-ptx-ph m) :reading) (consp (fn-ptx-b1 m)))
                         (<= *fn-ptx-sufhead-max* (fn-ptx-buf-len (fn-ptx-b3 m))))
                (implies (equal (fn-ptx-ph m) :hashing)
                         (and (< 0 (fn-ptx-buf-len (fn-ptx-b1 m)))
                              (<= (fn-ptx-buf-x (fn-ptx-b3 m)) (fn-ptx-buf-len (fn-ptx-b3 m)))))
                (implies (member-eq (fn-ptx-ph m) '(:extending :extsyncing)) (<= 2 (fn-ptx-nspans m)))
                (implies (member-eq (fn-ptx-ph m) '(:extending :extsyncing :payload-writing :log-writing :committing))
                         (and (fn-ptx-atoms-p (fn-rtc-get 1 (fn-ptx-hs m))) (equal (len (fn-rtc-get 1 (fn-ptx-hs m))) 32)))
                (fn-ptx-rows-p (fn-ptx-q m) 4)
                (<= (len (fn-ptx-q m)) *fn-ptx-k*)
                (fn-ptx-rows-p (fn-ptx-evd m) 3)
                (implies (member-eq (fn-ptx-ph m) '(:reading :hashing :extending :extsyncing :payload-writing :log-writing :committing))
                         (and (fn-ptx-atoms-p (fn-ptx-cur m)) (equal (len (fn-ptx-cur m)) 7)))
                (implies (equal (fn-ptx-ph m) :hashing)
                         (and (natp (fn-rtc-get 0 (fn-ptx-hs m)))
                              (equal (mod (fn-rtc-get 0 (fn-ptx-hs m)) *fn-ptx-window*) 0)
                              (< (fn-rtc-get 0 (fn-ptx-hs m)) (fn-ptx-nmsg m))
                              (<= (fn-ptx-nmsg m) (+ 10 (fn-ptx-fmax m)))
                              (fn-ptx-stack-bits-p (fn-rtc-get 1 (fn-ptx-hs m)) (floor (fn-rtc-get 0 (fn-ptx-hs m)) *fn-ptx-window*) 0)))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-okp (:executable-counterpart member-equal) member-equal (:executable-counterpart equal))))))
(defthm fn-ptx-okp-wfp (implies (fn-ptx-okp m) (fn-ptx-wfp m))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-okp)))))
(defun fn-ptx-entry-g (evd spans nw)
  (and (true-listp evd) (equal (len evd) (nfix nw)) (fn-ptx-spans-evd-p evd spans)))
(defun fn-ptx-wfp-c (ph cur q kd b1 b3 hs evd geo acc)
  (and (member-eq ph *fn-ptx-phases*)
       (<= (fn-rtc-size cur) 15) (<= (fn-rtc-size q) 21) (<= (fn-rtc-size kd) 75)
       (<= (fn-rtc-size b1) 9) (<= (fn-rtc-size b3) 9) (<= (fn-rtc-size hs) 4101)
       (<= (fn-rtc-size evd) 57) (<= (fn-rtc-size geo) 7) (<= (fn-rtc-size acc) (fn-ptx-acc-max-state))))
(defthm fn-ptx-okp-mk
  (implies (and (fn-ptx-wfp-c ph cur q kd b1 b3 hs evd geo acc)
                (<= (nfix (fn-rtc-get 1 geo)) *fn-frame-max-payload*)
                (or (member-eq ph '(:closed :fenced)) (equal (len (fn-ptx-kd-last kd)) 32))
                (case ph
                  ((:closed :idle :reading :hashing :extending :fenced) (null evd))
                  (:extsyncing (and (true-listp evd) (equal (len evd) 1) (fn-ptx-done-p (car evd) :extend nil)))
                  (:payload-writing (and (< (+ (nfix k) 1) (len (fn-ptx-spans-g b1 b3 cur))) (fn-ptx-entry-g (fn-ptx-strip-ext evd) (fn-ptx-spans-g b1 b3 cur) (nfix k))))
                  (:log-writing (and (equal (+ (nfix k) 1) (len (fn-ptx-spans-g b1 b3 cur))) (fn-ptx-entry-g (fn-ptx-strip-ext evd) (fn-ptx-spans-g b1 b3 cur) (nfix k))))
                  (:committing (fn-ptx-entry-g (fn-ptx-strip-ext evd) (fn-ptx-spans-g b1 b3 cur) (len (fn-ptx-spans-g b1 b3 cur))))
                  (otherwise nil))
                (implies (and (equal ph :reading) (consp b1))
                         (<= *fn-ptx-sufhead-max* (fn-ptx-buf-len b3)))
                (implies (equal ph :hashing)
                         (and (< 0 (fn-ptx-buf-len b1))
                              (<= (fn-ptx-buf-x b3) (fn-ptx-buf-len b3))))
                (implies (member-eq ph '(:extending :extsyncing)) (<= 2 (len (fn-ptx-spans-g b1 b3 cur))))
                (implies (member-eq ph '(:extending :extsyncing :payload-writing :log-writing :committing))
                         (and (fn-ptx-atoms-p (fn-rtc-get 1 hs)) (equal (len (fn-rtc-get 1 hs)) 32)))
                (fn-ptx-rows-p q 4)
                (<= (len q) *fn-ptx-k*)
                (fn-ptx-rows-p evd 3)
                (implies (member-eq ph '(:reading :hashing :extending :extsyncing :payload-writing :log-writing :committing))
                         (and (fn-ptx-atoms-p cur) (equal (len cur) 7)))
                (implies (equal ph :hashing)
                         (and (natp (fn-rtc-get 0 hs))
                              (equal (mod (fn-rtc-get 0 hs) *fn-ptx-window*) 0)
                              (< (fn-rtc-get 0 hs) (fn-ptx-spans-len (fn-ptx-spans-g b1 b3 cur)))
                              (<= (fn-ptx-spans-len (fn-ptx-spans-g b1 b3 cur)) (+ 10 (nfix (fn-rtc-get 1 geo))))
                              (fn-ptx-stack-bits-p (fn-rtc-get 1 hs) (floor (fn-rtc-get 0 hs) *fn-ptx-window*) 0))))
           (fn-ptx-okp (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
             '(fn-ptx-get-of-mk fn-ptx-accessors-of-mk fn-ptx-nspans-is-g fn-ptx-nmsg-is-g fn-ptx-entry-evd-is-g fn-ptx-entry-g fn-ptx-wfp-c
               fn-ptx-wfp-intro fn-ptx-spans-of-mk fn-ptx-fmax fn-ptx-geo fn-ptx-acc fn-ptx-size-of-atom nfix (:executable-counterpart nfix)
               fn-ptx-nspans fn-ptx-nmsg (:executable-counterpart member-equal) member-equal))
           :use ((:instance fn-ptx-okp-intro (m (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc))))
           :do-not-induct t)))
(deftheory fn-ptx-mt
  '(fn-ptx-get-of-mk fn-ptx-accessors-of-mk fn-ptx-nspans-is-g fn-ptx-nmsg-is-g fn-ptx-entry-evd-is-g fn-ptx-entry-g fn-ptx-wfp-c
    fn-ptx-spans-of-mk fn-ptx-nspans-of-mk fn-ptx-nmsg-of-mk fn-ptx-size-of-atom nfix (:executable-counterpart nfix)
    (:executable-counterpart member-equal) member-equal fn-ptx-ph fn-ptx-k fn-ptx-cur fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-committedp
    fn-ptx-fmax))
(defthm fn-ptx-okp-m0
  (implies (fn-ptx-okp m) (fn-ptx-okp (fn-ptx-chg m :committed nil)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) (theory 'fn-ptx-mt))
           :use ((:instance fn-ptx-okp-elim) (:instance fn-ptx-wfp-sizes) (:instance fn-ptx-wfp-phase)
                 (:instance fn-ptx-okp-mk (ph (fn-ptx-ph m)) (k (fn-ptx-k m)) (cur (fn-ptx-cur m)) (q (fn-ptx-q m)) (kd (fn-ptx-kd m))
                            (ext (fn-ptx-ext m)) (nxt (fn-ptx-nxt m)) (b1 (fn-ptx-b1 m)) (b3 (fn-ptx-b3 m)) (hs (fn-ptx-hs m))
                            (committed nil) (evd (fn-ptx-evd m)) (geo (fn-ptx-geo m)) (acc (fn-ptx-acc m))))
           :do-not-induct t)))
(defthm fn-ptx-atoms-p-size
  (implies (fn-ptx-atoms-p x) (equal (fn-rtc-size x) (+ 1 (* 2 (len x)))))
  :hints (("Goal" :in-theory (enable fn-ptx-atoms-p fn-rtc-size))))
(defthm fn-ptx-rows-p-size
  (implies (fn-ptx-rows-p x n)
           (equal (fn-rtc-size x) (+ 1 (* (len x) (+ 2 (* 2 (nfix n)))))))
  :hints (("Goal" :in-theory (enable fn-ptx-rows-p fn-rtc-size)
           :induct (fn-ptx-rows-p x n))
          ("Subgoal *1/2" :use ((:instance fn-ptx-atoms-p-size (x (car x)))))))
(defthm fn-ptx-atoms-p-get
  (implies (fn-ptx-atoms-p x) (atom (fn-rtc-get i x)))
  :hints (("Goal" :in-theory (enable fn-ptx-atoms-p fn-rtc-get))))
(defthm fn-ptx-atoms-p-cdr
  (implies (fn-ptx-atoms-p x) (fn-ptx-atoms-p (cdr x)))
  :hints (("Goal" :in-theory (enable fn-ptx-atoms-p))))
(defthm fn-ptx-rows-p-car
  (implies (and (fn-ptx-rows-p x n) (consp x)) (and (fn-ptx-atoms-p (car x)) (equal (len (car x)) n)))
  :hints (("Goal" :in-theory (enable fn-ptx-rows-p))))
(defthm fn-ptx-rows-p-cdr
  (implies (fn-ptx-rows-p x n) (fn-ptx-rows-p (cdr x) n))
  :hints (("Goal" :in-theory (enable fn-ptx-rows-p))))
(defthm fn-ptx-atoms-p-get-size
  (implies (fn-ptx-atoms-p x) (equal (fn-rtc-size (fn-rtc-get i x)) 1))
  :hints (("Goal" :use fn-ptx-atoms-p-get :in-theory (disable fn-ptx-atoms-p-get))))
(defthm fn-ptx-rows-p-size2
  (implies (fn-ptx-rows-p x n)
           (equal (fn-rtc-size x) (+ 1 (* (+ 2 (* 2 (nfix n))) (len x)))))
  :hints (("Goal" :use fn-ptx-rows-p-size :in-theory (disable fn-ptx-rows-p-size))))
(defthm fn-ptx-atoms-p-cons
  (equal (fn-ptx-atoms-p (cons a b)) (and (atom a) (fn-ptx-atoms-p b)))
  :hints (("Goal" :in-theory (enable fn-ptx-atoms-p))))
(defthm fn-ptx-atoms-p-nil (fn-ptx-atoms-p nil) :hints (("Goal" :in-theory (enable fn-ptx-atoms-p))))
(defthm fn-ptx-atom-of-get
  (implies (fn-ptx-atoms-p x) (equal (atom (fn-rtc-get i x)) t))
  :hints (("Goal" :use fn-ptx-atoms-p-get :in-theory (disable fn-ptx-atoms-p-get))))
(defthm fn-ptx-len-cons2 (equal (len (cons a b)) (+ 1 (len b))))
(defthm fn-ptx-start-ok
  (implies (and (fn-ptx-atoms-p p) (equal (len p) 4)
                (fn-ptx-rows-p q 4) (<= (len q) *fn-ptx-k*)
                (<= (fn-rtc-size kd) 75) (<= (fn-rtc-size geo) 7)
                (equal (len (fn-ptx-kd-last kd)) 32)
                (<= (nfix (fn-rtc-get 1 geo)) *fn-frame-max-payload*))
           (fn-ptx-okp (mv-nth 0 (fn-ptx-start p q kd ext geo committed))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    (union-theories (theory 'fn-ptx-mt)
                      '(fn-ptx-start (:executable-counterpart mv-nth) mv-nth fn-ptx-cur-fid fn-ptx-cur-finc fn-ptx-cur-bp fn-ptx-cur-len fn-ptx-kd-txid
                        fn-ptx-size-of-cons fn-ptx-size-of-atom fn-ptx-atoms-p-get-size fn-ptx-atoms-p-size fn-ptx-atoms-p-cons fn-ptx-atoms-p-nil fn-ptx-atom-of-get fn-ptx-len-cons2 fn-ptx-rows-p-size2 
                        fn-ptx-acc-begin-bounded (:executable-counterpart fn-ptx-atoms-p) (:executable-counterpart fn-ptx-rows-p) (:executable-counterpart len))))
           :use ((:instance fn-ptx-okp-mk (ph :reading) (k 0)
                            (cur (list (fn-ptx-cur-fid p) (fn-ptx-cur-finc p) (fn-ptx-cur-bp p) (fn-ptx-cur-len p) 0 (fn-ptx-kd-txid kd) (fn-ptx-cur-len p)))
                            (nxt ext) (b1 nil) (b3 nil) (hs nil) (evd nil) (acc (fn-ptx-acc-begin (fn-ptx-kd-txid kd)))))
           :do-not-induct t)))
(defthm fn-ptx-rows-p-nil (fn-ptx-rows-p nil n) :hints (("Goal" :in-theory (enable fn-ptx-rows-p))))
(defthm fn-ptx-rows-p-cons
  (equal (fn-ptx-rows-p (cons a b) n) (and (fn-ptx-atoms-p a) (equal (len a) n) (fn-ptx-rows-p b n)))
  :hints (("Goal" :in-theory (enable fn-ptx-rows-p))))
(defthm fn-ptx-len-cdr (implies (consp x) (equal (len (cdr x)) (- (len x) 1))))
(deftheory fn-ptx-mt4
  (union-theories (theory 'fn-ptx-mt)
    '(fn-ptx-size-of-cons fn-ptx-size-of-atom fn-ptx-atoms-p-get-size fn-ptx-atoms-p-size fn-ptx-rows-p-size2
      fn-ptx-rows-p-car fn-ptx-rows-p-cdr fn-ptx-len-cdr fn-ptx-rows-p-nil fn-ptx-rows-p-cons fn-ptx-atoms-p-cons fn-ptx-atoms-p-nil fn-ptx-atom-of-get fn-ptx-len-cons2 (:executable-counterpart len)
      (:executable-counterpart mv-nth) mv-nth)))
(defthm fn-ptx-end-ok
  (implies (and (fn-ptx-rows-p (fn-ptx-q m) 4) (<= (len (fn-ptx-q m)) *fn-ptx-k*)
                (<= (fn-rtc-size (fn-ptx-geo m)) 7) (<= (nfix (fn-rtc-get 1 (fn-ptx-geo m))) *fn-frame-max-payload*)
                (<= (fn-rtc-size kd) 75)
                (or fenced (equal (len (fn-ptx-kd-last kd)) 32)))
           (fn-ptx-okp (mv-nth 0 (fn-ptx-end m o kd ext fenced committed id inc st))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) (union-theories (theory 'fn-ptx-mt4) '(fn-ptx-end)))
           :cases (fenced (consp (fn-ptx-q m)))
           :use ((:instance fn-ptx-acc-max-state-pos)
                 (:instance fn-ptx-okp-mk (ph :fenced) (k 0) (cur nil) (q nil) (kd kd) (ext ext) (nxt ext) (b1 nil) (b3 nil) (hs nil)
                            (evd nil) (geo (fn-ptx-geo m)) (acc nil))
                 (:instance fn-ptx-okp-mk (ph :idle) (k 0) (cur nil) (q nil) (kd kd) (ext ext) (nxt ext) (b1 nil) (b3 nil) (hs nil)
                            (evd nil) (geo (fn-ptx-geo m)) (acc nil))
                 (:instance fn-ptx-start-ok (p (car (fn-ptx-q m))) (q (cdr (fn-ptx-q m))) (geo (fn-ptx-geo m))))
           :do-not-induct t)))
(defthm fn-ptx-opened-ok
  (implies (and (fn-ptx-wfp (fn-ptx-opened kd ext geo))
                (<= (fn-ptx-fmax (fn-ptx-opened kd ext geo)) *fn-frame-max-payload*)
                (equal (len (fn-ptx-kd-last (fn-ptx-kd (fn-ptx-opened kd ext geo)))) 32))
           (fn-ptx-okp (fn-ptx-opened kd ext geo)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) (union-theories (theory 'fn-ptx-mt4) '(fn-ptx-opened)))
           :use ((:instance fn-ptx-acc-max-state-pos)
                 (:instance fn-ptx-wfp-sizes (m (fn-ptx-opened kd ext geo)))
                 (:instance fn-ptx-okp-mk (ph :idle) (k 0) (cur nil) (q nil) (nxt ext) (b1 nil) (b3 nil) (hs nil) (evd nil) (committed nil) (acc nil)))
           :do-not-induct t)))
(defthm fn-ptx-span-len (<= (len (fn-ptx-span h off n)) 1)
  :rule-classes :linear :hints (("Goal" :in-theory (enable fn-ptx-span))))
(defthm fn-ptx-spans-g-len (<= (len (fn-ptx-spans-g b1 b3 cur)) 5)
  :rule-classes :linear
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-spans-g fn-ptx-len-append fn-ptx-span-len)))))
(defthm fn-ptx-strip-ext-len
  (<= (len evd) (+ 2 (len (fn-ptx-strip-ext evd))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-ptx-strip-ext))))
(defthm fn-ptx-atom-atom (atom (fn-ptx-atom x)) :hints (("Goal" :in-theory (enable fn-ptx-atom))))
(defthm fn-ptx-summary-shape
  (and (fn-ptx-atoms-p (fn-ptx-summary ev)) (equal (len (fn-ptx-summary ev)) 3))
  :hints (("Goal" :in-theory (enable fn-ptx-summary))))
(defthm fn-ptx-rows-p-append-single
  (implies (and (fn-ptx-rows-p evd n) (fn-ptx-atoms-p s) (equal (len s) n))
           (fn-ptx-rows-p (append evd (list s)) n))
  :hints (("Goal" :in-theory (enable fn-ptx-rows-p) :induct (fn-ptx-rows-p evd n))))
(defthm fn-ptx-rows-p-true-list (implies (fn-ptx-rows-p x n) (true-listp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-ptx-rows-p))))
(defthm fn-ptx-rows-p-evd+
  (implies (fn-ptx-rows-p (fn-ptx-evd m) 3) (fn-ptx-rows-p (fn-ptx-evd+ m ev) 3))
  :hints (("Goal" :in-theory (e/d (fn-ptx-evd+) (fn-ptx-summary-shape fn-ptx-rows-p-append-single))
           :use ((:instance fn-ptx-rows-p-append-single (evd (fn-ptx-evd m)) (n 3) (s (fn-ptx-summary ev)))
                 fn-ptx-summary-shape))))
(defthm fn-ptx-evd+-len
  (implies (true-listp (fn-ptx-evd m)) (equal (len (fn-ptx-evd+ m ev)) (+ 1 (len (fn-ptx-evd m)))))
  :hints (("Goal" :in-theory (enable fn-ptx-evd+))))
(defthm fn-ptx-evd+-nil
  (implies (null (fn-ptx-evd m)) (equal (fn-ptx-evd+ m ev) (list (fn-ptx-summary ev))))
  :hints (("Goal" :in-theory (enable fn-ptx-evd+))))
(defthm fn-ptx-summary-done-kind
  (implies (and (equal (fn-rtc-get 0 ev) kind) (atom kind) (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done))
           (fn-ptx-done-p (fn-ptx-summary ev) kind nil))
  :hints (("Goal" :in-theory (enable fn-ptx-summary fn-ptx-done-p fn-ptx-atom fn-rtc-get))))
(defthm fn-ptx-summary-done-n
  (implies (and (equal (fn-rtc-get 0 ev) kind) (atom kind) (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done)
                (equal (fn-rtc-get 1 (fn-rtc-get 1 ev)) n) (atom n))
           (fn-ptx-done-p (fn-ptx-summary ev) kind n))
  :hints (("Goal" :in-theory (enable fn-ptx-summary fn-ptx-done-p fn-ptx-atom fn-rtc-get))))
(defthm fn-ptx-size-summary (equal (fn-rtc-size (fn-ptx-summary ev)) 7)
  :hints (("Goal" :use (fn-ptx-summary-shape (:instance fn-ptx-atoms-p-size (x (fn-ptx-summary ev))))
           :in-theory (disable fn-ptx-summary-shape fn-ptx-atoms-p-size))))
(deftheory fn-ptx-mt6
  (union-theories (theory 'fn-ptx-mt4)
    '(fn-ptx-okp-mk fn-ptx-rows-p-evd+ fn-ptx-evd+-len fn-ptx-spans-g-len fn-ptx-nfix-nfix fn-ptx-rows-p-true-list
      fn-ptx-evd+-nil fn-ptx-summary-done-kind fn-ptx-summary-done-n fn-ptx-size-summary fn-ptx-summary-shape
      (:rewrite car-cons) (:rewrite cdr-cons) (:executable-counterpart true-listp) (:executable-counterpart consp)
      (:executable-counterpart fn-rtc-size) fn-ptx-done-p)))
(defthm fn-ptx-ok-extend-done
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :extending) (equal (fn-rtc-get 0 ev) :extend)
                (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done))
           (fn-ptx-okp (fn-ptx-chg (fn-ptx-chg m :committed nil) :ph :extsyncing :evd (fn-ptx-evd+ m ev))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) (theory 'fn-ptx-mt6))
           :use ((:instance fn-ptx-okp-elim) (:instance fn-ptx-wfp-sizes) (:instance fn-ptx-wfp-phase) (:instance fn-ptx-acc-max-state-pos)
                 (:instance fn-ptx-okp-mk (ph :extsyncing) (k (nfix (fn-rtc-get 1 m))) (cur (fn-rtc-get 2 m)) (q (fn-rtc-get 3 m)) (kd (fn-rtc-get 4 m)) (ext (nfix (fn-rtc-get 5 m))) (nxt (nfix (fn-rtc-get 6 m))) (b1 (fn-rtc-get 7 m)) (b3 (fn-rtc-get 8 m)) (hs (fn-rtc-get 9 m)) (committed nil) (evd (list (fn-ptx-summary ev))) (geo (fn-rtc-get 12 m)) (acc (fn-rtc-get 13 m))))
           :do-not-induct t)))
(defthm fn-ptx-len1
  (implies (and (true-listp x) (equal (len x) 1)) (equal x (list (car x))))
  :rule-classes nil)
(defthm fn-ptx-strip-ext-pair
  (implies (and (fn-ptx-done-p a :extend nil) (fn-ptx-done-p b :fsync nil))
           (equal (fn-ptx-strip-ext (list a b)) nil))
  :hints (("Goal" :in-theory (enable fn-ptx-strip-ext fn-rtc-get))))
(defthm fn-ptx-len-pos (implies (consp x) (< 0 (len x))) :rule-classes :linear)
(defthm fn-ptx-spans-evd-p-append
  (implies (and (true-listp rest) (fn-ptx-spans-evd-p rest spans) (< (len rest) (len spans))
                (fn-ptx-done-p s :pwrite (nfix (fn-rtc-get 2 (fn-rtc-get (len rest) spans)))))
           (fn-ptx-spans-evd-p (append rest (list s)) spans))
  :hints (("Goal" :in-theory (e/d (fn-ptx-spans-evd-p) (fn-ptx-done-p fn-rtc-get nfix)) :induct (fn-ptx-spans-evd-p rest spans))
          ("Subgoal *1/1" :in-theory (e/d (fn-ptx-spans-evd-p fn-rtc-get nfix) (fn-ptx-done-p)))))
(defthm fn-ptx-strip-ext-extsync
  (implies (and (true-listp evd) (equal (len evd) 1) (fn-ptx-done-p (car evd) :extend nil) (fn-ptx-done-p s :fsync nil))
           (equal (fn-ptx-strip-ext (append evd (list s))) nil))
  :hints (("Goal" :use ((:instance fn-ptx-len1 (x evd)) (:instance fn-ptx-strip-ext-pair (a (car evd)) (b s)))
           :in-theory (disable fn-ptx-strip-ext-pair fn-ptx-done-p fn-ptx-strip-ext))))
(defthm fn-ptx-strip-ext-extsync-evd+
  (implies (and (true-listp (fn-ptx-evd m)) (equal (len (fn-ptx-evd m)) 1) (fn-ptx-done-p (car (fn-ptx-evd m)) :extend nil)
                (fn-ptx-done-p (fn-ptx-summary ev) :fsync nil))
           (equal (fn-ptx-strip-ext (fn-ptx-evd+ m ev)) nil))
  :hints (("Goal" :use ((:instance fn-ptx-strip-ext-extsync (evd (fn-ptx-evd m)) (s (fn-ptx-summary ev))))
           :in-theory (e/d (fn-ptx-evd+) (fn-ptx-strip-ext-extsync fn-ptx-done-p fn-ptx-strip-ext)))))
(defthm fn-ptx-evd+-size-le
  (implies (and (fn-ptx-rows-p (fn-ptx-evd m) 3) (<= (len (fn-ptx-evd m)) 6))
           (<= (fn-rtc-size (fn-ptx-evd+ m ev)) 57))
  :hints (("Goal" :use (fn-ptx-rows-p-evd+ (:instance fn-ptx-evd+-len) (:instance fn-ptx-rows-p-size2 (x (fn-ptx-evd+ m ev)) (n 3)))
           :in-theory (disable fn-ptx-rows-p-evd+ fn-ptx-rows-p-size2 fn-ptx-evd+ fn-ptx-evd+-len))))
(defthm fn-ptx-spans-evd-p-nil (fn-ptx-spans-evd-p nil spans) :hints (("Goal" :in-theory (enable fn-ptx-spans-evd-p))))
(deftheory fn-ptx-mt7
  (union-theories (theory 'fn-ptx-mt6) '(fn-ptx-spans-evd-p-nil fn-ptx-evd+-size-le)))
(defthm fn-ptx-ok-extsync-done
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :extsyncing) (equal (fn-rtc-get 0 ev) :fsync) (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done))
           (fn-ptx-okp (fn-ptx-chg (fn-ptx-chg m :committed nil) :ph :payload-writing :k 0 :evd (fn-ptx-evd+ m ev))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) (union-theories (theory 'fn-ptx-mt7) '(fn-ptx-strip-ext-extsync-evd+)))
           :use ((:instance fn-ptx-okp-elim) (:instance fn-ptx-wfp-sizes) (:instance fn-ptx-wfp-phase) (:instance fn-ptx-acc-max-state-pos)
                 (:instance fn-ptx-okp-mk (ph :payload-writing) (k 0) (cur (fn-rtc-get 2 m)) (q (fn-rtc-get 3 m)) (kd (fn-rtc-get 4 m)) (ext (nfix (fn-rtc-get 5 m))) (nxt (nfix (fn-rtc-get 6 m))) (b1 (fn-rtc-get 7 m)) (b3 (fn-rtc-get 8 m)) (hs (fn-rtc-get 9 m)) (committed nil) (evd (fn-ptx-evd+ m ev)) (geo (fn-rtc-get 12 m)) (acc (fn-rtc-get 13 m))) (:instance fn-ptx-strip-ext-extsync-evd+) (:instance fn-ptx-summary-done-kind (kind :fsync)) (:instance fn-ptx-evd+-size-le))
           :do-not-induct t)))

(defthm fn-ptx-true-listp-append-single
  (implies (true-listp x) (true-listp (append x (list s)))))
(defthm fn-ptx-len-append-single
  (implies (true-listp x) (equal (len (append x (list s))) (+ 1 (len x)))))
(defthm fn-ptx-summary-done-nfix
  (implies (and (equal (fn-rtc-get 0 ev) :pwrite) (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done)
                (equal (fn-rtc-get 1 (fn-rtc-get 1 ev)) (nfix x)))
           (fn-ptx-done-p (fn-ptx-summary ev) :pwrite (nfix x)))
  :hints (("Goal" :in-theory (enable fn-ptx-summary fn-ptx-done-p fn-ptx-atom fn-rtc-get nfix))))
(defthm fn-ptx-tlf-id (implies (true-listp x) (equal (true-list-fix x) x)))
(defthm fn-ptx-evd+-append
  (implies (fn-ptx-rows-p (fn-ptx-evd m) 3) (equal (fn-ptx-evd+ m ev) (append (fn-ptx-evd m) (list (fn-ptx-summary ev)))))
  :hints (("Goal" :in-theory (enable fn-ptx-evd+))))
(defthm fn-ptx-nfix-succ (equal (nfix (+ 1 (nfix x))) (+ 1 (nfix x))))
(defthm fn-ptx-spans-evd-p-append-k
  (implies (and (true-listp rest) (fn-ptx-spans-evd-p rest spans) (equal (len rest) k) (< k (len spans))
                (fn-ptx-done-p s :pwrite (nfix (fn-rtc-get 2 (fn-rtc-get k spans)))))
           (fn-ptx-spans-evd-p (append rest (list s)) spans))
  :hints (("Goal" :use fn-ptx-spans-evd-p-append :in-theory (disable fn-ptx-spans-evd-p-append))))
(defthm fn-ptx-entry-evd-step
  (implies (and (fn-ptx-entry-evd-p (fn-ptx-strip-ext (fn-ptx-evd m)) m (fn-ptx-k m))
                (< (fn-ptx-k m) (fn-ptx-nspans m))
                (fn-ptx-rows-p (fn-ptx-evd m) 3)
                (equal (fn-rtc-get 0 ev) :pwrite)
                (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done)
                (equal (fn-rtc-get 1 (fn-rtc-get 1 ev)) (fn-ptx-span-n (fn-ptx-k m) m)))
           (fn-ptx-entry-evd-p (fn-ptx-strip-ext (fn-ptx-evd+ m ev)) m (+ 1 (fn-ptx-k m))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn-ptx-entry-evd-p fn-ptx-evd+-append fn-ptx-nspans fn-ptx-span-n fn-ptx-true-listp-append-single fn-ptx-len-append-single
                      fn-ptx-rows-p-true-list fn-ptx-strip-ext-append-ok fn-ptx-spans-evd-p-append-k fn-ptx-k fn-ptx-nfix-succ fn-ptx-nfix-nfix))
           :use ((:instance fn-ptx-summary-done-nfix (x (fn-rtc-get 2 (fn-rtc-get (fn-ptx-k m) (fn-ptx-spans m))))))
           :do-not-induct t)))
(defthm fn-ptx-ok-pwrite-more
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :payload-writing) (equal (fn-rtc-get 0 ev) :pwrite) (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done) (equal (fn-rtc-get 1 (fn-rtc-get 1 ev)) (fn-ptx-span-n (fn-ptx-k m) m)) (< (+ (fn-ptx-k m) 2) (fn-ptx-nspans m)))
           (fn-ptx-okp (fn-ptx-chg (fn-ptx-chg m :committed nil) :ph :payload-writing :k (+ (fn-ptx-k m) 1) :evd (fn-ptx-evd+ m ev))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) (union-theories (theory 'fn-ptx-mt7) '((:type-prescription len))))
           :use ((:instance fn-ptx-okp-elim) (:instance fn-ptx-wfp-sizes) (:instance fn-ptx-wfp-phase) (:instance fn-ptx-acc-max-state-pos)
                 (:instance fn-ptx-okp-mk (ph :payload-writing) (k (+ (fn-ptx-k m) 1)) (cur (fn-rtc-get 2 m)) (q (fn-rtc-get 3 m)) (kd (fn-rtc-get 4 m)) (ext (nfix (fn-rtc-get 5 m))) (nxt (nfix (fn-rtc-get 6 m))) (b1 (fn-rtc-get 7 m)) (b3 (fn-rtc-get 8 m)) (hs (fn-rtc-get 9 m)) (committed nil) (evd (fn-ptx-evd+ m ev)) (geo (fn-rtc-get 12 m)) (acc (fn-rtc-get 13 m))) (:instance fn-ptx-entry-evd-step) (:instance fn-ptx-strip-ext-len (evd (fn-ptx-evd m))) (:instance fn-ptx-spans-g-len (b1 (fn-ptx-b1 m)) (b3 (fn-ptx-b3 m)) (cur (fn-ptx-cur m))))
           :do-not-induct t)))
(defthm fn-ptx-ok-pwrite-last
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :payload-writing) (equal (fn-rtc-get 0 ev) :pwrite) (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done) (equal (fn-rtc-get 1 (fn-rtc-get 1 ev)) (fn-ptx-span-n (fn-ptx-k m) m)) (not (< (+ (fn-ptx-k m) 2) (fn-ptx-nspans m))))
           (fn-ptx-okp (fn-ptx-chg (fn-ptx-chg m :committed nil) :ph :log-writing :k (+ (fn-ptx-k m) 1) :evd (fn-ptx-evd+ m ev))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) (union-theories (theory 'fn-ptx-mt7) '((:type-prescription len))))
           :use ((:instance fn-ptx-okp-elim) (:instance fn-ptx-wfp-sizes) (:instance fn-ptx-wfp-phase) (:instance fn-ptx-acc-max-state-pos)
                 (:instance fn-ptx-okp-mk (ph :log-writing) (k (+ (fn-ptx-k m) 1)) (cur (fn-rtc-get 2 m)) (q (fn-rtc-get 3 m)) (kd (fn-rtc-get 4 m)) (ext (nfix (fn-rtc-get 5 m))) (nxt (nfix (fn-rtc-get 6 m))) (b1 (fn-rtc-get 7 m)) (b3 (fn-rtc-get 8 m)) (hs (fn-rtc-get 9 m)) (committed nil) (evd (fn-ptx-evd+ m ev)) (geo (fn-rtc-get 12 m)) (acc (fn-rtc-get 13 m))) (:instance fn-ptx-entry-evd-step) (:instance fn-ptx-strip-ext-len (evd (fn-ptx-evd m))) (:instance fn-ptx-spans-g-len (b1 (fn-ptx-b1 m)) (b3 (fn-ptx-b3 m)) (cur (fn-ptx-cur m))))
           :do-not-induct t)))
(defthm fn-ptx-ok-logwrite-done
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :log-writing) (equal (fn-rtc-get 0 ev) :pwrite) (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done) (equal (fn-rtc-get 1 (fn-rtc-get 1 ev)) (fn-ptx-span-n (fn-ptx-k m) m)))
           (fn-ptx-okp (fn-ptx-chg (fn-ptx-chg m :committed nil) :ph :committing :evd (fn-ptx-evd+ m ev))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) (union-theories (theory 'fn-ptx-mt7) '((:type-prescription len))))
           :use ((:instance fn-ptx-okp-elim) (:instance fn-ptx-wfp-sizes) (:instance fn-ptx-wfp-phase) (:instance fn-ptx-acc-max-state-pos)
                 (:instance fn-ptx-okp-mk (ph :committing) (k (nfix (fn-rtc-get 1 m))) (cur (fn-rtc-get 2 m)) (q (fn-rtc-get 3 m)) (kd (fn-rtc-get 4 m)) (ext (nfix (fn-rtc-get 5 m))) (nxt (nfix (fn-rtc-get 6 m))) (b1 (fn-rtc-get 7 m)) (b3 (fn-rtc-get 8 m)) (hs (fn-rtc-get 9 m)) (committed nil) (evd (fn-ptx-evd+ m ev)) (geo (fn-rtc-get 12 m)) (acc (fn-rtc-get 13 m))) (:instance fn-ptx-entry-evd-step) (:instance fn-ptx-strip-ext-len (evd (fn-ptx-evd m))) (:instance fn-ptx-spans-g-len (b1 (fn-ptx-b1 m)) (b3 (fn-ptx-b3 m)) (cur (fn-ptx-cur m))))
           :do-not-induct t)))
(defthm fn-ptx-kd-commit-shape
  (implies (and (fn-ptx-atoms-p tr) (equal (len tr) 32))
           (and (equal (fn-rtc-size (fn-ptx-kd-commit kd tr elen)) 75)
                (equal (len (fn-ptx-kd-last (fn-ptx-kd-commit kd tr elen))) 32)))
  :hints (("Goal" :in-theory (e/d (fn-ptx-kd-commit fn-ptx-kd-mk fn-ptx-kd-last fn-rtc-get fn-ptx-atoms-p-size fn-ptx-size-of-cons fn-ptx-size-of-atom) (fn-ptx-atoms-p-size))
           :use ((:instance fn-ptx-atoms-p-size (x tr))))))
(defthm fn-ptx-ok-end-m0
  (implies (and (fn-ptx-okp m) (or fenced (not (member-eq (fn-ptx-ph m) '(:closed :fenced)))))
           (fn-ptx-okp (mv-nth 0 (fn-ptx-end (fn-ptx-chg m :committed nil) o (fn-ptx-kd m) (fn-ptx-ext m) fenced nil id inc st))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) (union-theories (theory 'fn-ptx-mt7) '((:type-prescription len))))
           :use ((:instance fn-ptx-okp-elim) (:instance fn-ptx-wfp-sizes) (:instance fn-ptx-wfp-phase)
                 (:instance fn-ptx-end-ok (m (fn-ptx-chg m :committed nil)) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m)) (committed nil)))
           :do-not-induct t)))
(defthm fn-ptx-ok-end-posted
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :committing))
           (fn-ptx-okp (mv-nth 0 (fn-ptx-end (fn-ptx-chg m :committed nil) :posted
                                             (fn-ptx-kd-commit (fn-ptx-kd m) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-elen m))
                                             (fn-ptx-nxt m) nil t id inc st))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) (union-theories (theory 'fn-ptx-mt7) '((:type-prescription len))))
           :use ((:instance fn-ptx-okp-elim) (:instance fn-ptx-wfp-sizes) (:instance fn-ptx-wfp-phase)
                 (:instance fn-ptx-kd-commit-shape (kd (fn-ptx-kd m)) (tr (fn-rtc-get 1 (fn-ptx-hs m))) (elen (fn-ptx-elen m)))
                 (:instance fn-ptx-end-ok (m (fn-ptx-chg m :committed nil)) (o :posted)
                            (kd (fn-ptx-kd-commit (fn-ptx-kd m) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-elen m)))
                            (ext (fn-ptx-nxt m)) (fenced nil) (committed t)))
           :do-not-induct t)))
(defthm fn-ptx-handed-p-shape
  (and (fn-ptx-atoms-p (list (fn-ptx-atom (fn-rtc-get 4 ev)) (fn-ptx-atom (fn-rtc-get 5 ev)) (fn-rtc-h-buf (fn-rtc-get 6 ev)) (fn-rtc-h-len (fn-rtc-get 6 ev)))) (equal (len (list (fn-ptx-atom (fn-rtc-get 4 ev)) (fn-ptx-atom (fn-rtc-get 5 ev)) (fn-rtc-h-buf (fn-rtc-get 6 ev)) (fn-rtc-h-len (fn-rtc-get 6 ev)))) 4))
  :hints (("Goal" :in-theory (enable fn-rtc-h-buf fn-rtc-h-len fn-ptx-atoms-p fn-ptx-atom))))
(defthm fn-ptx-rows-p-q-append
  (implies (and (fn-ptx-rows-p q 4) (< (len q) *fn-ptx-k*) (fn-ptx-atoms-p p) (equal (len p) 4))
           (and (fn-ptx-rows-p (append (true-list-fix q) (list p)) 4) (<= (len (append (true-list-fix q) (list p))) *fn-ptx-k*)
                (<= (fn-rtc-size (append (true-list-fix q) (list p))) 21)))
  :hints (("Goal" :use ((:instance fn-ptx-rows-p-append-single (evd q) (n 4) (s p)) (:instance fn-ptx-rows-p-size2 (x (append q (list p))) (n 4))
                        (:instance fn-ptx-len-append-single (x q) (s p)))
           :in-theory (disable fn-ptx-rows-p-append-single fn-ptx-rows-p-size2 fn-ptx-len-append-single))))
(defthm fn-ptx-ok-handed-idle
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :idle))
           (fn-ptx-okp (mv-nth 0 (fn-ptx-start (list (fn-ptx-atom (fn-rtc-get 4 ev)) (fn-ptx-atom (fn-rtc-get 5 ev)) (fn-rtc-h-buf (fn-rtc-get 6 ev)) (fn-rtc-h-len (fn-rtc-get 6 ev))) nil (fn-ptx-kd m) (fn-ptx-ext m) (fn-ptx-geo m) nil))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) (union-theories (theory 'fn-ptx-mt7) '((:type-prescription len))))
           :use ((:instance fn-ptx-okp-elim) (:instance fn-ptx-wfp-sizes) (:instance fn-ptx-handed-p-shape)
                 (:instance fn-ptx-start-ok (p (list (fn-ptx-atom (fn-rtc-get 4 ev)) (fn-ptx-atom (fn-rtc-get 5 ev)) (fn-rtc-h-buf (fn-rtc-get 6 ev)) (fn-rtc-h-len (fn-rtc-get 6 ev)))) (q nil) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m)) (geo (fn-ptx-geo m)) (committed nil)))
           :do-not-induct t)))
(defthm fn-ptx-ok-handed-queue
  (implies (and (fn-ptx-okp m) (not (member-eq (fn-ptx-ph m) '(:fenced :closed))) (not (equal (fn-ptx-ph m) :idle)) (< (len (fn-ptx-q m)) *fn-ptx-k*))
           (fn-ptx-okp (fn-ptx-chg (fn-ptx-chg m :committed nil) :q (append (true-list-fix (fn-ptx-q m)) (list (list (fn-ptx-atom (fn-rtc-get 4 ev)) (fn-ptx-atom (fn-rtc-get 5 ev)) (fn-rtc-h-buf (fn-rtc-get 6 ev)) (fn-rtc-h-len (fn-rtc-get 6 ev))))))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) (union-theories (theory 'fn-ptx-mt7) '((:type-prescription len) )))
           :use ((:instance fn-ptx-okp-elim) (:instance fn-ptx-wfp-sizes) (:instance fn-ptx-wfp-phase) (:instance fn-ptx-acc-max-state-pos)
                 (:instance fn-ptx-okp-mk (ph (fn-rtc-get 0 m)) (k (nfix (fn-rtc-get 1 m))) (cur (fn-rtc-get 2 m)) (q (append (true-list-fix (fn-ptx-q m)) (list (list (fn-ptx-atom (fn-rtc-get 4 ev)) (fn-ptx-atom (fn-rtc-get 5 ev)) (fn-rtc-h-buf (fn-rtc-get 6 ev)) (fn-rtc-h-len (fn-rtc-get 6 ev)))))) (kd (fn-rtc-get 4 m)) (ext (nfix (fn-rtc-get 5 m))) (nxt (nfix (fn-rtc-get 6 m))) (b1 (fn-rtc-get 7 m)) (b3 (fn-rtc-get 8 m)) (hs (fn-rtc-get 9 m)) (committed nil) (evd (fn-rtc-get 11 m)) (geo (fn-rtc-get 12 m)) (acc (fn-rtc-get 13 m))) (:instance fn-ptx-handed-p-shape) (:instance fn-ptx-rows-p-q-append (q (fn-ptx-q m)) (p (list (fn-ptx-atom (fn-rtc-get 4 ev)) (fn-ptx-atom (fn-rtc-get 5 ev)) (fn-rtc-h-buf (fn-rtc-get 6 ev)) (fn-rtc-h-len (fn-rtc-get 6 ev))))))
           :do-not-induct t)))
(defthm fn-ptx-octet-listp-atoms
  (implies (fn-b3-octet-listp x) (fn-ptx-atoms-p x))
  :hints (("Goal" :in-theory (enable fn-b3-octet-listp fn-ptx-atoms-p))))
(defthm fn-ptx-finish-digest-atoms
  (and (fn-ptx-atoms-p (fn-ptx-finish-digest pos st n spans id inc fn-rtc-st))
       (equal (len (fn-ptx-finish-digest pos st n spans id inc fn-rtc-st)) 32))
  :hints (("Goal" :use (fn-ptx-finish-digest-shape (:instance fn-ptx-octet-listp-atoms (x (fn-ptx-finish-digest pos st n spans id inc fn-rtc-st))))
           :in-theory (disable fn-ptx-finish-digest-shape fn-ptx-octet-listp-atoms fn-ptx-finish-digest))))
(defthm fn-ptx-span-len-exact
  (equal (len (fn-ptx-span h off n)) (if (zp n) 0 1))
  :hints (("Goal" :in-theory (enable fn-ptx-span))))
(defthm fn-ptx-spans-g-two
  (implies (and (< 0 (fn-ptx-buf-len b1)) (< (fn-ptx-buf-x b3) (fn-ptx-buf-len b3)))
           (<= 2 (len (fn-ptx-spans-g b1 b3 cur))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-spans-g fn-ptx-len-append fn-ptx-span-len-exact (:type-prescription len)
                                                                       (:executable-counterpart zp) zp (:executable-counterpart nfix) nfix fn-ptx-buf-len fn-ptx-buf-x)))))
(defthm fn-ptx-get-list2
  (and (equal (fn-rtc-get 0 (list a b)) a) (equal (fn-rtc-get 1 (list a b)) b))
  :hints (("Goal" :in-theory (enable fn-rtc-get))))
(defthm fn-ptx-get-list3
  (and (equal (fn-rtc-get 0 (list a b c)) a) (equal (fn-rtc-get 1 (list a b c)) b) (equal (fn-rtc-get 2 (list a b c)) c))
  :hints (("Goal" :in-theory (enable fn-rtc-get))))
(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm fn-ptx-pos-c-bound
    (implies (and (natp pos) (< pos 8589934592)) (< (floor pos 1024) 18446744073709551616))
    :rule-classes nil))
(defthm fn-ptx-hs-size-pair
  (implies (and (natp pos) (fn-ptx-stack-bits-p st c 0) (natp c) (< c 18446744073709551616))
           (<= (fn-rtc-size (list pos st)) 4101))
  :hints (("Goal" :use ((:instance fn-ptx-stack-bits-size (h 0) (j 64)))
           :in-theory (e/d (fn-ptx-size-of-cons) (fn-ptx-stack-bits-size fn-ptx-stack-bits-p)))))
(defthm fn-ptx-hash-more-aux1
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :hashing)
                (< (+ (mv-nth 0 (fn-ptx-absorb nw (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-nmsg m) (fn-ptx-spans m) id inc st)) 1024)
                   (fn-ptx-nmsg m)))
           (let ((pos (mv-nth 0 (fn-ptx-absorb nw (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-nmsg m) (fn-ptx-spans m) id inc st)))
                 (stk (mv-nth 1 (fn-ptx-absorb nw (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-nmsg m) (fn-ptx-spans m) id inc st))))
             (and (natp pos) (equal (mod pos 1024) 0) (< pos (fn-ptx-nmsg m))
                  (fn-ptx-stack-bits-p stk (floor pos 1024) 0))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) (union-theories (theory 'fn-ptx-mt7)
                    '((:type-prescription len) fn-ptx-floor-1024-natp fn-ptx-spans-is-g)))
           :use ((:instance fn-ptx-okp-elim) (:instance fn-ptx-wfp-phase)
                 (:instance fn-ptx-absorb-bits (pos (fn-rtc-get 0 (fn-ptx-hs m))) (st (fn-rtc-get 1 (fn-ptx-hs m))) (n (fn-ptx-nmsg m)) (spans (fn-ptx-spans m)) (fn-rtc-st st)))
           :do-not-induct t)))
(defthm fn-ptx-hs-size-ok
  (implies (and (natp pos) (fn-ptx-stack-bits-p stk (floor pos 1024) 0) (< pos nmsg) (<= nmsg (+ 10 fmax)) (<= fmax 4294967295))
           (<= (fn-rtc-size (list pos stk)) 4101))
  :hints (("Goal" :use ((:instance fn-ptx-pos-c-bound) (:instance fn-ptx-hs-size-pair (st stk) (c (floor pos 1024)))
                        (:instance fn-ptx-floor-1024-natp))
           :in-theory (disable fn-ptx-hs-size-pair fn-ptx-floor-1024-natp fn-ptx-stack-bits-p))))
(defthm fn-ptx-ok-hash-more
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :hashing) (< (+ (mv-nth 0 (fn-ptx-absorb nw (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-nmsg m) (fn-ptx-spans m) id inc st)) 1024) (fn-ptx-nmsg m)))
           (fn-ptx-okp (fn-ptx-chg (fn-ptx-chg m :committed nil) :hs (list (mv-nth 0 (fn-ptx-absorb nw (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-nmsg m) (fn-ptx-spans m) id inc st)) (mv-nth 1 (fn-ptx-absorb nw (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-nmsg m) (fn-ptx-spans m) id inc st))))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) (union-theories (theory 'fn-ptx-mt7) '((:type-prescription len) fn-ptx-spans-is-g fn-ptx-get-list2)))
           :use ((:instance fn-ptx-okp-elim) (:instance fn-ptx-wfp-sizes) (:instance fn-ptx-wfp-phase) (:instance fn-ptx-acc-max-state-pos)
                 (:instance fn-ptx-okp-mk (ph (fn-rtc-get 0 m)) (k (nfix (fn-rtc-get 1 m))) (cur (fn-rtc-get 2 m)) (q (fn-rtc-get 3 m)) (kd (fn-rtc-get 4 m)) (ext (nfix (fn-rtc-get 5 m))) (nxt (nfix (fn-rtc-get 6 m))) (b1 (fn-rtc-get 7 m)) (b3 (fn-rtc-get 8 m)) (hs (list (mv-nth 0 (fn-ptx-absorb nw (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-nmsg m) (fn-ptx-spans m) id inc st)) (mv-nth 1 (fn-ptx-absorb nw (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-nmsg m) (fn-ptx-spans m) id inc st)))) (committed nil) (evd (fn-rtc-get 11 m)) (geo (fn-rtc-get 12 m)) (acc (fn-rtc-get 13 m))) (:instance fn-ptx-hash-more-aux1) (:instance fn-ptx-hs-size-ok (pos (mv-nth 0 (fn-ptx-absorb nw (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-nmsg m) (fn-ptx-spans m) id inc st))) (stk (mv-nth 1 (fn-ptx-absorb nw (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-nmsg m) (fn-ptx-spans m) id inc st))) (nmsg (fn-ptx-nmsg m)) (fmax (fn-ptx-fmax m))))
           :do-not-induct t)))
(defthm fn-ptx-strip-ext-nil (equal (fn-ptx-strip-ext nil) nil) :hints (("Goal" :in-theory (enable fn-ptx-strip-ext fn-ptx-done-p fn-rtc-get))))
(defthm fn-ptx-pad-len-natp (natp (fn-ptx-pad-len elen unit)) :hints (("Goal" :in-theory (enable fn-ptx-pad-len))))
(defthm fn-ptx-spans-len-natp (natp (fn-ptx-spans-len spans)) :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-ptx-spans-len))))
(defthm fn-ptx-pad-len-tp (natp (fn-ptx-pad-len elen unit)) :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-ptx-pad-len))))
(defthm fn-ptx-buf-of-list
  (and (equal (fn-ptx-buf-h (list a b c d)) (nfix a)) (equal (fn-ptx-buf-g (list a b c d)) (nfix b))
       (equal (fn-ptx-buf-len (list a b c d)) (nfix c)) (equal (fn-ptx-buf-x (list a b c d)) (nfix d)))
  :hints (("Goal" :in-theory (enable fn-ptx-buf-h fn-ptx-buf-g fn-ptx-buf-len fn-ptx-buf-x fn-rtc-get))))
(defthm fn-ptx-nfix-buf
  (and (equal (nfix (fn-ptx-buf-h b)) (fn-ptx-buf-h b)) (equal (nfix (fn-ptx-buf-g b)) (fn-ptx-buf-g b))
       (equal (nfix (fn-ptx-buf-len b)) (fn-ptx-buf-len b)) (equal (nfix (fn-ptx-buf-x b)) (fn-ptx-buf-x b)))
  :hints (("Goal" :in-theory (enable fn-ptx-buf-h fn-ptx-buf-g fn-ptx-buf-len fn-ptx-buf-x))))
(defthm fn-ptx-ok-hash-extending
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :hashing))
           (fn-ptx-okp (fn-ptx-chg (fn-ptx-chg m :committed nil) :ph :extending :k 0 :nxt nx :b3 (list (fn-ptx-buf-h (fn-ptx-b3 m)) (fn-ptx-buf-g (fn-ptx-b3 m)) (+ (fn-ptx-buf-len (fn-ptx-b3 m)) 32) (fn-ptx-buf-x (fn-ptx-b3 m))) :hs (list (fn-ptx-nmsg m) (fn-ptx-finish-digest (mv-nth 0 (fn-ptx-absorb nw (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-nmsg m) (fn-ptx-spans m) id inc st)) (mv-nth 1 (fn-ptx-absorb nw (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-nmsg m) (fn-ptx-spans m) id inc st)) (fn-ptx-nmsg m) (fn-ptx-spans m) id inc st) (fn-ptx-pad-len (+ (fn-ptx-nmsg m) 32) (fn-ptx-unit m))) :evd nil)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) (union-theories (theory 'fn-ptx-mt7) '((:type-prescription len) fn-ptx-spans-is-g fn-ptx-get-list2 fn-ptx-get-list3 fn-ptx-strip-ext-nil fn-ptx-pad-len-tp fn-ptx-spans-len-natp fn-ptx-buf-of-list fn-ptx-nfix-buf (:type-prescription fn-ptx-buf-h) (:type-prescription fn-ptx-buf-g) (:type-prescription fn-ptx-buf-len) (:type-prescription fn-ptx-buf-x))))
           :use ((:instance fn-ptx-okp-elim) (:instance fn-ptx-wfp-sizes) (:instance fn-ptx-wfp-phase) (:instance fn-ptx-acc-max-state-pos)
                 (:instance fn-ptx-okp-mk (ph :extending) (k 0) (cur (fn-rtc-get 2 m)) (q (fn-rtc-get 3 m)) (kd (fn-rtc-get 4 m)) (ext (nfix (fn-rtc-get 5 m))) (nxt nx) (b1 (fn-rtc-get 7 m)) (b3 (list (fn-ptx-buf-h (fn-ptx-b3 m)) (fn-ptx-buf-g (fn-ptx-b3 m)) (+ (fn-ptx-buf-len (fn-ptx-b3 m)) 32) (fn-ptx-buf-x (fn-ptx-b3 m)))) (hs (list (fn-ptx-nmsg m) (fn-ptx-finish-digest (mv-nth 0 (fn-ptx-absorb nw (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-nmsg m) (fn-ptx-spans m) id inc st)) (mv-nth 1 (fn-ptx-absorb nw (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-nmsg m) (fn-ptx-spans m) id inc st)) (fn-ptx-nmsg m) (fn-ptx-spans m) id inc st) (fn-ptx-pad-len (+ (fn-ptx-nmsg m) 32) (fn-ptx-unit m)))) (committed nil) (evd nil) (geo (fn-rtc-get 12 m)) (acc (fn-rtc-get 13 m))) (:instance fn-ptx-spans-g-two (b1 (fn-ptx-b1 m)) (b3 (list (fn-ptx-buf-h (fn-ptx-b3 m)) (fn-ptx-buf-g (fn-ptx-b3 m)) (+ (fn-ptx-buf-len (fn-ptx-b3 m)) 32) (fn-ptx-buf-x (fn-ptx-b3 m)))) (cur (fn-ptx-cur m))) (:instance fn-ptx-finish-digest-atoms (pos (mv-nth 0 (fn-ptx-absorb nw (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-nmsg m) (fn-ptx-spans m) id inc st))) (st (mv-nth 1 (fn-ptx-absorb nw (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-nmsg m) (fn-ptx-spans m) id inc st))) (n (fn-ptx-nmsg m)) (spans (fn-ptx-spans m)) (fn-rtc-st st)))
           :do-not-induct t)))
(defthm fn-ptx-ok-hash-payload
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :hashing))
           (fn-ptx-okp (fn-ptx-chg (fn-ptx-chg m :committed nil) :ph :payload-writing :k 0 :nxt (fn-ptx-ext m) :b3 (list (fn-ptx-buf-h (fn-ptx-b3 m)) (fn-ptx-buf-g (fn-ptx-b3 m)) (+ (fn-ptx-buf-len (fn-ptx-b3 m)) 32) (fn-ptx-buf-x (fn-ptx-b3 m))) :hs (list (fn-ptx-nmsg m) (fn-ptx-finish-digest (mv-nth 0 (fn-ptx-absorb nw (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-nmsg m) (fn-ptx-spans m) id inc st)) (mv-nth 1 (fn-ptx-absorb nw (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-nmsg m) (fn-ptx-spans m) id inc st)) (fn-ptx-nmsg m) (fn-ptx-spans m) id inc st) (fn-ptx-pad-len (+ (fn-ptx-nmsg m) 32) (fn-ptx-unit m))) :evd nil)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) (union-theories (theory 'fn-ptx-mt7) '((:type-prescription len) fn-ptx-spans-is-g fn-ptx-get-list2 fn-ptx-get-list3 fn-ptx-strip-ext-nil fn-ptx-pad-len-tp fn-ptx-spans-len-natp fn-ptx-buf-of-list fn-ptx-nfix-buf (:type-prescription fn-ptx-buf-h) (:type-prescription fn-ptx-buf-g) (:type-prescription fn-ptx-buf-len) (:type-prescription fn-ptx-buf-x))))
           :use ((:instance fn-ptx-okp-elim) (:instance fn-ptx-wfp-sizes) (:instance fn-ptx-wfp-phase) (:instance fn-ptx-acc-max-state-pos)
                 (:instance fn-ptx-okp-mk (ph :payload-writing) (k 0) (cur (fn-rtc-get 2 m)) (q (fn-rtc-get 3 m)) (kd (fn-rtc-get 4 m)) (ext (nfix (fn-rtc-get 5 m))) (nxt (fn-ptx-ext m)) (b1 (fn-rtc-get 7 m)) (b3 (list (fn-ptx-buf-h (fn-ptx-b3 m)) (fn-ptx-buf-g (fn-ptx-b3 m)) (+ (fn-ptx-buf-len (fn-ptx-b3 m)) 32) (fn-ptx-buf-x (fn-ptx-b3 m)))) (hs (list (fn-ptx-nmsg m) (fn-ptx-finish-digest (mv-nth 0 (fn-ptx-absorb nw (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-nmsg m) (fn-ptx-spans m) id inc st)) (mv-nth 1 (fn-ptx-absorb nw (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-nmsg m) (fn-ptx-spans m) id inc st)) (fn-ptx-nmsg m) (fn-ptx-spans m) id inc st) (fn-ptx-pad-len (+ (fn-ptx-nmsg m) 32) (fn-ptx-unit m)))) (committed nil) (evd nil) (geo (fn-rtc-get 12 m)) (acc (fn-rtc-get 13 m))) (:instance fn-ptx-spans-g-two (b1 (fn-ptx-b1 m)) (b3 (list (fn-ptx-buf-h (fn-ptx-b3 m)) (fn-ptx-buf-g (fn-ptx-b3 m)) (+ (fn-ptx-buf-len (fn-ptx-b3 m)) 32) (fn-ptx-buf-x (fn-ptx-b3 m)))) (cur (fn-ptx-cur m))) (:instance fn-ptx-finish-digest-atoms (pos (mv-nth 0 (fn-ptx-absorb nw (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-nmsg m) (fn-ptx-spans m) id inc st))) (st (mv-nth 1 (fn-ptx-absorb nw (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-nmsg m) (fn-ptx-spans m) id inc st))) (n (fn-ptx-nmsg m)) (spans (fn-ptx-spans m)) (fn-rtc-st st)))
           :do-not-induct t)))
(defthm fn-ptx-hash-0
  (equal (mv-nth 0 (fn-ptx-hash m q id inc st))
         (let* ((spans (fn-ptx-spans m)) (nmsg (fn-ptx-spans-len spans)) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m)) (b3 (fn-ptx-b3 m))
                (nw (min *fn-ptx-nw-max* (max 1 (floor (nfix q) *fn-ptx-window*))))
                (m0 (fn-ptx-chg m :committed nil))
                (pos (mv-nth 0 (fn-ptx-absorb nw (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) nmsg spans id inc st)))
                (stk (mv-nth 1 (fn-ptx-absorb nw (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) nmsg spans id inc st))))
           (if (< (+ pos 1024) nmsg)
               (fn-ptx-chg m0 :hs (list pos stk))
             (let* ((trailer (fn-ptx-finish-digest pos stk nmsg spans id inc st))
                    (pad (fn-ptx-pad-len (+ nmsg 32) (fn-ptx-unit m)))
                    (b3x (list (fn-ptx-buf-h b3) (fn-ptx-buf-g b3) (+ (fn-ptx-buf-len b3) 32) (fn-ptx-buf-x b3)))
                    (elen (+ nmsg 32 pad))
                    (front (fn-ptx-kd-frontier kd)))
               (if (fn-olr-extension-needed-p front elen ext (fn-ptx-unit m))
                   (let ((nx (fn-olr-extension-target front elen ext (fn-ptx-unit m))))
                     (if (<= (expt 2 64) nx)
                         (mv-nth 0 (fn-ptx-end m0 :refused kd ext nil nil id inc st))
                       (fn-ptx-chg m0 :ph :extending :k 0 :nxt nx :b3 b3x :hs (list nmsg trailer pad) :evd nil)))
                 (fn-ptx-chg m0 :ph :payload-writing :k 0 :nxt ext :b3 b3x :hs (list nmsg trailer pad) :evd nil))))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-hash (:executable-counterpart mv-nth) mv-nth fn-ptx-spans-len)) :do-not-induct t)))
(defthm fn-ptx-hash-ok
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :hashing))
           (fn-ptx-okp (mv-nth 0 (fn-ptx-hash m q id inc st))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn-ptx-hash-0 fn-ptx-nmsg (:executable-counterpart equal) (:executable-counterpart member-equal) member-equal))
           :do-not-induct t
           :use ((:instance fn-ptx-ok-hash-more (nw (min *fn-ptx-nw-max* (max 1 (floor (nfix q) *fn-ptx-window*)))))
                 (:instance fn-ptx-ok-hash-payload (nw (min *fn-ptx-nw-max* (max 1 (floor (nfix q) *fn-ptx-window*)))))
                 (:instance fn-ptx-ok-hash-extending (nw (min *fn-ptx-nw-max* (max 1 (floor (nfix q) *fn-ptx-window*))))
                            (nx (fn-olr-extension-target (fn-ptx-kd-frontier (fn-ptx-kd m))
                                                         (+ (fn-ptx-spans-len (fn-ptx-spans m)) 32
                                                            (fn-ptx-pad-len (+ (fn-ptx-spans-len (fn-ptx-spans m)) 32) (fn-ptx-unit m)))
                                                         (fn-ptx-ext m) (fn-ptx-unit m))))
                 (:instance fn-ptx-ok-end-m0 (o :refused) (fenced nil))))))
(defthm fn-ptx-read-0
  (equal (mv-nth 0 (fn-ptx-read m q id inc stx))
         (let* ((cur (fn-ptx-cur m)) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m)) (bp (fn-ptx-cur-bp cur)) (len (fn-ptx-cur-len cur)) (pos (fn-ptx-cur-hoff cur)) (lim (min len (fn-ptx-hmax m))) (w (fn-ptx-read-w q)) (m0 (fn-ptx-chg m :committed nil)) (fresh (not (consp (fn-ptx-b1 m)))) (h1 (if fresh (fn-ptx-free 0 nil id inc stx) (fn-ptx-buf-h (fn-ptx-b1 m)))) (h3 (if fresh (fn-ptx-free 0 h1 id inc stx) (fn-ptx-buf-h (fn-ptx-b3 m)))) (g1 (if fresh (+ 1 (fn-ptx-gen h1 id inc stx)) (fn-ptx-buf-g (fn-ptx-b1 m)))) (g3 (if fresh (+ 1 (fn-ptx-gen h3 id inc stx)) (fn-ptx-buf-g (fn-ptx-b3 m)))) (off (if fresh *fn-ptx-sufhead-max* (fn-ptx-buf-len (fn-ptx-b3 m)))) (e (fn-ptx-head-end bp pos (min lim (+ pos w 3)) id inc stx))) (if (not (and h1 h3)) (mv-nth 0 (fn-ptx-end m0 :refused kd ext nil nil id inc stx)) (let* ((m1 (fn-ptx-chg m0 :b1 (list h1 g1 0 0) :b3 (list h3 g3 off *fn-ptx-sufhead-max*))) (mr (fn-ptx-chg m0 :b1 nil :b3 nil)) (nfeed (if e (- e pos) (if (< (+ pos w 3) lim) w 0)))) (mv-let (a sp) (fn-ptx-acc-feed (fn-ptx-acc m) (fn-ptx-range bp pos nfeed id inc stx)) (let ((off2 (+ off (len sp)))) (cond ((not (<= (+ off2 32) (fn-ptx-cap h3 id inc stx))) (mv-nth 0 (fn-ptx-end mr :refused kd ext nil nil id inc stx))) (e (mv-let (ok pre ins ioff sh st) (fn-ptx-acc-end a (- len e)) (let* ((ioff (if (consp ins) (nfix ioff) len)) (start (- *fn-ptx-sufhead-max* (min (len sh) *fn-ptx-sufhead-max*))) (end (+ off2 (len st))) (rlen (+ (len pre) len (len ins) (- end start))) (b1 (append (fn-ptx-frame-header rlen) (fn-ptx-kd-last kd) pre))) (if (not (and ok (<= ioff len) (<= (+ 32 rlen) (fn-ptx-fmax m)) (<= (+ (len b1) (len ins)) (fn-ptx-cap h1 id inc stx)) (<= (+ end 32) (fn-ptx-cap h3 id inc stx)))) (mv-nth 0 (fn-ptx-end mr :refused kd ext nil nil id inc stx)) (fn-ptx-chg m1 :ph :hashing :k 0 :cur (list (fn-ptx-cur-fid cur) (fn-ptx-cur-finc cur) bp len e (fn-ptx-cur-txid cur) ioff) :b1 (list h1 g1 (len b1) (len ins)) :b3 (list h3 g3 end start) :hs (list 0 nil) :acc nil))))) ((< (+ pos w 3) lim) (fn-ptx-chg m1 :cur (list (fn-ptx-cur-fid cur) (fn-ptx-cur-finc cur) bp len (+ pos w) (fn-ptx-cur-txid cur) len) :b3 (list h3 g3 off2 *fn-ptx-sufhead-max*) :acc a)) (t (mv-nth 0 (fn-ptx-end mr :refused kd ext nil nil id inc stx))))))))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-read (:executable-counterpart mv-nth) mv-nth)) :do-not-induct t)))
(defthm fn-ptx-spans-len-append
  (equal (fn-ptx-spans-len (append a b)) (+ (fn-ptx-spans-len a) (fn-ptx-spans-len b)))
  :hints (("Goal" :in-theory (enable fn-ptx-spans-len))))
(defthm fn-ptx-spans-len-span
  (equal (fn-ptx-spans-len (fn-ptx-span h off n)) (nfix n))
  :hints (("Goal" :in-theory (enable fn-ptx-spans-len fn-ptx-span fn-rtc-get))))
(defthm fn-ptx-nfix-cur
  (and (equal (nfix (fn-ptx-cur-len c)) (fn-ptx-cur-len c)) (equal (nfix (fn-ptx-cur-ioff c)) (fn-ptx-cur-ioff c)))
  :hints (("Goal" :in-theory (enable fn-ptx-cur-len fn-ptx-cur-ioff))))
(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm fn-ptx-ar-min-split
    (implies (and (natp io) (natp al))
             (equal (+ (nfix (min io al)) (nfix (+ al (- (min io al))))) al))))
(defthm fn-ptx-spans-len-g
  (equal (fn-ptx-spans-len (fn-ptx-spans-g b1 b3 cur))
         (+ (fn-ptx-buf-len b1) (fn-ptx-buf-x b1) (fn-ptx-cur-len cur) (nfix (- (fn-ptx-buf-len b3) (fn-ptx-buf-x b3)))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                     '(fn-ptx-spans-g fn-ptx-spans-len-append fn-ptx-spans-len-span fn-ptx-nfix-cur fn-ptx-nfix-buf natp
                       (:type-prescription fn-ptx-buf-len) (:type-prescription fn-ptx-buf-x)
                       (:type-prescription fn-ptx-cur-len) (:type-prescription fn-ptx-cur-ioff))) 
           :use ((:instance fn-ptx-ar-min-split (io (fn-ptx-cur-ioff cur)) (al (fn-ptx-cur-len cur)))))))
(defthm fn-ptx-read-w-natp (natp (fn-ptx-read-w q)) :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-ptx-read-w))))
(defthm fn-ptx-wfp-of-mk
  (iff (fn-ptx-wfp (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc))
       (fn-ptx-wfp-c ph cur q kd b1 b3 hs evd geo acc))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) (theory 'fn-ptx-mt7))
           :use ((:instance fn-ptx-wfp-sizes (m (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc)))
                 (:instance fn-ptx-wfp-phase (m (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc)))
                 (:instance fn-ptx-wfp-intro (m (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc))))
           :do-not-induct t)))
(defthm fn-ptx-okp-mk-norm2
  (implies (syntaxp (not (and (equal ext ''0) (equal nxt ''0) (equal committed ''nil))))
           (iff (fn-ptx-okp (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc))
                (fn-ptx-okp (fn-ptx-mk ph k cur q kd 0 0 b1 b3 hs nil evd geo acc))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) (union-theories (theory 'fn-ptx-mt7) '(fn-ptx-wfp-of-mk)))
           :use ((:instance fn-ptx-okp-elim (m (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc)))
                 (:instance fn-ptx-okp-intro (m (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc)))
                 (:instance fn-ptx-okp-elim (m (fn-ptx-mk ph k cur q kd 0 0 b1 b3 hs nil evd geo acc)))
                 (:instance fn-ptx-okp-intro (m (fn-ptx-mk ph k cur q kd 0 0 b1 b3 hs nil evd geo acc))))
           :do-not-induct t)))
(defthm fn-ptx-ok-read-cont
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :reading) (atom h1) (atom g1) (atom h3) (atom g3) (natp off2) (<= 9 off2) (<= (fn-rtc-size a) (fn-ptx-acc-max-state)))
           (fn-ptx-okp (fn-ptx-chg (fn-ptx-chg (fn-ptx-chg m :committed nil) :b1 (list h1 g1 0 0) :b3 (list h3 g3 off *fn-ptx-sufhead-max*)) :cur (list (fn-ptx-cur-fid (fn-ptx-cur m)) (fn-ptx-cur-finc (fn-ptx-cur m)) (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-len (fn-ptx-cur m)) (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q)) (fn-ptx-cur-txid (fn-ptx-cur m)) (fn-ptx-cur-len (fn-ptx-cur m))) :b3 (list h3 g3 off2 *fn-ptx-sufhead-max*) :acc a)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) (union-theories (theory 'fn-ptx-mt7) '((:type-prescription len) fn-ptx-okp-mk-norm2 fn-ptx-buf-of-list fn-ptx-nfix-buf (:type-prescription fn-ptx-buf-h) (:type-prescription fn-ptx-buf-g) (:type-prescription fn-ptx-buf-len) (:type-prescription fn-ptx-buf-x) fn-ptx-nfix-cur natp (:type-prescription fn-ptx-cur-bp) (:type-prescription fn-ptx-cur-len) (:type-prescription fn-ptx-cur-hoff) (:type-prescription fn-ptx-cur-txid) (:type-prescription fn-ptx-cur-ioff) fn-ptx-cur-fid fn-ptx-cur-finc fn-ptx-read-w-natp)))
           :use ((:instance fn-ptx-okp-elim) (:instance fn-ptx-wfp-sizes) (:instance fn-ptx-wfp-phase) (:instance fn-ptx-acc-max-state-pos)
                 (:instance fn-ptx-okp-mk (ph (fn-rtc-get 0 m)) (k (nfix (fn-rtc-get 1 m))) (cur (list (fn-ptx-cur-fid (fn-ptx-cur m)) (fn-ptx-cur-finc (fn-ptx-cur m)) (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-len (fn-ptx-cur m)) (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q)) (fn-ptx-cur-txid (fn-ptx-cur m)) (fn-ptx-cur-len (fn-ptx-cur m)))) (q (fn-rtc-get 3 m)) (kd (fn-rtc-get 4 m)) (ext 0) (nxt 0) (b1 (list h1 g1 0 0)) (b3 (list h3 g3 off2 *fn-ptx-sufhead-max*)) (hs (fn-rtc-get 9 m)) (committed nil) (evd (fn-rtc-get 11 m)) (geo (fn-rtc-get 12 m)) (acc a)) )
           :do-not-induct t)))
(defthm fn-ptx-cur-of-list
  (and (equal (fn-ptx-cur-fid (list a b c d e f g)) a) (equal (fn-ptx-cur-finc (list a b c d e f g)) b)
       (equal (fn-ptx-cur-bp (list a b c d e f g)) (nfix c)) (equal (fn-ptx-cur-len (list a b c d e f g)) (nfix d))
       (equal (fn-ptx-cur-hoff (list a b c d e f g)) (nfix e)) (equal (fn-ptx-cur-txid (list a b c d e f g)) (nfix f))
       (equal (fn-ptx-cur-ioff (list a b c d e f g)) (nfix g)))
  :hints (("Goal" :in-theory (enable fn-ptx-cur-fid fn-ptx-cur-finc fn-ptx-cur-bp fn-ptx-cur-len fn-ptx-cur-hoff fn-ptx-cur-txid fn-ptx-cur-ioff fn-rtc-get))))
(defthm fn-ptx-ok-read-hashing
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :reading) (atom h1) (atom g1) (atom h3) (atom g3) (natp off2) (<= 9 off2) (atom e) (<= (if (consp ins) (nfix ioff0) (fn-ptx-cur-len (fn-ptx-cur m))) (fn-ptx-cur-len (fn-ptx-cur m))) (<= (+ 32 (+ (len pre) (fn-ptx-cur-len (fn-ptx-cur m)) (len ins) (- (+ off2 (len st2)) (- *fn-ptx-sufhead-max* (min (len sh) *fn-ptx-sufhead-max*))))) (fn-ptx-fmax m)))
           (fn-ptx-okp (fn-ptx-chg (fn-ptx-chg (fn-ptx-chg m :committed nil) :b1 (list h1 g1 0 0) :b3 (list h3 g3 off *fn-ptx-sufhead-max*)) :ph :hashing :k 0 :cur (list (fn-ptx-cur-fid (fn-ptx-cur m)) (fn-ptx-cur-finc (fn-ptx-cur m)) (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-len (fn-ptx-cur m)) e (fn-ptx-cur-txid (fn-ptx-cur m)) (if (consp ins) (nfix ioff0) (fn-ptx-cur-len (fn-ptx-cur m)))) :b1 (list h1 g1 (len (append (fn-ptx-frame-header (+ (len pre) (fn-ptx-cur-len (fn-ptx-cur m)) (len ins) (- (+ off2 (len st2)) (- *fn-ptx-sufhead-max* (min (len sh) *fn-ptx-sufhead-max*))))) (fn-ptx-kd-last (fn-ptx-kd m)) pre)) (len ins)) :b3 (list h3 g3 (+ off2 (len st2)) (- *fn-ptx-sufhead-max* (min (len sh) *fn-ptx-sufhead-max*))) :hs (list 0 nil) :acc nil)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) (union-theories (theory 'fn-ptx-mt7) '((:type-prescription len) fn-ptx-okp-mk-norm2 fn-ptx-buf-of-list fn-ptx-nfix-buf (:type-prescription fn-ptx-buf-h) (:type-prescription fn-ptx-buf-g) (:type-prescription fn-ptx-buf-len) (:type-prescription fn-ptx-buf-x) fn-ptx-nfix-cur natp (:type-prescription fn-ptx-cur-bp) (:type-prescription fn-ptx-cur-len) (:type-prescription fn-ptx-cur-hoff) (:type-prescription fn-ptx-cur-txid) (:type-prescription fn-ptx-cur-ioff) fn-ptx-cur-fid fn-ptx-cur-finc fn-ptx-read-w-natp fn-ptx-frame-header-len fn-ptx-len-append fn-ptx-spans-len-g fn-ptx-fmax fn-ptx-cur-of-list min (:executable-counterpart fn-rtc-get) (:executable-counterpart floor) (:executable-counterpart mod) fn-ptx-bits-zero)))
           :use ((:instance fn-ptx-okp-elim) (:instance fn-ptx-wfp-sizes) (:instance fn-ptx-wfp-phase) (:instance fn-ptx-acc-max-state-pos)
                 (:instance fn-ptx-okp-mk (ph :hashing) (k 0) (cur (list (fn-ptx-cur-fid (fn-ptx-cur m)) (fn-ptx-cur-finc (fn-ptx-cur m)) (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-len (fn-ptx-cur m)) e (fn-ptx-cur-txid (fn-ptx-cur m)) (if (consp ins) (nfix ioff0) (fn-ptx-cur-len (fn-ptx-cur m))))) (q (fn-rtc-get 3 m)) (kd (fn-rtc-get 4 m)) (ext 0) (nxt 0) (b1 (list h1 g1 (len (append (fn-ptx-frame-header (+ (len pre) (fn-ptx-cur-len (fn-ptx-cur m)) (len ins) (- (+ off2 (len st2)) (- *fn-ptx-sufhead-max* (min (len sh) *fn-ptx-sufhead-max*))))) (fn-ptx-kd-last (fn-ptx-kd m)) pre)) (len ins))) (b3 (list h3 g3 (+ off2 (len st2)) (- *fn-ptx-sufhead-max* (min (len sh) *fn-ptx-sufhead-max*)))) (hs (list 0 nil)) (committed nil) (evd (fn-rtc-get 11 m)) (geo (fn-rtc-get 12 m)) (acc nil)) )
           :do-not-induct t)))
(defthm fn-ptx-ok-end-mr
  (implies (and (fn-ptx-okp m) (not (member-eq (fn-ptx-ph m) '(:closed :fenced))))
           (fn-ptx-okp (mv-nth 0 (fn-ptx-end (fn-ptx-chg (fn-ptx-chg m :committed nil) :b1 nil :b3 nil) :refused (fn-ptx-kd m) (fn-ptx-ext m) nil nil id inc st))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) (union-theories (theory 'fn-ptx-mt7) '((:type-prescription len))))
           :use ((:instance fn-ptx-okp-elim) (:instance fn-ptx-wfp-sizes) (:instance fn-ptx-wfp-phase)
                 (:instance fn-ptx-end-ok (m (fn-ptx-chg (fn-ptx-chg m :committed nil) :b1 nil :b3 nil)) (o :refused) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m)) (fenced nil) (committed nil)))
           :do-not-induct t)))
(defthm fn-ptx-read-off-ge9
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :reading))
           (<= 9 (if (consp (fn-ptx-b1 m)) (fn-ptx-buf-len (fn-ptx-b3 m)) 9)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-ptx-okp-elim)) :in-theory (union-theories (theory 'minimal-theory) (theory 'fn-ptx-mt7)))))
(defthm fn-ptx-free-natp-or-nil
  (or (null (fn-ptx-free i skip id inc st)) (natp (fn-ptx-free i skip id inc st)))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-ptx-free i skip id inc st)
           :in-theory (e/d ((:induction fn-ptx-free)) (fn-rtc-st-v-owner fn-rtc-st-config fn-rtc-nbufs))
           :expand ((fn-ptx-free i skip id inc st)))))
(defthm fn-ptx-read-atoms
  (and (atom (if (not (consp (fn-ptx-b1 m))) (fn-ptx-free 0 nil id inc st) (fn-ptx-buf-h (fn-ptx-b1 m)))) (atom (if (not (consp (fn-ptx-b1 m))) (+ 1 (fn-ptx-gen (if (not (consp (fn-ptx-b1 m))) (fn-ptx-free 0 nil id inc st) (fn-ptx-buf-h (fn-ptx-b1 m))) id inc st)) (fn-ptx-buf-g (fn-ptx-b1 m)))) (atom (if (not (consp (fn-ptx-b1 m))) (fn-ptx-free 0 (if (not (consp (fn-ptx-b1 m))) (fn-ptx-free 0 nil id inc st) (fn-ptx-buf-h (fn-ptx-b1 m))) id inc st) (fn-ptx-buf-h (fn-ptx-b3 m)))) (atom (if (not (consp (fn-ptx-b1 m))) (+ 1 (fn-ptx-gen (if (not (consp (fn-ptx-b1 m))) (fn-ptx-free 0 (if (not (consp (fn-ptx-b1 m))) (fn-ptx-free 0 nil id inc st) (fn-ptx-buf-h (fn-ptx-b1 m))) id inc st) (fn-ptx-buf-h (fn-ptx-b3 m))) id inc st)) (fn-ptx-buf-g (fn-ptx-b3 m)))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn-ptx-free-natp-or-nil (:type-prescription fn-ptx-buf-h) (:type-prescription fn-ptx-buf-g)
                      (:type-prescription fn-ptx-buf-len) (:type-prescription fn-ptx-gen))))))
(defun fn-ptx-rd-end0 (m id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (mv-let (m2 r2 c2) (fn-ptx-end (fn-ptx-chg m :committed nil) :refused (fn-ptx-kd m) (fn-ptx-ext m) nil nil id inc fn-rtc-st)
    (declare (ignore r2 c2))
    m2))
(defun fn-ptx-rd-endr (m id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (mv-let (m2 r2 c2) (fn-ptx-end (fn-ptx-chg (fn-ptx-chg m :committed nil) :b1 nil :b3 nil) :refused (fn-ptx-kd m) (fn-ptx-ext m) nil nil id inc fn-rtc-st)
    (declare (ignore r2 c2))
    m2))
(defun fn-ptx-rd-cont (m q h1 g1 h3 g3 off off2 a)
  (let ((cur (fn-ptx-cur m)))
    (fn-ptx-chg (fn-ptx-chg (fn-ptx-chg m :committed nil) :b1 (list h1 g1 0 0) :b3 (list h3 g3 off *fn-ptx-sufhead-max*))
                :cur (list (fn-ptx-cur-fid cur) (fn-ptx-cur-finc cur) (fn-ptx-cur-bp cur) (fn-ptx-cur-len cur)
                           (+ (fn-ptx-cur-hoff cur) (fn-ptx-read-w q)) (fn-ptx-cur-txid cur) (fn-ptx-cur-len cur))
                :b3 (list h3 g3 off2 *fn-ptx-sufhead-max*) :acc a)))
(defun fn-ptx-rd-hashing (m h1 g1 h3 g3 off off2 e ioff pre ins sh st)
  (let* ((cur (fn-ptx-cur m)) (kd (fn-ptx-kd m)) (len (fn-ptx-cur-len cur))
         (start (- *fn-ptx-sufhead-max* (min (len sh) *fn-ptx-sufhead-max*)))
         (end (+ off2 (len st)))
         (rlen (+ (len pre) len (len ins) (- end start)))
         (b1 (append (fn-ptx-frame-header rlen) (fn-ptx-kd-last kd) pre))
         (m1 (fn-ptx-chg (fn-ptx-chg m :committed nil) :b1 (list h1 g1 0 0) :b3 (list h3 g3 off *fn-ptx-sufhead-max*))))
    (fn-ptx-chg m1 :ph :hashing :k 0
                :cur (list (fn-ptx-cur-fid cur) (fn-ptx-cur-finc cur) (fn-ptx-cur-bp cur) len e (fn-ptx-cur-txid cur) ioff)
                :b1 (list h1 g1 (len b1) (len ins)) :b3 (list h3 g3 end start) :hs (list 0 nil) :acc nil)))

(defthm fn-ptx-read-1
  (equal (mv-nth 0 (fn-ptx-read m q id inc stx))
         (let* ((cur (fn-ptx-cur m)) (kd (fn-ptx-kd m)) (bp (fn-ptx-cur-bp cur)) (len (fn-ptx-cur-len cur)) (pos (fn-ptx-cur-hoff cur)) (lim (min len (fn-ptx-hmax m))) (w (fn-ptx-read-w q)) (fresh (not (consp (fn-ptx-b1 m)))) (h1 (if fresh (fn-ptx-free 0 nil id inc stx) (fn-ptx-buf-h (fn-ptx-b1 m)))) (h3 (if fresh (fn-ptx-free 0 h1 id inc stx) (fn-ptx-buf-h (fn-ptx-b3 m)))) (g1 (if fresh (+ 1 (fn-ptx-gen h1 id inc stx)) (fn-ptx-buf-g (fn-ptx-b1 m)))) (g3 (if fresh (+ 1 (fn-ptx-gen h3 id inc stx)) (fn-ptx-buf-g (fn-ptx-b3 m)))) (off (if fresh *fn-ptx-sufhead-max* (fn-ptx-buf-len (fn-ptx-b3 m)))) (e (fn-ptx-head-end bp pos (min lim (+ pos w 3)) id inc stx))) (if (not (and h1 h3)) (fn-ptx-rd-end0 m id inc stx) (let* ((nfeed (if e (- e pos) (if (< (+ pos w 3) lim) w 0)))) (mv-let (a sp) (fn-ptx-acc-feed (fn-ptx-acc m) (fn-ptx-range bp pos nfeed id inc stx)) (let ((off2 (+ off (len sp)))) (cond ((not (<= (+ off2 32) (fn-ptx-cap h3 id inc stx))) (fn-ptx-rd-endr m id inc stx)) (e (mv-let (ok pre ins ioff sh st) (fn-ptx-acc-end a (- len e)) (let* ((ioff (if (consp ins) (nfix ioff) len)) (start (- *fn-ptx-sufhead-max* (min (len sh) *fn-ptx-sufhead-max*))) (end (+ off2 (len st))) (rlen (+ (len pre) len (len ins) (- end start))) (b1 (append (fn-ptx-frame-header rlen) (fn-ptx-kd-last kd) pre))) (if (not (and ok (<= ioff len) (<= (+ 32 rlen) (fn-ptx-fmax m)) (<= (+ (len b1) (len ins)) (fn-ptx-cap h1 id inc stx)) (<= (+ end 32) (fn-ptx-cap h3 id inc stx)))) (fn-ptx-rd-endr m id inc stx) (fn-ptx-rd-hashing m h1 g1 h3 g3 off off2 e ioff pre ins sh st))))) ((< (+ pos w 3) lim) (fn-ptx-rd-cont m q h1 g1 h3 g3 off off2 a)) (t (fn-ptx-rd-endr m id inc stx)))))))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn-ptx-read-0 fn-ptx-rd-end0 fn-ptx-rd-endr fn-ptx-rd-cont fn-ptx-rd-hashing (:executable-counterpart mv-nth) mv-nth))
           :do-not-induct t)))
(defthm fn-ptx-ok-rd-cont
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :reading) (atom h1) (atom g1) (atom h3) (atom g3) (natp off2) (<= 9 off2) (<= (fn-rtc-size a) (fn-ptx-acc-max-state)))
           (fn-ptx-okp (fn-ptx-rd-cont m q h1 g1 h3 g3 off off2 a)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) (union-theories (theory 'fn-ptx-mt7) '((:type-prescription len) fn-ptx-okp-mk-norm2 fn-ptx-buf-of-list fn-ptx-nfix-buf (:type-prescription fn-ptx-buf-h) (:type-prescription fn-ptx-buf-g) (:type-prescription fn-ptx-buf-len) (:type-prescription fn-ptx-buf-x) fn-ptx-nfix-cur natp (:type-prescription fn-ptx-cur-bp) (:type-prescription fn-ptx-cur-len) (:type-prescription fn-ptx-cur-hoff) (:type-prescription fn-ptx-cur-txid) (:type-prescription fn-ptx-cur-ioff) fn-ptx-rd-cont fn-ptx-cur-fid fn-ptx-cur-finc fn-ptx-read-w-natp)))
           :use ((:instance fn-ptx-okp-elim) (:instance fn-ptx-wfp-sizes) (:instance fn-ptx-wfp-phase) (:instance fn-ptx-acc-max-state-pos)
                 (:instance fn-ptx-okp-mk (ph (fn-rtc-get 0 m)) (k (nfix (fn-rtc-get 1 m))) (cur (list (fn-ptx-cur-fid (fn-ptx-cur m)) (fn-ptx-cur-finc (fn-ptx-cur m)) (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-len (fn-ptx-cur m)) (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q)) (fn-ptx-cur-txid (fn-ptx-cur m)) (fn-ptx-cur-len (fn-ptx-cur m)))) (q (fn-rtc-get 3 m)) (kd (fn-rtc-get 4 m)) (ext 0) (nxt 0) (b1 (list h1 g1 0 0)) (b3 (list h3 g3 off2 *fn-ptx-sufhead-max*)) (hs (fn-rtc-get 9 m)) (committed nil) (evd (fn-rtc-get 11 m)) (geo (fn-rtc-get 12 m)) (acc a)) )
           :do-not-induct t)))
(defthm fn-ptx-ok-rd-hashing
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :reading) (atom h1) (atom g1) (atom h3) (atom g3) (natp off2) (<= 9 off2) (atom e) (atom ioff) (<= ioff (fn-ptx-cur-len (fn-ptx-cur m))) (<= (+ 32 (+ (len pre) (fn-ptx-cur-len (fn-ptx-cur m)) (len ins) (- (+ off2 (len st)) (- *fn-ptx-sufhead-max* (min (len sh) *fn-ptx-sufhead-max*))))) (fn-ptx-fmax m)))
           (fn-ptx-okp (fn-ptx-rd-hashing m h1 g1 h3 g3 off off2 e ioff pre ins sh st)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) (union-theories (theory 'fn-ptx-mt7) '((:type-prescription len) fn-ptx-okp-mk-norm2 fn-ptx-buf-of-list fn-ptx-nfix-buf (:type-prescription fn-ptx-buf-h) (:type-prescription fn-ptx-buf-g) (:type-prescription fn-ptx-buf-len) (:type-prescription fn-ptx-buf-x) fn-ptx-nfix-cur natp (:type-prescription fn-ptx-cur-bp) (:type-prescription fn-ptx-cur-len) (:type-prescription fn-ptx-cur-hoff) (:type-prescription fn-ptx-cur-txid) (:type-prescription fn-ptx-cur-ioff) fn-ptx-rd-hashing fn-ptx-cur-fid fn-ptx-cur-finc fn-ptx-read-w-natp fn-ptx-frame-header-len fn-ptx-len-append fn-ptx-spans-len-g fn-ptx-fmax fn-ptx-cur-of-list min (:executable-counterpart fn-rtc-get) (:executable-counterpart floor) (:executable-counterpart mod) fn-ptx-bits-zero)))
           :use ((:instance fn-ptx-okp-elim) (:instance fn-ptx-wfp-sizes) (:instance fn-ptx-wfp-phase) (:instance fn-ptx-acc-max-state-pos)
                 (:instance fn-ptx-okp-mk (ph :hashing) (k 0) (cur (list (fn-ptx-cur-fid (fn-ptx-cur m)) (fn-ptx-cur-finc (fn-ptx-cur m)) (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-len (fn-ptx-cur m)) e (fn-ptx-cur-txid (fn-ptx-cur m)) ioff)) (q (fn-rtc-get 3 m)) (kd (fn-rtc-get 4 m)) (ext 0) (nxt 0) (b1 (list h1 g1 (len (append (fn-ptx-frame-header (+ (len pre) (fn-ptx-cur-len (fn-ptx-cur m)) (len ins) (- (+ off2 (len st)) (- *fn-ptx-sufhead-max* (min (len sh) *fn-ptx-sufhead-max*))))) (fn-ptx-kd-last (fn-ptx-kd m)) pre)) (len ins))) (b3 (list h3 g3 (+ off2 (len st)) (- *fn-ptx-sufhead-max* (min (len sh) *fn-ptx-sufhead-max*)))) (hs (list 0 nil)) (committed nil) (evd (fn-rtc-get 11 m)) (geo (fn-rtc-get 12 m)) (acc nil)) )
           :do-not-induct t)))
(defthm fn-ptx-ok-rd-end0
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :reading))
           (fn-ptx-okp (fn-ptx-rd-end0 m id inc st)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-rd-end0 (:executable-counterpart equal) (:executable-counterpart member-equal) member-equal))
           :use ((:instance fn-ptx-ok-end-m0 (o :refused) (fenced nil))))))
(defthm fn-ptx-ok-rd-endr
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :reading))
           (fn-ptx-okp (fn-ptx-rd-endr m id inc st)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-rd-endr (:executable-counterpart equal) (:executable-counterpart member-equal) member-equal))
           :use ((:instance fn-ptx-ok-end-mr)))))
(defthm fn-ptx-head-end-not-consp
  (implies (fn-ptx-head-end h i lim id inc st) (not (consp (fn-ptx-head-end h i lim id inc st))))
  :hints (("Goal" :use fn-ptx-head-end-int :in-theory (disable fn-ptx-head-end-int fn-ptx-head-end))))
(defthm fn-ptx-read-ok
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :reading))
           (fn-ptx-okp (mv-nth 0 (fn-ptx-read m q id inc st))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn-ptx-read-1 (:executable-counterpart equal) (:executable-counterpart member-equal) member-equal (:type-prescription len) (:type-prescription nfix)
                      (:type-prescription nfix) (:type-prescription fn-ptx-cur-len) (:type-prescription fn-ptx-cur-bp) (:type-prescription fn-ptx-cur-hoff) (:type-prescription fn-ptx-cur-txid) natp fn-ptx-head-end-int fn-ptx-head-end-not-consp fn-ptx-free-natp-or-nil (:type-prescription fn-ptx-buf-h) (:type-prescription fn-ptx-buf-g) (:type-prescription fn-ptx-buf-len)
                      fn-ptx-read-w-natp))
           :do-not-induct t
           :use ((:instance fn-ptx-ok-rd-cont (h1 (if (not (consp (fn-ptx-b1 m))) (fn-ptx-free 0 nil id inc st) (fn-ptx-buf-h (fn-ptx-b1 m)))) (g1 (if (not (consp (fn-ptx-b1 m))) (+ 1 (fn-ptx-gen (if (not (consp (fn-ptx-b1 m))) (fn-ptx-free 0 nil id inc st) (fn-ptx-buf-h (fn-ptx-b1 m))) id inc st)) (fn-ptx-buf-g (fn-ptx-b1 m)))) (h3 (if (not (consp (fn-ptx-b1 m))) (fn-ptx-free 0 (if (not (consp (fn-ptx-b1 m))) (fn-ptx-free 0 nil id inc st) (fn-ptx-buf-h (fn-ptx-b1 m))) id inc st) (fn-ptx-buf-h (fn-ptx-b3 m)))) (g3 (if (not (consp (fn-ptx-b1 m))) (+ 1 (fn-ptx-gen (if (not (consp (fn-ptx-b1 m))) (fn-ptx-free 0 (if (not (consp (fn-ptx-b1 m))) (fn-ptx-free 0 nil id inc st) (fn-ptx-buf-h (fn-ptx-b1 m))) id inc st) (fn-ptx-buf-h (fn-ptx-b3 m))) id inc st)) (fn-ptx-buf-g (fn-ptx-b3 m)))) (off (if (not (consp (fn-ptx-b1 m))) *fn-ptx-sufhead-max* (fn-ptx-buf-len (fn-ptx-b3 m)))) (off2 (+ (if (not (consp (fn-ptx-b1 m))) *fn-ptx-sufhead-max* (fn-ptx-buf-len (fn-ptx-b3 m))) (len (mv-nth 1 (fn-ptx-acc-feed (fn-ptx-acc m) (fn-ptx-range (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)) (if (fn-ptx-head-end (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)) (min (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m)) (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3)) id inc st) (- (fn-ptx-head-end (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)) (min (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m)) (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3)) id inc st) (fn-ptx-cur-hoff (fn-ptx-cur m))) (if (< (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3) (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m))) (fn-ptx-read-w q) 0)) id inc st)))))) (a (mv-nth 0 (fn-ptx-acc-feed (fn-ptx-acc m) (fn-ptx-range (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)) (if (fn-ptx-head-end (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)) (min (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m)) (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3)) id inc st) (- (fn-ptx-head-end (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)) (min (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m)) (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3)) id inc st) (fn-ptx-cur-hoff (fn-ptx-cur m))) (if (< (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3) (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m))) (fn-ptx-read-w q) 0)) id inc st)))) )
                 (:instance fn-ptx-ok-rd-hashing (h1 (if (not (consp (fn-ptx-b1 m))) (fn-ptx-free 0 nil id inc st) (fn-ptx-buf-h (fn-ptx-b1 m)))) (g1 (if (not (consp (fn-ptx-b1 m))) (+ 1 (fn-ptx-gen (if (not (consp (fn-ptx-b1 m))) (fn-ptx-free 0 nil id inc st) (fn-ptx-buf-h (fn-ptx-b1 m))) id inc st)) (fn-ptx-buf-g (fn-ptx-b1 m)))) (h3 (if (not (consp (fn-ptx-b1 m))) (fn-ptx-free 0 (if (not (consp (fn-ptx-b1 m))) (fn-ptx-free 0 nil id inc st) (fn-ptx-buf-h (fn-ptx-b1 m))) id inc st) (fn-ptx-buf-h (fn-ptx-b3 m)))) (g3 (if (not (consp (fn-ptx-b1 m))) (+ 1 (fn-ptx-gen (if (not (consp (fn-ptx-b1 m))) (fn-ptx-free 0 (if (not (consp (fn-ptx-b1 m))) (fn-ptx-free 0 nil id inc st) (fn-ptx-buf-h (fn-ptx-b1 m))) id inc st) (fn-ptx-buf-h (fn-ptx-b3 m))) id inc st)) (fn-ptx-buf-g (fn-ptx-b3 m)))) (off (if (not (consp (fn-ptx-b1 m))) *fn-ptx-sufhead-max* (fn-ptx-buf-len (fn-ptx-b3 m)))) (off2 (+ (if (not (consp (fn-ptx-b1 m))) *fn-ptx-sufhead-max* (fn-ptx-buf-len (fn-ptx-b3 m))) (len (mv-nth 1 (fn-ptx-acc-feed (fn-ptx-acc m) (fn-ptx-range (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)) (if (fn-ptx-head-end (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)) (min (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m)) (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3)) id inc st) (- (fn-ptx-head-end (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)) (min (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m)) (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3)) id inc st) (fn-ptx-cur-hoff (fn-ptx-cur m))) (if (< (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3) (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m))) (fn-ptx-read-w q) 0)) id inc st)))))) (e (fn-ptx-head-end (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)) (min (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m)) (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3)) id inc st)) (pre (mv-nth 1 (fn-ptx-acc-end (mv-nth 0 (fn-ptx-acc-feed (fn-ptx-acc m) (fn-ptx-range (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)) (if (fn-ptx-head-end (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)) (min (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m)) (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3)) id inc st) (- (fn-ptx-head-end (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)) (min (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m)) (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3)) id inc st) (fn-ptx-cur-hoff (fn-ptx-cur m))) (if (< (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3) (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m))) (fn-ptx-read-w q) 0)) id inc st))) (- (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-head-end (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)) (min (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m)) (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3)) id inc st))))) (ins (mv-nth 2 (fn-ptx-acc-end (mv-nth 0 (fn-ptx-acc-feed (fn-ptx-acc m) (fn-ptx-range (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)) (if (fn-ptx-head-end (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)) (min (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m)) (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3)) id inc st) (- (fn-ptx-head-end (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)) (min (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m)) (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3)) id inc st) (fn-ptx-cur-hoff (fn-ptx-cur m))) (if (< (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3) (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m))) (fn-ptx-read-w q) 0)) id inc st))) (- (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-head-end (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)) (min (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m)) (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3)) id inc st))))) (sh (mv-nth 4 (fn-ptx-acc-end (mv-nth 0 (fn-ptx-acc-feed (fn-ptx-acc m) (fn-ptx-range (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)) (if (fn-ptx-head-end (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)) (min (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m)) (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3)) id inc st) (- (fn-ptx-head-end (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)) (min (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m)) (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3)) id inc st) (fn-ptx-cur-hoff (fn-ptx-cur m))) (if (< (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3) (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m))) (fn-ptx-read-w q) 0)) id inc st))) (- (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-head-end (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)) (min (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m)) (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3)) id inc st))))) (ioff (if (consp (mv-nth 2 (fn-ptx-acc-end (mv-nth 0 (fn-ptx-acc-feed (fn-ptx-acc m) (fn-ptx-range (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)) (if (fn-ptx-head-end (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)) (min (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m)) (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3)) id inc st) (- (fn-ptx-head-end (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)) (min (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m)) (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3)) id inc st) (fn-ptx-cur-hoff (fn-ptx-cur m))) (if (< (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3) (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m))) (fn-ptx-read-w q) 0)) id inc st))) (- (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-head-end (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)) (min (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m)) (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3)) id inc st))))) (nfix (mv-nth 3 (fn-ptx-acc-end (mv-nth 0 (fn-ptx-acc-feed (fn-ptx-acc m) (fn-ptx-range (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)) (if (fn-ptx-head-end (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)) (min (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m)) (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3)) id inc st) (- (fn-ptx-head-end (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)) (min (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m)) (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3)) id inc st) (fn-ptx-cur-hoff (fn-ptx-cur m))) (if (< (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3) (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m))) (fn-ptx-read-w q) 0)) id inc st))) (- (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-head-end (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)) (min (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m)) (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3)) id inc st))))) (fn-ptx-cur-len (fn-ptx-cur m)))) (st (mv-nth 5 (fn-ptx-acc-end (mv-nth 0 (fn-ptx-acc-feed (fn-ptx-acc m) (fn-ptx-range (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)) (if (fn-ptx-head-end (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)) (min (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m)) (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3)) id inc st) (- (fn-ptx-head-end (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)) (min (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m)) (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3)) id inc st) (fn-ptx-cur-hoff (fn-ptx-cur m))) (if (< (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3) (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m))) (fn-ptx-read-w q) 0)) id inc st))) (- (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-head-end (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)) (min (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m)) (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3)) id inc st))))))
                 (:instance fn-ptx-ok-rd-end0)
                 (:instance fn-ptx-ok-rd-endr)
                 (:instance fn-ptx-read-atoms)
                 (:instance fn-ptx-read-off-ge9)
                 (:instance fn-ptx-acc-feed-bounded (a (fn-ptx-acc m)) (octets (fn-ptx-range (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)) (if (fn-ptx-head-end (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)) (min (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m)) (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3)) id inc st) (- (fn-ptx-head-end (fn-ptx-cur-bp (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)) (min (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m)) (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3)) id inc st) (fn-ptx-cur-hoff (fn-ptx-cur m))) (if (< (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3) (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m))) (fn-ptx-read-w q) 0)) id inc st)))))))
(defthm fn-ptx-step1-0
  (equal (mv-nth 0 (fn-ptx-step1 m ev stx q))
         (let* ((id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev)) (kind (fn-rtc-get 0 ev)) (out (fn-rtc-get 1 ev)) (tag (fn-rtc-get 0 out)) (n (fn-rtc-get 1 out)) (ph (fn-ptx-ph m)) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m)) (nxt (fn-ptx-nxt m)) (m0 (fn-ptx-chg m :committed nil))) (cond ((eq kind :opened) (if (and (eq ph :closed) (eq tag :done)) (let* ((d (fn-rtc-ev-opened-data ev)) (m1 (fn-ptx-opened (fn-rtc-get 0 d) (nfix (fn-rtc-get 1 d)) (fn-rtc-get 2 d)))) (if (and (fn-ptx-wfp m1) (<= (fn-ptx-fmax m1) *fn-frame-max-payload*) (equal (len (fn-ptx-kd-last (fn-ptx-kd m1))) 32)) m1 m0)) m0)) ((eq kind :handed) (let* ((hd (fn-rtc-get 6 ev)) (p (list (fn-ptx-atom (fn-rtc-get 4 ev)) (fn-ptx-atom (fn-rtc-get 5 ev)) (fn-rtc-h-buf hd) (fn-rtc-h-len hd)))) (cond ((member-eq ph '(:fenced :closed)) m0) ((eq ph :idle) (mv-nth 0 (fn-ptx-start p nil kd ext (fn-ptx-geo m) nil))) ((< (len (fn-ptx-q m)) *fn-ptx-k*) (fn-ptx-chg m0 :q (append (true-list-fix (fn-ptx-q m)) (list p)))) (t m0)))) ((and (eq ph :reading) (eq kind :timer)) (mv-nth 0 (fn-ptx-read m q id inc stx))) ((and (eq ph :hashing) (eq kind :timer)) (mv-nth 0 (fn-ptx-hash m q id inc stx))) ((and (eq ph :extending) (eq kind :extend)) (if (eq tag :done) (fn-ptx-chg m0 :ph :extsyncing :evd (fn-ptx-evd+ m ev)) (mv-nth 0 (fn-ptx-end m0 :refused kd ext t nil id inc stx)))) ((and (eq ph :extsyncing) (eq kind :fsync)) (if (eq tag :done) (let ((m1 (fn-ptx-chg m0 :ph :payload-writing :k 0 :evd (fn-ptx-evd+ m ev)))) m1) (mv-nth 0 (fn-ptx-end m0 :refused kd ext t nil id inc stx)))) ((and (eq ph :payload-writing) (eq kind :pwrite)) (let ((k (fn-ptx-k m))) (cond ((not (and (eq tag :done) (equal n (fn-ptx-span-n k m)))) (mv-nth 0 (fn-ptx-end m0 :uncertain kd ext t nil id inc stx))) (t (let ((m1 (fn-ptx-chg m0 :ph (if (< (+ k 2) (fn-ptx-nspans m)) :payload-writing :log-writing) :k (+ k 1) :evd (fn-ptx-evd+ m ev)))) m1))))) ((and (eq ph :log-writing) (eq kind :pwrite)) (if (and (eq tag :done) (equal n (fn-ptx-span-n (fn-ptx-k m) m))) (fn-ptx-chg m0 :ph :committing :evd (fn-ptx-evd+ m ev)) (mv-nth 0 (fn-ptx-end m0 :uncertain kd ext t nil id inc stx)))) ((and (eq ph :committing) (eq kind :fsync)) (if (eq tag :done) (mv-nth 0 (fn-ptx-end m0 :posted (fn-ptx-kd-commit kd (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-elen m)) nxt nil t id inc stx)) (mv-nth 0 (fn-ptx-end m0 :uncertain kd ext t nil id inc stx)))) ((eq kind :hand) m0) (t m0))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-step1 (:executable-counterpart mv-nth) mv-nth)) :do-not-induct t)))
(defthm fn-ptx-step1-ok
  (implies (fn-ptx-okp m)
           (fn-ptx-okp (mv-nth 0 (fn-ptx-step1 m ev st q))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn-ptx-step1-0 (:executable-counterpart equal) (:executable-counterpart member-equal) member-equal (:executable-counterpart eq)
                      (:executable-counterpart consp)))
           :do-not-induct t
           :use ((:instance fn-ptx-okp-m0)
                 (:instance fn-ptx-opened-ok (kd (fn-rtc-get 0 (fn-rtc-ev-opened-data ev))) (ext (nfix (fn-rtc-get 1 (fn-rtc-ev-opened-data ev)))) (geo (fn-rtc-get 2 (fn-rtc-ev-opened-data ev))))
                 (:instance fn-ptx-ok-handed-idle)
                 (:instance fn-ptx-ok-handed-queue)
                 (:instance fn-ptx-read-ok (id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev)))
                 (:instance fn-ptx-hash-ok (id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev)))
                 (:instance fn-ptx-ok-extend-done)
                 (:instance fn-ptx-ok-end-m0 (o :refused) (fenced t) (id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev)))
                 (:instance fn-ptx-ok-end-m0 (o :uncertain) (fenced t) (id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev)))
                 (:instance fn-ptx-ok-extsync-done)
                 (:instance fn-ptx-ok-pwrite-more)
                 (:instance fn-ptx-ok-pwrite-last)
                 (:instance fn-ptx-ok-logwrite-done)
                 (:instance fn-ptx-ok-end-posted (id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev)))))))
(defthm fn-ptx-step-keeps-ok
  (implies (fn-ptx-okp m) (fn-ptx-okp (mv-nth 0 (fn-ptx-step m ev st q))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-step (:executable-counterpart mv-nth) mv-nth))
           :use ((:instance fn-ptx-step1-ok) (:instance fn-ptx-okp-wfp))
           :do-not-induct t)))

(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm fn-ptx-ceil-natp
    (implies (natp a) (natp (ceiling a 1024)))
    :rule-classes :type-prescription)
  (defthm fn-ptx-ceil-mono
    (implies (and (natp a) (natp b) (<= a b)) (<= (ceiling a 1024) (ceiling b 1024)))
    :rule-classes :linear)
  (defthm fn-ptx-ceil-step
    (implies (and (natp a) (natp b) (<= (+ a 1024) b)) (<= (+ 1 (ceiling a 1024)) (ceiling b 1024)))
    :rule-classes :linear)
  (defthm fn-ptx-ceil-pos
    (implies (and (natp a) (< 0 a)) (<= 1 (ceiling a 1024)))
    :rule-classes :linear)
  (defthm fn-ptx-ceil-plus5
    (implies (natp a) (<= (ceiling (+ a 5) 1024) (+ 1 (ceiling a 1024))))
    :rule-classes :linear))

; -----------------------------------------------------------------------------
; P3 (Sonnet 5): fn-ptx-step-makes-progress.  The measure is len(q) * post-bound + rem;
; every arm lowers it: the end of a transaction is bounded by the start of the next post
; (fn-ptx-end-measure), the reading and hashing arms by the window they advance.
(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm fn-ptx-ar-end
    (implies (and (natp x) (natp y) (natp r) (<= r y))
             (<= (+ (* x y) r) (* (+ 1 x) y)))
    :rule-classes nil)
  (defthm fn-ptx-ceil-nonneg
    (implies (natp a) (and (integerp (ceiling a 1024)) (<= 0 (ceiling a 1024))))
    :rule-classes nil)
  (defthm fn-ptx-prod-nonneg
    (implies (and (natp x) (natp y)) (and (integerp (* x y)) (<= 0 (* x y))))
    :rule-classes nil))
(defthm fn-ptx-ceil-nfix-ge0
  (natp (ceiling (nfix a) 1024))
  :rule-classes :type-prescription
  :hints (("Goal" :use ((:instance fn-ptx-ceil-nonneg (a (nfix a)))))))
(defthm fn-ptx-ceil-plus10-ge0
  (natp (ceiling (+ 10 (nfix a)) 1024))
  :rule-classes :type-prescription
  :hints (("Goal" :use ((:instance fn-ptx-ceil-nonneg (a (+ 10 (nfix a))))))))
(defthm fn-ptx-min-nfix-le
  (<= (nfix (+ (min (nfix c) (nfix g)) 0)) (nfix g))
  :rule-classes :linear)
(defun fn-ptx-post-bound-geo (geo)
  (+ 11 (ceiling (nfix (fn-rtc-get 2 geo)) 1024) (ceiling (+ 10 (nfix (fn-rtc-get 1 geo))) 1024)))
(defthm fn-ptx-post-bound-m
  (equal (fn-ptx-post-bound m) (fn-ptx-post-bound-geo (fn-ptx-geo m)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-post-bound fn-ptx-post-bound-geo fn-ptx-hmax fn-ptx-fmax)) :do-not-induct t)))
(defthm fn-ptx-post-bound-of-mk
  (equal (fn-ptx-post-bound (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc))
         (fn-ptx-post-bound-geo geo))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-post-bound fn-ptx-post-bound-geo fn-ptx-hmax fn-ptx-fmax fn-ptx-accessors-of-mk))
           :do-not-induct t)))
(defthm fn-ptx-post-bound-geo-ge
  (<= 11 (fn-ptx-post-bound-geo geo))
  :rule-classes :linear
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-post-bound-geo fn-ptx-ceil-nfix-ge0 fn-ptx-ceil-plus10-ge0 natp (:type-prescription nfix) (:type-prescription fn-rtc-get)))
)))
(defthm fn-ptx-post-bound-geo-natp
  (natp (fn-ptx-post-bound-geo geo))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-post-bound-geo fn-ptx-ceil-nfix-ge0 fn-ptx-ceil-plus10-ge0 natp (:type-prescription nfix) (:type-prescription fn-rtc-get)))
)))
(defthm fn-ptx-measure-m
  (equal (fn-ptx-measure m) (+ (* (len (fn-ptx-q m)) (fn-ptx-post-bound-geo (fn-ptx-geo m))) (fn-ptx-rem m)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-measure fn-ptx-post-bound-m)))))
(defthm fn-ptx-measure-mk
  (equal (fn-ptx-measure (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc))
         (+ (* (len q) (fn-ptx-post-bound-geo geo))
            (fn-ptx-rem (fn-ptx-mk ph k cur q kd ext nxt b1 b3 hs committed evd geo acc))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn-ptx-measure fn-ptx-post-bound-of-mk fn-ptx-accessors-of-mk)) :do-not-induct t)))
(defthm fn-ptx-measure-reading
  (equal (fn-ptx-measure (fn-ptx-mk :reading k cur q kd ext nxt b1 b3 hs committed evd geo acc))
         (+ (* (len q) (fn-ptx-post-bound-geo geo))
            (+ (+ 10 (ceiling (+ 10 (nfix (fn-rtc-get 1 geo))) 1024)) 1
               (ceiling (nfix (+ (min (fn-ptx-cur-len cur) (nfix (fn-rtc-get 2 geo))) (- (fn-ptx-cur-hoff cur)))) 1024))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn-ptx-measure fn-ptx-rem fn-ptx-post-bound-geo fn-ptx-post-bound-of-mk fn-ptx-accessors-of-mk
                      fn-ptx-alen fn-ptx-hmax fn-ptx-fmax (:executable-counterpart equal) (:executable-counterpart fn-ptx-rem)))
           :do-not-induct t)))
(defthm fn-ptx-measure-idle
  (equal (fn-ptx-measure (fn-ptx-mk :idle k cur q kd ext nxt b1 b3 hs committed evd geo acc))
         (* (len q) (fn-ptx-post-bound-geo geo)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn-ptx-measure fn-ptx-rem fn-ptx-post-bound-of-mk fn-ptx-accessors-of-mk (:executable-counterpart equal)))
           :do-not-induct t)))
(defthm fn-ptx-measure-fenced
  (equal (fn-ptx-measure (fn-ptx-mk :fenced k cur q kd ext nxt b1 b3 hs committed evd geo acc))
         (* (len q) (fn-ptx-post-bound-geo geo)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn-ptx-measure fn-ptx-rem fn-ptx-post-bound-of-mk fn-ptx-accessors-of-mk (:executable-counterpart equal)))
           :do-not-induct t)))
(defthm fn-ptx-end-0
  (equal (mv-nth 0 (fn-ptx-end m o kd ext fenced committed id inc st))
         (if fenced
             (fn-ptx-mk :fenced 0 nil nil kd ext ext nil nil nil committed nil (fn-ptx-geo m) nil)
           (if (consp (fn-ptx-q m))
               (mv-nth 0 (fn-ptx-start (car (fn-ptx-q m)) (cdr (fn-ptx-q m)) kd ext (fn-ptx-geo m) committed))
             (fn-ptx-mk :idle 0 nil nil kd ext ext nil nil nil committed nil (fn-ptx-geo m) nil))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-end (:executable-counterpart mv-nth) mv-nth)) :do-not-induct t)))
(defthm fn-ptx-start-0
  (equal (mv-nth 0 (fn-ptx-start p q kd ext geo committed))
         (fn-ptx-mk :reading 0
                    (list (fn-ptx-cur-fid p) (fn-ptx-cur-finc p) (fn-ptx-cur-bp p) (fn-ptx-cur-len p) 0 (fn-ptx-kd-txid kd) (fn-ptx-cur-len p))
                    q kd ext ext nil nil nil committed nil geo (fn-ptx-acc-begin (fn-ptx-kd-txid kd))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-start (:executable-counterpart mv-nth) mv-nth)) :do-not-induct t)))
(defthm fn-ptx-start-measure
  (<= (fn-ptx-measure (mv-nth 0 (fn-ptx-start p q kd ext geo committed)))
      (+ (fn-ptx-post-bound-geo geo) (* (len q) (fn-ptx-post-bound-geo geo))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn-ptx-start-0 fn-ptx-measure-reading fn-ptx-accessors-of-mk fn-ptx-cur-of-list fn-ptx-post-bound-geo
                      (:executable-counterpart nfix) natp (:type-prescription nfix) fn-ptx-min-nfix-le
                      fn-ptx-ceil-nfix-ge0 fn-ptx-ceil-plus10-ge0 (:type-prescription nfix) fn-ptx-len-cons2))
           :use ((:instance fn-ptx-ceil-mono (a (nfix (+ (min (nfix (fn-ptx-cur-len p)) (nfix (fn-rtc-get 2 geo))) 0)))
                            (b (nfix (fn-rtc-get 2 geo))))
                 )
           :do-not-induct t)))
(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm fn-ptx-ar-dist1
    (equal (* (+ 1 x) y) (+ y (* x y)))))
(defthm fn-ptx-len-consp (implies (consp q) (equal (len q) (+ 1 (len (cdr q))))))
(defthm fn-ptx-len-atom (implies (not (consp q)) (equal (len q) 0)))
(defthm fn-ptx-times-0 (equal (* 0 x) 0))
(defthm fn-ptx-end-measure
  (<= (fn-ptx-measure (mv-nth 0 (fn-ptx-end m o kd ext fenced committed id inc st)))
      (* (len (fn-ptx-q m)) (fn-ptx-post-bound m)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn-ptx-end-0 fn-ptx-measure-idle fn-ptx-measure-fenced fn-ptx-post-bound-m fn-ptx-len-consp fn-ptx-len-atom fn-ptx-times-0 (:executable-counterpart len) fn-ptx-ar-dist1
                      (:type-prescription len) (:type-prescription fn-ptx-post-bound-geo-natp)
                      (:executable-counterpart consp) natp fn-ptx-start-measure))
           :cases (fenced (consp (fn-ptx-q m)))
           :use ((:instance fn-ptx-prod-nonneg (x (len (fn-ptx-q m))) (y (fn-ptx-post-bound-geo (fn-ptx-geo m))))
                 (:instance fn-ptx-start-measure (p (car (fn-ptx-q m))) (q (cdr (fn-ptx-q m))) (geo (fn-ptx-geo m)) (kd kd) (ext ext) (committed committed)))
           :do-not-induct t)))
(defthm fn-ptx-absorb-adv
  (and (natp (mv-nth 0 (fn-ptx-absorb nw pos st n spans id inc stx)))
       (<= (nfix pos) (mv-nth 0 (fn-ptx-absorb nw pos st n spans id inc stx)))
       (or (zp nw)
           (<= (+ (nfix pos) 1024) (mv-nth 0 (fn-ptx-absorb nw pos st n spans id inc stx)))
           (<= (nfix n) (+ 1024 (mv-nth 0 (fn-ptx-absorb nw pos st n spans id inc stx))))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-ptx-absorb nw pos st n spans id inc stx)
           :in-theory (disable fn-b3-cv-push fn-b3-node fn-ptx-msg-range)
           :expand ((fn-ptx-absorb nw pos st n spans id inc stx)))))
(defthm fn-ptx-rem-extending (implies (equal (fn-ptx-ph m) :extending) (equal (fn-ptx-rem m) 8))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-rem (:executable-counterpart equal))) :do-not-induct t)))
(defthm fn-ptx-rem-extsyncing (implies (equal (fn-ptx-ph m) :extsyncing) (equal (fn-ptx-rem m) 7))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-rem (:executable-counterpart equal))) :do-not-induct t)))
(defthm fn-ptx-rem-log-writing (implies (equal (fn-ptx-ph m) :log-writing) (equal (fn-ptx-rem m) 2))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-rem (:executable-counterpart equal))) :do-not-induct t)))
(defthm fn-ptx-rem-committing (implies (equal (fn-ptx-ph m) :committing) (equal (fn-ptx-rem m) 1))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-rem (:executable-counterpart equal))) :do-not-induct t)))
(defthm fn-ptx-rem-payload (implies (equal (fn-ptx-ph m) :payload-writing) (equal (fn-ptx-rem m) (nfix (- (+ 1 (fn-ptx-nspans m)) (fn-ptx-k m)))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-rem (:executable-counterpart equal))) :do-not-induct t)))
(defthm fn-ptx-rem-hashing (implies (equal (fn-ptx-ph m) :hashing)
                                    (equal (fn-ptx-rem m) (+ 10 (ceiling (nfix (- (fn-ptx-nmsg m) (nfix (fn-rtc-get 0 (fn-ptx-hs m))))) 1024))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-rem (:executable-counterpart equal))) :do-not-induct t)))
(defthm fn-ptx-rem-reading (implies (equal (fn-ptx-ph m) :reading)
                                    (equal (fn-ptx-rem m) (+ 10 (ceiling (+ 10 (nfix (fn-rtc-get 1 (fn-ptx-geo m)))) 1024) 1
                                                             (ceiling (nfix (+ (min (fn-ptx-cur-len (fn-ptx-cur m)) (nfix (fn-rtc-get 2 (fn-ptx-geo m)))) (- (fn-ptx-cur-hoff (fn-ptx-cur m))))) 1024))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-rem fn-ptx-alen fn-ptx-hmax fn-ptx-fmax (:executable-counterpart equal))) :do-not-induct t)))
(defthm fn-ptx-nmsg-natp (natp (fn-ptx-nmsg m)) :rule-classes :type-prescription
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-nmsg fn-ptx-spans-len-natp natp)))))
(defthm fn-ptx-measure-extending
  (equal (fn-ptx-measure (fn-ptx-mk :extending k cur q kd ext nxt b1 b3 hs committed evd geo acc))
         (+ (* (len q) (fn-ptx-post-bound-geo geo)) 8))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn-ptx-measure fn-ptx-rem fn-ptx-post-bound-of-mk fn-ptx-accessors-of-mk (:executable-counterpart equal))) :do-not-induct t)))
(defthm fn-ptx-measure-extsyncing
  (equal (fn-ptx-measure (fn-ptx-mk :extsyncing k cur q kd ext nxt b1 b3 hs committed evd geo acc))
         (+ (* (len q) (fn-ptx-post-bound-geo geo)) 7))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn-ptx-measure fn-ptx-rem fn-ptx-post-bound-of-mk fn-ptx-accessors-of-mk (:executable-counterpart equal))) :do-not-induct t)))
(defthm fn-ptx-measure-log-writing
  (equal (fn-ptx-measure (fn-ptx-mk :log-writing k cur q kd ext nxt b1 b3 hs committed evd geo acc))
         (+ (* (len q) (fn-ptx-post-bound-geo geo)) 2))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn-ptx-measure fn-ptx-rem fn-ptx-post-bound-of-mk fn-ptx-accessors-of-mk (:executable-counterpart equal))) :do-not-induct t)))
(defthm fn-ptx-measure-committing
  (equal (fn-ptx-measure (fn-ptx-mk :committing k cur q kd ext nxt b1 b3 hs committed evd geo acc))
         (+ (* (len q) (fn-ptx-post-bound-geo geo)) 1))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn-ptx-measure fn-ptx-rem fn-ptx-post-bound-of-mk fn-ptx-accessors-of-mk (:executable-counterpart equal))) :do-not-induct t)))
(defthm fn-ptx-measure-payload
  (equal (fn-ptx-measure (fn-ptx-mk :payload-writing k cur q kd ext nxt b1 b3 hs committed evd geo acc))
         (+ (* (len q) (fn-ptx-post-bound-geo geo))
            (nfix (- (+ 1 (len (fn-ptx-spans-g b1 b3 cur))) (nfix k)))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn-ptx-measure fn-ptx-rem fn-ptx-post-bound-of-mk fn-ptx-accessors-of-mk fn-ptx-nspans-of-mk (:executable-counterpart equal))) :do-not-induct t)))
(defthm fn-ptx-measure-hashing
  (equal (fn-ptx-measure (fn-ptx-mk :hashing k cur q kd ext nxt b1 b3 hs committed evd geo acc))
         (+ (* (len q) (fn-ptx-post-bound-geo geo))
            (+ 10 (ceiling (nfix (- (fn-ptx-spans-len (fn-ptx-spans-g b1 b3 cur)) (nfix (fn-rtc-get 0 hs)))) 1024))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn-ptx-measure fn-ptx-rem fn-ptx-post-bound-of-mk fn-ptx-accessors-of-mk fn-ptx-nmsg-of-mk (:executable-counterpart equal))) :do-not-induct t)))
(defthm fn-ptx-len-spans-g-m
  (equal (len (fn-ptx-spans-g (fn-ptx-b1 m) (fn-ptx-b3 m) (fn-ptx-cur m))) (fn-ptx-nspans m))
  :hints (("Goal" :use fn-ptx-nspans-is-g :in-theory (union-theories (theory 'minimal-theory) '()))))
(defthm fn-ptx-nfix-natp-rw (implies (natp x) (equal (nfix x) x)))
(defthm fn-ptx-nspans-natp (natp (fn-ptx-nspans m)) :rule-classes :type-prescription)
(defthm fn-ptx-step-0
  (implies (fn-ptx-okp m)
           (equal (mv-nth 0 (fn-ptx-step m ev st q)) (mv-nth 0 (fn-ptx-step1 m ev st q))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-step (:executable-counterpart mv-nth) mv-nth))
           :use ((:instance fn-ptx-okp-wfp)) :do-not-induct t)))
(deftheory fn-ptx-p3u
  (union-theories (theory 'minimal-theory)
    '(fn-ptx-step1-0 fn-ptx-measure-m fn-ptx-accessors-of-mk fn-ptx-post-bound-of-mk fn-ptx-post-bound-m
      fn-ptx-measure-extending fn-ptx-measure-extsyncing fn-ptx-measure-log-writing fn-ptx-measure-committing fn-ptx-measure-payload
      fn-ptx-measure-idle fn-ptx-measure-fenced
      fn-ptx-rem-extending fn-ptx-rem-extsyncing fn-ptx-rem-log-writing fn-ptx-rem-committing fn-ptx-rem-payload
      fn-ptx-len-spans-g-m fn-ptx-nspans-of-mk
      (:executable-counterpart equal) (:executable-counterpart member-equal) member-equal (:executable-counterpart eq) (:executable-counterpart consp)
      (:type-prescription fn-ptx-post-bound-geo-natp) (:type-prescription len) natp (:executable-counterpart nfix) fn-ptx-nfix-natp-rw fn-ptx-nspans-natp)))
(defthm fn-ptx-extending-progress
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :extending) (equal (fn-rtc-get 0 ev) :extend))
           (< (fn-ptx-measure (mv-nth 0 (fn-ptx-step1 m ev st q))) (fn-ptx-measure m)))
  :hints (("Goal" :in-theory (theory 'fn-ptx-p3u)
           :cases ((equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done))
           :use ((:instance fn-ptx-end-measure (m (fn-ptx-chg m :committed nil)) (o :refused) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m))
                            (fenced t) (committed nil) (id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev))))
           :do-not-induct t)))
(defthm fn-ptx-extsyncing-progress
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :extsyncing) (equal (fn-rtc-get 0 ev) :fsync))
           (< (fn-ptx-measure (mv-nth 0 (fn-ptx-step1 m ev st q))) (fn-ptx-measure m)))
  :hints (("Goal" :in-theory (theory 'fn-ptx-p3u)
           :cases ((equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done))
           :use ((:instance fn-ptx-end-measure (m (fn-ptx-chg m :committed nil)) (o :refused) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m))
                            (fenced t) (committed nil) (id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev)))
                 (:instance fn-ptx-spans-g-len (b1 (fn-ptx-b1 m)) (b3 (fn-ptx-b3 m)) (cur (fn-ptx-cur m))))
           :do-not-induct t)))
(defthm fn-ptx-logwrite-progress
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :log-writing) (equal (fn-rtc-get 0 ev) :pwrite))
           (< (fn-ptx-measure (mv-nth 0 (fn-ptx-step1 m ev st q))) (fn-ptx-measure m)))
  :hints (("Goal" :in-theory (theory 'fn-ptx-p3u)
           :cases ((and (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done) (equal (fn-rtc-get 1 (fn-rtc-get 1 ev)) (fn-ptx-span-n (fn-ptx-k m) m))))
           :use ((:instance fn-ptx-end-measure (m (fn-ptx-chg m :committed nil)) (o :uncertain) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m))
                            (fenced t) (committed nil) (id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev))))
           :do-not-induct t)))
(defthm fn-ptx-committing-progress
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :committing) (equal (fn-rtc-get 0 ev) :fsync))
           (< (fn-ptx-measure (mv-nth 0 (fn-ptx-step1 m ev st q))) (fn-ptx-measure m)))
  :hints (("Goal" :in-theory (theory 'fn-ptx-p3u)
           :cases ((equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done))
           :use ((:instance fn-ptx-end-measure (m (fn-ptx-chg m :committed nil)) (o :uncertain) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m))
                            (fenced t) (committed nil) (id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev)))
                 (:instance fn-ptx-end-measure (m (fn-ptx-chg m :committed nil)) (o :posted)
                            (kd (fn-ptx-kd-commit (fn-ptx-kd m) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-elen m))) (ext (fn-ptx-nxt m))
                            (fenced nil) (committed t) (id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev))))
           :do-not-induct t)))
(defthm fn-ptx-nfix-sub (implies (and (integerp a) (integerp b) (<= b a)) (equal (nfix (+ a (- b))) (+ a (- b))))
  :rule-classes nil)
(defthm fn-ptx-payload-progress
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :payload-writing) (equal (fn-rtc-get 0 ev) :pwrite))
           (< (fn-ptx-measure (mv-nth 0 (fn-ptx-step1 m ev st q))) (fn-ptx-measure m)))
  :hints (("Goal" :in-theory (union-theories (theory 'fn-ptx-p3u) '((:type-prescription fn-ptx-k)))
           :cases ((and (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done) (equal (fn-rtc-get 1 (fn-rtc-get 1 ev)) (fn-ptx-span-n (fn-ptx-k m) m))
                        (< (+ (fn-ptx-k m) 2) (fn-ptx-nspans m)))
                   (and (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done) (equal (fn-rtc-get 1 (fn-rtc-get 1 ev)) (fn-ptx-span-n (fn-ptx-k m) m))
                        (not (< (+ (fn-ptx-k m) 2) (fn-ptx-nspans m)))))
           :use ((:instance fn-ptx-end-measure (m (fn-ptx-chg m :committed nil)) (o :uncertain) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m))
                            (fenced t) (committed nil) (id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev)))
                 (:instance fn-ptx-okp-elim)
                 (:instance fn-ptx-nfix-sub (a (+ 1 (fn-ptx-nspans m))) (b (fn-ptx-k m)))
                 (:instance fn-ptx-nfix-sub (a (+ 1 (fn-ptx-nspans m))) (b (+ 1 (fn-ptx-k m)))))
           :do-not-induct t)))
(defthm fn-ptx-spans-len-g-m
  (equal (fn-ptx-spans-len (fn-ptx-spans-g (fn-ptx-b1 m) (fn-ptx-b3 m) (fn-ptx-cur m))) (fn-ptx-spans-len (fn-ptx-spans m)))
  :hints (("Goal" :use fn-ptx-spans-is-g :in-theory (union-theories (theory 'minimal-theory) '()))))
(defthm fn-ptx-minmax-pos
  (implies (natp f) (and (integerp (min 64 (max 1 f))) (< 0 (min 64 (max 1 f)))))
  :rule-classes nil :hints (("Goal" :in-theory (enable min max))))
(defthm fn-ptx-hash-nw-pos
  (let ((nw (min 64 (max 1 (floor (nfix q) 1024))))) (and (integerp nw) (< 0 nw)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-ptx-minmax-pos (f (floor (nfix q) 1024))) (:instance fn-ptx-floor-1024-natp (pos (nfix q)))))))
(defthm fn-ptx-hash-ceil
  (implies (and (natp n) (natp p0) (natp p2) (<= (+ p0 1024) p2) (< (+ p2 1024) n))
           (< (ceiling (nfix (- n p2)) 1024) (ceiling (nfix (- n p0)) 1024)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-ptx-ceil-step (a (- n p2)) (b (- n p0)))
                        (:instance fn-ptx-nfix-sub (a n) (b p2)) (:instance fn-ptx-nfix-sub (a n) (b p0)))
           :in-theory (disable fn-ptx-ceil-step))))
(defthm fn-ptx-absorb-adv2
  (implies (and (integerp nw) (< 0 nw))
           (and (natp (mv-nth 0 (fn-ptx-absorb nw pos st n spans id inc stx)))
                (<= (nfix pos) (mv-nth 0 (fn-ptx-absorb nw pos st n spans id inc stx)))
                (or (<= (+ (nfix pos) 1024) (mv-nth 0 (fn-ptx-absorb nw pos st n spans id inc stx)))
                    (<= (nfix n) (+ 1024 (mv-nth 0 (fn-ptx-absorb nw pos st n spans id inc stx)))))))
  :rule-classes nil
  :hints (("Goal" :use fn-ptx-absorb-adv :in-theory (union-theories (theory 'minimal-theory) '(zp)))))
(defthm fn-ptx-hash-progress
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :hashing))
           (< (fn-ptx-measure (mv-nth 0 (fn-ptx-hash m q id inc st))) (fn-ptx-measure m)))
  :hints (("Goal" :in-theory (union-theories (theory 'fn-ptx-p3u)
                    '(fn-ptx-hash-0 fn-ptx-measure-hashing fn-ptx-rem-hashing fn-ptx-nmsg fn-ptx-get-list2 fn-ptx-spans-len-g-m fn-ptx-spans-len-natp
                      fn-ptx-ceil-nfix-ge0 fn-ptx-ceil-plus10-ge0 (:type-prescription nfix) fn-ptx-spans-g-len))
           :cases ((< (+ (mv-nth 0 (fn-ptx-absorb (min 64 (max 1 (floor (nfix q) 1024))) (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m))
                                                  (fn-ptx-spans-len (fn-ptx-spans m)) (fn-ptx-spans m) id inc st)) 1024)
                      (fn-ptx-spans-len (fn-ptx-spans m))))
           :use ((:instance fn-ptx-hash-nw-pos)
                 (:instance fn-ptx-absorb-adv2 (nw (min 64 (max 1 (floor (nfix q) 1024)))) (pos (fn-rtc-get 0 (fn-ptx-hs m))) (st (fn-rtc-get 1 (fn-ptx-hs m)))
                            (n (fn-ptx-spans-len (fn-ptx-spans m))) (spans (fn-ptx-spans m)) (stx st))
                 (:instance fn-ptx-hash-ceil (n (fn-ptx-spans-len (fn-ptx-spans m))) (p0 (nfix (fn-rtc-get 0 (fn-ptx-hs m))))
                            (p2 (mv-nth 0 (fn-ptx-absorb (min 64 (max 1 (floor (nfix q) 1024))) (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m))
                                                         (fn-ptx-spans-len (fn-ptx-spans m)) (fn-ptx-spans m) id inc st))))
                 (:instance fn-ptx-end-measure (m (fn-ptx-chg m :committed nil)) (o :refused) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m))
                            (fenced nil) (committed nil))
                 (:instance fn-ptx-ceil-nonneg (a (+ (fn-ptx-spans-len (fn-ptx-spans m)) (- (fn-rtc-get 0 (fn-ptx-hs m))))))
                 (:instance fn-ptx-okp-elim))
           :do-not-induct t)))
(defthm fn-ptx-rd-ceil
  (implies (and (natp l) (natp p) (natp w) (<= 1024 w) (< (+ p w 3) l))
           (<= (+ 1 (ceiling (nfix (+ l (- (nfix (+ p w))))) 1024)) (ceiling (nfix (+ l (- p))) 1024)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-ptx-ceil-step (a (- l (+ p w))) (b (- l p)))
                        (:instance fn-ptx-nfix-sub (a l) (b (+ p w))) (:instance fn-ptx-nfix-sub (a l) (b p)))
           :in-theory (disable fn-ptx-ceil-step))))
(defthm fn-ptx-rd-cont-lt
  (implies (and (equal (fn-ptx-ph m) :reading)
                (< (+ (fn-ptx-cur-hoff (fn-ptx-cur m)) (fn-ptx-read-w q) 3) (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m))))
           (< (fn-ptx-measure (fn-ptx-rd-cont m q h1 g1 h3 g3 off off2 a)) (fn-ptx-measure m)))
  :hints (("Goal" :in-theory (union-theories (theory 'fn-ptx-p3u)
                    '(fn-ptx-rd-cont fn-ptx-measure-reading fn-ptx-rem-reading fn-ptx-cur-of-list fn-ptx-hmax fn-ptx-fmax fn-ptx-nfix-cur
                      fn-ptx-min-natp fn-ptx-read-w-natp fn-ptx-read-w-ge (:type-prescription fn-ptx-cur-len) (:type-prescription fn-ptx-cur-hoff)
                      (:type-prescription nfix) fn-ptx-ceil-nfix-ge0 fn-ptx-ceil-plus10-ge0 (:type-prescription nfix)))
           :use ((:instance fn-ptx-rd-ceil (l (min (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-hmax m))) (p (fn-ptx-cur-hoff (fn-ptx-cur m))) (w (fn-ptx-read-w q)))
                 (:instance fn-ptx-min-natp (a (fn-ptx-cur-len (fn-ptx-cur m))) (b (fn-ptx-hmax m))))
           :do-not-induct t)))
(defthm fn-ptx-rd-end0-lt
  (implies (equal (fn-ptx-ph m) :reading)
           (< (fn-ptx-measure (fn-ptx-rd-end0 m id inc st)) (fn-ptx-measure m)))
  :hints (("Goal" :in-theory (union-theories (theory 'fn-ptx-p3u)
                    '(fn-ptx-rd-end0 fn-ptx-rem-reading fn-ptx-hmax fn-ptx-fmax fn-ptx-ceil-nfix-ge0 fn-ptx-ceil-plus10-ge0 (:type-prescription nfix) (:type-prescription nfix) (:type-prescription fn-ptx-cur-len) (:type-prescription fn-ptx-cur-hoff) fn-ptx-min-natp))
           :use ((:instance fn-ptx-end-measure (m (fn-ptx-chg m :committed nil)) (o :refused) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m))
                            (fenced nil) (committed nil)))
           :do-not-induct t)))
(defthm fn-ptx-rd-endr-lt
  (implies (equal (fn-ptx-ph m) :reading)
           (< (fn-ptx-measure (fn-ptx-rd-endr m id inc st)) (fn-ptx-measure m)))
  :hints (("Goal" :in-theory (union-theories (theory 'fn-ptx-p3u)
                    '(fn-ptx-rd-endr fn-ptx-rem-reading fn-ptx-hmax fn-ptx-fmax fn-ptx-ceil-nfix-ge0 fn-ptx-ceil-plus10-ge0 (:type-prescription nfix) (:type-prescription nfix) (:type-prescription fn-ptx-cur-len) (:type-prescription fn-ptx-cur-hoff) fn-ptx-min-natp))
           :use ((:instance fn-ptx-end-measure (m (fn-ptx-chg (fn-ptx-chg m :committed nil) :b1 nil :b3 nil)) (o :refused) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m))
                            (fenced nil) (committed nil)))
           :do-not-induct t)))
(defthm fn-ptx-plus0 (implies (natp x) (equal (+ x 0) x)))
(defthm fn-ptx-rd-hashing-nmsg
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :reading) (natp off2) (<= 9 off2)
                (<= ioff (fn-ptx-cur-len (fn-ptx-cur m)))
                (<= (+ 32 (+ (len pre) (fn-ptx-cur-len (fn-ptx-cur m)) (len ins) (- (+ off2 (len st)) (- *fn-ptx-sufhead-max* (min (len sh) *fn-ptx-sufhead-max*))))) (fn-ptx-fmax m)))
           (<= (fn-ptx-nmsg (fn-ptx-rd-hashing m h1 g1 h3 g3 off off2 e ioff pre ins sh st)) (+ 10 (fn-ptx-fmax m))))
  :hints (("Goal" :in-theory (union-theories (theory 'fn-ptx-p3u)
                    '(fn-ptx-rd-hashing fn-ptx-nmsg-of-mk fn-ptx-spans-len-g fn-ptx-buf-of-list fn-ptx-nfix-buf fn-ptx-cur-of-list fn-ptx-nfix-cur
                      fn-ptx-frame-header-len fn-ptx-len-append fn-ptx-fmax natp min (:type-prescription len) (:type-prescription nfix)
                      (:type-prescription fn-ptx-cur-len) (:executable-counterpart fn-ptx-frame-header) fn-ptx-nfix-natp-rw))
           :use ((:instance fn-ptx-okp-elim))
           :do-not-induct t)))
(defthm fn-ptx-measure-rd-hashing
  (implies (equal (fn-ptx-ph m) :reading)
           (equal (fn-ptx-measure (fn-ptx-rd-hashing m h1 g1 h3 g3 off off2 e ioff pre ins sh st))
                  (+ (* (len (fn-ptx-q m)) (fn-ptx-post-bound-geo (fn-ptx-geo m)))
                     (+ 10 (ceiling (fn-ptx-nmsg (fn-ptx-rd-hashing m h1 g1 h3 g3 off off2 e ioff pre ins sh st)) 1024)))))
  :hints (("Goal" :in-theory (union-theories (theory 'fn-ptx-p3u)
                    '(fn-ptx-rd-hashing fn-ptx-measure-hashing fn-ptx-nmsg-of-mk fn-ptx-get-list2 (:executable-counterpart fn-rtc-get)
                      fn-ptx-nfix-natp-rw fn-ptx-spans-len-natp fn-ptx-plus0))
           :do-not-induct t)))
(defthm fn-ptx-rd-hashing-lt
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :reading) (natp off2) (<= 9 off2)
                (<= ioff (fn-ptx-cur-len (fn-ptx-cur m)))
                (<= (+ 32 (+ (len pre) (fn-ptx-cur-len (fn-ptx-cur m)) (len ins) (- (+ off2 (len st)) (- *fn-ptx-sufhead-max* (min (len sh) *fn-ptx-sufhead-max*))))) (fn-ptx-fmax m)))
           (< (fn-ptx-measure (fn-ptx-rd-hashing m h1 g1 h3 g3 off off2 e ioff pre ins sh st)) (fn-ptx-measure m)))
  :hints (("Goal" :in-theory (union-theories (theory 'fn-ptx-p3u)
                    '(fn-ptx-rem-reading fn-ptx-hmax fn-ptx-fmax fn-ptx-ceil-nfix-ge0 fn-ptx-ceil-plus10-ge0 (:type-prescription nfix) (:type-prescription nfix) (:type-prescription fn-ptx-cur-len)
                      (:type-prescription fn-ptx-cur-hoff) fn-ptx-min-natp fn-ptx-spans-len-natp fn-ptx-ceil-natp fn-ptx-nmsg-natp))
           :use ((:instance fn-ptx-measure-rd-hashing) (:instance fn-ptx-rd-hashing-nmsg)
                 (:instance fn-ptx-ceil-mono (a (fn-ptx-nmsg (fn-ptx-rd-hashing m h1 g1 h3 g3 off off2 e ioff pre ins sh st))) (b (+ 10 (fn-ptx-fmax m)))))
           :do-not-induct t)))
(defthm fn-ptx-read-b3-ge9
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :reading) (consp (fn-ptx-b1 m)))
           (<= 9 (fn-ptx-buf-len (fn-ptx-b3 m))))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-ptx-okp-elim)) :in-theory (union-theories (theory 'minimal-theory) (theory 'fn-ptx-mt7)))))
(defthm fn-ptx-measure-if
  (equal (fn-ptx-measure (if a b c)) (if a (fn-ptx-measure b) (fn-ptx-measure c))))
(defthm fn-ptx-lt-if
  (equal (< (if a x y) z) (if a (< x z) (< y z))))
(defthm fn-ptx-read-progress
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :reading))
           (< (fn-ptx-measure (mv-nth 0 (fn-ptx-read m q id inc stx))) (fn-ptx-measure m)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn-ptx-read-1 fn-ptx-measure-if fn-ptx-lt-if fn-ptx-rd-cont-lt fn-ptx-rd-end0-lt fn-ptx-rd-endr-lt fn-ptx-rd-hashing-lt
                      fn-ptx-read-b3-ge9 (:type-prescription len) (:type-prescription fn-ptx-buf-len) natp
                      (:type-prescription fn-ptx-cur-len) (:type-prescription fn-ptx-cur-hoff)))
           :cases ((consp (fn-ptx-b1 m)))
           :do-not-induct t)))
(defthm fn-ptx-reading-progress
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :reading) (equal (fn-rtc-get 0 ev) :timer))
           (< (fn-ptx-measure (mv-nth 0 (fn-ptx-step1 m ev st q))) (fn-ptx-measure m)))
  :hints (("Goal" :in-theory (theory 'fn-ptx-p3u) :use ((:instance fn-ptx-read-progress (id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev)) (stx st))) :do-not-induct t)))
(defthm fn-ptx-hashing-progress
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :hashing) (equal (fn-rtc-get 0 ev) :timer))
           (< (fn-ptx-measure (mv-nth 0 (fn-ptx-step1 m ev st q))) (fn-ptx-measure m)))
  :hints (("Goal" :in-theory (theory 'fn-ptx-p3u) :use ((:instance fn-ptx-hash-progress (id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev)))) :do-not-induct t)))
(defthm fn-ptx-step-makes-progress (fn-ptx-p3 m ev st q)
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn-ptx-p3 fn-ptx-step-0 fn-ptx-expected (:executable-counterpart equal) (:executable-counterpart member-equal) member-equal
                      (:executable-counterpart eq)))
           :cases ((equal (fn-ptx-ph m) :reading) (equal (fn-ptx-ph m) :hashing) (equal (fn-ptx-ph m) :extending) (equal (fn-ptx-ph m) :extsyncing)
                   (equal (fn-ptx-ph m) :payload-writing) (equal (fn-ptx-ph m) :log-writing) (equal (fn-ptx-ph m) :committing))
           :use (fn-ptx-reading-progress fn-ptx-hashing-progress fn-ptx-extending-progress fn-ptx-extsyncing-progress fn-ptx-payload-progress fn-ptx-logwrite-progress fn-ptx-committing-progress)
           :do-not-induct t)))
