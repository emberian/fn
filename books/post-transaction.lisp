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
(defun fn-ptx-code (o) (nfix (cdr (assoc-eq o *fn-ptx-codes*))))

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
  (local (defun fn-ptx-acc-begin (txid) (declare (ignore txid)) nil))
  (local (defun fn-ptx-acc-feed (a octets) (declare (ignore a octets)) (mv nil nil)))
  (local (defun fn-ptx-acc-feed-cost (a octets) (declare (ignore a octets)) 0))
  (local (defun fn-ptx-acc-end (a blen) (declare (ignore a blen)) (mv t nil nil 0 nil nil)))
  (local (defun fn-ptx-acc-max-state () 1))
  (local (defun fn-ptx-acc-out-max () 0))
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
  (list ph (nfix k) cur q kd (nfix ext) (nfix nxt) b1 b3 hs (and committed t) evd geo acc))
(defun fn-ptx-ph (m) (fn-rtc-get 0 m))
(defun fn-ptx-k (m) (nfix (fn-rtc-get 1 m)))
(defun fn-ptx-cur (m) (fn-rtc-get 2 m))
(defun fn-ptx-q (m) (fn-rtc-get 3 m))
(defun fn-ptx-kd (m) (fn-rtc-get 4 m))
(defun fn-ptx-ext (m) (nfix (fn-rtc-get 5 m)))
(defun fn-ptx-nxt (m) (nfix (fn-rtc-get 6 m)))
(defun fn-ptx-b1 (m) (fn-rtc-get 7 m))
(defun fn-ptx-b3 (m) (fn-rtc-get 8 m))
(defun fn-ptx-hs (m) (fn-rtc-get 9 m))
(defun fn-ptx-committedp (m) (and (fn-rtc-get 10 m) t))
(defun fn-ptx-evd (m) (fn-rtc-get 11 m))
(defun fn-ptx-geo (m) (fn-rtc-get 12 m))
(defun fn-ptx-acc (m) (fn-rtc-get 13 m))
(defun fn-ptx-unit (m) (max 1 (nfix (fn-rtc-get 0 (fn-ptx-geo m)))))
(defun fn-ptx-fmax (m) (nfix (fn-rtc-get 1 (fn-ptx-geo m))))
(defun fn-ptx-hmax (m) (nfix (fn-rtc-get 2 (fn-ptx-geo m))))

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

(defun fn-ptx-kd-mk (count last frontier txid acked) (list (nfix count) last (nfix frontier) (nfix txid) (nfix acked)))
(defun fn-ptx-kd-count (kd) (nfix (fn-rtc-get 0 kd)))
(defun fn-ptx-kd-last (kd) (fn-rtc-get 1 kd))
(defun fn-ptx-kd-frontier (kd) (nfix (fn-rtc-get 2 kd)))
(defun fn-ptx-kd-txid (kd) (nfix (fn-rtc-get 3 kd)))
(defun fn-ptx-kd-acked (kd) (nfix (fn-rtc-get 4 kd)))

; The opened machine: idle over the open's kernel projection, at extent EXT.
(defun fn-ptx-opened (kd ext geo) (fn-ptx-mk :idle 0 nil nil kd ext ext nil nil nil nil nil geo nil))

; Before the store opens: the static slot's initial state (fn-rtc-m-static-init
; takes only the slot), refusing every post until the open's :opened event.
(defun fn-ptx-closed () (fn-ptx-mk :closed 0 nil nil nil 0 0 nil nil nil nil nil nil nil))
; ADAPTER (rule 6b-5): owner P, retired by A's lease landing, which adds the :opened
; kind, (:opened ID INC DATA) with DATA = (KD EXT GEO), delivered to the static slot
; once as (:opened (:done 0) ID 1 DATA) (fn-rtc-ev-opened-data replaces this reader); the host emits it after the store opens, before the listener accepts.
(defun fn-ptxa-opened-data (ev) (fn-rtc-get 4 ev))

; The projection of a logical kernel (L's fn-lgk), for the P4 relation.
(defun fn-ptx-kd-of (ks)
  (fn-ptx-kd-mk (len (fn-lgk-committed ks)) (fn-lgk-last ks) (fn-lgk-frontier ks)
                (fn-lgk-next-txid ks) (fn-lgk-acked ks)))

(defun fn-ptx-cur-fid (c) (fn-rtc-get 0 c))
(defun fn-ptx-cur-finc (c) (fn-rtc-get 1 c))
(defun fn-ptx-cur-bp (c) (nfix (fn-rtc-get 2 c)))
(defun fn-ptx-cur-len (c) (nfix (fn-rtc-get 3 c)))
(defun fn-ptx-cur-hoff (c) (nfix (fn-rtc-get 4 c)))
(defun fn-ptx-cur-txid (c) (nfix (fn-rtc-get 5 c)))
(defun fn-ptx-cur-ioff (c) (nfix (fn-rtc-get 6 c)))
(defun fn-ptx-buf-h (b) (nfix (fn-rtc-get 0 b)))
(defun fn-ptx-buf-g (b) (nfix (fn-rtc-get 1 b)))
(defun fn-ptx-buf-len (b) (nfix (fn-rtc-get 2 b)))
(defun fn-ptx-buf-x (b) (nfix (fn-rtc-get 3 b)))

; -----------------------------------------------------------------------------
; The shape check.  (fn-ptx-size-rem X N) is N less X's size in words when that is
; at most N, else nil; it walks at most N words of X whatever X is.  A state is
; well formed when its phase is one of the machine's and each field fits its
; budget; the budgets cover every reachable state (keystone P0) with the digest's
; stack at most 64 entries deep (messages under 2^74 octets).
(defun fn-ptx-size-rem (x n)
  (declare (xargs :measure (acl2-count x)))
  (cond ((zp n) nil)
        ((atom x) (- n 1))
        (t (let ((r (fn-ptx-size-rem (car x) (- n 1))))
             (and r (fn-ptx-size-rem (cdr x) r))))))
(defconst *fn-ptx-phases*
  '(:closed :idle :reading :hashing :extending :extsyncing :payload-writing :log-writing :committing :fenced))
;                            ph k cur q  kd ext nxt b1 b3 hs   committed evd geo
(defconst *fn-ptx-budgets* '(1  1 15  21 75 1   1   9  9  4101 1         49  7))
(defun fn-ptx-fields-fit (m i bs)
  (declare (xargs :measure (len bs)))
  (if (consp bs)
      (and (fn-ptx-size-rem (fn-rtc-get i m) (nfix (car bs)))
           (fn-ptx-fields-fit m (+ 1 (nfix i)) (cdr bs)))
    t))
(defun fn-ptx-wfp (m)
  (and (member-eq (fn-ptx-ph m) *fn-ptx-phases*)
       (fn-ptx-fields-fit m 0 *fn-ptx-budgets*)
       (fn-ptx-size-rem (fn-ptx-acc m) (fn-ptx-acc-max-state))
       t))
; The check's charge: the words it may walk.
(defun fn-ptx-wf-cost () (+ 4290 (fn-ptx-acc-max-state)))
; A state that fails the check (none reachable) is replaced by this fenced one.
(defun fn-ptx-broken () (fn-ptx-mk :fenced 0 nil nil nil 0 0 nil nil nil nil nil nil nil))

; -----------------------------------------------------------------------------
; Reading the view (the owner's own workspaces and :out leases only).
(defun fn-ptx-byte (h i id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (nfix (fn-rtc-st-v-byte h i id inc fn-rtc-st)))
(defun fn-ptx-range (h i n id inc fn-rtc-st)
  ; octets [i, i+n) of buffer h, as a list (statement level; the exec twin reads in place)
  (declare (xargs :stobjs fn-rtc-st :measure (nfix n)))
  (if (zp n) nil
    (cons (fn-ptx-byte h i id inc fn-rtc-st)
          (fn-ptx-range h (+ 1 (nfix i)) (- n 1) id inc fn-rtc-st))))
(defun fn-ptx-gen (h id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (fn-rtc-st-v-gen h id inc fn-rtc-st))
(defun fn-ptx-cap (h id inc fn-rtc-st)
  ; buffer H's capacity under the layer's configuration
  (declare (xargs :stobjs fn-rtc-st) (ignore id inc))
  (fn-rtc-buf-cap h (fn-rtc-st-config fn-rtc-st)))

; The head's length: the least i in [I, LIM - 3) with CR LF CR LF at [i, i+4),
; plus 4; nil when there is none.
(defun fn-ptx-head-end (h i lim id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :measure (nfix (- (nfix lim) (nfix i)))))
  (let ((i (nfix i)))
    (if (< (+ i 3) (nfix lim))
        (if (and (equal (fn-ptx-byte h i id inc fn-rtc-st) 13) (equal (fn-ptx-byte h (+ i 1) id inc fn-rtc-st) 10)
                 (equal (fn-ptx-byte h (+ i 2) id inc fn-rtc-st) 13) (equal (fn-ptx-byte h (+ i 3) id inc fn-rtc-st) 10))
            (+ i 4)
          (fn-ptx-head-end h (+ i 1) lim id inc fn-rtc-st))
      nil)))

; The first free owner home buffer at or above I other than SKIP (home buffers of
; slot 1 are [0, qfixed)).
(defun fn-ptx-free (i skip id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st
                  :measure (nfix (- (min (fn-rtc-qfixed (fn-rtc-st-config fn-rtc-st)) (fn-rtc-nbufs (fn-rtc-st-config fn-rtc-st))) (nfix i)))))
  (let ((i (nfix i)))
    (if (< i (min (fn-rtc-qfixed (fn-rtc-st-config fn-rtc-st)) (fn-rtc-nbufs (fn-rtc-st-config fn-rtc-st))))
        (if (and (not (equal i skip)) (equal (fn-rtc-st-v-owner i id inc fn-rtc-st) '(:free)))
            i
          (fn-ptx-free (+ 1 i) skip id inc fn-rtc-st))
      nil)))

; -----------------------------------------------------------------------------
; The entry's spans, in file order: b1's [0,l1) (frame header ++ chain field ++
; PRE), the article [0,ioff), b1's [l1, l1+lins) (INS), the article [ioff,len),
; b3's [start,end) (SUF, and the trailer once hashed); empty spans dropped.  Each
; span is (h off n).  The entry is written one pwrite per span from the buffer it
; lies in; the record moves nowhere.
(defun fn-ptx-span (h off n) (if (zp n) nil (list (list (nfix h) (nfix off) (nfix n)))))
(defun fn-ptx-spans (m)
  (let* ((b1 (fn-ptx-b1 m)) (b3 (fn-ptx-b3 m)) (cur (fn-ptx-cur m))
         (l1 (fn-ptx-buf-len b1)) (lins (fn-ptx-buf-x b1))
         (alen (fn-ptx-cur-len cur)) (ioff (min (fn-ptx-cur-ioff cur) alen)))
    (append (fn-ptx-span (fn-ptx-buf-h b1) 0 l1)
            (fn-ptx-span (fn-ptx-cur-bp cur) 0 ioff)
            (fn-ptx-span (fn-ptx-buf-h b1) l1 lins)
            (fn-ptx-span (fn-ptx-cur-bp cur) ioff (- alen ioff))
            (fn-ptx-span (fn-ptx-buf-h b3) (fn-ptx-buf-x b3) (- (fn-ptx-buf-len b3) (fn-ptx-buf-x b3))))))
(defun fn-ptx-spans-len (spans)
  (if (consp spans) (+ (nfix (fn-rtc-get 2 (car spans))) (fn-ptx-spans-len (cdr spans))) 0))

; Octet I of the message the spans make, and N octets from I, read through the view.
(defun fn-ptx-msg-byte (i spans id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :measure (len spans)))
  (if (consp spans)
      (let ((n (nfix (fn-rtc-get 2 (car spans)))))
        (if (< (nfix i) n)
            (fn-ptx-byte (fn-rtc-get 0 (car spans)) (+ (nfix (fn-rtc-get 1 (car spans))) (nfix i)) id inc fn-rtc-st)
          (fn-ptx-msg-byte (- (nfix i) n) (cdr spans) id inc fn-rtc-st)))
    0))
(defun fn-ptx-msg-range (i n spans id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :measure (nfix n)))
  (if (zp n) nil
    (cons (fn-ptx-msg-byte i spans id inc fn-rtc-st)
          (fn-ptx-msg-range (+ 1 (nfix i)) (- n 1) spans id inc fn-rtc-st))))

; The digest's held state (pos stack) over a message of N octets: absorb up to
; NW windows; a window is pushed only when more than a window remains after it
; (fn-b3-window-outs' rule), the last one by the finish.
(defun fn-ptx-absorb (nw pos st n spans id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :measure (nfix nw)))
  (let ((pos (nfix pos)) (n (nfix n)))
    (if (or (zp nw) (<= n (+ pos *fn-ptx-window*)))
        (mv pos st)
      (fn-ptx-absorb (- nw 1) (+ pos *fn-ptx-window*)
                     (fn-b3-cv-push *fn-b3-iv* 0 *fn-ptx-wexp*
                                    (fn-b3-node *fn-b3-iv*
                                                (fn-ptx-msg-range pos *fn-ptx-window* spans id inc fn-rtc-st)
                                                (floor pos 1024) 0)
                                    st)
                     n spans id inc fn-rtc-st))))
(defun fn-ptx-finish-digest (pos st n spans id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let ((pos (nfix pos)))
    (fn-b3-output-root
     (fn-b3-stack-fold *fn-b3-iv* 0
                       (fn-b3-cv-push *fn-b3-iv* 0 *fn-ptx-wexp*
                                      (fn-b3-node *fn-b3-iv*
                                                  (fn-ptx-msg-range pos (- (nfix n) pos) spans id inc fn-rtc-st)
                                                  (floor pos 1024) 0)
                                      st)))))

; -----------------------------------------------------------------------------
; Requests.
(defun fn-ptx-timer () (list :submit :timer nil (list 0)))
(defun fn-ptx-pwrite (h g off n pos) (list :submit :pwrite (list (nfix h) (nfix g) (nfix off) (nfix n)) (list *fn-ptx-lfile* (nfix pos))))
(defun fn-ptx-fsync () (list :submit :fsync nil (list *fn-ptx-lfile*)))
; ADAPTER (rule 6b-5): owner P, retired by A's lease landing, which adds the unbuffered
; :extend kind to *fn-rtc-kinds* in exactly this shape; until then the layer refuses it.
(defun fn-ptxa-extend (ext nxt) (list :submit :extend nil (list *fn-ptx-lfile* (nfix ext) (nfix nxt))))

; The answer O to post P = (fid finc bp len ...): octet 0 of the poster's own
; buffer becomes the code, the whole buffer goes back by a hand.  The generation
; is the view's now (a lease's end advances it).
(defun fn-ptx-answer (p o id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let* ((h (fn-ptx-cur-bp p)) (g (fn-ptx-gen h id inc fn-rtc-st))
         (fl (max 1 (nfix (fn-rtc-st-v-fill h id inc fn-rtc-st)))))
    (list (list :write h g 0 (list (fn-ptx-code o)))
          (list :submit :hand (list h g 0 fl) (list (fn-ptx-cur-fid p) (fn-ptx-cur-finc p))))))

; The frame header of an entry whose record is R octets long (kind 1, one record).
(defun fn-ptx-frame-header (rlen)
  (fn-frame-header *fn-lg-magic* *fn-lg-version* *fn-lg-record-kind* (+ 32 (nfix rlen))))
(defun fn-ptx-pad-len (elen unit) (fn-lg-pad-len (nfix elen) unit))

; Start post P = (fid finc bp len) over kernel projection KD: the head search and
; the acceptance begin on the zero-delay timer.  Constant work.  Q is the queue
; after P; COMMITTED is the step's commit flag, carried.
(defun fn-ptx-start (p q kd ext geo committed)
  (mv (fn-ptx-mk :reading 0
                 (list (fn-ptx-cur-fid p) (fn-ptx-cur-finc p) (fn-ptx-cur-bp p) (fn-ptx-cur-len p) 0 (fn-ptx-kd-txid kd)
                       (fn-ptx-cur-len p))
                 q kd ext ext nil nil nil committed nil geo (fn-ptx-acc-begin (fn-ptx-kd-txid kd)))
      (list (fn-ptx-timer))
      1))

; End the current transaction with outcome O: release b1 and b3, answer, then
; start the next waiting post unless FENCED (then every waiting post is refused).
(defun fn-ptx-release-bufs (m id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
    ; at the view's generation: a pwrite's lease ending advances it
  (append (if (consp (fn-ptx-b1 m)) (list (list :release (fn-ptx-buf-h (fn-ptx-b1 m)) (fn-ptx-gen (fn-ptx-buf-h (fn-ptx-b1 m)) id inc fn-rtc-st))) nil)
          (if (consp (fn-ptx-b3 m)) (list (list :release (fn-ptx-buf-h (fn-ptx-b3 m)) (fn-ptx-gen (fn-ptx-buf-h (fn-ptx-b3 m)) id inc fn-rtc-st))) nil)))
(defun fn-ptx-refuse-all (q id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (if (consp q)
      (append (fn-ptx-answer (car q) :refused id inc fn-rtc-st) (fn-ptx-refuse-all (cdr q) id inc fn-rtc-st))
    nil))
(defun fn-ptx-end (m o kd ext fenced committed id inc fn-rtc-st)
  ; (mv m reqs cost); KD and EXT the kernel projection and extent after this end
  (declare (xargs :stobjs fn-rtc-st))
  (let* ((cur (fn-ptx-cur m)) (q (fn-ptx-q m))
         (done (append (fn-ptx-release-bufs m id inc fn-rtc-st) (fn-ptx-answer cur o id inc fn-rtc-st))))
    (cond (fenced
           (mv (fn-ptx-mk :fenced 0 nil nil kd ext ext nil nil nil committed nil (fn-ptx-geo m) nil)
               (append done (fn-ptx-refuse-all q id inc fn-rtc-st)) 1))
          ((consp q)
           (mv-let (m2 r2 c2) (fn-ptx-start (car q) (cdr q) kd ext (fn-ptx-geo m) committed)
             (mv m2 (append done r2) (+ 1 c2))))
          (t (mv (fn-ptx-mk :idle 0 nil nil kd ext ext nil nil nil committed nil (fn-ptx-geo m) nil) done 1)))))

; The kernel projection after the barrier's :ok and the acknowledgement
; (fn-lgk-fence then fn-lgk-finish-one of a batch of one): one more committed
; record, the chain head the new trailer, the frontier past the entry.
(defun fn-ptx-kd-commit (kd trailer elen)
  (fn-ptx-kd-mk (+ 1 (fn-ptx-kd-count kd)) trailer (+ (fn-ptx-kd-frontier kd) (nfix elen))
                (+ 1 (fn-ptx-kd-txid kd))
                (+ 1 (fn-ptx-kd-acked kd))))

; The entry's geometry for the current transaction.
(defun fn-ptx-alen (m) (fn-ptx-cur-len (fn-ptx-cur m)))
(defun fn-ptx-nspans (m) (len (fn-ptx-spans m)))
(defun fn-ptx-span-n (i m) (nfix (fn-rtc-get 2 (fn-rtc-get i (fn-ptx-spans m)))))
(defun fn-ptx-nmsg (m) (fn-ptx-spans-len (fn-ptx-spans m)))     ; with the trailer once hashed
(defun fn-ptx-elen (m) (+ (fn-ptx-nmsg m) (nfix (fn-rtc-get 2 (fn-ptx-hs m)))))
; The pwrite of span I of the entry at frontier FRONT: from its buffer at the
; view's generation, to the entry's offset of the span.
(defun fn-ptx-span-pwrite (i m front id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let* ((spans (fn-ptx-spans m)) (sp (fn-rtc-get i spans)) (h (nfix (fn-rtc-get 0 sp))))
    (fn-ptx-pwrite h (fn-ptx-gen h id inc fn-rtc-st) (fn-rtc-get 1 sp) (fn-rtc-get 2 sp)
                   (+ (nfix front) (fn-ptx-spans-len (take (nfix i) spans))))))

(defun fn-ptx-atom (x) (if (consp x) nil x))
(defun fn-ptx-summary (ev)
  (list (fn-ptx-atom (fn-rtc-get 0 ev)) (fn-ptx-atom (fn-rtc-get 0 (fn-rtc-get 1 ev)))
        (fn-ptx-atom (fn-rtc-get 1 (fn-rtc-get 1 ev)))))
(defun fn-ptx-evd+ (m ev) (append (true-list-fix (fn-ptx-evd m)) (list (fn-ptx-summary ev))))

; The reading step.  The first acquires the two workspaces (b1 empty, b3 at the
; base); each searches the head in [pos, pos + w + 3) and feeds the octets before
; the head's end (or the window) to the acceptance, appending its suffix part to
; b3; at the head's end it ends the acceptance, writes b1 = frame header ++ chain
; field ++ PRE ++ INS, the suffix's head just below the base and its tail after the
; parts, then hashes.  W is an eighth of the quantum (at least a window): the
; search is charged W + 3, the feed its cost (at most 4(W + 3) + K), the suffix
; part written at most 2(W + 3) + K octets, so the step fits Q + C.
(defun fn-ptx-read-w (q) (max *fn-ptx-window* (floor (nfix q) 8)))
(defun fn-ptx-write-nz (h g off octets)
  ; the workspace write of OCTETS at OFF, none when empty
  (if (consp octets) (list (list :write (nfix h) (nfix g) (nfix off) octets)) nil))
(defun fn-ptx-read (m q id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let* ((cur (fn-ptx-cur m)) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m))
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
                (mv m2 (append acq rel r2) (+ cost c2)))))))))))

; The hashing step: up to NW windows, then the trailer and fn-ptd's begin.
(defun fn-ptx-hash (m q id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
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
                    (list wr (fn-ptxa-extend ext nx)) cost)))
            (let ((m1 (fn-ptx-chg m0 :ph :payload-writing :k 0 :nxt ext :b3 b3x :hs (list nmsg trailer pad) :evd nil)))
              (mv m1 (list wr (fn-ptx-span-pwrite 0 m1 front id inc fn-rtc-st)) cost))))))))

; The step on a well-formed state: (mv m2 requests cost).
(defun fn-ptx-step1 (m ev fn-rtc-st q)
  (declare (xargs :stobjs fn-rtc-st))
  (let* ((id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev))
         (kind (fn-rtc-get 0 ev)) (out (fn-rtc-get 1 ev)) (tag (fn-rtc-get 0 out)) (n (fn-rtc-get 1 out))
         (ph (fn-ptx-ph m)) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m)) (nxt (fn-ptx-nxt m))
         (m0 (fn-ptx-chg m :committed nil)))
    (cond
     ;; the store opened: the kernel projection, the extent and the geometry
     ((eq kind :opened)
      (if (and (eq ph :closed) (eq tag :done))
          ;; an open whose projection does not fit the budgets, or whose frame
          ;; bound is not below 2^64, leaves the owner closed
          (let* ((d (fn-ptxa-opened-data ev))
                 (m1 (fn-ptx-opened (fn-rtc-get 0 d) (nfix (fn-rtc-get 1 d)) (fn-rtc-get 2 d))))
            (if (and (fn-ptx-wfp m1) (< (fn-ptx-fmax m1) (expt 2 64)))
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

; The step: the shape check, then the machine.  (mv m2 requests cost).
(defun fn-ptx-step (m ev fn-rtc-st q)
  (declare (xargs :stobjs fn-rtc-st))
  (if (fn-ptx-wfp m)
      (mv-let (m2 reqs cost) (fn-ptx-step1 m ev fn-rtc-st q)
        (mv m2 reqs (+ (fn-ptx-wf-cost) (nfix cost))))
    (mv (fn-ptx-broken) nil (fn-ptx-wf-cost))))

; The layer's bounds for this machine: the charge's constant part (the shape
; check, a window's search slack and the trailer, the workspaces' writes), the
; requests one step may make (an end refusing a full queue), and the state's
; size (every field at its budget plus one step's growth: a post queued, a
; completion's summary, NW-MAX digest windows).
(defun fn-ptx-c () (+ (fn-ptx-wf-cost) (* 8 *fn-ptx-window*) 1024 (* 10 (fn-ptx-acc-out-max))))
(defun fn-ptx-max-reqs () 32)
(defun fn-ptx-max-state () (+ 8500 (fn-ptx-acc-max-state)))

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

; P0: the invariant.  Well formed; the frame bound below 2^64; the evidence is
; what the phase says (the extension's two completions first when there was
; one); while hashing, the held stack is the binary counter of the windows
; absorbed and the message is within the frame bound.
(defun fn-ptx-okp (m)
  (let* ((ph (fn-ptx-ph m)) (evd (fn-ptx-evd m)) (rest (fn-ptx-strip-ext evd))
         (hs (fn-ptx-hs m)) (pos (fn-rtc-get 0 hs))
         (nmsg (fn-ptx-nmsg m)) (k (fn-ptx-k m)) (n (fn-ptx-nspans m)))
    (and (fn-ptx-wfp m)
         (< (fn-ptx-fmax m) (expt 2 64))
         (case ph
           ((:closed :idle :reading :hashing :extending :fenced) (null evd))
           (:extsyncing (and (true-listp evd) (equal (len evd) 1) (fn-ptx-done-p (car evd) :extend nil)))
           (:payload-writing (and (< (+ k 1) n) (fn-ptx-entry-evd-p rest m k)))
           (:log-writing (and (equal (+ k 1) n) (fn-ptx-entry-evd-p rest m k)))
           (:committing (fn-ptx-entry-evd-p rest m n))
           (otherwise nil))
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
; Proofs (Sonnet 3)
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
                (<= (fn-rtc-size (fn-rtc-get 10 m)) 1) (<= (fn-rtc-size (fn-ptx-evd m)) 49)
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
       (equal (fn-rtc-get 0 (fn-ptxa-extend ext nxt)) :submit))
  :hints (("Goal" :in-theory (enable fn-ptx-timer fn-ptx-fsync fn-ptx-pwrite fn-ptxa-extend fn-rtc-get))))
(defthm fn-ptx-span-pwrite-head
  (equal (fn-rtc-get 0 (fn-ptx-span-pwrite i m front id inc st)) :submit)
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                             '(fn-ptx-span-pwrite fn-ptx-submit-heads)))))
(defthm fn-ptx-hash-charge
  (implies (and (natp q) (<= (fn-rtc-size (fn-ptx-q m)) 21))
           (<= (+ (mv-nth 2 (fn-ptx-hash m q id inc st)) (fn-rtc-reqs-octets (mv-nth 1 (fn-ptx-hash m q id inc st))))
               (+ q 9216 (* 10 (fn-ptx-acc-out-max)))))
  :hints (("Goal" :in-theory (e/d (fn-ptx-hash) (fn-ptx-end fn-ptx-mk fn-ptx-absorb fn-ptx-finish-digest fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-rtc-get fn-ptx-committedp
                                                   fn-ptx-unit fn-ptx-buf-h fn-ptx-buf-g fn-ptx-buf-len fn-ptx-buf-x fn-ptx-spans fn-ptx-spans-len min max floor fn-olr-extension-needed-p fn-olr-extension-target fn-ptx-pad-len fn-ptx-kd-frontier fn-ptx-span-pwrite mv-nth fn-ptx-timer fn-ptxa-extend fn-ptx-pwrite fn-ptx-fsync))
           :do-not-induct t)))

(defthm fn-ptx-hash-cost-natp
  (natp (mv-nth 2 (fn-ptx-hash m q id inc st)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (fn-ptx-hash) (fn-ptx-end fn-ptx-mk fn-ptx-absorb fn-ptx-finish-digest fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-rtc-get fn-ptx-committedp
                                                   fn-ptx-unit fn-ptx-spans fn-ptx-spans-len min max floor fn-olr-extension-needed-p fn-olr-extension-target fn-ptx-pad-len fn-ptx-kd-frontier fn-ptx-span-pwrite mv-nth fn-ptx-timer fn-ptxa-extend fn-ptx-pwrite fn-ptx-fsync))
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
                                                   fn-ptx-unit fn-ptx-spans fn-ptx-spans-len min max floor fn-olr-extension-needed-p fn-olr-extension-target fn-ptx-pad-len fn-ptx-kd-frontier fn-ptx-span-pwrite mv-nth fn-ptx-timer fn-ptxa-extend fn-ptx-pwrite fn-ptx-fsync))
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
                (<= (fn-rtc-size (fn-ptx-evd m)) 49) (<= (fn-rtc-size (fn-ptx-ph m)) 1))
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
                (<= (fn-rtc-size (fn-ptx-evd m)) 49) (<= (fn-rtc-size (fn-ptx-ph m)) 1))
           (<= (fn-rtc-size (mv-nth 0 (fn-ptx-hash m q id inc st))) (+ 8500 (fn-ptx-acc-max-state))))
  :hints (("Goal" :in-theory (e/d (fn-ptx-hash) (fn-ptx-buf-h fn-ptx-buf-g fn-ptx-buf-len fn-ptx-buf-x fn-ptx-end fn-ptx-mk fn-ptx-absorb fn-ptx-finish-digest fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-rtc-get fn-ptx-committedp
                                                   fn-ptx-unit fn-ptx-spans fn-ptx-spans-len min max floor fn-olr-extension-needed-p fn-olr-extension-target fn-ptx-pad-len fn-ptx-kd-frontier fn-ptx-span-pwrite mv-nth fn-ptx-timer fn-ptxa-extend fn-ptx-pwrite fn-ptx-fsync))
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
                (<= (fn-rtc-size (fn-ptx-evd m)) 49) (<= (fn-rtc-size (fn-ptx-ph m)) 1))
           (<= (fn-rtc-size (mv-nth 0 (fn-ptx-read m q id inc st))) (+ 8000 (fn-ptx-acc-max-state))))
  :rule-classes :linear
  :hints (("Goal" :use fn-ptx-read-size :in-theory (disable fn-ptx-read fn-ptx-read-size))))
(defthm fn-ptx-hash-size-lin
  (implies (and (natp q) (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-geo m)) 7) (<= (fn-rtc-size (fn-ptx-kd m)) 75)
                (<= (fn-rtc-size (fn-ptx-cur m)) 15) (<= (fn-rtc-size (fn-ptx-acc m)) (fn-ptx-acc-max-state))
                (<= (fn-rtc-size (fn-ptx-b1 m)) 9) (<= (fn-rtc-size (fn-ptx-b3 m)) 9) (<= (fn-rtc-size (fn-ptx-hs m)) 4101)
                (<= (fn-rtc-size (fn-ptx-evd m)) 49) (<= (fn-rtc-size (fn-ptx-ph m)) 1))
           (<= (fn-rtc-size (mv-nth 0 (fn-ptx-hash m q id inc st))) (+ 8500 (fn-ptx-acc-max-state))))
  :rule-classes :linear
  :hints (("Goal" :use fn-ptx-hash-size :in-theory (disable fn-ptx-hash fn-ptx-hash-size))))
(defthm fn-ptx-read-size-car
  (implies (and (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-geo m)) 7) (<= (fn-rtc-size (fn-ptx-kd m)) 75)
                (<= (fn-rtc-size (fn-ptx-cur m)) 15) (<= (fn-rtc-size (fn-ptx-acc m)) (fn-ptx-acc-max-state))
                (<= (fn-rtc-size (fn-ptx-b1 m)) 9) (<= (fn-rtc-size (fn-ptx-b3 m)) 9) (<= (fn-rtc-size (fn-ptx-hs m)) 4101)
                (<= (fn-rtc-size (fn-ptx-evd m)) 49) (<= (fn-rtc-size (fn-ptx-ph m)) 1))
           (<= (fn-rtc-size (car (fn-ptx-read m q id inc st))) (+ 8000 (fn-ptx-acc-max-state))))
  :rule-classes :linear
  :hints (("Goal" :use fn-ptx-read-size-lin :in-theory (disable fn-ptx-read fn-ptx-read-size-lin))))
(defthm fn-ptx-hash-size-car
  (implies (and (natp q) (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-geo m)) 7) (<= (fn-rtc-size (fn-ptx-kd m)) 75)
                (<= (fn-rtc-size (fn-ptx-cur m)) 15) (<= (fn-rtc-size (fn-ptx-acc m)) (fn-ptx-acc-max-state))
                (<= (fn-rtc-size (fn-ptx-b1 m)) 9) (<= (fn-rtc-size (fn-ptx-b3 m)) 9) (<= (fn-rtc-size (fn-ptx-hs m)) 4101)
                (<= (fn-rtc-size (fn-ptx-evd m)) 49) (<= (fn-rtc-size (fn-ptx-ph m)) 1))
           (<= (fn-rtc-size (car (fn-ptx-hash m q id inc st))) (+ 8500 (fn-ptx-acc-max-state))))
  :rule-classes :linear
  :hints (("Goal" :use fn-ptx-hash-size-lin :in-theory (disable fn-ptx-hash fn-ptx-hash-size-lin))))

(defthm fn-ptx-step1-cost-natp
  (implies (and (natp q) (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-kd m)) 75))
           (natp (mv-nth 2 (fn-ptx-step1 m ev st q))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1) (fn-ptx-mk fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-ptx-committedp
fn-ptx-end fn-ptx-read fn-ptx-hash fn-ptx-start fn-ptx-answer fn-rtc-get fn-ptx-opened fn-ptx-wfp fn-ptx-evd+ fn-ptx-summary fn-ptx-kd-commit
fn-ptx-elen fn-ptx-nmsg fn-ptx-nspans fn-ptx-span-n fn-ptx-spans fn-ptx-spans-len fn-ptx-buf-len fn-ptx-gen fn-ptx-kd-frontier fn-ptx-pwrite fn-ptx-fsync fn-ptxa-extend fn-ptx-atom fn-ptx-span-pwrite mv-nth fn-ptx-release-bufs))
           :do-not-induct t)))
(defthm fn-ptx-step1-charge
  (implies (and (natp q) (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-kd m)) 75))
           (<= (+ (mv-nth 2 (fn-ptx-step1 m ev st q)) (fn-rtc-reqs-octets (mv-nth 1 (fn-ptx-step1 m ev st q))))
               (+ q 9216 (* 10 (fn-ptx-acc-out-max)))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1) (fn-ptx-mk fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-ptx-committedp
fn-ptx-end fn-ptx-read fn-ptx-hash fn-ptx-start fn-ptx-answer fn-rtc-get fn-ptx-opened fn-ptx-wfp fn-ptx-evd+ fn-ptx-summary fn-ptx-kd-commit
fn-ptx-elen fn-ptx-nmsg fn-ptx-nspans fn-ptx-span-n fn-ptx-spans fn-ptx-spans-len fn-ptx-buf-len fn-ptx-gen fn-ptx-kd-frontier fn-ptx-pwrite fn-ptx-fsync fn-ptxa-extend fn-ptx-atom fn-ptx-span-pwrite mv-nth fn-ptx-release-bufs))
           :do-not-induct t)))
(defthm fn-ptx-step1-len
  (implies (and (<= (fn-rtc-size (fn-ptx-q m)) 21))
           (<= (len (mv-nth 1 (fn-ptx-step1 m ev st q))) 29))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1) (fn-ptx-mk fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-ptx-committedp
fn-ptx-end fn-ptx-read fn-ptx-hash fn-ptx-start fn-ptx-answer fn-rtc-get fn-ptx-opened fn-ptx-wfp fn-ptx-evd+ fn-ptx-summary fn-ptx-kd-commit
fn-ptx-elen fn-ptx-nmsg fn-ptx-nspans fn-ptx-span-n fn-ptx-spans fn-ptx-spans-len fn-ptx-buf-len fn-ptx-gen fn-ptx-kd-frontier fn-ptx-pwrite fn-ptx-fsync fn-ptxa-extend fn-ptx-atom fn-ptx-span-pwrite mv-nth fn-ptx-release-bufs))
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
                (<= (fn-rtc-size (fn-ptx-evd m)) 49) (<= (fn-rtc-size (fn-ptx-ph m)) 1) (natp q) (equal (fn-rtc-get 0 ev) :opened))
           (<= (fn-rtc-size (car (fn-ptx-step1 m ev st q))) (+ 8500 (fn-ptx-acc-max-state))))
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1) (fn-ptx-mk fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-ptx-committedp
                                                   fn-ptx-end fn-ptx-read fn-ptx-hash fn-ptx-start fn-ptx-answer fn-rtc-get fn-ptx-opened fn-ptx-wfp fn-ptx-evd+ fn-ptx-summary fn-ptx-kd-commit
                                                   fn-ptx-elen fn-ptx-nmsg fn-ptx-nspans fn-ptx-span-n fn-ptx-spans fn-ptx-spans-len fn-ptx-buf-len fn-ptx-span-pwrite mv-nth fn-ptx-release-bufs fn-ptx-gen fn-ptx-kd-frontier fn-ptx-pwrite fn-ptx-fsync fn-ptxa-extend fn-ptx-atom))
           :do-not-induct t)))
(defthm fn-ptx-atom-size
  (equal (fn-rtc-size (fn-ptx-atom x)) 1)
  :hints (("Goal" :in-theory (enable fn-ptx-atom))))
(defthm fn-ptx-step1-size-handed
  (implies (and (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-geo m)) 7) (<= (fn-rtc-size (fn-ptx-kd m)) 75)
                (<= (fn-rtc-size (fn-ptx-cur m)) 15) (<= (fn-rtc-size (fn-ptx-acc m)) (fn-ptx-acc-max-state))
                (<= (fn-rtc-size (fn-ptx-b1 m)) 9) (<= (fn-rtc-size (fn-ptx-b3 m)) 9) (<= (fn-rtc-size (fn-ptx-hs m)) 4101)
                (<= (fn-rtc-size (fn-ptx-evd m)) 49) (<= (fn-rtc-size (fn-ptx-ph m)) 1) (natp q) (equal (fn-rtc-get 0 ev) :handed))
           (<= (fn-rtc-size (car (fn-ptx-step1 m ev st q))) (+ 8500 (fn-ptx-acc-max-state))))
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1) (fn-ptx-mk fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-ptx-committedp
                                                   fn-ptx-end fn-ptx-read fn-ptx-hash fn-ptx-start fn-ptx-answer fn-rtc-get fn-ptx-opened fn-ptx-wfp fn-ptx-evd+ fn-ptx-summary fn-ptx-kd-commit
                                                   fn-ptx-elen fn-ptx-nmsg fn-ptx-nspans fn-ptx-span-n fn-ptx-spans fn-ptx-spans-len fn-ptx-buf-len fn-ptx-span-pwrite mv-nth fn-ptx-release-bufs fn-ptx-gen fn-ptx-kd-frontier fn-ptx-pwrite fn-ptx-fsync fn-ptxa-extend fn-ptx-atom))
           :do-not-induct t)))
(defthm fn-ptx-step1-size-timer
  (implies (and (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-geo m)) 7) (<= (fn-rtc-size (fn-ptx-kd m)) 75)
                (<= (fn-rtc-size (fn-ptx-cur m)) 15) (<= (fn-rtc-size (fn-ptx-acc m)) (fn-ptx-acc-max-state))
                (<= (fn-rtc-size (fn-ptx-b1 m)) 9) (<= (fn-rtc-size (fn-ptx-b3 m)) 9) (<= (fn-rtc-size (fn-ptx-hs m)) 4101)
                (<= (fn-rtc-size (fn-ptx-evd m)) 49) (<= (fn-rtc-size (fn-ptx-ph m)) 1) (natp q) (equal (fn-rtc-get 0 ev) :timer))
           (<= (fn-rtc-size (car (fn-ptx-step1 m ev st q))) (+ 8500 (fn-ptx-acc-max-state))))
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1) (fn-ptx-mk fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-ptx-committedp
                                                   fn-ptx-end fn-ptx-read fn-ptx-hash fn-ptx-start fn-ptx-answer fn-rtc-get fn-ptx-opened fn-ptx-wfp fn-ptx-evd+ fn-ptx-summary fn-ptx-kd-commit
                                                   fn-ptx-elen fn-ptx-nmsg fn-ptx-nspans fn-ptx-span-n fn-ptx-spans fn-ptx-spans-len fn-ptx-buf-len fn-ptx-span-pwrite mv-nth fn-ptx-release-bufs fn-ptx-gen fn-ptx-kd-frontier fn-ptx-pwrite fn-ptx-fsync fn-ptxa-extend fn-ptx-atom))
           :do-not-induct t)))
(defthm fn-ptx-step1-size-extend
  (implies (and (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-geo m)) 7) (<= (fn-rtc-size (fn-ptx-kd m)) 75)
                (<= (fn-rtc-size (fn-ptx-cur m)) 15) (<= (fn-rtc-size (fn-ptx-acc m)) (fn-ptx-acc-max-state))
                (<= (fn-rtc-size (fn-ptx-b1 m)) 9) (<= (fn-rtc-size (fn-ptx-b3 m)) 9) (<= (fn-rtc-size (fn-ptx-hs m)) 4101)
                (<= (fn-rtc-size (fn-ptx-evd m)) 49) (<= (fn-rtc-size (fn-ptx-ph m)) 1) (natp q) (equal (fn-rtc-get 0 ev) :extend))
           (<= (fn-rtc-size (car (fn-ptx-step1 m ev st q))) (+ 8500 (fn-ptx-acc-max-state))))
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1) (fn-ptx-mk fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-ptx-committedp
                                                   fn-ptx-end fn-ptx-read fn-ptx-hash fn-ptx-start fn-ptx-answer fn-rtc-get fn-ptx-opened fn-ptx-wfp fn-ptx-evd+ fn-ptx-summary fn-ptx-kd-commit
                                                   fn-ptx-elen fn-ptx-nmsg fn-ptx-nspans fn-ptx-span-n fn-ptx-spans fn-ptx-spans-len fn-ptx-buf-len fn-ptx-span-pwrite mv-nth fn-ptx-release-bufs fn-ptx-gen fn-ptx-kd-frontier fn-ptx-pwrite fn-ptx-fsync fn-ptxa-extend fn-ptx-atom))
           :do-not-induct t)))
(defthm fn-ptx-step1-size-fsync
  (implies (and (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-geo m)) 7) (<= (fn-rtc-size (fn-ptx-kd m)) 75)
                (<= (fn-rtc-size (fn-ptx-cur m)) 15) (<= (fn-rtc-size (fn-ptx-acc m)) (fn-ptx-acc-max-state))
                (<= (fn-rtc-size (fn-ptx-b1 m)) 9) (<= (fn-rtc-size (fn-ptx-b3 m)) 9) (<= (fn-rtc-size (fn-ptx-hs m)) 4101)
                (<= (fn-rtc-size (fn-ptx-evd m)) 49) (<= (fn-rtc-size (fn-ptx-ph m)) 1) (natp q) (equal (fn-rtc-get 0 ev) :fsync))
           (<= (fn-rtc-size (car (fn-ptx-step1 m ev st q))) (+ 8500 (fn-ptx-acc-max-state))))
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1) (fn-ptx-mk fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-ptx-committedp
                                                   fn-ptx-end fn-ptx-read fn-ptx-hash fn-ptx-start fn-ptx-answer fn-rtc-get fn-ptx-opened fn-ptx-wfp fn-ptx-evd+ fn-ptx-summary fn-ptx-kd-commit
                                                   fn-ptx-elen fn-ptx-nmsg fn-ptx-nspans fn-ptx-span-n fn-ptx-spans fn-ptx-spans-len fn-ptx-buf-len fn-ptx-span-pwrite mv-nth fn-ptx-release-bufs fn-ptx-gen fn-ptx-kd-frontier fn-ptx-pwrite fn-ptx-fsync fn-ptxa-extend fn-ptx-atom))
           :do-not-induct t)))
(defthm fn-ptx-step1-size-pwrite
  (implies (and (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-geo m)) 7) (<= (fn-rtc-size (fn-ptx-kd m)) 75)
                (<= (fn-rtc-size (fn-ptx-cur m)) 15) (<= (fn-rtc-size (fn-ptx-acc m)) (fn-ptx-acc-max-state))
                (<= (fn-rtc-size (fn-ptx-b1 m)) 9) (<= (fn-rtc-size (fn-ptx-b3 m)) 9) (<= (fn-rtc-size (fn-ptx-hs m)) 4101)
                (<= (fn-rtc-size (fn-ptx-evd m)) 49) (<= (fn-rtc-size (fn-ptx-ph m)) 1) (natp q) (equal (fn-rtc-get 0 ev) :pwrite))
           (<= (fn-rtc-size (car (fn-ptx-step1 m ev st q))) (+ 8500 (fn-ptx-acc-max-state))))
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1) (fn-ptx-mk fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-ptx-committedp
                                                   fn-ptx-end fn-ptx-read fn-ptx-hash fn-ptx-start fn-ptx-answer fn-rtc-get fn-ptx-opened fn-ptx-wfp fn-ptx-evd+ fn-ptx-summary fn-ptx-kd-commit
                                                   fn-ptx-elen fn-ptx-nmsg fn-ptx-nspans fn-ptx-span-n fn-ptx-spans fn-ptx-spans-len fn-ptx-buf-len fn-ptx-span-pwrite mv-nth fn-ptx-release-bufs fn-ptx-gen fn-ptx-kd-frontier fn-ptx-pwrite fn-ptx-fsync fn-ptxa-extend fn-ptx-atom))
           :do-not-induct t)))
(defthm fn-ptx-step1-size-hand
  (implies (and (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-geo m)) 7) (<= (fn-rtc-size (fn-ptx-kd m)) 75)
                (<= (fn-rtc-size (fn-ptx-cur m)) 15) (<= (fn-rtc-size (fn-ptx-acc m)) (fn-ptx-acc-max-state))
                (<= (fn-rtc-size (fn-ptx-b1 m)) 9) (<= (fn-rtc-size (fn-ptx-b3 m)) 9) (<= (fn-rtc-size (fn-ptx-hs m)) 4101)
                (<= (fn-rtc-size (fn-ptx-evd m)) 49) (<= (fn-rtc-size (fn-ptx-ph m)) 1) (natp q) (equal (fn-rtc-get 0 ev) :hand))
           (<= (fn-rtc-size (car (fn-ptx-step1 m ev st q))) (+ 8500 (fn-ptx-acc-max-state))))
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1) (fn-ptx-mk fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-ptx-committedp
                                                   fn-ptx-end fn-ptx-read fn-ptx-hash fn-ptx-start fn-ptx-answer fn-rtc-get fn-ptx-opened fn-ptx-wfp fn-ptx-evd+ fn-ptx-summary fn-ptx-kd-commit
                                                   fn-ptx-elen fn-ptx-nmsg fn-ptx-nspans fn-ptx-span-n fn-ptx-spans fn-ptx-spans-len fn-ptx-buf-len fn-ptx-span-pwrite mv-nth fn-ptx-release-bufs fn-ptx-gen fn-ptx-kd-frontier fn-ptx-pwrite fn-ptx-fsync fn-ptxa-extend fn-ptx-atom))
           :do-not-induct t)))
(defthm fn-ptx-step1-size-other
  (implies (and (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-geo m)) 7) (<= (fn-rtc-size (fn-ptx-kd m)) 75)
                (<= (fn-rtc-size (fn-ptx-cur m)) 15) (<= (fn-rtc-size (fn-ptx-acc m)) (fn-ptx-acc-max-state))
                (<= (fn-rtc-size (fn-ptx-b1 m)) 9) (<= (fn-rtc-size (fn-ptx-b3 m)) 9) (<= (fn-rtc-size (fn-ptx-hs m)) 4101)
                (<= (fn-rtc-size (fn-ptx-evd m)) 49) (<= (fn-rtc-size (fn-ptx-ph m)) 1) (natp q) (not (member-equal (fn-rtc-get 0 ev) '(:opened :handed :timer :extend :fsync :pwrite :hand))))
           (<= (fn-rtc-size (car (fn-ptx-step1 m ev st q))) (+ 8500 (fn-ptx-acc-max-state))))
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1) (fn-ptx-mk fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-ptx-committedp
                                                   fn-ptx-end fn-ptx-read fn-ptx-hash fn-ptx-start fn-ptx-answer fn-rtc-get fn-ptx-opened fn-ptx-wfp fn-ptx-evd+ fn-ptx-summary fn-ptx-kd-commit
                                                   fn-ptx-elen fn-ptx-nmsg fn-ptx-nspans fn-ptx-span-n fn-ptx-spans fn-ptx-spans-len fn-ptx-buf-len fn-ptx-span-pwrite mv-nth fn-ptx-release-bufs fn-ptx-gen fn-ptx-kd-frontier fn-ptx-pwrite fn-ptx-fsync fn-ptxa-extend fn-ptx-atom))
           :do-not-induct t)))
(defthm fn-ptx-step1-size
  (implies (and (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-geo m)) 7) (<= (fn-rtc-size (fn-ptx-kd m)) 75)
                (<= (fn-rtc-size (fn-ptx-cur m)) 15) (<= (fn-rtc-size (fn-ptx-acc m)) (fn-ptx-acc-max-state))
                (<= (fn-rtc-size (fn-ptx-b1 m)) 9) (<= (fn-rtc-size (fn-ptx-b3 m)) 9) (<= (fn-rtc-size (fn-ptx-hs m)) 4101)
                (<= (fn-rtc-size (fn-ptx-evd m)) 49) (<= (fn-rtc-size (fn-ptx-ph m)) 1) (natp q))
           (<= (fn-rtc-size (car (fn-ptx-step1 m ev st q))) (+ 8500 (fn-ptx-acc-max-state))))
  :hints (("Goal" :in-theory (disable fn-ptx-step1 fn-rtc-get fn-ptx-q fn-ptx-geo fn-ptx-kd fn-ptx-cur fn-ptx-acc fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-ph)
           :do-not-induct t :use (fn-ptx-step1-size-opened fn-ptx-step1-size-handed fn-ptx-step1-size-timer fn-ptx-step1-size-extend
                 fn-ptx-step1-size-fsync fn-ptx-step1-size-pwrite fn-ptx-step1-size-hand fn-ptx-step1-size-other))))
(defthm fn-ptx-step1-size-lin
  (implies (and (<= (fn-rtc-size (fn-ptx-q m)) 21) (<= (fn-rtc-size (fn-ptx-geo m)) 7) (<= (fn-rtc-size (fn-ptx-kd m)) 75)
                (<= (fn-rtc-size (fn-ptx-cur m)) 15) (<= (fn-rtc-size (fn-ptx-acc m)) (fn-ptx-acc-max-state))
                (<= (fn-rtc-size (fn-ptx-b1 m)) 9) (<= (fn-rtc-size (fn-ptx-b3 m)) 9) (<= (fn-rtc-size (fn-ptx-hs m)) 4101)
                (<= (fn-rtc-size (fn-ptx-evd m)) 49) (<= (fn-rtc-size (fn-ptx-ph m)) 1) (natp q))
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
                                                 fn-ptx-unit fn-ptx-buf-h fn-ptx-buf-g fn-ptx-buf-len fn-ptx-spans fn-ptx-spans-len fn-ptx-span-pwrite min max floor fn-olr-extension-needed-p fn-olr-extension-target fn-ptx-pad-len fn-ptx-kd-frontier fn-ptx-timer fn-ptxa-extend fn-ptx-pwrite fn-ptx-fsync))
           :do-not-induct t)))

(defthm fn-ptx-opened-uncommitted
  (not (fn-ptx-committedp (fn-ptx-opened kd ext geo)))
  :hints (("Goal" :in-theory (e/d (fn-ptx-opened) (fn-ptx-mk fn-ptx-committedp)))))
(defthm fn-ptx-step1-committed
  (implies (fn-ptx-committedp (car (fn-ptx-step1 m ev st q)))
           (and (equal (fn-ptx-ph m) :committing) (fn-rtc-fsync-done-p ev)))
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1 fn-rtc-fsync-done-p) (fn-ptx-mk fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-ptx-committedp
                                                   fn-ptx-read fn-ptx-hash fn-ptx-opened fn-ptx-wfp fn-ptx-evd+ fn-ptx-kd-commit fn-ptx-answer fn-ptx-start fn-ptx-end fn-rtc-get
                                                   fn-ptx-elen fn-ptx-nmsg fn-ptx-nspans fn-ptx-span-n fn-ptx-spans fn-ptx-spans-len fn-ptx-buf-len fn-ptx-span-pwrite mv-nth fn-ptx-release-bufs fn-ptx-gen fn-ptx-kd-frontier fn-ptx-pwrite fn-ptx-fsync fn-ptxa-extend fn-ptx-atom fn-ptx-summary))
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
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1 fn-ptx-fsync fn-ptx-timer fn-ptx-pwrite fn-ptxa-extend)
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
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1 fn-ptx-fsync fn-ptx-timer fn-ptx-pwrite fn-ptxa-extend)
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
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1 fn-ptx-fsync fn-ptx-timer fn-ptx-pwrite fn-ptxa-extend)
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
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1 fn-ptx-fsync fn-ptx-timer fn-ptx-pwrite fn-ptxa-extend)
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
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1 fn-ptx-fsync fn-ptx-timer fn-ptx-pwrite fn-ptxa-extend)
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
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1 fn-ptx-fsync fn-ptx-timer fn-ptx-pwrite fn-ptxa-extend)
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
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1 fn-ptx-fsync fn-ptx-timer fn-ptx-pwrite fn-ptxa-extend)
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
(defthm fn-ptx-extend-nohand (not (fn-ptx-submit-hand-p (fn-ptxa-extend ext nxt)))
  :hints (("Goal" :in-theory (enable fn-ptx-submit-hand-p fn-ptxa-extend fn-rtc-get))))
(defthm fn-ptx-span-pwrite-nohand (not (fn-ptx-submit-hand-p (fn-ptx-span-pwrite i m front id inc st)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn-ptx-submit-hand-p fn-ptx-span-pwrite-kind fn-ptx-span-pwrite-head (:executable-counterpart equal) (:executable-counterpart not))))))

(defthm fn-ptx-hash-cur-code
  (let ((cc (fn-ptx-cur-code m (mv-nth 1 (fn-ptx-hash m q id inc st)))))
    (or (null cc) (equal cc 1)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ptx-hash) (fn-ptx-end fn-ptx-mk fn-ptx-absorb fn-ptx-finish-digest fn-ptx-ph fn-ptx-k fn-ptx-q fn-ptx-kd fn-ptx-ext fn-ptx-nxt fn-ptx-b1 fn-ptx-b3 fn-ptx-hs fn-ptx-evd fn-ptx-geo fn-ptx-acc fn-ptx-cur fn-rtc-get fn-ptx-committedp
                                   fn-ptx-unit fn-ptx-buf-h fn-ptx-buf-g fn-ptx-buf-len fn-ptx-spans fn-ptx-spans-len fn-ptx-span-pwrite min max floor fn-olr-extension-needed-p fn-olr-extension-target fn-ptx-pad-len fn-ptx-kd-frontier fn-ptx-timer fn-ptxa-extend fn-ptx-pwrite fn-ptx-fsync
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
  :hints (("Goal" :in-theory (e/d (fn-ptx-step1 fn-ptx-fsync fn-ptx-timer fn-ptx-pwrite fn-ptxa-extend)
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
