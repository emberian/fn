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
(defconst *fn-ptx-codes* '((:posted . 0) (:refused . 1) (:uncertain . 2) (:busy . 3)))
(defun fn-ptx-code (o) (nfix (cdr (assoc-eq o *fn-ptx-codes*))))

; -----------------------------------------------------------------------------
; The acceptance, constrained and streaming (the seam with M's admission gate):
; begun at the record's txid, fed the head's octets window by window, ended with
; the article body's length, it answers whether the article is accepted and the
; record's prefix PRE (the record fields before the article, the article's
; byte-string header, the injected header block) and suffix SUF (the fields after
; the article).  Its state and outputs are bounded by constants of the gate's code.
(encapsulate
  (((fn-ptx-acc-begin *) => *)
   ((fn-ptx-acc-feed * *) => *)
   ((fn-ptx-acc-end * *) => (mv * * *))
   ((fn-ptx-acc-max-state) => *)
   ((fn-ptx-acc-out-max) => *))
  (local (defun fn-ptx-acc-begin (txid) (declare (ignore txid)) nil))
  (local (defun fn-ptx-acc-feed (a octets) (declare (ignore a octets)) nil))
  (local (defun fn-ptx-acc-end (a blen) (declare (ignore a blen)) (mv t nil nil)))
  (local (defun fn-ptx-acc-max-state () 1))
  (local (defun fn-ptx-acc-out-max () 0))
  (defthm fn-ptx-acc-max-state-natp (natp (fn-ptx-acc-max-state)) :rule-classes :type-prescription)
  (defthm fn-ptx-acc-out-max-natp (natp (fn-ptx-acc-out-max)) :rule-classes :type-prescription)
  (defthm fn-ptx-acc-begin-bounded (<= (fn-rtc-size (fn-ptx-acc-begin txid)) (fn-ptx-acc-max-state))
    :rule-classes :linear)
  (defthm fn-ptx-acc-feed-bounded (<= (fn-rtc-size (fn-ptx-acc-feed a octets)) (fn-ptx-acc-max-state))
    :rule-classes :linear)
  (defthm fn-ptx-acc-end-shape
    (mv-let (ok pre suf) (fn-ptx-acc-end a blen)
      (declare (ignore ok))
      (and (fn-cbor-octet-listp pre) (fn-cbor-octet-listp suf)
           (<= (len pre) (fn-ptx-acc-out-max)) (<= (len suf) (fn-ptx-acc-out-max))))
    :rule-classes nil))

; -----------------------------------------------------------------------------
; State: (ph k cur q kd ext nxt b1 b3 hs committed evd geo acc).
;   cur  (fid finc bp len hoff txid): the poster's slot, its handed buffer BP holding
;        the article at [0,len); HOFF the head's length once found (while :reading,
;        the position the head search has reached); the record's txid
;   q    waiting posts (fid finc bp len), at most *fn-ptx-k*
;   kd   the log kernel's projection (count last frontier next-txid acked): what
;        fn-ptd's actions read of fn-lgk, without COMMITTED's elements
;   ext nxt  fn-ptd's extent and the sealed extent
;   b1 b3  owner workspaces (h g len): b1 = frame header ++ chain field ++ PRE,
;        b3 = SUF ++ trailer (SUF alone until the digest is known)
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
; kind, (:opened ID INC DATA) with DATA = (KD EXT GEO), routed once per incarnation to
; the static slot; the host emits it after the store opens, before the listener accepts.
(defun fn-ptxa-opened-data (ev) (fn-rtc-get 3 ev))

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
(defun fn-ptx-buf-h (b) (nfix (fn-rtc-get 0 b)))
(defun fn-ptx-buf-g (b) (nfix (fn-rtc-get 1 b)))
(defun fn-ptx-buf-len (b) (nfix (fn-rtc-get 2 b)))

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
(defconst *fn-ptx-budgets* '(1  1 13  21 75 1   1   7  7  4101 1         49  7))
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
(defun fn-ptx-wf-cost () (+ 4284 (fn-ptx-acc-max-state)))
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
; The entry's protected prefix M = b1 ++ article ++ SUF, read through the view:
; b1 = frame header ++ chain field ++ PRE (owner buffer H1, L1 octets), the article
; [0, alen) of the poster's buffer BP, SUF (owner buffer H3, LS octets).
(defun fn-ptx-msg-byte (i h1 l1 bp alen h3 id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let ((i (nfix i)) (l1 (nfix l1)) (alen (nfix alen)))
    (cond ((< i l1) (fn-ptx-byte h1 i id inc fn-rtc-st))
          ((< i (+ l1 alen)) (fn-ptx-byte bp (- i l1) id inc fn-rtc-st))
          (t (fn-ptx-byte h3 (- i (+ l1 alen)) id inc fn-rtc-st)))))
(defun fn-ptx-msg-range (i n h1 l1 bp alen h3 id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :measure (nfix n)))
  (if (zp n) nil
    (cons (fn-ptx-msg-byte i h1 l1 bp alen h3 id inc fn-rtc-st)
          (fn-ptx-msg-range (+ 1 (nfix i)) (- n 1) h1 l1 bp alen h3 id inc fn-rtc-st))))

; The digest's held state (pos stack) over a message of N octets: absorb up to
; NW windows; a window is pushed only when more than a window remains after it
; (fn-b3-window-outs' rule), the last one by the finish.
(defun fn-ptx-absorb (nw pos st n h1 l1 bp alen h3 id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :measure (nfix nw)))
  (let ((pos (nfix pos)) (n (nfix n)))
    (if (or (zp nw) (<= n (+ pos *fn-ptx-window*)))
        (mv pos st)
      (fn-ptx-absorb (- nw 1) (+ pos *fn-ptx-window*)
                     (fn-b3-cv-push *fn-b3-iv* 0 *fn-ptx-wexp*
                                    (fn-b3-node *fn-b3-iv*
                                                (fn-ptx-msg-range pos *fn-ptx-window* h1 l1 bp alen h3 id inc fn-rtc-st)
                                                (floor pos 1024) 0)
                                    st)
                     n h1 l1 bp alen h3 id inc fn-rtc-st))))
(defun fn-ptx-finish-digest (pos st n h1 l1 bp alen h3 id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let ((pos (nfix pos)))
    (fn-b3-output-root
     (fn-b3-stack-fold *fn-b3-iv* 0
                       (fn-b3-cv-push *fn-b3-iv* 0 *fn-ptx-wexp*
                                      (fn-b3-node *fn-b3-iv*
                                                  (fn-ptx-msg-range pos (- (nfix n) pos) h1 l1 bp alen h3 id inc fn-rtc-st)
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
                 (list (fn-ptx-cur-fid p) (fn-ptx-cur-finc p) (fn-ptx-cur-bp p) (fn-ptx-cur-len p) 0 (fn-ptx-kd-txid kd))
                 q kd ext ext nil nil nil committed nil geo (fn-ptx-acc-begin (fn-ptx-kd-txid kd)))
      (list (fn-ptx-timer))
      1))

; End the current transaction with outcome O: release b1 and b3, answer, then
; start the next waiting post unless FENCED (then every waiting post is refused).
(defun fn-ptx-release-bufs (m id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
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
(defun fn-ptx-l1 (m) (fn-ptx-buf-len (fn-ptx-b1 m)))
(defun fn-ptx-alen (m) (fn-ptx-cur-len (fn-ptx-cur m)))
(defun fn-ptx-l3 (m) (fn-ptx-buf-len (fn-ptx-b3 m)))           ; SUF ++ trailer once hashed
(defun fn-ptx-elen (m) (+ (fn-ptx-l1 m) (fn-ptx-alen m) (fn-ptx-l3 m) (nfix (fn-rtc-get 2 (fn-ptx-hs m)))))

(defun fn-ptx-atom (x) (if (consp x) nil x))
(defun fn-ptx-summary (ev)
  (list (fn-ptx-atom (fn-rtc-get 0 ev)) (fn-ptx-atom (fn-rtc-get 0 (fn-rtc-get 1 ev)))
        (fn-ptx-atom (fn-rtc-get 1 (fn-rtc-get 1 ev)))))
(defun fn-ptx-evd+ (m ev) (append (true-list-fix (fn-ptx-evd m)) (list (fn-ptx-summary ev))))

; The reading step: search the head in [pos, pos + w) and feed those octets to the
; acceptance; at the head's end, end the acceptance and lay out the entry's
; workspaces, then hash.  W is the quantum (at least a window).
(defun fn-ptx-read (m q id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let* ((cur (fn-ptx-cur m)) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m))
         (bp (fn-ptx-cur-bp cur)) (len (fn-ptx-cur-len cur)) (pos (fn-ptx-cur-hoff cur))
         (lim (min len (fn-ptx-hmax m)))
         (w (max *fn-ptx-window* (nfix q)))
         (e (fn-ptx-head-end bp pos (min lim (+ pos w 3)) id inc fn-rtc-st))
         (m0 (fn-ptx-chg m :committed nil)))
    (cond
     (e
      (let ((a (fn-ptx-acc-feed (fn-ptx-acc m) (fn-ptx-range bp pos (- e pos) id inc fn-rtc-st))))
        (mv-let (ok pre suf) (fn-ptx-acc-end a (- len e))
          (let* ((h1 (fn-ptx-free 0 nil id inc fn-rtc-st))
                 (h3 (fn-ptx-free 0 h1 id inc fn-rtc-st))
                 (rlen (+ (len pre) len (len suf)))
                 (b1 (append (fn-ptx-frame-header rlen) (fn-ptx-kd-last kd) pre))
                 (cost (+ w 3 (* 2 (fn-ptx-acc-out-max)) 64)))
            (if (not (and ok h1 h3 (<= (+ 32 rlen) (fn-ptx-fmax m))
                          (<= (len b1) (fn-ptx-cap h1 id inc fn-rtc-st))
                          (<= (+ 32 (len suf)) (fn-ptx-cap h3 id inc fn-rtc-st))))
                (mv-let (m2 r2 c2) (fn-ptx-end m0 :refused kd ext nil nil id inc fn-rtc-st)
                  (mv m2 r2 (+ cost c2)))
              (let ((g1 (+ 1 (fn-ptx-gen h1 id inc fn-rtc-st))) (g3 (+ 1 (fn-ptx-gen h3 id inc fn-rtc-st))))
                (mv (fn-ptx-chg m0 :ph :hashing :k 0
                                :cur (list (fn-ptx-cur-fid cur) (fn-ptx-cur-finc cur) bp len e (fn-ptx-cur-txid cur))
                                :b1 (list h1 g1 (len b1)) :b3 (list h3 g3 (len suf)) :hs (list 0 nil) :acc nil)
                    (list (list :acquire h1) (list :write h1 g1 0 b1)
                          (list :acquire h3) (list :write h3 g3 0 suf)
                          (fn-ptx-timer))
                    cost)))))))
     ((< (+ pos w 3) lim)
      ;; no head end yet: feed the window, continue
      (mv (fn-ptx-chg m0 :cur (list (fn-ptx-cur-fid cur) (fn-ptx-cur-finc cur) bp len (+ pos w) (fn-ptx-cur-txid cur))
                      :acc (fn-ptx-acc-feed (fn-ptx-acc m) (fn-ptx-range bp pos w id inc fn-rtc-st)))
          (list (fn-ptx-timer))
          (+ w 3)))
     (t
      ;; no head within the head limit: refused before any log action
      (mv-let (m2 r2 c2) (fn-ptx-end m0 :refused kd ext nil nil id inc fn-rtc-st)
        (mv m2 r2 (+ w 3 c2)))))))

; The hashing step: up to NW windows, then the trailer and fn-ptd's begin.
(defun fn-ptx-hash (m q id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let* ((cur (fn-ptx-cur m)) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m))
         (b1 (fn-ptx-b1 m)) (b3 (fn-ptx-b3 m)) (l1 (fn-ptx-l1 m)) (alen (fn-ptx-alen m)) (ls (fn-ptx-l3 m))
         (nmsg (+ l1 alen ls)) (hs (fn-ptx-hs m))
         (nw (min *fn-ptx-nw-max* (max 1 (floor (nfix q) *fn-ptx-window*))))
         (m0 (fn-ptx-chg m :committed nil)))
    (mv-let (pos st)
      (fn-ptx-absorb nw (fn-rtc-get 0 hs) (fn-rtc-get 1 hs) nmsg (fn-ptx-buf-h b1) l1
                     (fn-ptx-cur-bp cur) alen (fn-ptx-buf-h b3) id inc fn-rtc-st)
      (if (< (+ pos *fn-ptx-window*) nmsg)
          (mv (fn-ptx-chg m0 :hs (list pos st)) (list (fn-ptx-timer)) (* nw *fn-ptx-window*))
        ;; the last window: the trailer, then fn-ptd's begin.  The padding is not
        ;; written: the extent past the frontier reads zeros (fn-lgk-relp clause 2).
        (let* ((trailer (fn-ptx-finish-digest pos st nmsg (fn-ptx-buf-h b1) l1 (fn-ptx-cur-bp cur)
                                              alen (fn-ptx-buf-h b3) id inc fn-rtc-st))
               (pad (fn-ptx-pad-len (+ nmsg 32) (fn-ptx-unit m)))
               (b3x (list (fn-ptx-buf-h b3) (fn-ptx-buf-g b3) (+ ls 32)))
               (elen (+ nmsg 32 pad))
               (front (fn-ptx-kd-frontier kd))
               (wr (list :write (fn-ptx-buf-h b3) (fn-ptx-buf-g b3) ls trailer))
               (cost (+ (* nw *fn-ptx-window*) *fn-ptx-window* 32)))
          (if (fn-olr-extension-needed-p front elen ext (fn-ptx-unit m))
              (let ((nx (fn-olr-extension-target front elen ext (fn-ptx-unit m))))
                (mv (fn-ptx-chg m0 :ph :extending :k 0 :nxt nx :b3 b3x :hs (list nmsg trailer pad) :evd nil)
                    (list wr (fn-ptxa-extend ext nx)) cost))
            (mv (fn-ptx-chg m0 :ph :payload-writing :k 0 :nxt ext :b3 b3x :hs (list nmsg trailer pad) :evd nil)
                (list wr (fn-ptx-pwrite (fn-ptx-buf-h b1) (fn-ptx-buf-g b1) 0 l1 front)) cost)))))))

; The step on a well-formed state: (mv m2 requests cost).
(defun fn-ptx-step1 (m ev fn-rtc-st q)
  (declare (xargs :stobjs fn-rtc-st))
  (let* ((id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev))
         (kind (fn-rtc-get 0 ev)) (out (fn-rtc-get 1 ev)) (tag (fn-rtc-get 0 out)) (n (fn-rtc-get 1 out))
         (ph (fn-ptx-ph m)) (cur (fn-ptx-cur m)) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m)) (nxt (fn-ptx-nxt m))
         (m0 (fn-ptx-chg m :committed nil)))
    (cond
     ;; the store opened: the kernel projection, the extent and the geometry
     ((eq kind :opened)
      (if (eq ph :closed)
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
          (let ((b1 (fn-ptx-b1 m)))
            (mv (fn-ptx-chg m0 :ph :payload-writing :k 0 :evd (fn-ptx-evd+ m ev))
                (list (fn-ptx-pwrite (fn-ptx-buf-h b1) (fn-ptx-gen (fn-ptx-buf-h b1) id inc fn-rtc-st) 0 (fn-ptx-l1 m)
                                     (fn-ptx-kd-frontier kd)))
                1))
        (fn-ptx-end m0 :refused kd ext t nil id inc fn-rtc-st)))
     ;; the entry's writes: any outcome but the whole write is uncertain and fences
     ((and (eq ph :payload-writing) (eq kind :pwrite))
      (let ((want (if (zp (fn-ptx-k m)) (fn-ptx-l1 m) (fn-ptx-alen m)))
            (front (fn-ptx-kd-frontier kd)))
        (cond ((not (and (eq tag :done) (equal n want)))
               (fn-ptx-end m0 :uncertain kd ext t nil id inc fn-rtc-st))
              ((zp (fn-ptx-k m))
               (let ((bp (fn-ptx-cur-bp cur)))
                 (mv (fn-ptx-chg m0 :k 1 :evd (fn-ptx-evd+ m ev))
                     (list (fn-ptx-pwrite bp (fn-ptx-gen bp id inc fn-rtc-st) 0 (fn-ptx-alen m)
                                          (+ front (fn-ptx-l1 m))))
                     1)))
              (t
               (let ((b3 (fn-ptx-b3 m)))
                 (mv (fn-ptx-chg m0 :ph :log-writing :evd (fn-ptx-evd+ m ev))
                     (list (fn-ptx-pwrite (fn-ptx-buf-h b3) (fn-ptx-gen (fn-ptx-buf-h b3) id inc fn-rtc-st) 0 (fn-ptx-l3 m)
                                          (+ front (fn-ptx-l1 m) (fn-ptx-alen m))))
                     1))))))
     ((and (eq ph :log-writing) (eq kind :pwrite))
      (if (and (eq tag :done) (equal n (fn-ptx-l3 m)))
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
(defun fn-ptx-c () (+ (fn-ptx-wf-cost) (* 2 *fn-ptx-window*) 512 (* 4 (fn-ptx-acc-out-max))))
(defun fn-ptx-max-reqs () 32)
(defun fn-ptx-max-state () (+ 8500 (fn-ptx-acc-max-state)))

; -----------------------------------------------------------------------------
; The keystones' predicates (packet draft 3).  Each keystone is a theorem over
; fn-ptx-step stated with these; the scratch sweeps evaluate their generated
; list twins (fn-ptxl-*) after every owner completion.

(defun fn-ptx-done-p (x kind n)
  (and (equal (fn-rtc-get 0 x) kind) (equal (fn-rtc-get 1 x) :done) (or (null n) (equal (fn-rtc-get 2 x) n))))

; The evidence a :posted answer rests on: [extend fsync] pwrite(l1) pwrite(alen)
; pwrite(l3) fsync, each :done and whole, in that order.
(defun fn-ptx-strip-ext (evd)
  (if (and (fn-ptx-done-p (fn-rtc-get 0 evd) :extend nil) (fn-ptx-done-p (fn-rtc-get 1 evd) :fsync nil))
      (cddr evd)
    evd))
(defun fn-ptx-entry-evd-p (evd m nwrites)
  ; NWRITES completed entry writes, each :done and whole: l1, alen, l3
  (and (true-listp evd) (equal (len evd) (nfix nwrites))
       (or (< (nfix nwrites) 1) (fn-ptx-done-p (fn-rtc-get 0 evd) :pwrite (fn-ptx-l1 m)))
       (or (< (nfix nwrites) 2) (fn-ptx-done-p (fn-rtc-get 1 evd) :pwrite (fn-ptx-alen m)))
       (or (< (nfix nwrites) 3) (fn-ptx-done-p (fn-rtc-get 2 evd) :pwrite (fn-ptx-l3 m)))))
(defun fn-ptx-posted-evidence-p (evd m)
  (let ((e (fn-ptx-strip-ext evd)))
    (and (equal (len e) 4)
         (fn-ptx-entry-evd-p (take 3 e) m 3)
         (fn-ptx-done-p (fn-rtc-get 3 e) :fsync nil))))

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
         (nmsg (+ (fn-ptx-l1 m) (fn-ptx-alen m) (fn-ptx-l3 m))))
    (and (fn-ptx-wfp m)
         (< (fn-ptx-fmax m) (expt 2 64))
         (case ph
           ((:closed :idle :reading :hashing :extending :fenced) (null evd))
           (:extsyncing (and (true-listp evd) (equal (len evd) 1) (fn-ptx-done-p (car evd) :extend nil)))
           (:payload-writing (and (<= (fn-ptx-k m) 1) (fn-ptx-entry-evd-p rest m (fn-ptx-k m))))
           (:log-writing (fn-ptx-entry-evd-p rest m 2))
           (:committing (fn-ptx-entry-evd-p rest m 3))
           (otherwise nil))
         (implies (equal ph :hashing)
                  (and (natp pos) (equal (mod pos *fn-ptx-window*) 0) (< pos nmsg)
                       (<= nmsg (+ 10 (fn-ptx-fmax m)))
                       (fn-ptx-stack-bits-p (fn-rtc-get 1 hs) (floor pos *fn-ptx-window*) 0))))))

; The codes the requests write at octet 0 of handed-back buffers: ((h code) ...).
(defun fn-ptx-codes-to (reqs)
  (if (consp reqs)
      (let ((r (car reqs)))
        (if (and (eq (fn-rtc-get 0 r) :write) (equal (fn-rtc-get 3 r) 0) (equal (len (fn-rtc-get 4 r)) 1))
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
; head limit, the hashing at the frame bound, six log actions); a completion of
; the kind the phase waits for lowers it.
(defun fn-ptx-post-bound (m)
  (+ 9 (ceiling (fn-ptx-hmax m) *fn-ptx-window*) (ceiling (+ 10 (fn-ptx-fmax m)) *fn-ptx-window*)))
(defun fn-ptx-rem (m)
  (let* ((ph (fn-ptx-ph m)) (nmsg (+ (fn-ptx-l1 m) (fn-ptx-alen m) (fn-ptx-l3 m)))
         (hashb (+ 7 (ceiling (+ 10 (fn-ptx-fmax m)) *fn-ptx-window*))))
    (case ph
      (:reading (+ hashb 1 (ceiling (nfix (- (min (fn-ptx-alen m) (fn-ptx-hmax m)) (fn-ptx-cur-hoff (fn-ptx-cur m))))
                                    *fn-ptx-window*)))
      (:hashing (+ 6 1 (ceiling (nfix (- nmsg (nfix (fn-rtc-get 0 (fn-ptx-hs m))))) *fn-ptx-window*)))
      (:extending 6) (:extsyncing 5) (:payload-writing (- 4 (min 1 (fn-ptx-k m)))) (:log-writing 2) (:committing 1)
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
