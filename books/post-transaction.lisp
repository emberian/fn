; fn: the POST transaction machine (Builder P; RUNTIME-MODEL section 3 as ruled
; 2026-10-10: PAYLOAD_WRITING -> LOG_WRITING -> COMMITTING -> PUBLISHED, no payload
; barrier).  DRAFT: packet draft 2's definitions, admitted; the keystones P0-P6 are
; stated in the packet (build/post-runs/, the lane's scratch) and not yet proved, so
; this book is not in ACL2_BOOKS and certifies nothing of record.
;
; The owner, static slot 1 under contract v2.1, takes a poster's handed article
; buffer and writes one log entry from spans: b1 (frame header, chain field, the
; record's prefix P with the edited head) from an owner workspace, the body from the
; poster's buffer unmoved, b3 (the record's suffix S and the trailer) from a second
; workspace; the padding is never written (the extent past the frontier reads
; zeros).  The three writes are L's fn-ptd one record write (books/post-transaction-
; durable.lisp); :posted only on the barrier's (:done).  The digest is BLAKE3 over
; 1024-octet windows on the zero-delay timer (books/blake3-tree.lisp's held state).
; Geometry (unit fmax hmax) is the opened store's, never a constant (D27).
(in-package "ACL2")
(include-book "post-transaction-durable")
(include-book "runtime-contract-layer")
(include-book "blake3-tree")
(set-verify-guards-eagerness 0)

; -----------------------------------------------------------------------------
; Bounds and constants.
(defconst *fn-ptx-k* 2)              ; posts waiting, at most
(defconst *fn-ptx-lfile* 2)          ; the log segment's file reference
(defconst *fn-ptx-wexp* 0)           ; digest window = 1024 * 2^wexp octets
(defconst *fn-ptx-window* 1024)
; The step's constant charge: the timer step's finishing window and trailer.  The
; start's head work (scan up to HMAX, the b1 and S writes) is charged at its size:
; OWED, the start becomes a q-bounded continuation (packet section "Owed").
(defconst *fn-ptx-c* (+ (* 2 *fn-ptx-window*) 256))
; D27 (coordinator ruling 2026-10-10): no bound on data is a typed constant.  The
; geometry GEO = (unit fmax hmax) is the opened store's: UNIT the write unit (the
; profile's device page size or read at open), FMAX the log frame bound
; (fn-lg-batch-entry-bound once A's lane is on dev; until then the frame limit
; handed in at open), HMAX the head limit (the sealed profile's header limits plus
; the injected block's bound, M's term).
(defconst *fn-ptx-codes* '((:posted . 0) (:refused . 1) (:uncertain . 2) (:busy . 3)))
(defun fn-ptx-code (o) (nfix (cdr (assoc-eq o *fn-ptx-codes*))))

; -----------------------------------------------------------------------------
; The acceptance, constrained: from the head's octets, the body's length and the
; record's txid, the record's prefix P (everything before the body: the record
; fields before the article, the article's byte-string header, the edited head)
; and suffix S (the record fields after the article).  The record is
; P ++ body ++ S.  Instanced by the owner's acceptance (M's admission gate and
; filing) in landing 2; here only shape is assumed.
(encapsulate
  (((fn-ptx-accept * * *) => (mv * * *)))
  (local (defun fn-ptx-accept (head blen txid)
           (declare (ignore blen txid))
           (mv t (if (fn-cbor-octet-listp head) head nil) nil)))
  (defthm fn-ptx-accept-shape
    (mv-let (ok p s) (fn-ptx-accept head blen txid)
      (implies ok
               (and (fn-cbor-octet-listp p) (fn-cbor-octet-listp s)
                    (<= (len p) (+ 64 (* 2 (len head))))
                    (<= (len s) (+ 64 (len head))))))
    :rule-classes nil))

; -----------------------------------------------------------------------------
; State: (ph k cur q kd ext nxt b1 b3 hs committed evd), every field bounded.
;   cur  (fid finc bp len hoff txid): the poster's slot, its handed buffer BP holding
;        the article at [0,len), the body from HOFF, the record's txid
;   q    waiting posts (fid finc bp len), at most *fn-ptx-k*
;   kd   the log kernel's projection (count last frontier next-txid acked): what
;        fn-ptd's actions read of fn-lgk, without COMMITTED's elements
;   ext nxt  fn-ptd's extent and the sealed extent
;   b1 b3  owner workspaces (h g len): b1 = frame header ++ chain field ++ P,
;        b3 = S ++ trailer (S alone until the digest is known); padding is never written
;   hs   the digest's held state (pos stack): message octets absorbed, CV stack
;   evd  ghost: this transaction's completions (kind tag n), in order
(defun fn-ptx-mk (ph k cur q kd ext nxt b1 b3 hs committed evd geo)
  (list ph (nfix k) cur q kd (nfix ext) (nfix nxt) b1 b3 hs (and committed t) evd geo))
(defun fn-ptx-geo (m) (fn-rtc-get 12 m))
(defun fn-ptx-unit (m) (max 1 (nfix (fn-rtc-get 0 (fn-ptx-geo m)))))
(defun fn-ptx-fmax (m) (nfix (fn-rtc-get 1 (fn-ptx-geo m))))
(defun fn-ptx-hmax (m) (nfix (fn-rtc-get 2 (fn-ptx-geo m))))
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

(defun fn-ptx-kd-mk (count last frontier txid acked) (list (nfix count) last (nfix frontier) (nfix txid) (nfix acked)))
(defun fn-ptx-kd-count (kd) (nfix (fn-rtc-get 0 kd)))
(defun fn-ptx-kd-last (kd) (fn-rtc-get 1 kd))
(defun fn-ptx-kd-frontier (kd) (nfix (fn-rtc-get 2 kd)))
(defun fn-ptx-kd-txid (kd) (nfix (fn-rtc-get 3 kd)))
(defun fn-ptx-kd-acked (kd) (nfix (fn-rtc-get 4 kd)))

; The opened machine: idle over the open's kernel projection, at extent EXT.
(defun fn-ptx-opened (kd ext geo) (fn-ptx-mk :idle 0 nil nil kd ext ext nil nil nil nil nil geo))

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

; The head's length: the least i < min(len, head-max) - 3 with CR LF CR LF at
; [i, i+4), plus 4; nil when there is none.
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
; The entry's protected prefix M = b1 ++ body ++ S, read through the view:
; b1 = frame header ++ chain field ++ P (owner buffer H1, L1 octets), the body
; [hoff, len) of the poster's buffer BP, S (owner buffer H3, LS octets).
(defun fn-ptx-msg-byte (i h1 l1 bp hoff blen h3 id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let ((i (nfix i)) (l1 (nfix l1)) (blen (nfix blen)))
    (cond ((< i l1) (fn-ptx-byte h1 i id inc fn-rtc-st))
          ((< i (+ l1 blen)) (fn-ptx-byte bp (+ (nfix hoff) (- i l1)) id inc fn-rtc-st))
          (t (fn-ptx-byte h3 (- i (+ l1 blen)) id inc fn-rtc-st)))))
(defun fn-ptx-msg-range (i n h1 l1 bp hoff blen h3 id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :measure (nfix n)))
  (if (zp n) nil
    (cons (fn-ptx-msg-byte i h1 l1 bp hoff blen h3 id inc fn-rtc-st)
          (fn-ptx-msg-range (+ 1 (nfix i)) (- n 1) h1 l1 bp hoff blen h3 id inc fn-rtc-st))))

; The digest's held state (pos stack) over a message of N octets: absorb up to
; NW windows; a window is pushed only when more than a window remains after it
; (fn-b3-window-outs' rule), the last one by the finish.
(defun fn-ptx-absorb (nw pos st n h1 l1 bp hoff blen h3 id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :measure (nfix nw)))
  (let ((pos (nfix pos)) (n (nfix n)))
    (if (or (zp nw) (<= n (+ pos *fn-ptx-window*)))
        (mv pos st)
      (fn-ptx-absorb (- nw 1) (+ pos *fn-ptx-window*)
                     (fn-b3-cv-push *fn-b3-iv* 0 *fn-ptx-wexp*
                                    (fn-b3-node *fn-b3-iv*
                                                (fn-ptx-msg-range pos *fn-ptx-window* h1 l1 bp hoff blen h3 id inc fn-rtc-st)
                                                (floor pos 1024) 0)
                                    st)
                     n h1 l1 bp hoff blen h3 id inc fn-rtc-st))))
(defun fn-ptx-finish-digest (pos st n h1 l1 bp hoff blen h3 id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let ((pos (nfix pos)))
    (fn-b3-output-root
     (fn-b3-stack-fold *fn-b3-iv* 0
                       (fn-b3-cv-push *fn-b3-iv* 0 *fn-ptx-wexp*
                                      (fn-b3-node *fn-b3-iv*
                                                  (fn-ptx-msg-range pos (- (nfix n) pos) h1 l1 bp hoff blen h3 id inc fn-rtc-st)
                                                  (floor pos 1024) 0)
                                      st)))))

; -----------------------------------------------------------------------------
; Requests.
(defun fn-ptx-timer () (list :submit :timer nil (list 0)))
(defun fn-ptx-pwrite (h g off n pos) (list :submit :pwrite (list (nfix h) (nfix g) (nfix off) (nfix n)) (list *fn-ptx-lfile* (nfix pos))))
(defun fn-ptx-fsync () (list :submit :fsync nil (list *fn-ptx-lfile*)))
; ADAPTER (rule 6b-5, owner P, retired by A's lease landing adding :extend to *fn-rtc-kinds*).
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

; Start post P = (fid finc bp len) over kernel projection KD: find the head,
; accept, acquire b1 and b3 and write them, then hash.  (mv m reqs cost) where a
; refusal answers at once and leaves the machine idle (the caller continues
; with the queue).  Q is the queue after P.
(defun fn-ptx-start (p q kd ext geo id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let* ((bp (fn-ptx-cur-bp p)) (len (fn-ptx-cur-len p))
         (hmax (nfix (fn-rtc-get 2 geo)))
         (hoff (fn-ptx-head-end bp 0 (min len hmax) id inc fn-rtc-st))
         (cost (+ 1 hmax)))
    (if (not hoff)
        (mv (fn-ptx-mk :idle 0 nil q kd ext ext nil nil nil nil nil geo) (fn-ptx-answer p :refused id inc fn-rtc-st) cost)
      (let ((blen (- len hoff)) (txid (fn-ptx-kd-txid kd)))
        (mv-let (ok pre suf) (fn-ptx-accept (fn-ptx-range bp 0 hoff id inc fn-rtc-st) blen txid)
          (let* ((h1 (fn-ptx-free 0 nil id inc fn-rtc-st))
                 (h3 (fn-ptx-free 0 h1 id inc fn-rtc-st))
                 (rlen (+ (len pre) blen (len suf)))
                 (b1 (append (fn-ptx-frame-header rlen) (fn-rtc-get 1 kd) pre)))
            (if (not (and ok h1 h3 (<= (+ 32 rlen) (nfix (fn-rtc-get 1 geo)))))
                (mv (fn-ptx-mk :idle 0 nil q kd ext ext nil nil nil nil nil geo) (fn-ptx-answer p :refused id inc fn-rtc-st) cost)
              (let ((g1 (+ 1 (fn-ptx-gen h1 id inc fn-rtc-st))) (g3 (+ 1 (fn-ptx-gen h3 id inc fn-rtc-st))))
                (mv (fn-ptx-mk :hashing 0 (list (fn-ptx-cur-fid p) (fn-ptx-cur-finc p) bp len hoff txid) q kd ext ext
                               (list h1 g1 (len b1)) (list h3 g3 (len suf)) (list 0 nil) nil nil geo)
                    (list (list :acquire h1) (list :write h1 g1 0 b1)
                          (list :acquire h3) (list :write h3 g3 0 suf)
                          (fn-ptx-timer))
                    cost)))))))))

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
           (mv (fn-ptx-mk :fenced 0 nil nil kd ext ext nil nil nil committed nil (fn-ptx-geo m))
               (append done (fn-ptx-refuse-all q id inc fn-rtc-st)) 1))
          ((consp q)
           (mv-let (m2 r2 c2) (fn-ptx-start (car q) (cdr q) kd ext (fn-ptx-geo m) id inc fn-rtc-st)
             (mv (fn-rtc-set 10 (and committed t) m2) (append done r2) (+ 1 c2))))
          (t (mv (fn-ptx-mk :idle 0 nil nil kd ext ext nil nil nil committed nil (fn-ptx-geo m)) done 1)))))

; The kernel projection after the barrier's :ok and the acknowledgement
; (fn-lgk-fence then fn-lgk-finish-one of a batch of one): one more committed
; record, the chain head the new trailer, the frontier past the entry.
(defun fn-ptx-kd-commit (kd trailer elen)
  (fn-ptx-kd-mk (+ 1 (fn-ptx-kd-count kd)) trailer (+ (fn-ptx-kd-frontier kd) (nfix elen))
                (+ 1 (fn-ptx-kd-txid kd))
                (+ 1 (fn-ptx-kd-acked kd))))

; The entry's geometry for the current transaction.
(defun fn-ptx-l1 (m) (fn-ptx-buf-len (fn-ptx-b1 m)))
(defun fn-ptx-blen (m) (nfix (- (fn-ptx-cur-len (fn-ptx-cur m)) (fn-ptx-cur-hoff (fn-ptx-cur m)))))
(defun fn-ptx-l3 (m) (fn-ptx-buf-len (fn-ptx-b3 m)))           ; S ++ trailer once hashed
(defun fn-ptx-elen (m) (+ (fn-ptx-l1 m) (fn-ptx-blen m) (fn-ptx-l3 m) (nfix (fn-rtc-get 2 (fn-ptx-hs m)))))

(defun fn-ptx-summary (ev) (list (fn-rtc-get 0 ev) (fn-rtc-get 0 (fn-rtc-get 1 ev)) (fn-rtc-get 1 (fn-rtc-get 1 ev))))
(defun fn-ptx-with-evd (m ev) (fn-rtc-set 11 (append (true-list-fix (fn-ptx-evd m)) (list (fn-ptx-summary ev))) m))

; The step: (mv m2 requests cost).
(defun fn-ptx-step (m ev fn-rtc-st q)
  (declare (xargs :stobjs fn-rtc-st))
  (let* ((id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev))
         (kind (fn-rtc-get 0 ev)) (out (fn-rtc-get 1 ev)) (tag (fn-rtc-get 0 out)) (n (fn-rtc-get 1 out))
         (ph (fn-ptx-ph m)) (cur (fn-ptx-cur m)) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m)) (nxt (fn-ptx-nxt m))
         (m0 (fn-rtc-set 10 nil m)))
    (cond
     ;; an article handed in: (:handed (:done 0) id inc fid finc (h g 0 len))
     ((eq kind :handed)
      (let* ((hd (fn-rtc-get 6 ev))
             (p (list (fn-rtc-get 4 ev) (fn-rtc-get 5 ev) (fn-rtc-h-buf hd) (fn-rtc-h-len hd))))
        (cond ((eq ph :fenced) (mv m0 (fn-ptx-answer p :refused id inc fn-rtc-st) 1))
              ((eq ph :idle) (fn-ptx-start p nil kd ext (fn-ptx-geo m) id inc fn-rtc-st))
              ((< (len (fn-ptx-q m)) *fn-ptx-k*)
               (mv (fn-rtc-set 3 (append (true-list-fix (fn-ptx-q m)) (list p)) m0) nil 1))
              (t (mv m0 (fn-ptx-answer p :busy id inc fn-rtc-st) 1)))))
     ;; hashing, continued on the zero-delay timer
     ((and (eq ph :hashing) (eq kind :timer))
      (let* ((b1 (fn-ptx-b1 m)) (b3 (fn-ptx-b3 m)) (l1 (fn-ptx-l1 m)) (blen (fn-ptx-blen m)) (ls (fn-ptx-l3 m))
             (nmsg (+ l1 blen ls)) (hs (fn-ptx-hs m)) (nw (max 1 (floor (nfix q) *fn-ptx-window*))))
        (mv-let (pos st)
          (fn-ptx-absorb nw (fn-rtc-get 0 hs) (fn-rtc-get 1 hs) nmsg (fn-ptx-buf-h b1) l1
                         (fn-ptx-cur-bp cur) (fn-ptx-cur-hoff cur) blen (fn-ptx-buf-h b3) id inc fn-rtc-st)
          (if (< (+ pos *fn-ptx-window*) nmsg)
              (mv (fn-rtc-set 9 (list pos st) m0) (list (fn-ptx-timer)) (* nw *fn-ptx-window*))
            ;; the last window: the trailer, the padding, then fn-ptd's begin
            (let* ((trailer (fn-ptx-finish-digest pos st nmsg (fn-ptx-buf-h b1) l1 (fn-ptx-cur-bp cur)
                                                  (fn-ptx-cur-hoff cur) blen (fn-ptx-buf-h b3) id inc fn-rtc-st))
                   (pad (fn-ptx-pad-len (+ nmsg 32) (fn-ptx-unit m)))
                   ;; the padding is not written: the extent past the frontier reads
                   ;; zeros (fn-lgk-relp clause 2), so the entry's padding is already there
                   (tail trailer)
                   (b3x (list (fn-ptx-buf-h b3) (fn-ptx-buf-g b3) (+ ls 32)))
                   (elen (+ nmsg 32 pad))
                   (front (fn-ptx-kd-frontier kd))
                   (wr (list :write (fn-ptx-buf-h b3) (fn-ptx-buf-g b3) ls tail))
                   (cost (+ (* nw *fn-ptx-window*) *fn-ptx-window* 32)))
              (if (fn-olr-extension-needed-p front elen ext (fn-ptx-unit m))
                  (let ((nx (fn-olr-extension-target front elen ext (fn-ptx-unit m))))
                    (mv (fn-ptx-mk :extending 0 cur (fn-ptx-q m) kd ext nx b1 b3x (list nmsg trailer pad) nil nil (fn-ptx-geo m))
                        (list wr (fn-ptxa-extend ext nx)) cost))
                (mv (fn-ptx-mk :payload-writing 0 cur (fn-ptx-q m) kd ext ext b1 b3x (list nmsg trailer pad) nil nil (fn-ptx-geo m))
                    (list wr (fn-ptx-pwrite (fn-ptx-buf-h b1) (fn-ptx-buf-g b1) 0 l1 front)) cost)))))))
     ;; fn-ptd's extension (a failure refuses and fences: fn-ptd-complete's :extending arm)
     ((and (eq ph :extending) (eq kind :extend))
      (if (eq tag :done)
          (mv (fn-ptx-with-evd (fn-rtc-set 0 :extsyncing m0) ev) (list (fn-ptx-fsync)) 1)
        (fn-ptx-end m0 :refused kd ext t nil id inc fn-rtc-st)))
     ((and (eq ph :extsyncing) (eq kind :fsync))
      (if (eq tag :done)
          (let ((b1 (fn-ptx-b1 m)))
            (mv (fn-ptx-with-evd (fn-rtc-set 1 0 (fn-rtc-set 0 :payload-writing m0)) ev)
                (list (fn-ptx-pwrite (fn-ptx-buf-h b1) (fn-ptx-gen (fn-ptx-buf-h b1) id inc fn-rtc-st) 0 (fn-ptx-l1 m)
                                     (fn-ptx-kd-frontier kd)))
                1))
        (fn-ptx-end m0 :refused kd ext t nil id inc fn-rtc-st)))
     ;; the entry's writes: any outcome but the whole write is uncertain and fences
     ((and (eq ph :payload-writing) (eq kind :pwrite))
      (let ((want (if (zp (fn-ptx-k m)) (fn-ptx-l1 m) (fn-ptx-blen m)))
            (front (fn-ptx-kd-frontier kd)))
        (cond ((not (and (eq tag :done) (equal n want)))
               (fn-ptx-end m0 :uncertain kd ext t nil id inc fn-rtc-st))
              ((and (zp (fn-ptx-k m)) (< 0 (fn-ptx-blen m)))
               (let ((bp (fn-ptx-cur-bp cur)))
                 (mv (fn-ptx-with-evd (fn-rtc-set 1 1 m0) ev)
                     (list (fn-ptx-pwrite bp (fn-ptx-gen bp id inc fn-rtc-st) (fn-ptx-cur-hoff cur) (fn-ptx-blen m)
                                          (+ front (fn-ptx-l1 m))))
                     1)))
              (t
               (let ((b3 (fn-ptx-b3 m)))
                 (mv (fn-ptx-with-evd (fn-rtc-set 0 :log-writing m0) ev)
                     (list (fn-ptx-pwrite (fn-ptx-buf-h b3) (fn-ptx-gen (fn-ptx-buf-h b3) id inc fn-rtc-st) 0 (fn-ptx-l3 m)
                                          (+ front (fn-ptx-l1 m) (fn-ptx-blen m))))
                     1))))))
     ((and (eq ph :log-writing) (eq kind :pwrite))
      (if (and (eq tag :done) (equal n (fn-ptx-l3 m)))
          (mv (fn-ptx-with-evd (fn-rtc-set 0 :committing m0) ev) (list (fn-ptx-fsync)) 1)
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
