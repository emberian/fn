; The article input feed (layer D, quest D4; docs/d-machines-nntp.md
; section 14.2): a dot-stuffed block (RFC 3977 section 3.1.1) read from a
; connection's RX slot and written, dot-unstuffed, into an upload's chunk.
; A library over the pool: the connection's article-input arm calls it
; through one declared operation, and tests/upload-feed-unit.lisp drives it
; on a local pool.
;
; It is a streaming octet machine, not a line framer: a body line may be
; longer than the connection's RX slot (H's model sets no body line bound),
; so nothing is retained between octets but MODE. RX octets are read under
; the connection's owner and chunk octets written under the upload's, each
; through the pool's checked exports (no list, no copy of RX).
;
; MODE: 0 at a line start, 1 inside a line, 2 after a CR inside a line, 3
; after a dot at a line start, 4 after ".CR" at a line start. The framing of
; H's model (tests/model/framing.py, decode_block): lines end in CRLF;
; a bare CR, a bare LF or a NUL is malformed; a line starting with one dot is
; malformed unless it is the terminator "." or starts with "..", which is
; unstuffed to ".". After a framing error the block is drained to its
; terminator and nothing more is written (DISCARD).
(in-package "ACL2")
(include-book "grammar")
(fn2-book-layer :d)

(defconst *fn2-feed-bol* 0)
(defconst *fn2-feed-mid* 1)
(defconst *fn2-feed-cr* 2)
(defconst *fn2-feed-dot* 3)
(defconst *fn2-feed-dotcr* 4)

; One octet B in MODE: (mv next emit error terminator). EMIT is the number
; of octets it releases: 1 (B itself, or the "." of a "..") or 2 (CR LF).
(defun fn2-feed-step (mode b)
  (declare (xargs :guard (and (natp mode) (natp b))))
  (let ((cr 13) (lf 10) (dot 46))
    (cond ((equal mode *fn2-feed-bol*)
           (cond ((= b dot) (mv *fn2-feed-dot* 0 nil nil))
                 ((= b cr) (mv *fn2-feed-cr* 0 nil nil))
                 ((or (= b lf) (= b 0)) (mv *fn2-feed-mid* 0 t nil))
                 (t (mv *fn2-feed-mid* 1 nil nil))))
          ((equal mode *fn2-feed-cr*)
           (cond ((= b lf) (mv *fn2-feed-bol* 2 nil nil))
                 ((= b cr) (mv *fn2-feed-cr* 0 t nil))
                 (t (mv *fn2-feed-mid* 0 t nil))))
          ((equal mode *fn2-feed-dot*)
           (cond ((= b dot) (mv *fn2-feed-mid* 1 nil nil))
                 ((= b cr) (mv *fn2-feed-dotcr* 0 nil nil))
                 (t (mv *fn2-feed-mid* 0 t nil))))
          ((equal mode *fn2-feed-dotcr*)
           (cond ((= b lf) (mv *fn2-feed-bol* 0 nil t))
                 ((= b cr) (mv *fn2-feed-cr* 0 t nil))
                 (t (mv *fn2-feed-mid* 0 t nil))))
          (t ; inside a line
           (cond ((= b cr) (mv *fn2-feed-cr* 0 nil nil))
                 ((or (= b lf) (= b 0)) (mv *fn2-feed-mid* 0 t nil))
                 (t (mv *fn2-feed-mid* 1 nil nil)))))))
(defthm fn2-feed-step-types
  (and (natp (car (fn2-feed-step mode b)))
       (natp (mv-nth 1 (fn2-feed-step mode b)))
       (<= (mv-nth 1 (fn2-feed-step mode b)) 2))
  :rule-classes ((:type-prescription :corollary (natp (car (fn2-feed-step mode b))))
                 (:type-prescription :corollary (natp (mv-nth 1 (fn2-feed-step mode b))))
                 (:linear :corollary (<= (mv-nth 1 (fn2-feed-step mode b)) 2))))
(in-theory (disable fn2-feed-step))

; Write the octets one step releases: B, or for a ".." its second dot (B),
; or CR LF.
(defun fn2-feed-emit (n b dslot dgen dk ds dg fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp n) (natp b))))
  (cond ((equal n 2)
         (mv-let (code fn2-pool) (fn2-gram-put 13 dslot dgen dk ds dg fn2-pool)
           (if (eq code :ok) (fn2-gram-put 10 dslot dgen dk ds dg fn2-pool) (mv code fn2-pool))))
        ((equal n 1) (fn2-gram-put b dslot dgen dk ds dg fn2-pool))
        (t (mv :ok fn2-pool))))
(fn2-pool-preserves fn2-feed-emit (n b dslot dgen dk ds dg fn2-pool) :position 1 :rows nil)

; The exact octets fn2-feed-emit writes: two are CR LF, one is B.
(defun fn2-feed-emitted-lf (n b)
  (declare (xargs :guard (and (natp n) (natp b))))
  (if (or (equal n 2) (and (equal n 1) (equal b 10))) 1 0))
(defthm fn2-feed-emitted-lf-natp
  (natp (fn2-feed-emitted-lf n b))
  :rule-classes :type-prescription)

; The state a raw feed steps from: a dot at a line start is data.
(defun fn2-feed-in (raw mode b)
  (declare (xargs :guard t))
  (if (and raw (equal mode *fn2-feed-bol*) (equal b 46)) *fn2-feed-mid* mode))
(defthm fn2-feed-in-natp (implies (natp mode) (natp (fn2-feed-in raw mode b))) :rule-classes :type-prescription)
(in-theory (disable fn2-feed-in))

(defun fn2-feed-cap (slot fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (if (and (natp slot) (< slot (fn2-pool-rows fn2-pool))) (nfix (fn2-pool-cap slot fn2-pool)) 0))
(defthm fn2-feed-cap-natp (natp (fn2-feed-cap slot fn2-pool)) :rule-classes :type-prescription)
(in-theory (disable fn2-feed-cap))

; Checked two-byte delimiter read, shared by the in-flight line cut and
; the next call's already-complete-header check.
(defun fn2-feed-crlf-at (slot gen off kind owner owner-gen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp off))))
  (mv-let (ok0 b0) (fn2-gram-read slot gen off kind owner owner-gen fn2-pool)
    (mv-let (ok1 b1) (fn2-gram-read slot gen (+ 1 off) kind owner owner-gen fn2-pool)
      (mv (if (and ok0 ok1) :ok :fault)
          (and ok0 ok1 (= b0 13) (= b1 10))))))
; A blank CRLF ends the header.  The feed's line mode knows this LF completes
; a line; the last two written octets distinguish empty from ordinary.
(defun fn2-feed-header-end-p (slot gen kind owner owner-gen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (let ((filled (fn2-gram-fill slot fn2-pool)))
    (cond ((zp filled) (mv :ok t))
          ((< filled 2) (mv :ok nil))
          (t (fn2-feed-crlf-at slot gen (- filled 2) kind owner owner-gen fn2-pool)))))
; At a later call, C0's actual filled trailer is the routing authority even
; when the separately scheduled header scan has not caught up.  At most four
; pool reads recognize the first empty line or CRLF CRLF.
(defun fn2-feed-header-complete-p (slot gen kind owner owner-gen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (let ((filled (fn2-gram-fill slot fn2-pool)))
    (if (< filled 2) (mv :ok nil)
      (mv-let (code tail) (fn2-feed-crlf-at slot gen (- filled 2) kind owner owner-gen fn2-pool)
        (cond ((not (eq code :ok)) (mv code nil))
              ((not tail) (mv :ok nil))
              ((= filled 2) (mv :ok t))
              ((< filled 4) (mv :ok nil))
              (t (fn2-feed-crlf-at slot gen (- filled 4) kind owner owner-gen fn2-pool)))))))

; The feed: at most LEFT octets of [i, end) of RX, written into the chunk
; DSLOT while it has room. Returns (mv status i mode discard copied lines
; fn2-pool):
;   :terminator  the terminator's LF was consumed; I is the octet after it;
;   :need-more   every octet up to END is consumed;
;   :budget      LEFT is spent;
;   :header      the header's empty CRLF was consumed when STOP-HEADER;
;   :full        the next octet releases more than logical LIMIT has room for
;                (I is that octet, not consumed: switch chunks and resume);
;   :fault       the pool refused a read or a write.
; DISCARD becomes t at a framing error; from then nothing is written.
; COPIED counts octets written and LINES counts LF octets emitted by this
; call. RAW reads [i, end) as the
; article's own octets (a consumer's append frame, e-surface.md 3.3): a dot
; at a line start is data, so no terminator is framed and the caller ends
; the block at END; the line framing (CR LF; no bare CR, LF or NUL) is the
; same.  LIMIT is the caller's logical destination bound, independently of
; the pool slot's physical capacity; STOP-HEADER chooses the header cut.
(defun fn2-upload-feed-loop (left i end mode discard raw copied lines rslot rgen rk rs rg dslot dgen dk ds dg limit stop-header fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix left)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp left) (natp i) (natp end)
                              (natp mode) (natp copied) (natp lines) (natp limit))
                  :guard-hints (("Goal" :in-theory (disable fn2-gram-read fn2-feed-emit fn2-gram-fill)))))
  (cond ((zp left) (mv :budget (nfix i) mode discard (nfix copied) (nfix lines) fn2-pool))
        ((<= (nfix end) (nfix i)) (mv :need-more (nfix i) mode discard (nfix copied) (nfix lines) fn2-pool))
        (t
         (mv-let (ok b) (fn2-gram-read rslot rgen (nfix i) rk rs rg fn2-pool)
           (if (not ok) (mv :fault (nfix i) mode discard (nfix copied) (nfix lines) fn2-pool)
             (mv-let (next emit err term)
               (fn2-feed-step (fn2-feed-in raw mode b) b)
               (let* ((discard (or discard err))
                      (emit (if (or discard (equal (nfix dslot) *fn2-none*)) 0 emit)))
                 (cond
                  (term (mv :terminator (+ 1 (nfix i)) next discard (nfix copied) (nfix lines) fn2-pool))
                  ((< (min (nfix limit) (fn2-feed-cap dslot fn2-pool))
                      (+ (fn2-gram-fill dslot fn2-pool) emit))
                   (mv :full (nfix i) mode discard (nfix copied) (nfix lines) fn2-pool))
                  (t (mv-let (hcode header)
                       (if (and stop-header (equal emit 2) (equal next *fn2-feed-bol*))
                           (fn2-feed-header-end-p dslot dgen dk ds dg fn2-pool)
                         (mv :ok nil))
                       (if (not (eq hcode :ok))
                           (mv :fault (nfix i) mode discard (nfix copied) (nfix lines) fn2-pool)
                         (mv-let (code fn2-pool) (fn2-feed-emit emit b dslot dgen dk ds dg fn2-pool)
                           (if (not (eq code :ok)) (mv :fault (nfix i) mode discard (nfix copied) (nfix lines) fn2-pool)
                             (let ((lines2 (+ (nfix lines) (fn2-feed-emitted-lf emit b))))
                               (if header
                                   (mv :header (+ 1 (nfix i)) next discard (+ (nfix copied) emit) lines2 fn2-pool)
                                 (fn2-upload-feed-loop (- left 1) (+ 1 (nfix i)) end next discard raw (+ (nfix copied) emit)
                                                       lines2 rslot rgen rk rs rg dslot dgen dk ds dg limit stop-header fn2-pool))))))))))))))))
(defthm fn2-upload-feed-loop-types
  (and (natp (mv-nth 1 (fn2-upload-feed-loop left i end mode discard raw copied lines rslot rgen rk rs rg dslot dgen dk ds dg limit stop-header fn2-pool)))
       (natp (mv-nth 4 (fn2-upload-feed-loop left i end mode discard raw copied lines rslot rgen rk rs rg dslot dgen dk ds dg limit stop-header fn2-pool))))
  :rule-classes ((:type-prescription :corollary (natp (mv-nth 1 (fn2-upload-feed-loop left i end mode discard raw copied lines rslot rgen rk rs rg dslot dgen dk ds dg limit stop-header fn2-pool))))
                 (:type-prescription :corollary (natp (mv-nth 4 (fn2-upload-feed-loop left i end mode discard raw copied lines rslot rgen rk rs rg dslot dgen dk ds dg limit stop-header fn2-pool)))))
  :hints (("Goal" :in-theory (disable fn2-feed-emitted-lf min nfix))))
(defthm fn2-upload-feed-loop-mode
  (implies (natp mode)
           (natp (mv-nth 2 (fn2-upload-feed-loop left i end mode discard raw copied lines rslot rgen rk rs rg dslot dgen dk ds dg limit stop-header fn2-pool))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (disable fn2-feed-emitted-lf min nfix))))
(defthm fn2-upload-feed-loop-lines-natp
  (natp (mv-nth 5 (fn2-upload-feed-loop left i end mode discard raw copied lines rslot rgen rk rs rg dslot dgen dk ds dg limit stop-header fn2-pool)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (disable fn2-feed-emitted-lf min nfix))))
(fn2-pool-preserves fn2-upload-feed-loop (left i end mode discard raw copied lines rslot rgen rk rs rg dslot dgen dk ds dg limit stop-header fn2-pool)
  :position 6 :rows nil
  :hints (("Goal" :in-theory (disable fn2-feed-emitted-lf min nfix))))

; Counted public feed for the actual upload row.  A call reports only its
; own copied octets and emitted LF octets; the caller retains both totals.
(defun fn2-upload-feed-counted (left i end mode discard raw rslot rgen rk rs rg dslot dgen dk ds dg limit stop-header fn2-pool)
  (declare (xargs :stobjs fn2-pool
                  :guard (and (fn2-pool-wfp fn2-pool) (natp left) (natp i)
                              (natp end) (natp mode) (natp limit))))
  (fn2-upload-feed-loop left i end mode discard raw 0 0 rslot rgen rk rs rg
                        dslot dgen dk ds dg limit stop-header fn2-pool))
(fn2-pool-preserves fn2-upload-feed-counted (left i end mode discard raw rslot rgen rk rs rg dslot dgen dk ds dg limit stop-header fn2-pool)
  :position 6 :rows nil)

; One call from the connection's continuation: [i, fill) of RX.
(defun fn2-upload-feed (left i mode discard rslot rgen rk rs rg dslot dgen dk ds dg fn2-pool)
  (declare (xargs :stobjs fn2-pool
                  :guard (and (fn2-pool-wfp fn2-pool) (natp left) (natp i) (natp mode))))
  (mv-let (status next mode2 discard2 copied lines fn2-pool)
    (fn2-upload-feed-counted left i (fn2-gram-fill rslot fn2-pool) mode discard nil
                             rslot rgen rk rs rg dslot dgen dk ds dg
                             (fn2-feed-cap dslot fn2-pool) nil fn2-pool)
    (declare (ignore lines))
    (mv status next mode2 discard2 copied fn2-pool)))
(fn2-pool-preserves fn2-upload-feed (left i mode discard rslot rgen rk rs rg dslot dgen dk ds dg fn2-pool)
  :position 5 :rows nil)

(assert-event
 (fn2-assert-compliant-p '(fn2-feed-step fn2-feed-emit fn2-feed-emitted-lf fn2-feed-crlf-at
                           fn2-feed-header-end-p fn2-feed-header-complete-p
                           fn2-upload-feed-loop fn2-upload-feed-counted fn2-upload-feed) (w state)))

; Shared LF counter: upload retains counts before source windows can roll;
; transaction counter controls call this same primitive.
(defun fn2-txn-count-loop (n slot gen off lines okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix n)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp n) (natp off) (natp lines))))
  (if (zp n) (mv :ok lines)
    (mv-let (ok byte) (fn2-gram-read slot gen off okind oslot ogen fn2-pool)
      (if (not ok) (mv :bounds lines)
        (fn2-txn-count-loop (- n 1) slot gen (+ 1 off) (if (equal byte 10) (+ 1 (nfix lines)) (nfix lines))
                            okind oslot ogen fn2-pool)))))
(defthm fn2-txn-count-loop-natp
  (implies (natp lines) (natp (mv-nth 1 (fn2-txn-count-loop n slot gen off lines okind oslot ogen fn2-pool))))
  :rule-classes :type-prescription)
(defthm fn2-txn-count-loop-bound
  (implies (natp lines) (<= (mv-nth 1 (fn2-txn-count-loop n slot gen off lines okind oslot ogen fn2-pool))
                            (+ lines (nfix n))))
  :rule-classes :linear)
(in-theory (disable fn2-txn-count-loop))
