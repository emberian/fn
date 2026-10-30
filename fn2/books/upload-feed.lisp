; The article input feed (layer D, quest D4; fn2/docs/d-machines-nntp.md
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
; H's model (fn2/tests/model/framing.py, decode_block): lines end in CRLF;
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

(defun fn2-feed-cap (slot fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (if (and (natp slot) (< slot (fn2-pool-rows fn2-pool))) (nfix (fn2-pool-cap slot fn2-pool)) 0))
(defthm fn2-feed-cap-natp (natp (fn2-feed-cap slot fn2-pool)) :rule-classes :type-prescription)
(in-theory (disable fn2-feed-cap))

; The feed: at most LEFT octets of [i, end) of RX, written into the chunk
; DSLOT while it has room. Returns (mv status i mode discard copied
; fn2-pool):
;   :terminator  the terminator's LF was consumed; I is the octet after it;
;   :need-more   every octet up to END is consumed;
;   :budget      LEFT is spent;
;   :full        the next octet releases more than the chunk has room for
;                (I is that octet, not consumed: switch chunks and resume);
;   :fault       the pool refused a read or a write.
; DISCARD becomes t at a framing error; from then nothing is written.
; COPIED counts the octets written by this call.
(defun fn2-upload-feed-loop (left i end mode discard copied rslot rgen rk rs rg dslot dgen dk ds dg fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix left)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp left) (natp i) (natp end) (natp mode) (natp copied))
                  :guard-hints (("Goal" :in-theory (disable fn2-gram-read fn2-feed-emit fn2-gram-fill)))))
  (cond ((zp left) (mv :budget (nfix i) mode discard (nfix copied) fn2-pool))
        ((<= (nfix end) (nfix i)) (mv :need-more (nfix i) mode discard (nfix copied) fn2-pool))
        (t
         (mv-let (ok b) (fn2-gram-read rslot rgen (nfix i) rk rs rg fn2-pool)
           (if (not ok) (mv :fault (nfix i) mode discard (nfix copied) fn2-pool)
             (mv-let (next emit err term) (fn2-feed-step mode b)
               (let* ((discard (or discard err))
                      (emit (if discard 0 emit)))
                 (cond
                  (term (mv :terminator (+ 1 (nfix i)) next discard (nfix copied) fn2-pool))
                  ((< (fn2-feed-cap dslot fn2-pool) (+ (fn2-gram-fill dslot fn2-pool) emit))
                   (mv :full (nfix i) mode discard (nfix copied) fn2-pool))
                  (t (mv-let (code fn2-pool) (fn2-feed-emit emit b dslot dgen dk ds dg fn2-pool)
                       (if (not (eq code :ok)) (mv :fault (nfix i) mode discard (nfix copied) fn2-pool)
                         (fn2-upload-feed-loop (- left 1) (+ 1 (nfix i)) end next discard (+ (nfix copied) emit)
                                               rslot rgen rk rs rg dslot dgen dk ds dg fn2-pool))))))))))))
(defthm fn2-upload-feed-loop-types
  (and (natp (mv-nth 1 (fn2-upload-feed-loop left i end mode discard copied rslot rgen rk rs rg dslot dgen dk ds dg fn2-pool)))
       (natp (mv-nth 4 (fn2-upload-feed-loop left i end mode discard copied rslot rgen rk rs rg dslot dgen dk ds dg fn2-pool))))
  :rule-classes ((:type-prescription :corollary (natp (mv-nth 1 (fn2-upload-feed-loop left i end mode discard copied rslot rgen rk rs rg dslot dgen dk ds dg fn2-pool))))
                 (:type-prescription :corollary (natp (mv-nth 4 (fn2-upload-feed-loop left i end mode discard copied rslot rgen rk rs rg dslot dgen dk ds dg fn2-pool))))))
(defthm fn2-upload-feed-loop-mode
  (implies (natp mode)
           (natp (mv-nth 2 (fn2-upload-feed-loop left i end mode discard copied rslot rgen rk rs rg dslot dgen dk ds dg fn2-pool))))
  :rule-classes :type-prescription)
(fn2-pool-preserves fn2-upload-feed-loop (left i end mode discard copied rslot rgen rk rs rg dslot dgen dk ds dg fn2-pool)
  :position 5 :rows nil)

; One call from the connection's continuation: [i, fill) of RX.
(defun fn2-upload-feed (left i mode discard rslot rgen rk rs rg dslot dgen dk ds dg fn2-pool)
  (declare (xargs :stobjs fn2-pool
                  :guard (and (fn2-pool-wfp fn2-pool) (natp left) (natp i) (natp mode))))
  (fn2-upload-feed-loop left i (fn2-gram-fill rslot fn2-pool) mode discard 0
                        rslot rgen rk rs rg dslot dgen dk ds dg fn2-pool))
(fn2-pool-preserves fn2-upload-feed (left i mode discard rslot rgen rk rs rg dslot dgen dk ds dg fn2-pool)
  :position 5 :rows nil)

(assert-event
 (fn2-assert-compliant-p '(fn2-feed-step fn2-feed-emit fn2-upload-feed-loop fn2-upload-feed) (w state)))
