; Arbitrary HDR/XPAT field backing using the existing header parser.
; A completed query borrows one source span; it never copies a field value.
(in-package "ACL2")
(include-book "legacy-parser-cursor")
(include-book "nov-span-window")

; CURSOR = (legacy parser cursor fixed name candidates). FIELD comes from
; the bounded parsed NNTP command. Only its small request token is normalized;
; the article/header/source and resulting value remain immutable references.
(defun fn-lhq-begin (h n pin field)
  (declare (xargs :guard (and (natp h) (natp n))))
  (let ((names (list (fn-article-ascii-downcase field) :miss :miss :miss :miss)))
    (list (fn-lpc-begin h n pin) names)))

(defun fn-lhq-verdict (cursor)
  (declare (xargs :guard t))
  (fn-lpc-verdict (fn-lpc-at 0 cursor)))

(defun fn-lhq-field (cursor)
  (declare (xargs :guard t))
  (fn-lpc-field (fn-lpc-at 0 cursor) 0))

(defun fn-lhq-ready-p (cursor fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (fn-lpc-ready-p (fn-lpc-at 0 cursor) fn-arena))

; USED counts actual scalar source reads/parser transitions. A cold read
; escapes before any result is returned; the caller retains exactly CURSOR
; and retries it under the same captured handle/pin/window authority.
(defun fn-lhq-tick (cursor fuel fn-arena)
  (declare (xargs :stobjs fn-arena :measure (nfix fuel) :verify-guards nil
                  :guard (and (natp fuel) (fn-lhq-ready-p cursor fn-arena))))
  (let ((s (fn-lpc-at 0 cursor)) (names (fn-lpc-at 1 cursor)))
    (if (or (zp fuel) (<= (fn-lpc-at 1 s) (fn-lpc-at 3 s)))
        (mv cursor 0)
      (mv-let (next used)
        (fn-lhq-tick
          (list (fn-lpc-byte-names s
                  (fn-arena-get (fn-lpc-at 0 s) (fn-lpc-at 3 s) fn-arena) names) names)
          (- fuel 1) fn-arena)
        (mv next (+ 1 used))))))

(defthm fn-lhq-tick-used-natural
  (natp (mv-nth 1 (fn-lhq-tick cursor fuel fn-arena)))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-lhq-tick cursor fuel fn-arena)
                  :in-theory (disable fn-lpc-byte-names fn-lpc-at))))

(defthm fn-lhq-tick-work-bounded
  (<= (mv-nth 1 (fn-lhq-tick cursor fuel fn-arena)) (nfix fuel))
  :hints (("Goal" :induct (fn-lhq-tick cursor fuel fn-arena)
                  :in-theory (disable fn-lpc-byte-names fn-lpc-at))))

(defthm fn-lhq-tick-preserves-source
  (let ((out (fn-lpc-at 0 (mv-nth 0 (fn-lhq-tick cursor fuel fn-arena))))
        (s (fn-lpc-at 0 cursor)))
    (and (equal (fn-lpc-at 0 out) (fn-lpc-at 0 s))
         (equal (fn-lpc-at 1 out) (fn-lpc-at 1 s))
         (equal (fn-lpc-at 2 out) (fn-lpc-at 2 s))))
  :hints (("Goal" :induct (fn-lhq-tick cursor fuel fn-arena)
                  :in-theory (e/d (fn-lhq-tick fn-lpc-at)
                                  (fn-lpc-byte-names fn-lpc-verdict)))))

(defthm fn-lhq-tick-preserves-ready
  (implies (fn-lhq-ready-p cursor fn-arena)
           (fn-lhq-ready-p (mv-nth 0 (fn-lhq-tick cursor fuel fn-arena)) fn-arena))
  :hints (("Goal" :induct (fn-lhq-tick cursor fuel fn-arena)
                  :in-theory (e/d (fn-lhq-tick fn-lhq-ready-p fn-lpc-ready-p)
                                  (fn-lpc-byte-names fn-lpc-verdict)))))

; Fixed record projection needed for recursive guard preservation.
(defthm fn-lhq-parser-of-pair-by-definition
  (equal (fn-lpc-at 0 (list s names)) s)
  :hints (("Goal" :in-theory (enable fn-lpc-at))))

(verify-guards fn-lhq-tick
  :hints (("Goal" :in-theory
            (e/d (fn-lhq-ready-p fn-lpc-ready-p)
                 (fn-lpc-byte-names fn-lpc-at fn-lhq-tick
                  fn-arena-count-is-len fn-arena-get-is-nth
                  fn-arena-payload-len-is-len-nth)))))
