(in-package "ACL2")
(include-book "../../books/legacy-parser-header")

(defconst *lpht-source*
  '(83 117 98 106 101 99 116 58 32 120 13 10 32 121 13 10 13 10 98 13 10))

; Literal preserved span invariant and the concrete formatter read guard,
; reached through begin and a complete actual-arena tick.
(defthm lpht-span-bounds-positive
  (let* ((arena (list *lpht-source*)) (n (len *lpht-source*))
         (s (fn-lpc-begin 0 n '(:origin 17)))
         (out (mv-nth 0 (fn-lpc-tick s n arena)))
         (span (fn-lpc-field out 0)))
    (and (fn-lpc-cursor-bounds-p s)
         (fn-lpc-cursor-bounds-p out)
         (fn-lpc-ready-p out arena) (natp 0) span
         (< 0 (fn-lpc-at 2 span))
         (fn-lpc-span-bound-p span (fn-lpc-at 0 out)
                              (fn-lpc-at 2 out) (fn-lpc-at 3 out))
         (fn-lpc-span-ready-p span 0 arena)
         (equal (fn-lpc-span-get span 0 arena) 120)))
  :rule-classes nil)

; CORRUPTED STATE: removing the sole invariant premise from the tick's
; preservation theorem can leave an out-of-bounds, unpinned field reference.
(defthm lpht-without-bounds-corrupted-span
  (let* ((arena (list *lpht-source*)) (n (len *lpht-source*))
         (s0 (fn-lpc-begin 0 n '(:origin 17)))
         (head (fn-lpc-at 4 s0))
         (bad-head (fn-lpc-put 8 '((9 900 10 :wrong-pin)) head))
         (bad (fn-lpc-put 4 bad-head s0))
         (out (mv-nth 0 (fn-lpc-tick bad 1 arena))))
    (and (not (fn-lpc-cursor-bounds-p bad))
         (not (fn-lpc-cursor-bounds-p out))))
  :rule-classes nil)

; Name candidates match the actual parser's ASCII-downcase convention.
(assert-event
 (and (equal (fn-lpc-name-key
              (fn-lpc-names-scan *fn-lpc-names* '(115 85 98 74 101 67 116))) 0)
      (equal (fn-article-ascii-downcase '(115 85 98 74 101 67 116))
             *fn-nov-subject-name*)
      (not (equal (fn-lpc-name-key
                   (fn-lpc-names-scan *fn-lpc-names* '(115 85 98 74 101 67 117))) 0))))
