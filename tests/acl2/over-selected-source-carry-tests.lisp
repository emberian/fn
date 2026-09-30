(in-package "ACL2")
(include-book "../../books/over-selected-source-carry")

(defun-nx oshst-parser ()
 (let* ((bytes '(83 117 98 106 101 99 116 58 32 120 13 10 13 10))
        (fn-arena (list bytes)))
  (mv-nth 0 (fn-lpc-tick (fn-lpc-begin 0 14 '(:source 17)) 14 fn-arena))))

(defthm oshst-parser-pieces-source-positive
 (let ((parser (oshst-parser)))
  (and (equal (fn-lpc-verdict parser) :valid)
       (fn-lpc-cursor-bounds-p parser)
       (fn-osh-pieces-source-p (fn-obc-parser-pieces 1 parser)
                               (fn-lpc-at 0 parser) (fn-lpc-at 2 parser))))
 :rule-classes nil)

; Corrupted-state hypothesis removal: replace one actual completed field
; with a foreign payload handle; original parser/source remain unchanged.
(defthm oshst-parser-pieces-source-without-bounds
 (let* ((parser (oshst-parser))
        (header (fn-lpc-at 4 parser))
        (bad (fn-lpc-put 4
               (fn-lpc-put 8 (cons '(1 9 1 (:source 17))
                                  (cdr (fn-lpc-at 8 header))) header) parser)))
  (and (equal (fn-lpc-verdict bad) :valid)
       (not (fn-lpc-cursor-bounds-p bad))
       (not (fn-osh-pieces-source-p (fn-obc-parser-pieces 1 bad)
                                  (fn-lpc-at 0 bad) (fn-lpc-at 2 bad)))))
 :rule-classes nil)
