(in-package "ACL2")
(include-book "../../books/over-held-row")

(defun-nx ohrt-conclusion (s fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let ((result (fn-ohr-active-one s fn-arena)))
    (and (equal (append (mv-nth 0 result)
                        (fn-npw-remaining (nth 4 (mv-nth 1 result))
                                          (nth 5 (mv-nth 1 result)) fn-arena))
                (fn-npw-remaining (nth 4 s) (nth 5 s) fn-arena))
         (equal (nth 0 (mv-nth 1 result)) (nth 0 s))
         (implies (mv-nth 1 result)
                  (equal (nth 1 (mv-nth 1 result)) (nth 1 s)))
         (<= (len (mv-nth 0 result)) 1)
         (implies (consp (nth 4 s))
                  (fn-ohr-active-p (mv-nth 1 result) fn-arena)))))

(defthm ohrt-positive-actual-emission-and-retained-source
  (let* ((fn-arena nil)
         (s (fn-obc-make '("fn.test" 2 8 7 nil nil)
                         '(:response 4 9) :emit nil '("abc") 0)))
    (and (fn-ohr-active-p s fn-arena)
         (equal (nth 2 s) :emit)
         (ohrt-conclusion s fn-arena)
         (equal (mv-nth 0 (fn-ohr-active-one s fn-arena)) '(97))))
  :rule-classes nil)

; Corrupted continuation; the retained phase premise is affirmative.
(defthm ohrt-removal-active-carry
  (let* ((fn-arena nil)
         (s (fn-obc-make '("fn.test" 2 8 7 nil nil)
                         '(:response 4 9) :emit nil '("abc" 300) 0)))
    (and (not (fn-ohr-active-p s fn-arena))
         (equal (nth 2 s) :emit)
         (not (ohrt-conclusion s fn-arena))))
  :rule-classes nil)

; A reachable terminal invalid parser changes the next-number coordinate;
; it cannot be treated as an emitting continuation.
(defthm ohrt-removal-emission-phase
  (let* ((fn-arena '((120 13 10)))
         (parser (mv-nth 0 (fn-lpc-tick (fn-lpc-begin 0 3 '(:response 4 9))
                                        3 fn-arena)))
         (s (fn-obc-make '("fn.test" 1 8 7 nil nil)
                         '(:response 4 9) :parse parser nil 0)))
    (and (fn-ohr-active-p s fn-arena)
         (not (equal (nth 2 s) :emit))
         (not (ohrt-conclusion s fn-arena))))
  :rule-classes nil)

(defun ohrt-row (facts)
  (declare (xargs :guard t))
  (fn-held-make 0 1 0 "<e@x>" 0 '("fn.test") "o" "s" "e" 1 5 facts
                (fn-hc-make (fn-stx-make-verdict :absent nil 0) nil 0)
                '(("fn.test" . 1)) nil))

(defthm ohrt-positive-selected-cached-row-then-actual-one
  (let* ((fn-arena '((120 13 10)))
         (facts (fn-hf-make 3 nil 0
                  (list nil nil nil
                        (fn-hnov-make nil t "a" "c" "d" "<e@x>" ""))))
         (row (ohrt-row facts))
         (range '("fn.test" 1 8 7 nil t))
         (s (fn-ohr-selected-row-begin range '(:response 4 9) row fn-arena)))
    (and (true-listp range)
         (natp (fn-record-payload row))
         (< (fn-record-payload row) (fn-arena-count fn-arena))
         (equal (nth 2 s) :emit)
         (fn-ohr-active-p s fn-arena)
         (ohrt-conclusion s fn-arena)
         (equal (nth 1 (nth 0 s)) 2)
         (not (nth 5 (nth 0 s)))))
  :rule-classes nil)

(defthm ohrt-positive-selected-cached-invalid-preserves-owed
  (let* ((fn-arena '((120 13 10)))
         (row (ohrt-row
                (fn-hf-make 3 nil 0
                  (list nil nil nil
                        (fn-hnov-make nil nil "" "" "" "" "")))))
         (range '("fn.test" 1 8 7 nil t))
         (s (fn-ohr-selected-row-begin range '(:response 4 9) row fn-arena)))
    (and (true-listp range)
         (natp (fn-record-payload row))
         (< (fn-record-payload row) (fn-arena-count fn-arena))
         (equal (nth 2 s) :seek)
         (equal (nth 1 (nth 0 s)) 2)
         (equal (nth 5 (nth 0 s)) t)
         (equal (nth 1 s) '(:response 4 9))))
  :rule-classes nil)

(defthm ohrt-positive-selected-uncached-parser-same-source
  (let* ((fn-arena '((120 13 10)))
         (row (ohrt-row (fn-hf-make 3 nil 0 nil)))
         (range '("fn.test" 1 8 7 nil t))
         (s (fn-ohr-selected-row-begin range '(:response 4 9) row fn-arena))
         (next (mv-nth 1 (fn-ohr-active-one s fn-arena))))
    (and (true-listp range)
         (natp (fn-record-payload row))
         (< (fn-record-payload row) (fn-arena-count fn-arena))
         (equal (nth 2 s) :parse)
         (fn-ohr-active-p s fn-arena)
         (equal (fn-lpc-at 0 (nth 3 s)) (fn-record-payload row))
         (equal (fn-lpc-at 1 (nth 3 s)) 3)
         (equal (fn-lpc-at 2 (nth 3 s)) '(:response 4 9))
         (equal (nth 2 next) :parse)
         (fn-ohr-active-p next fn-arena)
         (equal (fn-lpc-at 0 (nth 3 next)) (fn-record-payload row))
         (equal (fn-lpc-at 3 (nth 3 next)) 1)))
  :rule-classes nil)
