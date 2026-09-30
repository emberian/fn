; Branch-sensitive source trace/refinement teeth. No runtime allocator claim.
(in-package "ACL2")
(include-book "../../books/legacy-parser-trace-constructors")

(defun lptrace-events (tag trace)
 (declare (xargs :guard (symbolp tag)))
 (if (consp trace)
  (+ (if (eq (fn-ag-car (car trace)) tag) 1 0)
     (lptrace-events tag (cdr trace))) 0))

; Complete literal conclusion, nonempty transition, no hypotheses to remove.
(defthm lptrace-tick-positive
 (let* ((arena '((83 58 32 120 13 10 13 10)))
        (s (fn-lpc-begin 0 8 :pin)) (fuel 1)
        (trace (mv-nth 4 (fn-lpt-tick s fuel arena))))
  (and
   (equal (mv-nth 0 (fn-lpt-tick s fuel arena)) (mv-nth 0 (fn-lpc-tick s fuel arena)))
   (equal (mv-nth 1 (fn-lpt-tick s fuel arena)) (mv-nth 1 (fn-lpc-tick s fuel arena)))
   (equal (mv-nth 2 (fn-lpt-tick s fuel arena)) (mv-nth 2 (fn-lpc-tick s fuel arena)))
   (equal (mv-nth 3 (fn-lpt-tick s fuel arena)) (mv-nth 3 (fn-lpc-tick s fuel arena)))
   (equal (mv-nth 2 (fn-lpc-tick s fuel arena)) 1)
   (equal (lptrace-events :arena-read trace) 1)
   (equal (fn-lpt-constructor-cells trace) (fn-lpa-tick-conses s fuel arena))
   (<= (fn-lpt-constructor-cells trace)
       (+ 4 (* 39 (mv-nth 2 (fn-lpc-tick s fuel arena)))))))
 :rule-classes nil)

; Short-circuit stop performs no source read and no byte transition.
(defthm lptrace-short-circuit-positive
 (let* ((s (fn-lpc-begin 0 1 :pin))
        (trace (mv-nth 4 (fn-lpt-tick s 0 '((83))))))
  (and (equal (lptrace-events :arena-read trace) 0)
       (equal (fn-lpt-constructor-cells trace) 4)
       (< 0 (lptrace-events :signed trace))))
 :rule-classes nil)

; MUTATION: returning only the visible eight-cell cursor spine misses
; executed header/name constructors and both logical return tuples.
(defthm lptrace-constructor-mutation
 (let* ((s (fn-lpc-begin 0 1 :pin))
        (trace (mv-nth 4 (fn-lpt-tick s 1 '((83))))))
  (and (equal (fn-lpt-constructor-cells trace) 32)
       (not (equal (fn-lpt-constructor-cells trace) 8))))
 :rule-classes nil)

; CORRUPTED state: projection/count equality are unconditional, including
; malformed header/cursor shapes; this is not a supported served state.
(defthm lptrace-corrupted-state
 (let ((s '(0 1 :pin 0 (:name -2) 4 (:cr -9) t)) (arena '((10))))
  (and (equal (mv-nth 0 (fn-lpt-tick s 1 arena))
              (mv-nth 0 (fn-lpc-tick s 1 arena)))
       (equal (fn-lpt-constructor-cells (mv-nth 4 (fn-lpt-tick s 1 arena)))
              (fn-lpa-tick-conses s 1 arena))))
 :rule-classes nil)

(defun lptrace-exec-case (bytes fuel fn-arena)
 (declare (xargs :stobjs fn-arena :verify-guards nil))
 (let* ((fn-arena (fn-arena-clear fn-arena))
        (fn-arena (fn-arena-seal-list bytes fn-arena))
        (s (fn-lpc-begin 0 (len bytes) :pin)))
  (mv-let (t-next t-consumed t-work t-verdict trace) (fn-lpt-tick s fuel fn-arena)
   (mv-let (next consumed work verdict) (fn-lpc-tick s fuel fn-arena)
    (mv (and (equal t-next next) (equal t-consumed consumed)
             (equal t-work work) (equal t-verdict verdict)
             (equal (lptrace-events :arena-read trace) work)
             (equal (fn-lpt-constructor-cells trace) (fn-lpa-tick-conses s fuel fn-arena))
             (<= (fn-lpt-constructor-cells trace) (+ 4 (* 39 work)))) fn-arena)))))
(defun lptrace-exec (bytes fuel)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-arena
  (mv-let (result fn-arena) (lptrace-exec-case bytes fuel fn-arena) result)))
(assert-event
 (and (lptrace-exec '(83 58 32 120 13 10 13 10) 1)
      (lptrace-exec '(83 58 32 120 13 10 13 10) 8)
      (lptrace-exec '(13 10 0 13 10) 5)
      (lptrace-exec nil 0)))

(defthm lptrace-ascii-downcase-byte-projection-positive
 (equal (car (fn-lpt-ascii-downcase-byte 83)) (fn-article-ascii-downcase-byte 83))
 :rule-classes nil)

(defthm lptrace-at-projection-positive
 (equal (car (fn-lpt-at 2 '(a b c d))) (fn-lpc-at 2 '(a b c d)))
 :rule-classes nil)

(defthm lptrace-put-projection-positive
 (equal (car (fn-lpt-put 2 :replacement '(a b c d))) (fn-lpc-put 2 :replacement '(a b c d)))
 :rule-classes nil)

(defthm lptrace-span-projection-positive
 (equal (car (fn-lpt-span 0 1 3 :pin)) (fn-lpc-span 0 1 3 :pin))
 :rule-classes nil)

(defthm lptrace-name-byte-projection-positive
 (equal (car (fn-lpt-name-byte '(115 117) 83)) (fn-lpc-name-byte '(115 117) 83))
 :rule-classes nil)

(defthm lptrace-name-step-projection-positive
 (equal (car (fn-lpt-name-step *fn-lpc-names* 83)) (fn-lpc-name-step *fn-lpc-names* 83))
 :rule-classes nil)

(defthm lptrace-name-key-projection-positive
 (equal (car (fn-lpt-name-key *fn-lpc-names*)) (fn-lpc-name-key *fn-lpc-names*))
 :rule-classes nil)

(defthm lptrace-header-begin-projection-positive
 (equal (car (fn-lpt-header-begin )) (fn-lpc-header-begin ))
 :rule-classes nil)

(defthm lptrace-header-bad-projection-positive
 (equal (car (fn-lpt-header-bad '(:start 0 t t 0 1 4 (nil nil nil nil nil) (nil nil nil nil nil) t :plain))) (fn-lpc-header-bad '(:start 0 t t 0 1 4 (nil nil nil nil nil) (nil nil nil nil nil) t :plain)))
 :rule-classes nil)

(defthm lptrace-close-fields-projection-positive
 (equal (car (fn-lpt-close-fields '(:start 0 t t 0 1 4 (nil nil nil nil nil) (nil nil nil nil nil) t :plain) 0 :pin)) (fn-lpc-close-fields '(:start 0 t t 0 1 4 (nil nil nil nil nil) (nil nil nil nil nil) t :plain) 0 :pin))
 :rule-classes nil)

(defthm lptrace-value-byte-projection-positive
 (equal (car (fn-lpt-value-byte '(:start 0 t t 0 1 4 (nil nil nil nil nil) (nil nil nil nil nil) t :plain) 83 1)) (fn-lpc-value-byte '(:start 0 t t 0 1 4 (nil nil nil nil nil) (nil nil nil nil nil) t :plain) 83 1))
 :rule-classes nil)

(defthm lptrace-header-byte-projection-positive
 (equal (car (fn-lpt-header-byte '(:start 0 t t 0 1 4 (nil nil nil nil nil) (nil nil nil nil nil) t :plain) 83 1 0 :pin)) (fn-lpc-header-byte '(:start 0 t t 0 1 4 (nil nil nil nil nil) (nil nil nil nil nil) t :plain) 83 1 0 :pin))
 :rule-classes nil)

(defthm lptrace-split-byte-projection-positive
 (equal (car (fn-lpt-split-byte 3 83)) (fn-lpc-split-byte 3 83))
 :rule-classes nil)

(defthm lptrace-body-byte-projection-positive
 (equal (car (fn-lpt-body-byte '(:start 0 t t 0 1 4 (nil nil nil nil nil) (nil nil nil nil nil) t :plain) 83)) (fn-lpc-body-byte '(:start 0 t t 0 1 4 (nil nil nil nil nil) (nil nil nil nil nil) t :plain) 83))
 :rule-classes nil)

(defthm lptrace-begin-projection-positive
 (equal (car (fn-lpt-begin 0 8 :pin)) (fn-lpc-begin 0 8 :pin))
 :rule-classes nil)

(defthm lptrace-byte-projection-positive
 (equal (car (fn-lpt-byte (fn-lpc-begin 0 8 :pin) 83)) (fn-lpc-byte (fn-lpc-begin 0 8 :pin) 83))
 :rule-classes nil)

(defthm lptrace-verdict-projection-positive
 (equal (car (fn-lpt-verdict (fn-lpc-begin 0 8 :pin))) (fn-lpc-verdict (fn-lpc-begin 0 8 :pin)))
 :rule-classes nil)

(defthm lptrace-field-projection-positive
 (equal (car (fn-lpt-field (fn-lpc-begin 0 8 :pin) 0)) (fn-lpc-field (fn-lpc-begin 0 8 :pin) 0))
 :rule-classes nil)

(defthm lptrace-body-lines-projection-positive
 (equal (car (fn-lpt-body-lines (fn-lpc-begin 0 8 :pin))) (fn-lpc-body-lines (fn-lpc-begin 0 8 :pin)))
 :rule-classes nil)

(defthm lptrace-tombstonep-projection-positive
 (equal (car (fn-lpt-tombstonep (fn-lpc-begin 0 8 :pin))) (fn-lpc-tombstonep (fn-lpc-begin 0 8 :pin)))
 :rule-classes nil)

(defthm lptrace-ascii-downcase-byte-trace-constructor-cells-positive
 (equal (fn-lpt-constructor-cells (cdr (fn-lpt-ascii-downcase-byte 83))) 0)
 :rule-classes nil)

(defthm lptrace-at-trace-constructor-cells-positive
 (equal (fn-lpt-constructor-cells (cdr (fn-lpt-at 2 (quote (a b c d))))) 0)
 :rule-classes nil)

(defthm lptrace-put-trace-constructor-cells-positive
 (equal (fn-lpt-constructor-cells (cdr (fn-lpt-put 2 :replacement (quote (a b c d))))) (+ 1 (nfix 2)))
 :rule-classes nil)

(defthm lptrace-span-trace-constructor-cells-positive
 (equal (fn-lpt-constructor-cells (cdr (fn-lpt-span 0 1 3 :pin))) 4)
 :rule-classes nil)

(defthm lptrace-name-byte-trace-constructor-cells-positive
 (equal (fn-lpt-constructor-cells (cdr (fn-lpt-name-byte (quote (115 117)) 83))) 0)
 :rule-classes nil)

(defthm lptrace-name-step-trace-constructor-cells-positive
 (equal (fn-lpt-constructor-cells (cdr (fn-lpt-name-step (quote (nil :miss :miss :miss :miss)) 83))) 5)
 :rule-classes nil)

(defthm lptrace-name-key-trace-constructor-cells-positive
 (equal (fn-lpt-constructor-cells (cdr (fn-lpt-name-key (quote (nil :miss :miss :miss :miss))))) 0)
 :rule-classes nil)

(defthm lptrace-header-bad-trace-constructor-cells-positive
 (equal (fn-lpt-constructor-cells (cdr (fn-lpt-header-bad (quote (:start 0 t t 0 1 4 (nil nil nil nil nil) (nil nil nil nil nil) t :plain))))) 1)
 :rule-classes nil)

(defthm lptrace-close-fields-trace-constructor-cells-positive
 (equal (fn-lpt-constructor-cells (cdr (fn-lpt-close-fields (quote (:start 0 t t 0 1 4 (nil nil nil nil nil) (nil nil nil nil nil) t :plain)) 0 :pin))) (fn-lpa-close-conses (quote (:start 0 t t 0 1 4 (nil nil nil nil nil) (nil nil nil nil nil) t :plain))))
 :rule-classes nil)

(defthm lptrace-value-byte-trace-constructor-cells-positive
 (equal (fn-lpt-constructor-cells (cdr (fn-lpt-value-byte (quote (:start 0 t t 0 1 4 (nil nil nil nil nil) (nil nil nil nil nil) t :plain)) 83 1))) (fn-lpa-value-conses (quote (:start 0 t t 0 1 4 (nil nil nil nil nil) (nil nil nil nil nil) t :plain)) 83))
 :rule-classes nil)

(defthm lptrace-header-byte-trace-constructor-cells-positive
 (equal (fn-lpt-constructor-cells (cdr (fn-lpt-header-byte (quote (:start 0 t t 0 1 4 (nil nil nil nil nil) (nil nil nil nil nil) t :plain)) 83 1 0 :pin))) (fn-lpa-header-conses (quote (:start 0 t t 0 1 4 (nil nil nil nil nil) (nil nil nil nil nil) t :plain)) 83))
 :rule-classes nil)

(defthm lptrace-split-byte-trace-constructor-cells-positive
 (equal (fn-lpt-constructor-cells (cdr (fn-lpt-split-byte 3 83))) 0)
 :rule-classes nil)

(defthm lptrace-body-byte-trace-constructor-cells-positive
 (equal (fn-lpt-constructor-cells (cdr (fn-lpt-body-byte (quote (:start 0 t t 0 1 4 (nil nil nil nil nil) (nil nil nil nil nil) t :plain)) 83))) (fn-lpa-body-conses (quote (:start 0 t t 0 1 4 (nil nil nil nil nil) (nil nil nil nil nil) t :plain))))
 :rule-classes nil)

(defthm lptrace-byte-trace-constructor-cells-positive
 (equal (fn-lpt-constructor-cells (cdr (fn-lpt-byte (fn-lpc-begin 0 8 :pin) 83))) (fn-lpa-byte-conses (fn-lpc-begin 0 8 :pin) 83))
 :rule-classes nil)

(defthm lptrace-verdict-trace-constructor-cells-positive
 (equal (fn-lpt-constructor-cells (cdr (fn-lpt-verdict (fn-lpc-begin 0 8 :pin)))) 0)
 :rule-classes nil)

(defthm lptrace-stop-trace-constructor-cells-positive
 (equal (fn-lpt-constructor-cells (cdr (fn-lpt-stop (fn-lpc-begin 0 8 :pin) 1))) 0)
 :rule-classes nil)

(defthm lptrace-tick-trace-constructor-cells-positive
 (equal (fn-lpt-constructor-cells (mv-nth 4 (fn-lpt-tick (fn-lpc-begin 0 8 :pin) 1 (quote ((83 58 32 120 13 10 13 10)))))) (fn-lpa-tick-conses (fn-lpc-begin 0 8 :pin) 1 (quote ((83 58 32 120 13 10 13 10)))))
 :rule-classes nil)

(defthm lptrace-tick-trace-constructor-cells-bounded-by-work-positive
 (<= (fn-lpt-constructor-cells (mv-nth 4 (fn-lpt-tick (fn-lpc-begin 0 8 :pin) 1 (quote ((83 58 32 120 13 10 13 10)))))) (+ 4 (* 39 (mv-nth 2 (fn-lpc-tick (fn-lpc-begin 0 8 :pin) 1 (quote ((83 58 32 120 13 10 13 10))))))))
 :rule-classes nil)
