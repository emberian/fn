; SCN-1009: executable checks against fn-hnov-of and fn-hf-body-lines-of.
; These fixtures exercise the full reference, not an approximate parser.
(in-package "ACL2")
(include-book "../../books/legacy-parser-reference")

(defconst *lpct-all-fields* '(83 117 98 106 101 99 116 58 32 79 110 101 13 10 70 114 111 109 58 9 87 114 105 116 101 114 13 10 68 97 116 101 58 32 84 117 101 13 10 77 101 115 115 97 103 101 45 73 68 58 32 60 120 64 121 62 13 10 82 101 102 101 114 101 110 99 101 115 58 32 60 97 64 121 62 13 10 13 10 98 111 100 121 13 10))
(assert-event (fn-lpc-agreesp *lpct-all-fields* '(:origin 17)))

(defconst *lpct-first-header* '(115 85 98 74 101 67 116 58 32 102 105 114 115 116 13 10 83 117 98 106 101 99 116 58 32 115 101 99 111 110 100 13 10 13 10))
(assert-event (fn-lpc-agreesp *lpct-first-header* '(:origin 17)))

(defconst *lpct-folded* '(83 117 98 106 101 99 116 58 32 111 110 101 13 10 9 116 119 111 13 10 32 116 104 114 101 101 13 10 13 10))
(assert-event (fn-lpc-agreesp *lpct-folded* '(:origin 17)))

(defconst *lpct-empty-first-value* '(82 101 102 101 114 101 110 99 101 115 58 13 10 32 60 97 64 121 62 13 10 13 10))
(assert-event (fn-lpc-agreesp *lpct-empty-first-value* '(:origin 17)))

(defconst *lpct-one-space-only* '(83 117 98 106 101 99 116 58 32 32 116 119 111 32 115 112 97 99 101 115 13 10 13 10))
(assert-event (fn-lpc-agreesp *lpct-one-space-only* '(:origin 17)))

(defconst *lpct-first-tab* '(83 117 98 106 101 99 116 58 9 111 110 101 13 10 13 10))
(assert-event (fn-lpc-agreesp *lpct-first-tab* '(:origin 17)))

(defconst *lpct-leading-empty-fold* '(83 117 98 106 101 99 116 58 32 13 10 32 111 110 101 13 10 13 10))
(assert-event (fn-lpc-agreesp *lpct-leading-empty-fold* '(:origin 17)))

(defconst *lpct-missing-fields* '(88 45 79 116 104 101 114 58 32 118 97 108 117 101 13 10 13 10))
(assert-event (fn-lpc-agreesp *lpct-missing-fields* '(:origin 17)))

(defconst *lpct-empty-header* '(13 10 98 111 100 121 13 10))
(assert-event (fn-lpc-agreesp *lpct-empty-header* '(:origin 17)))

(defconst *lpct-no-separator* '(83 117 98 106 101 99 116 58 32 120 13 10))
(assert-event (fn-lpc-agreesp *lpct-no-separator* '(:origin 17)))

(defconst *lpct-orphan-fold* '(32 98 97 100 13 10 13 10 98 111 100 121 13 10))
(assert-event (fn-lpc-agreesp *lpct-orphan-fold* '(:origin 17)))

(defconst *lpct-no-colon* '(83 117 98 106 101 99 116 32 120 13 10 13 10 98 111 100 121 13 10))
(assert-event (fn-lpc-agreesp *lpct-no-colon* '(:origin 17)))

(defconst *lpct-empty-name* '(58 32 120 13 10 13 10))
(assert-event (fn-lpc-agreesp *lpct-empty-name* '(:origin 17)))

(defconst *lpct-no-leading-wsp* '(83 117 98 106 101 99 116 58 120 13 10 13 10))
(assert-event (fn-lpc-agreesp *lpct-no-leading-wsp* '(:origin 17)))

(defconst *lpct-invalid-name* '(66 97 100 32 78 97 109 101 58 32 120 13 10 13 10))
(assert-event (fn-lpc-agreesp *lpct-invalid-name* '(:origin 17)))

(defconst *lpct-empty-field* '(83 117 98 106 101 99 116 58 32 13 10 13 10))
(assert-event (fn-lpc-agreesp *lpct-empty-field* '(:origin 17)))

(defconst *lpct-empty-field-before-next* '(83 117 98 106 101 99 116 58 32 13 10 70 114 111 109 58 32 120 13 10 13 10))
(assert-event (fn-lpc-agreesp *lpct-empty-field-before-next* '(:origin 17)))

(defconst *lpct-bad-header-nul* '(83 117 98 106 101 99 116 58 32 120 0 121 13 10 13 10 98 111 100 121 13 10))
(assert-event (fn-lpc-agreesp *lpct-bad-header-nul* '(:origin 17)))

(defconst *lpct-bare-header-lf* '(83 117 98 106 101 99 116 58 32 120 10 121 13 10 13 10 98 111 100 121 13 10))
(assert-event (fn-lpc-agreesp *lpct-bare-header-lf* '(:origin 17)))

(defconst *lpct-bare-header-cr* '(83 117 98 106 101 99 116 58 32 120 13 121 13 10 13 10 98 111 100 121 13 10))
(assert-event (fn-lpc-agreesp *lpct-bare-header-cr* '(:origin 17)))

(defconst *lpct-body-nul* '(83 117 98 106 101 99 116 58 32 120 13 10 13 10 120 0 121 13 10))
(assert-event (fn-lpc-agreesp *lpct-body-nul* '(:origin 17)))

(defconst *lpct-body-unterminated* '(83 117 98 106 101 99 116 58 32 120 13 10 13 10 108 97 115 116))
(assert-event (fn-lpc-agreesp *lpct-body-unterminated* '(:origin 17)))

(defconst *lpct-body-bare-cr* '(83 117 98 106 101 99 116 58 32 120 13 10 13 10 120 13))
(assert-event (fn-lpc-agreesp *lpct-body-bare-cr* '(:origin 17)))

(defconst *lpct-body-bare-lf* '(83 117 98 106 101 99 116 58 32 120 13 10 13 10 120 10))
(assert-event (fn-lpc-agreesp *lpct-body-bare-lf* '(:origin 17)))

(defconst *lpct-body-high-byte* '(83 117 98 106 101 99 116 58 32 120 13 10 13 10 255 13 10))
(assert-event (fn-lpc-agreesp *lpct-body-high-byte* '(:origin 17)))

(defconst *lpct-empty-source* '())
(assert-event (fn-lpc-agreesp *lpct-empty-source* '(:origin 17)))

; Boundary physical line lengths, folds exceeding a quantum, and malformed
; field closure after an otherwise complete selected first field.
(assert-event (fn-lpc-agreesp
 (append '(83 117 98 106 101 99 116 58 32) (make-list-ac 989 120 nil) '(13 10 13 10)) :pin))
(assert-event (fn-lpc-agreesp
 (append '(83 117 98 106 101 99 116 58 32) (make-list-ac 990 120 nil) '(13 10 13 10)) :pin))
(assert-event (fn-lpc-agreesp
 (append '(83 117 98 106 101 99 116 58 13 10 32)
         (make-list-ac 997 120 nil) '(13 10 13 10)) :pin))

; REACHABLE positive: literal complete antecedent/conclusion for bounded
; work, source retention, maintained guard and productive progress.
(defthm lpct-tick-positive
  (let* ((arena (list *lpct-all-fields*))
         (s (fn-lpc-begin 0 (len *lpct-all-fields*) '(:origin 17)))
         (r (fn-lpc-tick s 3 arena)) (out (mv-nth 0 r)))
    (and (natp 3) (fn-lpc-ready-p s arena) (posp 3)
         (< (fn-lpc-at 3 s) (fn-lpc-at 1 s))
         (natp (mv-nth 1 r)) (equal (mv-nth 1 r) (mv-nth 2 r))
         (<= (mv-nth 2 r) 3) (< 0 (mv-nth 2 r))
         (equal (fn-lpc-at 0 out) (fn-lpc-at 0 s))
         (equal (fn-lpc-at 1 out) (fn-lpc-at 1 s))
         (equal (fn-lpc-at 2 out) (fn-lpc-at 2 s))
         (fn-lpc-ready-p out arena)
         (equal (fn-lpc-at 3 out) (+ (fn-lpc-at 3 s) (mv-nth 1 r)))))
  :rule-classes nil)

; HYPOTHESIS REMOVAL: a negative budget violates the literal <= fuel
; conclusion. There are no other premises on fn-lpc-tick-bounded.
(defthm lpct-without-natural-fuel
  (let* ((s (fn-lpc-begin 0 3 :pin))
         (r (fn-lpc-tick s -1 '((65 66 67)))))
    (and (not (natp -1)) (not (<= (mv-nth 2 r) -1))))
  :rule-classes nil)

; MUTATION: selecting the last duplicate would overwrite the first field.
(assert-event
 (let* ((s (fn-lpc-feed *lpct-first-header*
                       (fn-lpc-begin 0 (len *lpct-first-header*) :pin)))
        (got (fn-lpc-span-value (fn-lpc-field s 0) (list *lpct-first-header*))))
   (and (eq (fn-lpc-verdict s) :valid)
        (equal got '(102 105 114 115 116))
        (not (equal got '(115 101 99 111 110 100))))))

; Literal unconditional body-facts theorem, on actual arena ticks with a
; valid article and with rejected header grammar but a valid nonempty body.
(defthm lpct-body-facts-positive
  (let* ((arena (list *lpct-all-fields* *lpct-orphan-fold*))
         (n0 (fn-arena-payload-len 0 arena))
         (n1 (fn-arena-payload-len 1 arena))
         (s0 (mv-nth 0 (fn-lpc-tick (fn-lpc-begin 0 n0 :pin) n0 arena)))
         (s1 (mv-nth 0 (fn-lpc-tick (fn-lpc-begin 1 n1 :pin) n1 arena))))
    (and (equal (fn-lpc-body-lines s0) (fn-hf-body-lines-of (nth 0 arena)))
         (equal (fn-lpc-body-lines s1) (fn-hf-body-lines-of (nth 1 arena)))
         (eq (fn-lpc-verdict s0) :valid)
         (eq (fn-lpc-verdict s1) :invalid)
         (equal (fn-lpc-body-lines s0) 1)
         (equal (fn-lpc-body-lines s1) 1)))
  :rule-classes nil)

; CORRUPTED STATE: dropping the ready premise need not produce a ready
; output. No hypotheses remain in the literal preservation theorem.
(defthm lpct-without-ready-corrupted-handle
  (let* ((arena '((65 66 67))) (s (fn-lpc-begin 8 3 :pin))
         (out (mv-nth 0 (fn-lpc-tick s 1 arena))))
    (and (not (fn-lpc-ready-p s arena))
         (not (fn-lpc-ready-p out arena))))
  :rule-classes nil)

; HYPOTHESIS REMOVAL: the numeric position equation needs natural offset.
(defthm lpct-without-natural-offset
  (let* ((arena '((65 66 67)))
         (s (fn-lpc-put 3 -1 (fn-lpc-begin 0 3 :pin)))
         (r (fn-lpc-tick s 1 arena)))
    (and (not (natp (fn-lpc-at 3 s)))
         (not (equal (fn-lpc-at 3 (mv-nth 0 r))
                     (+ (fn-lpc-at 3 s) (mv-nth 1 r))))))
  :rule-classes nil)

; MUTATION: trimming all initial whitespace changes the second initial SP.
(assert-event
 (let* ((s (fn-lpc-feed *lpct-one-space-only*
                       (fn-lpc-begin 0 (len *lpct-one-space-only*) :pin)))
        (span (fn-lpc-field s 0))
        (good (fn-lpc-span-value span (list *lpct-one-space-only*))))
   (and (equal (car good) 32)
        (not (equal good (cdr good))))))

(defun lpct-chunked (s fuel steps fn-arena)
  (declare (xargs :stobjs fn-arena :measure (nfix steps) :verify-guards nil))
  (if (or (zp steps) (not (eq (fn-lpc-verdict s) :yield))) s
    (mv-let (next consumed work verdict) (fn-lpc-tick s fuel fn-arena)
      (declare (ignore consumed work verdict))
      (lpct-chunked next fuel (1- steps) fn-arena))))

(defun lpct-chunked-case (bytes fuel fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-arena (fn-arena-seal-list bytes fn-arena))
         (s (lpct-chunked (fn-lpc-begin 0 (len bytes) '(:origin 17))
                         fuel (+ 1 (len bytes)) fn-arena)))
    (mv (and (equal (fn-lpc-nov-value s (list bytes)) (fn-hnov-of bytes))
             (equal (fn-lpc-body-lines s) (fn-hf-body-lines-of bytes))
             (not (eq (fn-lpc-verdict s) :yield))
             (equal (fn-lpc-at 2 s) '(:origin 17))) fn-arena)))

(defun lpct-chunked-exec (bytes fuel)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena) (lpct-chunked-case bytes fuel fn-arena) result)))

; W=1 crosses every byte boundary; W=3 crosses different line/header cuts.
(assert-event (and (lpct-chunked-exec *lpct-all-fields* 1)
                   (lpct-chunked-exec *lpct-folded* 1)
                   (lpct-chunked-exec *lpct-empty-first-value* 1)
                   (lpct-chunked-exec *lpct-first-header* 1)
                   (lpct-chunked-exec *lpct-body-nul* 1)
                   (lpct-chunked-exec *lpct-orphan-fold* 1)
                   (lpct-chunked-exec *lpct-all-fields* 3)))
