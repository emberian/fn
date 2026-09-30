; Structural source-cons demand only: runtime allocation remains open.
(in-package "ACL2")
(include-book "../../books/legacy-parser-allocation")

; Reachable begin/first-field tick: exact actual work plus model ceiling.
(defthm lpalloc-first-field-positive
  (let* ((arena '((83 58 32 120 13 10 13 10)))
         (s (fn-lpc-begin 0 8 :pin)) (fuel 3)
         (work (mv-nth 2 (fn-lpc-tick s fuel arena)))
         (demand (fn-lpa-tick-conses s fuel arena)))
    (and (natp fuel) (equal work 3) (natp demand)
         (<= demand (+ 4 (* 39 work)))
         (<= demand (+ 4 (* 39 fuel)))))
  :rule-classes nil)

; Empty and zero fuel return exactly the final four-cell tuple inventory.
(defthm lpalloc-zero-fuel-positive
  (let* ((arena '((83 58 32 120 13 10 13 10)))
         (s (fn-lpc-begin 0 8 :pin)) (fuel 0)
         (work (mv-nth 2 (fn-lpc-tick s fuel arena))))
    (and (natp fuel) (equal work 0) (equal (fn-lpa-tick-conses s fuel arena) 4)
         (<= (fn-lpa-tick-conses s fuel arena) (+ 4 (* 39 work)))
         (<= (fn-lpa-tick-conses s fuel arena) (+ 4 (* 39 fuel)))))
  :rule-classes nil)

; HYPOTHESIS REMOVAL: negative logical fuel stops immediately. Its natural
; antecedent fails, while the affine bound becomes negative and fails too.
(defthm lpalloc-without-natural-fuel
  (let* ((arena '((83))) (s (fn-lpc-begin 0 1 :pin)) (fuel -1))
    (and (not (natp fuel)) (equal (fn-lpa-tick-conses s fuel arena) 4)
         (not (<= (fn-lpa-tick-conses s fuel arena) (+ 4 (* 39 fuel))))))
  :rule-classes nil)

; Exact constructor arms. The fields are a carried current References field,
; about to be closed when a new Subject begins. Four new span cells plus
; five copied cells of the selected fields spine are transient, not output size.
(defconst *lpalloc-close-last* '(:start 0 t t 0 1 4 (nil nil nil nil nil) (nil nil nil nil nil) t :plain))
(assert-event
 (and (equal (fn-lpa-close-conses *lpalloc-close-last*) 9)
      (equal (fn-lpa-header-conses *lpalloc-close-last* 83) 25)
      (equal (fn-lpa-header-conses (fn-lpc-header-begin) 83) 16)
      (equal (fn-lpa-header-conses '(:name) 58) 10)
      (equal (fn-lpa-header-conses '(:name) 83) 15)
      (equal (fn-lpa-header-conses '(:cr-start) 10) 10)
      (equal (fn-lpa-body-conses '(:bad 4)) 0)
      (equal (fn-lpa-body-conses '(:line 4)) 2)))

; MUTATION: counting only the newly returned header/name spines omits the
; nine span/path-copy constructors of this reachable selected-key branch.
(assert-event
 (let ((correct (fn-lpa-header-conses *lpalloc-close-last* 83)) (mutated (+ 11 5)))
   (and (equal correct 25) (<= correct 25) (not (equal mutated correct)))))

; Real stobj execution observes the same demanded model at byte quanta.
(defun lpalloc-exec-case (bytes fuel fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-arena (fn-arena-seal-list bytes fn-arena))
         (s (fn-lpc-begin 0 (len bytes) :pin))
         (demand (fn-lpa-tick-conses s fuel fn-arena)))
    (mv-let (next consumed work verdict) (fn-lpc-tick s fuel fn-arena)
      (declare (ignore next verdict))
      (mv (and (natp fuel) (equal consumed work) (<= work fuel)
               (natp demand) (<= demand (+ 4 (* 39 work)))
               (<= demand (+ 4 (* 39 fuel)))) fn-arena))))
(defun lpalloc-exec (bytes fuel)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena) (lpalloc-exec-case bytes fuel fn-arena) result)))
(assert-event
 (and (lpalloc-exec '(83 58 32 120 13 10 13 10) 1)
      (lpalloc-exec '(83 58 32 120 13 10 13 10) 3)
      (lpalloc-exec '(83 58 32 120 13 10 13 10) 8)
      (lpalloc-exec '(13 10 0 13 10) 5)
      (lpalloc-exec nil 0)))
