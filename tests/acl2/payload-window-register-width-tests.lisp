; SCN-1039 continuation: literal whole-quantum state carry witnesses.
; Invalid uint8 representation witnesses execute only the ACL2 logical model.
(in-package "ACL2")
(include-book "../../books/payload-window-register-width")

(defun-nx pzwrwt-stored-probe (mode bits nbits code length n table input quantum)
  (let* ((state (fn-zin-reset (create-fn-zin-st)))
         (state (fn-zin-set 0 mode state))
         (state (fn-zin-set 1 bits state))
         (state (fn-zin-set 2 nbits state))
         (state (fn-zin-set 3 n state))
         (state (fn-zin-set 8 code state))
         (state (fn-zin-set 11 length state))
         (state (fn-zin-set 14 257 state))
         (state (fn-zin-set 15 1 state))
         (r (fn-pzw-stored-chunk quantum quantum 0 (len input) (len input) 100
                                 state input
                                 (make-list 65536 :initial-element 0) table nil))
         (after (mv-nth 3 r)))
    (list (fn-pzw-state-walk-widthp state)
          (not (equal (car r) '(:refused :bad-code)))
          (fn-pzw-state-walk-widthp after)
          (fn-pzw-state-walk-scalarp after)
          (fn-pzw-state-header-widthp state)
          (fn-pzw-table-representationp table)
          (fn-pzw-state-header-widthp after)
          (car r)
          (fn-pzw-state-walk-scalarp (fn-zin-set 8 40000 after))
          (fn-pzw-state-header-widthp (fn-zin-set 18 32769 after))
          (fn-pzw-state-walk-widthp (fn-zin-set 8 40000 after)))))

; Literal positive witnesses for both strong non-bad-code carry and the
; unconditional all-exit scalar theorem; actual quantum pulls one255octet.
(defthm pzwrwt-actual-stored-register-positive
  (let ((r (pzwrwt-stored-probe 0 0 0 0 1 0
                               (make-list 3494 :initial-element 0) '(255) 1)))
    (and (nth 0 r) (nth 1 r) (nth 2 r) (nth 3 r)
         (nth 4 r) (nth 5 r) (nth 6 r)
         (equal (nth 7 r) :yield)))
  :rule-classes nil)

; Omit the initial strong register carry. Non-bad-code remains true, and
; both literal strong and all-exit scalar conclusions affirmatively fail.
(defthm pzwrwt-remove-walk-carry
  (let ((r (pzwrwt-stored-probe 0 0 0 40000 1 0
                               (make-list 3494 :initial-element 0) nil 0)))
    (and (not (nth 0 r)) (nth 1 r) (not (nth 2 r)) (not (nth 3 r))))
  :rule-classes nil)

; Omit only the non-bad-code exit premise. All carried strong registers
; hold on entry, but the deepest malformed code breaks length-relative
; carry. Its scalar registers still meet the separate all-exit theorem.
(defthm pzwrwt-remove-non-bad-code
  (let ((r (pzwrwt-stored-probe 8 1 1 32766 15 0
                               (make-list 3494 :initial-element 0) nil 1)))
    (and (nth 0 r) (not (nth 1 r)) (not (nth 2 r)) (nth 3 r)
         (equal (nth 7 r) '(:refused :bad-code))))
  :rule-classes nil)

; Header carry removal retains the complete fixed table representation.
(defthm pzwrwt-remove-header-carry
  (let ((r (pzwrwt-stored-probe 0 0 0 0 1 65536
                               (make-list 3494 :initial-element 0) nil 0)))
    (and (not (nth 4 r)) (nth 5 r) (not (nth 6 r))))
  :rule-classes nil)

; Invalid table representation (not native vector corruption). The actual
; code-length symbol decode sees65536, writes it to SYM and breaks header
; width. Initial header carry is true, table representation and conclusion
; are affirmatively false. Exact length3494 is retained.
(defthm pzwrwt-remove-table-representation
  (let* ((table (update-nth 1376 65536
                            (update-nth 1346 1 (make-list 3494 :initial-element 0))))
         (r (pzwrwt-stored-probe 6 0 1 0 1 0 table nil 1)))
    (and (nth 4 r) (not (nth 5 r)) (not (nth 6 r))))
  :rule-classes nil)

; Labelled post-state mutations, each retains the complete literal
; antecedent and the actual conclusion before corrupting one register.
(defthm pzwrwt-register-mutations
  (let ((r (pzwrwt-stored-probe 0 0 0 0 1 0
                               (make-list 3494 :initial-element 0) '(255) 1)))
    (and (nth 0 r) (nth 1 r) (nth 2 r) (nth 3 r)
         (nth 4 r) (nth 5 r) (nth 6 r)
         (not (nth 8 r)) (not (nth 9 r)) (not (nth 10 r))))
  :rule-classes nil)

(defun-nx pzwrwt-initialize-probe ()
  (let* ((state (fn-zin-set 3 (expt 2 100) (create-fn-zin-st)))
         (state (fn-zin-set 8 40000 state))
         (state (fn-zin-set 18 (expt 2 100) state))
         (r (fn-pzw-initialize '(1 2 3) state nil nil nil))
         (after (car r)))
    (list (fn-pzw-state-walk-widthp after)
          (fn-pzw-state-header-widthp after)
          (fn-zin-preset after)
          (fn-pzw-state-walk-widthp (fn-zin-set 8 1 after))
          (fn-pzw-state-header-widthp (fn-zin-set 18 32769 after)))))

; Both actual initializer theorems are unconditional. Corrupt previous
; fields are replaced, the exact preset length is3, and labelled mutants
; negate each literal conclusion after initialization.
(defthm pzwrwt-actual-initialize-positive-and-mutations
  (equal (pzwrwt-initialize-probe) '(t t 3 nil nil))
  :rule-classes nil)
