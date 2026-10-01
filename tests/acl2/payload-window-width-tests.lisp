; SCN-1039. Ground logical witnesses: invalid representation witnesses are
; intentionally logical only; no native uint8 vector is populated with256.
(in-package "ACL2")
(include-book "../../books/payload-window-width")

(defun-nx pzwwt-stored-probe (nbits bits input quantum)
  (let* ((state (fn-zin-reset (create-fn-zin-st)))
         (state (fn-zin-set 1 bits state))
         (state (fn-zin-set 2 nbits state))
         (r (fn-pzw-stored-chunk quantum quantum 0 (len input) (len input) 100
                                  state input
                                  (make-list 65536 :initial-element 0)
                                  (make-list 3494 :initial-element 0) nil))
         (after (mv-nth 3 r)))
    (list (fn-pzw-state-bits-widthp state) (fn-cbor-octet-listp input)
          (fn-pzw-state-bits-widthp after) (fn-zin-nbits after)
          (fn-zin-bits after)
          (fn-pzw-state-bits-widthp
           (fn-zin-set 2 (1- (fn-zin-nbits after)) after)))))

; Literal complete antecedent and conclusion of actual-stored-chunk-bits-width.
(defthm pzwwt-stored-bits-positive
  (equal (pzwwt-stored-probe 0 0 '(255) 1) '(t t t 8 255 nil))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-pzw-actual-stored-chunk-bits-width))))

; Retains the octet input hypothesis, negates the omitted carried-state
; hypothesis, and affirmatively negates the literal conclusion.
(defthm pzwwt-stored-remove-bits-carry
  (let ((r (pzwwt-stored-probe 40 0 '(0) 0)))
    (and (not (car r)) (cadr r) (not (caddr r))))
  :rule-classes nil)

; Invalid-representation hypothesis removal, distinct from native corruption:
; every retained scalar carry hypothesis holds; input-octet and conclusion fail.
(defthm pzwwt-stored-remove-octet-input
  (let ((r (pzwwt-stored-probe 0 0 '(256) 1)))
    (and (car r) (not (cadr r)) (not (caddr r))))
  :rule-classes nil)

; Mutation: the actual pull records8 bits; recording7 after the same255 byte
; breaks the carry. This is a labelled mutant, not a hypothesis removal.
(defthm pzwwt-stored-bit-count-mutation
  (let ((r (pzwwt-stored-probe 0 0 '(255) 1)))
    (and (car r) (cadr r) (caddr r) (equal (nth 3 r) 8)
         (equal (nth 4 r) 255) (not (nth 5 r))))
  :rule-classes nil)

(defun-nx pzwwt-walk-probe (code first index length table nbits)
  (let ((r (fn-zin-walk 0 0 nbits code first index length table)))
    (list (fn-pzw-walk-widthp code first index length)
          (fn-cbor-octet-listp table) (natp nbits)
          (not (equal (car r) 2))
          (fn-pzw-walk-widthp (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r) (mv-nth 7 r))
          (and (natp (mv-nth 4 r)) (<= (mv-nth 4 r) 32767)
               (natp (mv-nth 5 r)) (<= (mv-nth 5 r) 2147319810)
               (natp (mv-nth 6 r)) (<= (mv-nth 6 r) 917490)
               (integerp (mv-nth 7 r)) (<= 1 (mv-nth 7 r)) (<= (mv-nth 7 r) 15)))))

; A suspended symbol and the deepest malformed-code refusal both use the
; literal actual walker, not a separately implemented Huffman machine.
(defthm pzwwt-walk-suspension-positive
  (equal (pzwwt-walk-probe 0 0 0 1 (make-list 3494 :initial-element 0) 1) '(t t t t t t))
  :rule-classes nil)

(defthm pzwwt-walk-malformed-refusal-positive
  (equal (pzwwt-walk-probe 0 0 0 1 (make-list 3494 :initial-element 0) 15) '(t t t nil t t))
  :rule-classes nil)

; A corrupt suspended register stays corrupt if zero bits arrive. All other
; literal hypotheses are true, non-error conclusion is affirmatively false.
(defthm pzwwt-walk-remove-register-carry
  (equal (pzwwt-walk-probe 40000 0 0 1 (make-list 3494 :initial-element 0) 0) '(nil t t t nil nil))
  :rule-classes nil)

; Retains the carried registers; the omitted non-error premise is false.
; The literal length-relative carry fails after this deepest bad-code exit.
(defthm pzwwt-walk-remove-non-error
  (let* ((r (fn-zin-walk 0 1 1 32766 0 0 15
                         (make-list 3494 :initial-element 0))))
    (and (fn-pzw-walk-widthp 32766 0 0 15)
         (equal (car r) 2)
         (not (fn-pzw-walk-widthp (mv-nth 4 r) (mv-nth 5 r)
                                  (mv-nth 6 r) (mv-nth 7 r)))
         (equal (mv-nth 4 r) 32767)))
  :rule-classes nil)

(defun-nx pzwwt-initialize-probe ()
  (let* ((state (fn-zin-set 1 (expt 2 100) (create-fn-zin-st)))
         (state (fn-zin-set 2 100 state))
         (r (fn-pzw-initialize nil state nil nil nil))
         (after (mv-nth 0 r)))
    (list (fn-pzw-state-bits-widthp after) (fn-zin-bits after)
          (fn-zin-nbits after)
          (fn-pzw-state-bits-widthp (fn-zin-set 2 40 after)))))

; The actual initializer's theorem has no hypotheses: even corrupt previous
; registers are replaced. The fourth answer is a labelled post-init mutant.
(defthm pzwwt-actual-initialize-positive-and-mutation
  (equal (pzwwt-initialize-probe) '(t 0 0 nil))
  :rule-classes nil)

(defun-nx pzwwt-stored-span-probe (start end quantum)
  (let* ((r (fn-pzw-stored-chunk quantum quantum start end 1 100
                                  (fn-zin-reset (create-fn-zin-st)) '(255)
                                  (make-list 65536 :initial-element 0)
                                  (make-list 3494 :initial-element 0) nil))
         (ip (mv-nth 2 r)))
    (list (natp start) (<= start end) (natp ip) (<= start ip) (<= ip end) ip)))

(defthm pzwwt-actual-stored-input-span-positive
  (equal (pzwwt-stored-span-probe 0 1 1) '(t t t t t 1))
  :rule-classes nil)

; Logical guard/representation removal: no negative physical buffer index is
; issued. Retained START<=END holds, omitted nat-START and nat-IP fail.
(defthm pzwwt-input-span-remove-natural-start
  (equal (pzwwt-stored-span-probe -1 1 0) '(nil t nil t t -1))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (pzwwt-stored-span-probe fn-pzw-stored-chunk fn-pzw-chunk fn-zin-feed fn-zin-loop)
                ((:executable-counterpart pzwwt-stored-span-probe)
                 (:executable-counterpart fn-pzw-stored-chunk)
                 (:executable-counterpart fn-pzw-chunk)
                 (:executable-counterpart fn-zin-feed)
                 (:executable-counterpart fn-zin-loop))))))

; Retains natural START; reverses the span. IP remains START on a zero
; quantum, affirmatively contradicting the literal IP<=END conclusion.
(defthm pzwwt-input-span-remove-order
  (equal (pzwwt-stored-span-probe 1 0 0) '(t nil t t nil 1))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (pzwwt-stored-span-probe fn-pzw-stored-chunk fn-pzw-chunk fn-zin-feed fn-zin-loop)
                ((:executable-counterpart pzwwt-stored-span-probe)
                 (:executable-counterpart fn-pzw-stored-chunk)
                 (:executable-counterpart fn-pzw-chunk)
                 (:executable-counterpart fn-zin-feed)
                 (:executable-counterpart fn-zin-loop))))))

; Mutation: an otherwise positive returned span with one extra consumed byte.
(defthm pzwwt-input-span-ip-mutation
  (let ((r (pzwwt-stored-span-probe 0 1 1)))
    (and (car r) (cadr r) (caddr r) (nth 3 r) (nth 4 r)
         (equal (nth 5 r) 1) (not (<= (1+ (nth 5 r)) 1))))
  :rule-classes nil)

; Mutation: the actual suspended walk satisfies both endpoints, while a
; substituted40000 output code violates each literal register conclusion.
(defthm pzwwt-walk-output-code-mutation
  (let ((r (fn-zin-walk 0 0 1 0 0 0 1 (make-list 3494 :initial-element 0))))
    (and (fn-pzw-walk-widthp 0 0 0 1) (not (equal (car r) 2))
         (fn-pzw-walk-widthp (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r) (mv-nth 7 r))
         (natp (mv-nth 4 r)) (<= (mv-nth 4 r) 32767)
         (natp (mv-nth 5 r)) (<= (mv-nth 5 r) 2147319810)
         (natp (mv-nth 6 r)) (<= (mv-nth 6 r) 917490)
         (integerp (mv-nth 7 r)) (<= 1 (mv-nth 7 r)) (<= (mv-nth 7 r) 15)
         (not (fn-pzw-walk-widthp 40000 (mv-nth 5 r) (mv-nth 6 r) (mv-nth 7 r)))
         (not (<= 40000 32767))))
  :rule-classes nil)
