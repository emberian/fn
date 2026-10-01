; Teeth for books/checkpoint-reserve (lane recovery-refinement, 2026-10-01):
; fn-ckr-two-generations-fit-the-reserve-at-every-cut on the quiet ground
; store of tests/acl2/byte-store-state-checkpoint-program-tests.lisp (an old
; checkpoint of two octets at inode 3, next inode 5, a new one of three
; octets), at every state of the publish run; then the violating values:
; a new image past the bound, and an old one past it, each refused.
(in-package "ACL2")
(include-book "must-fail-checked")
(include-book "../../books/checkpoint-reserve")

(defconst *ckr-t-bs*
  (fn-bs-make 4 (list (cons 3 '(7 7)))
              (list (cons :root (list (cons "store-checkpoint.fnsc" 3)))
                    (cons :staging nil))
              nil 5))
(defconst *ckr-t-octets* '(1 2 3))
(defconst *ckr-t-run*
  (fn-bs-run *ckr-t-bs* nil (fn-bs-scp-program ".stage-state-checkpoint-1" *ckr-t-octets*)
             nil nil 0))

; Reachable: the quiet store, the whole run (ten states), both images within
; the bound 3, and every state's two generations within 2 * 3.
(assert-event
 (and (fn-bs-scp-inputp *ckr-t-bs* ".stage-state-checkpoint-1" 3)
      (equal (len *ckr-t-run*) 10)
      (<= (len *ckr-t-octets*) 3)
      (<= (len (fn-bs-durable-content *ckr-t-bs* 3)) 3)
      (fn-ckr-all-fit *ckr-t-run* 3 5 3)
      ; the two generations at the staged-durable cut: 2 + 3 octets
      (equal (fn-ckr-generations-octets (car (nth 5 *ckr-t-run*)) 3 5) 5)
      ; the reserve over a profile's bounds is two file bounds
      (equal (fn-ckr-reserve-octets 1000 100)
             (* 2 (fn-sccr-file-read-bound 1000 100)))))

; The first publication: no old image, the new one alone.
(defconst *ckr-t-fresh*
  (fn-bs-make 4 (list (cons 3 '(7 7)))
              (list (cons :root nil) (cons :staging nil))
              nil 5))
(assert-event
 (and (fn-bs-scp-inputp *ckr-t-fresh* ".stage-state-checkpoint-1" nil)
      (fn-ckr-all-fit (fn-bs-run *ckr-t-fresh* nil
                                 (fn-bs-scp-program ".stage-state-checkpoint-1" *ckr-t-octets*)
                                 nil nil 0)
                      nil 5 3)))

; Violating values, one hypothesis removed each (the Codex review of
; 2d1b10ed7, F3).  A new image of three octets under the bound 2: the old
; image (two octets) is within the bound, the new one is not, and the
; staged-durable state holds 2 + 3 > 2 * 2.
(assert-event
 (and (<= (len (fn-bs-durable-content *ckr-t-bs* 3)) 2)      ; old within: kept
      (not (<= (len *ckr-t-octets*) 2))                      ; new past: removed
      (not (fn-ckr-all-fit *ckr-t-run* 3 5 2))))             ; the conclusion fails
(must-fail-checked
 (defthm ckr-t-new-image-past-the-bound
   (fn-ckr-all-fit *ckr-t-run* 3 5 2)))
; An old image past the bound (five octets, bound 3): the new image (three
; octets) is within the bound, the old one is not, and 5 + 3 > 2 * 3.
(defconst *ckr-t-big-old*
  (fn-bs-make 4 (list (cons 3 '(7 7 7 7 7)))
              (list (cons :root (list (cons "store-checkpoint.fnsc" 3)))
                    (cons :staging nil))
              nil 5))
(defconst *ckr-t-big-old-run*
  (fn-bs-run *ckr-t-big-old* nil (fn-bs-scp-program ".stage-state-checkpoint-1" *ckr-t-octets*)
             nil nil 0))
(assert-event
 (and (fn-bs-scp-inputp *ckr-t-big-old* ".stage-state-checkpoint-1" 3)  ; kept
      (<= (len *ckr-t-octets*) 3)                                       ; new within: kept
      (not (<= (len (fn-bs-durable-content *ckr-t-big-old* 3)) 3))      ; old past: removed
      (not (fn-ckr-all-fit *ckr-t-big-old-run* 3 5 3))))                ; the conclusion fails
(must-fail-checked
 (defthm ckr-t-old-image-past-the-bound
   (fn-ckr-all-fit *ckr-t-big-old-run* 3 5 3)))
