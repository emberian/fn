; fn: the host's growth loop when every region outgrows (lane
; arena-store-4, 2026-09-28); split from
; tests/acl2/history-pages-grow-then-append-tests.lisp for time.
;
; What this book is evidence FOR.  Five regions of 16384 octets each, placed
; canonically in 6 pages, take an event (every region's cap goes from one
; page to two): the writer answers (:grow 0 2), (:grow 1 2), ..., (:grow 4
; 2), each after the previous region's relocation (`fn-hp-x-relocate' R 2
; to the image's end), then :ok -- five relocations, in increasing order,
; as `fn-hp-grow-then-append' bounds them.  The loop runs over the live page
; store (the guard-verified executables the host calls), from a store of six
; zero pages grown by `pgs-x-grow-image'.
(in-package "ACL2")
(include-book "../../books/history-pages-grow-then-append")

(defconst *hgf-s* '(1 2 3 4 5))
(defconst *hgt-ev* (list :other 9 nil))
(defconst *hgt-lm* '(16384 16384 16384 16384 16384))

;; The loop as the host runs it, over the live page store: append; on
;; (:grow R C) relocate R C and append again.  Each step's answers are
;; recorded: (APPEND-VERDICT RELOCATE-VERDICT STARTS2 NP2), the last one
;; (APPEND-VERDICT N2 LENS2).
(defun hgf-drive (k ev lens starts np acc pgs-mem)
  (declare (xargs :mode :program :stobjs pgs-mem))
  (mv-let (v n2 lens2 pgs-mem)
    (fn-hp-x-append ev 0 0 lens starts np pgs-mem)
    (if (and (consp v) (eq (car v) :grow) (not (zp k)))
        (mv-let (rv starts2 np2 pgs-mem)
          (fn-hp-x-relocate (cadr v) (caddr v) 0 lens starts np pgs-mem)
          (hgf-drive (1- k) ev lens starts2 np2 (cons (list v rv starts2 np2) acc) pgs-mem))
      (mv (reverse (cons (list v n2 lens2) acc)) pgs-mem))))

(defun hgf-run ()
  ; a store of six zero pages, verified (`pgs-x-grow-image' from empty)
  (declare (xargs :mode :program))
  (with-local-stobj pgs-mem
    (mv-let (res pgs-mem)
      (let ((pgs-mem (pgs-x-grow-image 6 pgs-mem)))
        (hgf-drive 10 *hgt-ev* *hgt-lm* *hgf-s* 6 nil pgs-mem))
      res)))

(assert-event
 (equal (hgf-run)
        (list (list '(:grow 0 2) :ok '(6 2 3 4 5) 8)
              (list '(:grow 1 2) :ok '(6 8 3 4 5) 10)
              (list '(:grow 2 2) :ok '(6 8 10 4 5) 12)
              (list '(:grow 3 2) :ok '(6 8 10 12 5) 14)
              (list '(:grow 4 2) :ok '(6 8 10 12 14) 16)
              (list :ok 1 (fn-hp-x-lens-after *hgt-ev* *hgt-lm*)))))
