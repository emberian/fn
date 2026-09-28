; Teeth for books/memory-credits (lane f8-reservation): a small node's
; ledger under ember's 256 MiB accountable envelope (D35's F8 split,
; 2026-09-28), article credits at zero-copy-commit's reserve, every
; transition's reachable witness, the refusals by name, the keystone's
; hypothesis needed (from an unfunded ledger a transition stays unfunded),
; its must-fail, and a mutant acquire that skips the check.
(in-package "ACL2")
(include-book "../../books/memory-credits")
(include-book "must-fail-checked")
(include-book "std/testing/assert-bang" :dir :system)

(defconst *mct-mib* 1048576)
;; B 256 MiB; base 160 MiB (image, threads, collector headroom); runtime 16
;; MiB; completion 8 MiB; no cache, nothing drawn, no operation.
(defconst *mct-l0* (fn-mcr-make (* 256 *mct-mib*) (* 160 *mct-mib*) 0 (* 8 *mct-mib*)
                                (* 16 *mct-mib*) 0 nil))
;; One article credit at the small preset: 2 x 16 x (512 + A + HDR), A 32 KiB,
;; HDR 16 KiB (books/heap-store-figure.lisp fn-heap-article-reserve-octets,
;; lane zero-copy-commit): nothing owned yet, all reserved.
(defconst *mct-r* 1589248)

(assert! (fn-mcr-fundedp *mct-l0*))
(assert! (equal (fn-mcr-total *mct-l0*) (* 184 *mct-mib*)))

;; Acquire: admitted while it fits (72 MiB of room: 47 credits), refused by
;; name past it, the ledger unchanged.
(defun mct-acquire-n (l n)
  (declare (xargs :mode :program))
  (if (zp n) l (mct-acquire-n (cadr (fn-mcr-acquire l n 0 *mct-r*)) (1- n))))
(defconst *mct-l47* (mct-acquire-n *mct-l0* 47))
(assert! (fn-mcr-fundedp *mct-l47*))
(assert! (equal (len (fn-mcr-ops *mct-l47*)) 47))
(assert! (equal (fn-mcr-acquire *mct-l47* 48 0 *mct-r*) '(:refused :memory-budget-exhausted)))
(assert! (equal (fn-mcr-acquire *mct-l47* 47 0 1) '(:refused :operation-already-admitted)))
(assert! (not (<= (+ (fn-mcr-total *mct-l47*) *mct-r*) (fn-mcr-budget *mct-l47*))))

;; Grow within the reserve: admitted, the total unchanged; past it refused.
(defconst *mct-g* (fn-mcr-grow *mct-l47* 1 40000))
(assert! (equal (car *mct-g*) :ok))
(assert! (equal (fn-mcr-total (cadr *mct-g*)) (fn-mcr-total *mct-l47*)))
(assert! (equal (fn-mcr-op 1 (fn-mcr-ops (cadr *mct-g*))) (cons 40000 (- *mct-r* 40000))))
(assert! (equal (fn-mcr-grow *mct-l47* 1 (1+ *mct-r*)) '(:refused :past-the-reserve)))
(assert! (equal (fn-mcr-grow *mct-l47* 99 1) '(:refused :operation-not-admitted)))

;; Retain 30,000 of the 40,000 owned into the cache: the rest and the
;; reserve come back; past what it owns refused.
(defconst *mct-t* (fn-mcr-retain (cadr *mct-g*) 1 30000))
(assert! (equal (car *mct-t*) :ok))
(assert! (equal (fn-mcr-cache (cadr *mct-t*)) 30000))
(assert! (equal (fn-mcr-total (cadr *mct-t*)) (- (fn-mcr-total *mct-l47*) (- *mct-r* 30000))))
(assert! (equal (fn-mcr-retain (cadr *mct-g*) 1 40001) '(:refused :past-what-it-owns)))

;; The freed credit admits the 48th article.
(assert! (equal (car (fn-mcr-acquire (cadr *mct-t*) 48 0 *mct-r*)) :ok))

;; Evict: credit back by exactly what was evicted; past the cache refused.
(assert! (equal (fn-mcr-cache (cadr (fn-mcr-evict (cadr *mct-t*) 10000))) 20000))
(assert! (equal (fn-mcr-evict (cadr *mct-t*) 30001) '(:refused :past-the-cache)))

;; Release and overdraw.
(assert! (equal (car (fn-mcr-release *mct-l47* 2)) :ok))
(assert! (equal (len (fn-mcr-ops (cadr (fn-mcr-release *mct-l47* 2)))) 46))
(assert! (equal (fn-mcr-release *mct-l47* 99) '(:refused :operation-not-admitted)))
(defconst *mct-o* (fn-mcr-overdraw *mct-l47* 3 (* 8 *mct-mib*)))
(assert! (equal (car *mct-o*) :ok))
(assert! (equal (fn-mcr-total (cadr *mct-o*)) (fn-mcr-total *mct-l47*)))
(assert! (equal (fn-mcr-overdraw (cadr *mct-o*) 3 1) '(:refused :completion-reserve-exhausted)))

;; Every transition keeps the witness ledgers funded (the keystone's
;; conclusions, reached).
(assert! (and (fn-mcr-fundedp (cadr *mct-g*)) (fn-mcr-fundedp (cadr *mct-t*))
              (fn-mcr-fundedp (cadr (fn-mcr-release *mct-l47* 2)))
              (fn-mcr-fundedp (cadr (fn-mcr-evict (cadr *mct-t*) 10000)))
              (fn-mcr-fundedp (cadr *mct-o*))))

;; The hypothesis is needed: a ledger already past its budget (a base of 300
;; MiB) stays unfunded after an admitted release.
(defconst *mct-over* (fn-mcr-make (* 256 *mct-mib*) (* 300 *mct-mib*) 0 0 0 0 '((1 0 . 5))))
(assert! (not (fn-mcr-fundedp *mct-over*)))
(assert! (equal (car (fn-mcr-release *mct-over* 1)) :ok))
(assert! (not (fn-mcr-fundedp (cadr (fn-mcr-release *mct-over* 1)))))
(must-fail-checked
 (defthm mct-release-keeps-funded-without-the-hypothesis
   (implies (equal (car (fn-mcr-release l id)) :ok)
            (fn-mcr-fundedp (cadr (fn-mcr-release l id)))))
 :step-limit 20000)

;; Mutation: an acquire that skips the budget check admits the 48th credit
;; into an unfunded ledger.
(defun mct-acquire-unchecked (l id u r)
  (declare (xargs :mode :program))
  (list :ok (fn-mcr-with l (fn-mcr-cache l) (fn-mcr-drawn l)
                         (fn-mcr-put id (cons (nfix u) (nfix r)) (fn-mcr-ops l)))))
(assert! (not (fn-mcr-fundedp (cadr (mct-acquire-unchecked *mct-l47* 48 0 *mct-r*)))))
