; Literal complete acc/arena boundary plus unavailable metadata mutation.
; Snapshot carries here are fixture values, not a served decoder producer.
(in-package "ACL2")
(include-book "../../books/statement-recover-sized")
(include-book "../../books/codec-attach")
(defconst *ssrst-snapshot* (fn-stxk-make 0 0 0 0 '(1) '(7 8)))
(defconst *ssrst-article*
 (fn-record-make 1 1 1 "<sized@example>" '(65 13 10) '("example")
                 "o" "s" "e" 1 841000000))
(defconst *ssrst-wires* (list *ssrst-snapshot* *ssrst-article*))
(defun ssrst-fields (xs)
 (if (consp xs) (cons (fn-scs-summary (car xs)) (ssrst-fields (cdr xs))) nil))
(defun ssrst-arena-list (i fn-arena)
 (declare (xargs :stobjs fn-arena :verify-guards nil
                 :measure (nfix (- (fn-arena-count fn-arena) (nfix i)))))
 (if (and (natp i) (< i (fn-arena-count fn-arena)))
  (cons (fn-arena-payload i fn-arena) (ssrst-arena-list (1+ i) fn-arena)) nil))
(defun ssrst-run-in (newp fields snapshot-carries mode fn-arena)
 (declare (xargs :stobjs fn-arena :verify-guards nil))
 (let ((seed (fn-ssr-seed (fn-stxk-initial-context 0))))
  (if newp
   (mv-let (acc next-fields status fn-arena)
    (fn-ssrs-intern-step seed fields *ssrst-wires* nil nil mode nil snapshot-carries fn-arena)
    (mv (list acc (ssrst-arena-list 0 fn-arena) next-fields status) fn-arena))
   (mv-let (acc fn-arena)
    (fn-ssr-intern-step seed *ssrst-wires* nil nil mode nil fn-arena)
    (mv (list acc (ssrst-arena-list 0 fn-arena)) fn-arena)))))
(defun ssrst-run (newp fields snapshot-carries mode)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-arena
  (mv-let (out fn-arena) (ssrst-run-in newp fields snapshot-carries mode fn-arena) out)))
; Unconditional literal theorem: no removable hypotheses. Nonempty accepted
; rows allocate real payload cells in both subjects from fresh equal arenas.
(assert-event
 (let* ((ctx (fn-stxk-initial-context 0))
        (fields (ssrst-fields ctx))
        (children (list (fn-scs-summary *ssrst-snapshot*) nil))
        (old (ssrst-run nil fields children :resident))
        (new (ssrst-run t fields children :resident)))
  (and (equal (list (car new) (cadr new)) old)
       (not (eq (car new) :bad))
       (equal (len (fn-ssr-at 0 (car new))) 2)
       (equal (fn-stxk-context-next (fn-ssr-at 3 (car new))) 2)
       (equal (cadr new) '((65 13 10)))
       (eq (cadddr new) :carried)
       (fn-scs-correspondsp (caddr new) (fn-ssr-at 3 (car new))))))
; Mutation witnesses: absent snapshot carry or malformed field metadata
; affects availability only. The public complete accumulator/arena survives.
(assert-event
 (let* ((ctx (fn-stxk-initial-context 0))
        (fields (ssrst-fields ctx))
        (old (ssrst-run nil fields nil :resident))
        (missing (ssrst-run t fields nil :resident))
        (malformed (ssrst-run t '(:bad-metadata) nil :resident)))
  (and (equal (list (car missing) (cadr missing)) old)
       (equal (list (car malformed) (cadr malformed)) old)
       (not (eq (car old) :bad))
       (null (caddr missing)) (eq (cadddr missing) :unavailable)
       (null (caddr malformed)) (eq (cadddr malformed) :unavailable))))
(assert-event
 (let* ((fields (ssrst-fields (fn-stxk-initial-context 0)))
        (children (list (fn-scs-summary *ssrst-snapshot*) nil)))
  (and (equal (list (car (ssrst-run t fields children :extent))
                    (cadr (ssrst-run t fields children :extent)))
              (ssrst-run nil fields children :extent))
       (equal (list (car (ssrst-run t fields children :lz))
                    (cadr (ssrst-run t fields children :lz)))
              (ssrst-run nil fields children :lz)))))
