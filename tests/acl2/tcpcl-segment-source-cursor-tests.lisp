; Internal cursor fixtures; source/constructor installation is not inferred.
(in-package "ACL2")
(include-book "../../books/tcpcl-segment-source-cursor")
(include-book "../../books/tcpcl-received-source")
; A turn's bytes are a true list (the harness appends them).
(local (defthm tsc-turn-loop-bytes-true-listp
  (implies (true-listp rev)
           (true-listp (mv-nth 2 (fn-tsc-turn-loop job quantum rev used))))
  :hints (("Goal" :in-theory (enable fn-tsc-turn-loop)))))
(local (defthm tsc-turn-bytes-true-listp
  (true-listp (mv-nth 2 (fn-tsc-turn job quantum)))
  :hints (("Goal" :in-theory (enable fn-tsc-turn)))))
(defun fn-tsc-test-run (job quantum turns out)
 (declare (xargs :guard (and (natp quantum) (<= quantum 64) (natp turns)
                            (true-listp out)) :measure (nfix turns)))
 (if (zp turns) (list :exhausted job out)
  (mv-let (word next bytes used) (fn-tsc-turn job quantum)
   (if (or (eq word :source-complete) (eq word :refused))
    (list word next (append out bytes) used)
    (fn-tsc-test-run next quantum (1- turns) (append out bytes))))))
(defconst *tsc-source-completion*
 (fn-tcl-complete-source nil 7 3 4 '((67 68) (65 66)) 0))
(defconst *tsc-source-event*
 (cadr (fn-tcl-result-events *tsc-source-completion*)))
(defconst *tsc-source-job*
 (fn-tsc-begin (caddr *tsc-source-event*) (cadddr *tsc-source-event*)))
(assert-event
 (and (equal *tsc-source-event* '(:bundle-segments-received 7 ((67 68) (65 66)) 4))
      (equal (cadr (car (fn-tcl-result-events *tsc-source-completion*)))
             (fn-tcl-make-xfer-ack 3 7 4))))
(assert-event
 (let ((one (fn-tsc-test-run *tsc-source-job* 1 20 nil))
       (wide (fn-tsc-test-run *tsc-source-job* 64 2 nil)))
  (and (equal (car one) :source-complete) (equal (car wide) :source-complete)
       (equal (caddr one) '(65 66 67 68)) (equal (caddr wide) '(65 66 67 68))
       (equal (fn-tsc-at 8 (cadr one)) '((67 68) (65 66)))
       (equal (fn-tsc-at 8 (cadr wide)) '((67 68) (65 66))))))
(assert-event
 (mv-let (word next bytes used) (fn-tsc-turn *tsc-source-job* 1)
  (and (eq word :yield) (equal used 1) (equal bytes nil)
       (equal (fn-tsc-at 8 next) '((67 68) (65 66)))
       (equal (fn-tsc-at 4 next) '((65 66))))))
; Corrupted internal counts, chains and octets refuse, retaining the root.
(assert-event
 (let ((short (fn-tsc-test-run (fn-tsc-begin '((65 66)) 3) 64 2 nil))
       (over (fn-tsc-test-run (fn-tsc-begin '((65 66)) 1) 64 2 nil))
       (bad (fn-tsc-test-run (fn-tsc-begin '((256)) 1) 64 2 nil))
       (chain (fn-tsc-test-run (fn-tsc-begin '((65) . broken) 1) 64 2 nil)))
  (and (eq (car short) :refused) (eq (fn-tsc-at 7 (cadr short)) :source-count-short)
       (eq (car over) :refused) (eq (fn-tsc-at 7 (cadr over)) :source-count-overrun)
       (eq (car bad) :refused) (eq (fn-tsc-at 7 (cadr bad)) :source-octet)
       (eq (car chain) :refused) (eq (fn-tsc-at 7 (cadr chain)) :source-chain)
       (equal (fn-tsc-at 8 (cadr short)) '((65 66)))
       (equal (fn-tsc-at 8 (cadr over)) '((65 66)))
       (equal (fn-tsc-at 8 (cadr bad)) '((256)))
       (equal (fn-tsc-at 8 (cadr chain)) '((65) . broken)))))
