; Exact source constructor count of branch-selected trace. No runtime verdict.
(in-package "ACL2")
(include-book "legacy-parser-trace-tick")
(include-book "legacy-parser-allocation")

(defun fn-lpt-constructor-cells (trace)
 (declare (xargs :guard t))
 (if (consp trace)
  (+ (if (eq (fn-ag-car (car trace)) :constructor)
         (nfix (fn-ag-car (fn-ag-cdr (fn-ag-cdr (car trace))))) 0)
     (fn-lpt-constructor-cells (cdr trace))) 0))

(defthm fn-lpt-constructor-cells-append
 (equal (fn-lpt-constructor-cells (append a b))
  (+ (fn-lpt-constructor-cells a) (fn-lpt-constructor-cells b))))

(defthm fn-lpt-ascii-downcase-byte-trace-constructor-cells
 (equal (fn-lpt-constructor-cells (cdr (fn-lpt-ascii-downcase-byte byte))) 0)
 :hints (("Goal" :do-not '(preprocess)
 :in-theory (e/d (fn-lpt-ascii-downcase-byte fn-lpt-constructor-cells fn-ag-car fn-ag-cdr) (fn-lpt-at fn-lpt-put fn-lpt-span fn-lpt-name-byte fn-lpt-name-step fn-lpt-name-key fn-lpt-header-bad fn-lpt-close-fields fn-lpt-value-byte fn-lpt-header-byte fn-lpt-split-byte fn-lpt-body-byte fn-lpt-byte fn-lpt-verdict fn-lpc-at fn-lpc-put fn-lpc-header-bad fn-lpc-span fn-lpc-name-byte fn-lpc-name-step fn-lpc-name-key fn-lpc-close-fields fn-lpc-value-byte fn-lpc-header-byte fn-lpc-body-byte fn-lpc-split-byte fn-lpc-byte fn-lpc-verdict fn-article-ascii-downcase-byte fn-article-header-bytep fn-article-ftextp fn-article-wspp fn-article-vcharp fn-lpa-close-conses fn-lpa-value-conses fn-lpa-header-conses fn-lpa-body-conses fn-lpa-byte-conses)))))

(defthm fn-lpt-at-trace-constructor-cells
 (equal (fn-lpt-constructor-cells (cdr (fn-lpt-at i x))) 0)
 :hints (("Goal" :induct (fn-lpt-at i x) :do-not '(preprocess)
 :in-theory (e/d (fn-lpt-at fn-lpt-constructor-cells fn-ag-car fn-ag-cdr) (fn-lpt-ascii-downcase-byte fn-lpt-put fn-lpt-span fn-lpt-name-byte fn-lpt-name-step fn-lpt-name-key fn-lpt-header-bad fn-lpt-close-fields fn-lpt-value-byte fn-lpt-header-byte fn-lpt-split-byte fn-lpt-body-byte fn-lpt-byte fn-lpt-verdict fn-lpc-at fn-lpc-put fn-lpc-header-bad fn-lpc-span fn-lpc-name-byte fn-lpc-name-step fn-lpc-name-key fn-lpc-close-fields fn-lpc-value-byte fn-lpc-header-byte fn-lpc-body-byte fn-lpc-split-byte fn-lpc-byte fn-lpc-verdict fn-article-ascii-downcase-byte fn-article-header-bytep fn-article-ftextp fn-article-wspp fn-article-vcharp fn-lpa-close-conses fn-lpa-value-conses fn-lpa-header-conses fn-lpa-body-conses fn-lpa-byte-conses)))))

(defthm fn-lpt-put-trace-constructor-cells
 (equal (fn-lpt-constructor-cells (cdr (fn-lpt-put i v x))) (+ 1 (nfix i)))
 :hints (("Goal" :induct (fn-lpt-put i v x) :do-not '(preprocess)
 :in-theory (e/d (fn-lpt-put fn-lpt-constructor-cells fn-ag-car fn-ag-cdr) (fn-lpt-ascii-downcase-byte fn-lpt-at fn-lpt-span fn-lpt-name-byte fn-lpt-name-step fn-lpt-name-key fn-lpt-header-bad fn-lpt-close-fields fn-lpt-value-byte fn-lpt-header-byte fn-lpt-split-byte fn-lpt-body-byte fn-lpt-byte fn-lpt-verdict fn-lpc-at fn-lpc-put fn-lpc-header-bad fn-lpc-span fn-lpc-name-byte fn-lpc-name-step fn-lpc-name-key fn-lpc-close-fields fn-lpc-value-byte fn-lpc-header-byte fn-lpc-body-byte fn-lpc-split-byte fn-lpc-byte fn-lpc-verdict fn-article-ascii-downcase-byte fn-article-header-bytep fn-article-ftextp fn-article-wspp fn-article-vcharp fn-lpa-close-conses fn-lpa-value-conses fn-lpa-header-conses fn-lpa-body-conses fn-lpa-byte-conses)))))

(defthm fn-lpt-span-trace-constructor-cells
 (equal (fn-lpt-constructor-cells (cdr (fn-lpt-span h start end pin))) 4)
 :hints (("Goal" :do-not '(preprocess)
 :in-theory (e/d (fn-lpt-span fn-lpt-constructor-cells fn-ag-car fn-ag-cdr) (fn-lpt-ascii-downcase-byte fn-lpt-at fn-lpt-put fn-lpt-name-byte fn-lpt-name-step fn-lpt-name-key fn-lpt-header-bad fn-lpt-close-fields fn-lpt-value-byte fn-lpt-header-byte fn-lpt-split-byte fn-lpt-body-byte fn-lpt-byte fn-lpt-verdict fn-lpc-at fn-lpc-put fn-lpc-header-bad fn-lpc-span fn-lpc-name-byte fn-lpc-name-step fn-lpc-name-key fn-lpc-close-fields fn-lpc-value-byte fn-lpc-header-byte fn-lpc-body-byte fn-lpc-split-byte fn-lpc-byte fn-lpc-verdict fn-article-ascii-downcase-byte fn-article-header-bytep fn-article-ftextp fn-article-wspp fn-article-vcharp fn-lpa-close-conses fn-lpa-value-conses fn-lpa-header-conses fn-lpa-body-conses fn-lpa-byte-conses)))))

(defthm fn-lpt-name-byte-trace-constructor-cells
 (equal (fn-lpt-constructor-cells (cdr (fn-lpt-name-byte candidate byte))) 0)
 :hints (("Goal" :do-not '(preprocess)
 :in-theory (e/d (fn-lpt-name-byte fn-lpt-constructor-cells fn-ag-car fn-ag-cdr) (fn-lpt-ascii-downcase-byte fn-lpt-at fn-lpt-put fn-lpt-span fn-lpt-name-step fn-lpt-name-key fn-lpt-header-bad fn-lpt-close-fields fn-lpt-value-byte fn-lpt-header-byte fn-lpt-split-byte fn-lpt-body-byte fn-lpt-byte fn-lpt-verdict fn-lpc-at fn-lpc-put fn-lpc-header-bad fn-lpc-span fn-lpc-name-byte fn-lpc-name-step fn-lpc-name-key fn-lpc-close-fields fn-lpc-value-byte fn-lpc-header-byte fn-lpc-body-byte fn-lpc-split-byte fn-lpc-byte fn-lpc-verdict fn-article-ascii-downcase-byte fn-article-header-bytep fn-article-ftextp fn-article-wspp fn-article-vcharp fn-lpa-close-conses fn-lpa-value-conses fn-lpa-header-conses fn-lpa-body-conses fn-lpa-byte-conses)))))

(defthm fn-lpt-name-step-trace-constructor-cells
 (equal (fn-lpt-constructor-cells (cdr (fn-lpt-name-step candidates byte))) 5)
 :hints (("Goal" :do-not '(preprocess)
 :in-theory (e/d (fn-lpt-name-step fn-lpt-constructor-cells fn-ag-car fn-ag-cdr) (fn-lpt-ascii-downcase-byte fn-lpt-at fn-lpt-put fn-lpt-span fn-lpt-name-byte fn-lpt-name-key fn-lpt-header-bad fn-lpt-close-fields fn-lpt-value-byte fn-lpt-header-byte fn-lpt-split-byte fn-lpt-body-byte fn-lpt-byte fn-lpt-verdict fn-lpc-at fn-lpc-put fn-lpc-header-bad fn-lpc-span fn-lpc-name-byte fn-lpc-name-step fn-lpc-name-key fn-lpc-close-fields fn-lpc-value-byte fn-lpc-header-byte fn-lpc-body-byte fn-lpc-split-byte fn-lpc-byte fn-lpc-verdict fn-article-ascii-downcase-byte fn-article-header-bytep fn-article-ftextp fn-article-wspp fn-article-vcharp fn-lpa-close-conses fn-lpa-value-conses fn-lpa-header-conses fn-lpa-body-conses fn-lpa-byte-conses)))))

(defthm fn-lpt-name-key-trace-constructor-cells
 (equal (fn-lpt-constructor-cells (cdr (fn-lpt-name-key candidates))) 0)
 :hints (("Goal" :do-not '(preprocess)
 :in-theory (e/d (fn-lpt-name-key fn-lpt-constructor-cells fn-ag-car fn-ag-cdr) (fn-lpt-ascii-downcase-byte fn-lpt-at fn-lpt-put fn-lpt-span fn-lpt-name-byte fn-lpt-name-step fn-lpt-header-bad fn-lpt-close-fields fn-lpt-value-byte fn-lpt-header-byte fn-lpt-split-byte fn-lpt-body-byte fn-lpt-byte fn-lpt-verdict fn-lpc-at fn-lpc-put fn-lpc-header-bad fn-lpc-span fn-lpc-name-byte fn-lpc-name-step fn-lpc-name-key fn-lpc-close-fields fn-lpc-value-byte fn-lpc-header-byte fn-lpc-body-byte fn-lpc-split-byte fn-lpc-byte fn-lpc-verdict fn-article-ascii-downcase-byte fn-article-header-bytep fn-article-ftextp fn-article-wspp fn-article-vcharp fn-lpa-close-conses fn-lpa-value-conses fn-lpa-header-conses fn-lpa-body-conses fn-lpa-byte-conses)))))

(defthm fn-lpt-header-bad-trace-constructor-cells
 (equal (fn-lpt-constructor-cells (cdr (fn-lpt-header-bad s))) 1)
 :hints (("Goal" :do-not '(preprocess)
 :in-theory (e/d (fn-lpt-header-bad fn-lpt-constructor-cells fn-ag-car fn-ag-cdr) (fn-lpt-ascii-downcase-byte fn-lpt-at fn-lpt-put fn-lpt-span fn-lpt-name-byte fn-lpt-name-step fn-lpt-name-key fn-lpt-close-fields fn-lpt-value-byte fn-lpt-header-byte fn-lpt-split-byte fn-lpt-body-byte fn-lpt-byte fn-lpt-verdict fn-lpc-at fn-lpc-put fn-lpc-header-bad fn-lpc-span fn-lpc-name-byte fn-lpc-name-step fn-lpc-name-key fn-lpc-close-fields fn-lpc-value-byte fn-lpc-header-byte fn-lpc-body-byte fn-lpc-split-byte fn-lpc-byte fn-lpc-verdict fn-article-ascii-downcase-byte fn-article-header-bytep fn-article-ftextp fn-article-wspp fn-article-vcharp fn-lpa-close-conses fn-lpa-value-conses fn-lpa-header-conses fn-lpa-body-conses fn-lpa-byte-conses)))))

(defthm fn-lpt-close-fields-trace-constructor-cells
 (equal (fn-lpt-constructor-cells (cdr (fn-lpt-close-fields s h pin))) (fn-lpa-close-conses s))
 :hints (("Goal" :do-not '(preprocess)
 :in-theory (e/d (fn-lpt-close-fields fn-lpt-constructor-cells fn-ag-car fn-ag-cdr fn-lpa-close-conses) (fn-lpt-ascii-downcase-byte fn-lpt-at fn-lpt-put fn-lpt-span fn-lpt-name-byte fn-lpt-name-step fn-lpt-name-key fn-lpt-header-bad fn-lpt-value-byte fn-lpt-header-byte fn-lpt-split-byte fn-lpt-body-byte fn-lpt-byte fn-lpt-verdict fn-lpc-at fn-lpc-put fn-lpc-header-bad fn-lpc-span fn-lpc-name-byte fn-lpc-name-step fn-lpc-name-key fn-lpc-close-fields fn-lpc-value-byte fn-lpc-header-byte fn-lpc-body-byte fn-lpc-split-byte fn-lpc-byte fn-lpc-verdict fn-article-ascii-downcase-byte fn-article-header-bytep fn-article-ftextp fn-article-wspp fn-article-vcharp fn-lpa-value-conses fn-lpa-header-conses fn-lpa-body-conses fn-lpa-byte-conses)))))

(defthm fn-lpt-value-byte-trace-constructor-cells
 (equal (fn-lpt-constructor-cells (cdr (fn-lpt-value-byte s byte pos))) (fn-lpa-value-conses s byte))
 :hints (("Goal" :do-not '(preprocess)
 :in-theory (e/d (fn-lpt-value-byte fn-lpt-constructor-cells fn-ag-car fn-ag-cdr fn-lpa-value-conses) (fn-lpt-ascii-downcase-byte fn-lpt-at fn-lpt-put fn-lpt-span fn-lpt-name-byte fn-lpt-name-step fn-lpt-name-key fn-lpt-header-bad fn-lpt-close-fields fn-lpt-header-byte fn-lpt-split-byte fn-lpt-body-byte fn-lpt-byte fn-lpt-verdict fn-lpc-at fn-lpc-put fn-lpc-header-bad fn-lpc-span fn-lpc-name-byte fn-lpc-name-step fn-lpc-name-key fn-lpc-close-fields fn-lpc-value-byte fn-lpc-header-byte fn-lpc-body-byte fn-lpc-split-byte fn-lpc-byte fn-lpc-verdict fn-article-ascii-downcase-byte fn-article-header-bytep fn-article-ftextp fn-article-wspp fn-article-vcharp fn-lpa-close-conses fn-lpa-header-conses fn-lpa-body-conses fn-lpa-byte-conses)))))

(defthm fn-lpt-header-byte-trace-constructor-cells
 (equal (fn-lpt-constructor-cells (cdr (fn-lpt-header-byte s byte pos h pin))) (fn-lpa-header-conses s byte))
 :hints (("Goal" :do-not '(preprocess)
 :in-theory (e/d (fn-lpa-value-conses fn-lpt-header-byte fn-lpt-constructor-cells fn-ag-car fn-ag-cdr fn-lpa-header-conses) (fn-lpt-ascii-downcase-byte fn-lpt-at fn-lpt-put fn-lpt-span fn-lpt-name-byte fn-lpt-name-step fn-lpt-name-key fn-lpt-header-bad fn-lpt-close-fields fn-lpt-value-byte fn-lpt-split-byte fn-lpt-body-byte fn-lpt-byte fn-lpt-verdict fn-lpc-at fn-lpc-put fn-lpc-header-bad fn-lpc-span fn-lpc-name-byte fn-lpc-name-step fn-lpc-name-key fn-lpc-close-fields fn-lpc-value-byte fn-lpc-header-byte fn-lpc-body-byte fn-lpc-split-byte fn-lpc-byte fn-lpc-verdict fn-article-ascii-downcase-byte fn-article-header-bytep fn-article-ftextp fn-article-wspp fn-article-vcharp fn-lpa-close-conses fn-lpa-body-conses fn-lpa-byte-conses)))))

(defthm fn-lpt-split-byte-trace-constructor-cells
 (equal (fn-lpt-constructor-cells (cdr (fn-lpt-split-byte matched byte))) 0)
 :hints (("Goal" :do-not '(preprocess)
 :in-theory (e/d (fn-lpt-split-byte fn-lpt-constructor-cells fn-ag-car fn-ag-cdr) (fn-lpt-ascii-downcase-byte fn-lpt-at fn-lpt-put fn-lpt-span fn-lpt-name-byte fn-lpt-name-step fn-lpt-name-key fn-lpt-header-bad fn-lpt-close-fields fn-lpt-value-byte fn-lpt-header-byte fn-lpt-body-byte fn-lpt-byte fn-lpt-verdict fn-lpc-at fn-lpc-put fn-lpc-header-bad fn-lpc-span fn-lpc-name-byte fn-lpc-name-step fn-lpc-name-key fn-lpc-close-fields fn-lpc-value-byte fn-lpc-header-byte fn-lpc-body-byte fn-lpc-split-byte fn-lpc-byte fn-lpc-verdict fn-article-ascii-downcase-byte fn-article-header-bytep fn-article-ftextp fn-article-wspp fn-article-vcharp fn-lpa-close-conses fn-lpa-value-conses fn-lpa-header-conses fn-lpa-body-conses fn-lpa-byte-conses)))))

(defthm fn-lpt-body-byte-trace-constructor-cells
 (equal (fn-lpt-constructor-cells (cdr (fn-lpt-body-byte s byte))) (fn-lpa-body-conses s))
 :hints (("Goal" :do-not '(preprocess)
 :in-theory (e/d (fn-lpt-body-byte fn-lpt-constructor-cells fn-ag-car fn-ag-cdr fn-lpa-body-conses) (fn-lpt-ascii-downcase-byte fn-lpt-at fn-lpt-put fn-lpt-span fn-lpt-name-byte fn-lpt-name-step fn-lpt-name-key fn-lpt-header-bad fn-lpt-close-fields fn-lpt-value-byte fn-lpt-header-byte fn-lpt-split-byte fn-lpt-byte fn-lpt-verdict fn-lpc-at fn-lpc-put fn-lpc-header-bad fn-lpc-span fn-lpc-name-byte fn-lpc-name-step fn-lpc-name-key fn-lpc-close-fields fn-lpc-value-byte fn-lpc-header-byte fn-lpc-body-byte fn-lpc-split-byte fn-lpc-byte fn-lpc-verdict fn-article-ascii-downcase-byte fn-article-header-bytep fn-article-ftextp fn-article-wspp fn-article-vcharp fn-lpa-close-conses fn-lpa-value-conses fn-lpa-header-conses fn-lpa-byte-conses)))))

(defthm fn-lpt-byte-trace-constructor-cells
 (equal (fn-lpt-constructor-cells (cdr (fn-lpt-byte s byte))) (fn-lpa-byte-conses s byte))
 :hints (("Goal" :do-not '(preprocess)
 :in-theory (e/d (fn-lpt-byte fn-lpt-constructor-cells fn-ag-car fn-ag-cdr fn-lpa-byte-conses) (fn-lpt-ascii-downcase-byte fn-lpt-at fn-lpt-put fn-lpt-span fn-lpt-name-byte fn-lpt-name-step fn-lpt-name-key fn-lpt-header-bad fn-lpt-close-fields fn-lpt-value-byte fn-lpt-header-byte fn-lpt-split-byte fn-lpt-body-byte fn-lpt-verdict fn-lpc-at fn-lpc-put fn-lpc-header-bad fn-lpc-span fn-lpc-name-byte fn-lpc-name-step fn-lpc-name-key fn-lpc-close-fields fn-lpc-value-byte fn-lpc-header-byte fn-lpc-body-byte fn-lpc-split-byte fn-lpc-byte fn-lpc-verdict fn-article-ascii-downcase-byte fn-article-header-bytep fn-article-ftextp fn-article-wspp fn-article-vcharp fn-lpa-close-conses fn-lpa-value-conses fn-lpa-header-conses fn-lpa-body-conses)))))

(defthm fn-lpt-verdict-trace-constructor-cells
 (equal (fn-lpt-constructor-cells (cdr (fn-lpt-verdict s))) 0)
 :hints (("Goal" :do-not '(preprocess)
 :in-theory (e/d (fn-lpt-verdict fn-lpt-constructor-cells fn-ag-car fn-ag-cdr) (fn-lpt-ascii-downcase-byte fn-lpt-at fn-lpt-put fn-lpt-span fn-lpt-name-byte fn-lpt-name-step fn-lpt-name-key fn-lpt-header-bad fn-lpt-close-fields fn-lpt-value-byte fn-lpt-header-byte fn-lpt-split-byte fn-lpt-body-byte fn-lpt-byte fn-lpc-at fn-lpc-put fn-lpc-header-bad fn-lpc-span fn-lpc-name-byte fn-lpc-name-step fn-lpc-name-key fn-lpc-close-fields fn-lpc-value-byte fn-lpc-header-byte fn-lpc-body-byte fn-lpc-split-byte fn-lpc-byte fn-lpc-verdict fn-article-ascii-downcase-byte fn-article-header-bytep fn-article-ftextp fn-article-wspp fn-article-vcharp fn-lpa-close-conses fn-lpa-value-conses fn-lpa-header-conses fn-lpa-body-conses fn-lpa-byte-conses)))))

(defthm fn-lpt-stop-trace-constructor-cells
 (equal (fn-lpt-constructor-cells (cdr (fn-lpt-stop s fuel))) 0)
 :hints (("Goal" :do-not '(preprocess)
  :in-theory (e/d (fn-lpt-stop fn-lpt-constructor-cells fn-ag-car fn-ag-cdr)
                 (fn-lpc-at)))))

(defthm fn-lpt-tick-trace-constructor-cells
 (equal (fn-lpt-constructor-cells (mv-nth 4 (fn-lpt-tick s fuel fn-arena)))
        (fn-lpa-tick-conses s fuel fn-arena))
 :hints (("Goal" :induct (fn-lpc-tick s fuel fn-arena)
   :do-not '(preprocess)
   :in-theory (e/d (fn-lpt-tick fn-lpt-constructor-cells fn-lpa-tick-conses
                    fn-ag-car fn-ag-cdr)
    (fn-lpc-byte fn-lpc-at fn-lpc-verdict fn-lpa-byte-conses)))))

(defthm fn-lpt-tick-trace-constructor-cells-bounded-by-work
 (<= (fn-lpt-constructor-cells (mv-nth 4 (fn-lpt-tick s fuel fn-arena)))
     (+ 4 (* 39 (mv-nth 2 (fn-lpc-tick s fuel fn-arena)))))
 :hints (("Goal" :use fn-lpa-tick-conses-are-bounded-by-actual-work
  :in-theory (disable fn-lpa-tick-conses fn-lpt-tick fn-lpt-constructor-cells
               fn-lpc-tick fn-lpa-tick-conses-are-bounded-by-actual-work))))
