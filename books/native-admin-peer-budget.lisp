; fn: `peer list' shows each peer's opaque-carriage budget (PKT-211, PRF-179).
;
; `peer budget NAME OCTETS COUNT' (books/native-admin-peer.lisp, PRF-099)
; writes a peer's two budget rows (books/peer-carriage-rows.lisp
; fn-pcb-budget-rows: whole Store charge pages and a count); `peer list'
; did not render them.  This book renders them as two more words at the end
; of the peer's line, before its newline:
;
;     ... budget-octets=OCTETS budget-count=COUNT
;
; OCTETS is the budget in octets as the Store keeps it (charge pages times
; *fn-id-charge-page-octets*), COUNT the count.  A peer with no budget rows
; gets no words.  The words come after every word an older `peer list'
; printed, so an older reader of the line (fn-native-admin-peer-extra-decode)
; reads the same values and finds the new words in its tail.  It is a book
; of its own so books/native-admin-peer.lisp does not grow (PKT-371).

(in-package "ACL2")
(include-book "native-admin-peer")
(local (include-book "arithmetic-5/top" :dir :system))

; -----------------------------------------------------------------------------
; Decimal octets of a natural, most significant first, and their value.

(defun fn-napb-decimal (n)
  (declare (xargs :guard t :measure (nfix n)))
  (if (or (not (natp n)) (< n 10))
      (list (+ 48 (nfix n)))
    (append (fn-napb-decimal (floor n 10)) (list (+ 48 (mod n 10))))))

(defun fn-napb-digitp (x)
  (declare (xargs :guard t))
  (and (natp x) (<= 48 x) (<= x 57)))

(defun fn-napb-digit-run (xs)
  (declare (xargs :guard t))
  (if (and (consp xs) (fn-napb-digitp (car xs)))
      (cons (car xs) (fn-napb-digit-run (cdr xs)))
    nil))

(defun fn-napb-fold (acc xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (fn-napb-fold (+ (* 10 (nfix acc)) (- (nfix (car xs)) 48)) (cdr xs))
    (nfix acc)))

(defun fn-napb-all-digitsp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-napb-digitp (car xs)) (fn-napb-all-digitsp (cdr xs)))
    t))

(local (defthm fn-napb-fold-of-append
  (equal (fn-napb-fold acc (append a b))
         (fn-napb-fold (fn-napb-fold acc a) b))))

(local (defthm fn-napb-all-digitsp-of-append
  (equal (fn-napb-all-digitsp (append a b))
         (and (fn-napb-all-digitsp a) (fn-napb-all-digitsp b)))))

(defthm fn-napb-decimal-is-digits
  (and (fn-napb-all-digitsp (fn-napb-decimal n))
       (consp (fn-napb-decimal n))
       (true-listp (fn-napb-decimal n))))

(defthm fn-napb-fold-of-decimal
  (implies (natp n) (equal (fn-napb-fold 0 (fn-napb-decimal n)) n)))

(local (defthm fn-napb-digit-run-of-append-digits
  (implies (and (fn-napb-all-digitsp a) (true-listp a))
           (equal (fn-napb-digit-run (append a b))
                  (append a (fn-napb-digit-run b))))))

(defthm fn-napb-digit-run-of-decimal
  (implies (not (fn-napb-digitp (car tail)))
           (equal (fn-napb-digit-run (append (fn-napb-decimal n) tail))
                  (fn-napb-decimal n))))

(in-theory (disable fn-napb-decimal fn-napb-fold fn-napb-digit-run))

; -----------------------------------------------------------------------------
; The budget words.

(defconst *fn-napb-octets-head* (fn-record-string-octets " budget-octets="))
(defconst *fn-napb-count-head* (fn-record-string-octets " budget-count="))

(defun fn-native-admin-peer-budget-octets (rows)
  "The two budget words of a peer's row group, or nothing without a budget."
  (declare (xargs :guard t))
  (let ((budget (fn-pcb-budget-of-rows rows)))
    (if budget
        (append *fn-napb-octets-head*
                (fn-napb-decimal (* *fn-id-charge-page-octets* (nfix (car budget))))
                *fn-napb-count-head*
                (fn-napb-decimal (nfix (cadr budget))))
      nil)))

; The reader of the two words: (OCTETS COUNT TAIL), or (nil nil OCTETS) when
; the octets do not start with them.
(defun fn-native-admin-peer-budget-decode (octets)
  (declare (xargs :guard t))
  (let* ((r1 (fn-native-admin-peer-drop *fn-napb-octets-head* octets))
         (d1 (fn-napb-digit-run r1))
         (r2 (fn-native-admin-peer-drop d1 r1))
         (r3 (fn-native-admin-peer-drop *fn-napb-count-head* r2))
         (d2 (fn-napb-digit-run r3)))
    (if (and (fn-native-admin-peer-head-p *fn-napb-octets-head* octets)
             (consp d1)
             (fn-native-admin-peer-head-p *fn-napb-count-head* r2)
             (consp d2))
        (list (fn-napb-fold 0 d1) (fn-napb-fold 0 d2)
              (fn-native-admin-peer-drop d2 r3))
      (list nil nil octets))))

(local (defthm drop-of-append-head
  (implies (true-listp head)
           (equal (fn-native-admin-peer-drop head (append head x)) x))))
(local (defthm head-p-of-append-head
  (fn-native-admin-peer-head-p head (append head x))))

; KEYSTONE (the render).  The words `peer list' prints for a peer's row
; group read back as exactly its configured budget: the octets the Store
; charges against (pages times the page size) and the count, whatever
; follows them that is not a digit (the line's newline, or a later word).
(defthm fn-native-admin-peer-budget-decode-reads-the-configured-budget
  (let ((budget (fn-pcb-budget-of-rows rows)))
    (implies (and budget (not (fn-napb-digitp (car tail))))
             (equal (fn-native-admin-peer-budget-decode
                     (append (fn-native-admin-peer-budget-octets rows) tail))
                    (list (* *fn-id-charge-page-octets* (car budget))
                          (cadr budget)
                          tail))))
  :hints (("Goal" :in-theory (enable fn-pcb-budget-of-rows))))

; A peer with no budget rows prints no budget words, and its line decodes
; to no budget.
(defthm fn-native-admin-peer-budget-octets-without-a-budget
  (implies (not (fn-pcb-budget-of-rows rows))
           (and (equal (fn-native-admin-peer-budget-octets rows) nil)
                (equal (car (fn-native-admin-peer-budget-decode
                             (append (fn-native-admin-peer-budget-octets rows)
                                     (list 10))))
                       nil))))

(in-theory (disable fn-native-admin-peer-budget-octets
                    fn-native-admin-peer-budget-decode))

; -----------------------------------------------------------------------------
; The line: the older `peer list' line with the budget words inserted before
; its newline.

(defun fn-napb-before-last (line extra)
  (declare (xargs :guard t))
  (if (and (consp line) (consp (cdr line)))
      (cons (car line) (fn-napb-before-last (cdr line) extra))
    (append (true-list-fix extra) (true-list-fix line))))

(defthm fn-napb-before-last-of-append-newline
  (implies (and (true-listp a) (true-listp extra))
           (equal (fn-napb-before-last (append a (list 10)) extra)
                  (append a extra (list 10)))))

(defun fn-native-admin-peer-budget-row-octets (p rows)
  "One `peer list' line: fn-native-admin-peer-row-octets's line, then the
budget words of ROWS (the peer's row group), then the newline."
  (declare (xargs :guard t))
  (fn-napb-before-last (fn-native-admin-peer-row-octets p rows)
                       (fn-native-admin-peer-budget-octets rows)))

(defun fn-native-admin-peer-budget-report-rows (names peers)
  (declare (xargs :guard t))
  (if (consp names)
      (let ((p (fn-cfg-peer-find (car names) peers)))
        (append (if p
                    (fn-native-admin-peer-budget-row-octets
                     p (fn-cfg-rows-with-key peers (car names)))
                  nil)
                (fn-native-admin-peer-budget-report-rows (cdr names) peers)))
    nil))

(defun fn-native-admin-peer-budget-report (peers)
  "The `peer list' report: books/native-admin.lisp fn-native-admin-query-report
and books/native-live-status.lisp fn-nls-report (:peers) call it."
  (declare (xargs :guard t))
  (fn-native-admin-peer-budget-report-rows (fn-cfg-peer-names peers) peers))

;; A line that ends in its newline: inserting before the last octet is
;; inserting before the newline.
(local (defthm last-of-append-consp
  (implies (consp b) (equal (last (append a b)) (last b)))))
(local (defthm last-of-cons-consp
  (implies (consp b) (equal (last (cons x b)) (last b)))))
(local (defthm before-last-is-before-the-newline
  (implies (and (consp line) (true-listp line) (true-listp extra))
           (equal (fn-napb-before-last line extra)
                  (append (take (1- (len line)) line) extra (last line))))))

(defthm fn-native-admin-peer-row-octets-ends-in-its-newline
  (let ((line (fn-native-admin-peer-row-octets p rows)))
    (and (consp line) (true-listp line) (equal (last line) (list 10))))
  :hints (("Goal" :in-theory (disable fn-native-admin-peer-label-octets
                                      fn-native-admin-peer-transport-octets
                                      fn-native-admin-peer-auth-octets
                                      fn-native-admin-peer-extra-octets))))

; The line is the older line's octets up to its newline, then the budget
; words, then the newline: nothing an older reader parsed moves.
(defthm fn-native-admin-peer-budget-row-octets-extends-the-older-line
  (let ((older (fn-native-admin-peer-row-octets p rows)))
    (equal (fn-native-admin-peer-budget-row-octets p rows)
           (append (take (1- (len older)) older)
                   (fn-native-admin-peer-budget-octets rows)
                   (list 10))))
  :hints (("Goal" :in-theory (e/d (fn-native-admin-peer-budget-octets)
                                  (fn-native-admin-peer-row-octets))
           :use ((:instance fn-native-admin-peer-row-octets-ends-in-its-newline)))))

(in-theory (disable fn-native-admin-peer-budget-row-octets))

; -----------------------------------------------------------------------------
; The older reader over the new line (the lemmas native-admin-peer keeps
; local, again).

(local (defthm append-assoc-napb
  (equal (append (append a b) c) (append a (append b c)))))
(local (defthm head-p-of-append-when-diverged
  (implies (and (not (fn-native-admin-peer-head-p h1 h2))
                (not (fn-native-admin-peer-head-p h2 h1)))
           (not (fn-native-admin-peer-head-p h1 (append h2 x))))))
(local (defthm head-p-of-list-octets-when-diverged
  (implies (and (consp vs)
                (not (fn-native-admin-peer-head-p h1 h2))
                (not (fn-native-admin-peer-head-p h2 h1)))
           (not (fn-native-admin-peer-head-p
                 h1 (append (fn-native-admin-peer-list-octets h2 vs) x))))
  :hints (("Goal" :expand ((fn-native-admin-peer-list-octets h2 vs))))))
(local (defthm list-decode-when-not-head
  (implies (not (fn-native-admin-peer-head-p head octets))
           (equal (fn-native-admin-peer-list-decode head octets)
                  (list nil octets)))))
(local (defthm list-octets-of-atom
  (implies (not (consp vs))
           (equal (fn-native-admin-peer-list-octets h vs) nil))))
(local (defthm boundaryp-of-list-octets
  (implies (and (fn-native-admin-peer-boundaryp x)
                (consp head)
                (not (fn-native-admin-peer-word-octetp (car head))))
           (fn-native-admin-peer-boundaryp
            (append (fn-native-admin-peer-list-octets head values) x)))
  :hints (("Goal" :expand ((fn-native-admin-peer-list-octets head values))))))

(local (defthm budget-tail-facts
  (let ((tail (append (fn-native-admin-peer-budget-octets rows) (list 10))))
    (and (fn-native-admin-peer-boundaryp tail)
         (not (fn-native-admin-peer-head-p
               *fn-native-admin-peer-carries-principal-head* tail))
         (not (fn-native-admin-peer-head-p
               *fn-native-admin-peer-carries-head* tail))
         (not (fn-native-admin-peer-head-p
               *fn-native-admin-peer-releases-for-head* tail))))
  :hints (("Goal" :in-theory (enable fn-native-admin-peer-budget-octets)))))

; KEYSTONE (an older reader).  Over a peer's clean row group (every group
; `bp-boundary add' writes: fn-native-admin-bp-boundary-plan-rows-render-
; clean), the older reader of the line's tail reads the same carried
; principals, carried sources and release issuers as before the budget
; words existed, and leaves exactly the budget words and the newline.
(defthm fn-native-admin-peer-extra-decode-reads-past-the-budget
  (implies (fn-native-admin-peer-extra-cleanp rows)
           (equal (fn-native-admin-peer-extra-decode
                   (append (fn-native-admin-peer-extra-octets rows)
                           (fn-native-admin-peer-budget-octets rows)
                           (list 10)))
                  (list (fn-native-admin-peer-label-octets-list
                         (fn-native-admin-peer-slot-values rows "carries-principal"))
                        (fn-native-admin-peer-label-octets-list
                         (fn-native-admin-peer-slot-values rows "bp-boundary-carries"))
                        (fn-native-admin-peer-label-octets-list
                         (fn-native-admin-peer-slot-values rows "bp-boundary-releases-for"))
                        (append (fn-native-admin-peer-budget-octets rows)
                                (list 10)))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable fn-native-admin-peer-list-octets
                                      fn-native-admin-peer-list-decode
                                      fn-native-admin-peer-slot-values
                                      fn-native-admin-peer-clean-valuesp
                                      fn-native-admin-peer-label-octets-list
                                      fn-native-admin-peer-label-octets)
                  :cases ((and (consp (fn-native-admin-peer-slot-values rows "bp-boundary-carries"))
                               (consp (fn-native-admin-peer-slot-values rows "bp-boundary-releases-for")))
                          (and (consp (fn-native-admin-peer-slot-values rows "bp-boundary-carries"))
                               (not (consp (fn-native-admin-peer-slot-values rows "bp-boundary-releases-for"))))
                          (and (not (consp (fn-native-admin-peer-slot-values rows "bp-boundary-carries")))
                               (consp (fn-native-admin-peer-slot-values rows "bp-boundary-releases-for")))))))
