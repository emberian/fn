; fn: witnesses for books/store-reclaim-stream.lisp (PKT-686 item 2): the
; reclaim's fold, one record at a time, carries the whole-history quantities
; of books/store-reclaim-pack.lisp (`fn-rcls-fold-of-init'), over the owner
; fixture of owner-served-invariants-tests.  The keystone this fold feeds is
; books/store-log-reclaim.lisp's `fn-lgr-decide-stream-is-lgr-decide' (its
; teeth are store-log-reclaim-tests').
(in-package "ACL2")
(include-book "../../books/store-reclaim-stream")
(include-book "owner-served-invariants-tests")
(include-book "must-fail-checked")

(defconst *rst-s* (fn-own-store (cdr (osi-finish *osi-completing* *osi-cfg* *osi-completing-prior*))))

(defun rst-encode-all (rs)
  (declare (xargs :mode :program))
  (if (consp rs) (cons (fn-store-event-encode (car rs)) (rst-encode-all (cdr rs))) nil))
(defconst *rst-wire* (fn-hrt-wire-of *osi-completing-prior* (fn-sf-records (fn-sn-files *rst-s*))))
(defmacro rst-events () '(rst-encode-all *rst-wire*))
(defconst *rst-rule* '(:released-by-all-holders))
(defconst *rst-ctx* (fn-rclp-ctx *rst-rule* 0 *rst-s*))
(defmacro rst-long () '(append (rst-events) (make-list 4096 :initial-element '(1 2 3))))

(defun rst-acc (events)
  (declare (xargs :mode :program))
  (fn-rcls-fold events *rst-ctx* (fn-rcls-init)))

; The fold of the fixture's history is the whole-history quantities: the
; count, the rewritten Message-IDs (at least one: the fixture's released
; article) and the freed octets (positive: the payload became its tombstone).
(assert-event (let ((acc (rst-acc (rst-events))))
                (and (true-listp (rst-events))
                     (equal (nth 0 acc) (len (rst-events)))
                     (consp (nth 1 acc))
                     (equal (rev (nth 1 acc)) (fn-rclp-rewritten-msgids (rst-events) *rst-ctx*))
                     (equal (nth 2 acc) (fn-rclp-freed (rst-events) *rst-ctx*))
                     (< 0 (nth 2 acc)))))

; The fold carries three quantities and no history: a long history's fold
; is three elements, and its count is the long history's length.
(assert-event (let ((acc (rst-acc (rst-long))))
                (and (equal (len acc) 3)
                     (equal (nth 0 acc) (len (rst-long)))
                     (equal (rev (nth 1 acc)) (fn-rclp-rewritten-msgids (rst-events) *rst-ctx*)))))

; fn-rcls-step-reads-no-article-list / fn-rclp-event-reads-no-article-list
; (row A8): the fixture's fold, and its released record's rewrite, are the
; same with the context's article list replaced by nil; teeth: with the
; INDEX replaced by nil instead (the slot the step does read) the fold
; rewrites nothing and the record is not rewritten.
(defconst *rst-no-articles* (update-nth 4 nil *rst-ctx*))
(defconst *rst-no-index* (update-nth 6 nil *rst-ctx*))
(assert-event (equal (fn-rcls-fold (rst-events) *rst-no-articles* (fn-rcls-init))
                     (rst-acc (rst-events))))
(assert-event (equal (fn-rclp-events (rst-events) *rst-no-articles*)
                     (fn-rclp-events (rst-events) *rst-ctx*)))
(assert-event (consp (nth 1 (rst-acc (rst-events)))))
(must-fail-checked
 (assert-event (equal (fn-rcls-fold (rst-events) *rst-no-index* (fn-rcls-init))
                      (rst-acc (rst-events)))))
(assert-event (atom (nth 1 (fn-rcls-fold (rst-events) *rst-no-index* (fn-rcls-init)))))
