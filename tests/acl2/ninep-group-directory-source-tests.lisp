(in-package "ACL2")
(include-book "../../books/ninep-group-directory-source")

; Finite actual persistent bit trie for group "a" (octet97), retaining a
; local high watermark5 and an empty number root. No supplied flat catalog.
(defun ninep-directory-one-path (bits value)
 (if (consp bits)
     (if (equal (car bits) 0)
         (cons nil (cons (ninep-directory-one-path (cdr bits) value) nil))
       (cons nil (cons nil (ninep-directory-one-path (cdr bits) value))))
   (cons value (cons nil nil))))

(defun ninep-directory-observe (fuel tasks)
 (if (zp fuel) (fn-9p-ge-remaining tasks)
   (mv-let (word entry next) (fn-9p-ge-step tasks)
    (append (if (eq word :group) (list entry) nil)
            (ninep-directory-observe (1- fuel) next)))))

(defthm ninep-directory-complete-positive
 (let* ((value (fn-gns-group-value 5 nil))
        (root (ninep-directory-one-path '(1 0 0 0 0 1 1 0) value))
        (tasks (fn-9p-ge-begin root)))
  (and (equal (fn-gns-group-get "a" 0 0 root) value)
       (equal (fn-9p-ge-remaining tasks)
              '((:group-path (0 1 1 0 0 0 0 1) 8 (:group-number 5 nil))))
       (equal (ninep-directory-observe 40 tasks)
              '((:group-path (0 1 1 0 0 0 0 1) 8 (:group-number 5 nil))))))
 :rule-classes nil)

(defthm ninep-directory-quantum-does-not-truncate
 (let* ((value (fn-gns-group-value 5 nil))
        (root (ninep-directory-one-path '(1 0 0 0 0 1 1 0) value))
        (tasks (fn-9p-ge-begin root)))
  (and (equal (ninep-directory-observe 0 tasks) (fn-9p-ge-remaining tasks))
       (equal (ninep-directory-observe 1 tasks) (fn-9p-ge-remaining tasks))
       (equal (ninep-directory-observe 3 tasks) (fn-9p-ge-remaining tasks))))
 :rule-classes nil)

(defthm ninep-directory-wrong-phase-refusal-retains-source
 (let* ((tasks '((:wrong-phase ((:group-number 5 nil) nil) nil 0)))
        (step (fn-9p-ge-step tasks)))
  (and (equal (mv-nth 0 step) :refused)
       (equal (mv-nth 2 step) tasks)))
 :rule-classes nil)
