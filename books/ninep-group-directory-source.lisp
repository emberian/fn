; Bounded immutable group-trie enumeration. A result borrows its persistent
; bit path and actual group value; this leaf neither makes names/stat records
; nor grants a mount from an arbitrary root.
(in-package "ACL2")
(include-book "group-number-source-assignment")
(local (include-book "arithmetic-5/top" :dir :system))

(defun fn-9p-ge-entry (node path depth)
 (declare (xargs :guard t))
 (if (and (equal (mod (nfix depth) 8) 0)
          (fn-gns-group-valuep (fn-gnix-val node)))
     (list :group-path path (nfix depth) (fn-gnix-val node))
   nil))

(defun fn-9p-ge-tree (node path depth)
 (declare (xargs :guard t :measure (acl2-count node)))
 (if (consp node)
     (append (if (fn-9p-ge-entry node path depth)
                 (list (fn-9p-ge-entry node path depth)) nil)
             (fn-9p-ge-tree (fn-gnix-zero node) (cons 0 path) (1+ (nfix depth)))
             (fn-9p-ge-tree (fn-gnix-one node) (cons 1 path) (1+ (nfix depth))))
   nil))

; Logical whole-tree enumeration is a reference only, never a host scheduling
; subject. Tasks borrow the tree and share path spines across their children.
(defun fn-9p-ge-remaining (tasks)
 (declare (xargs :guard t :measure (acl2-count tasks)))
 (if (consp tasks)
     (let* ((task (car tasks)) (phase (fn-gns-at 0 task))
            (node (fn-gns-at 1 task)) (path (fn-gns-at 2 task))
            (depth (fn-gns-at 3 task)))
       (append
        (cond ((eq phase :visit) (fn-9p-ge-tree node path depth))
              ((and (eq phase :descend) (consp node))
               (append
                (fn-9p-ge-tree (fn-gnix-zero node) (cons 0 path) (1+ (nfix depth)))
                (fn-9p-ge-tree (fn-gnix-one node) (cons 1 path) (1+ (nfix depth)))))
              (t nil))
        (fn-9p-ge-remaining (cdr tasks))))
   nil))

(defun fn-9p-ge-begin (root)
 (declare (xargs :guard t))
 (list (list :visit root nil 0)))

; One action inspects one current node or pushes two fixed child frames.
; No LEN, tree recognition, full-name reconstruction or catalogue copy.
(defun fn-9p-ge-step (tasks)
 (declare (xargs :guard t))
 (if (not (consp tasks)) (mv :complete nil tasks)
   (let* ((task (car tasks)) (phase (fn-gns-at 0 task))
          (node (fn-gns-at 1 task)) (path (fn-gns-at 2 task))
          (depth (fn-gns-at 3 task)) (tail (cdr tasks)))
    (cond
     ((not (consp node)) (mv :yield nil tail))
     ((eq phase :visit)
      (let ((entry (fn-9p-ge-entry node path depth)))
       (mv (if entry :group :yield) entry
           (cons (list :descend node path depth) tail))))
     ((eq phase :descend)
      (let ((next-depth (1+ (nfix depth))))
       (mv :yield nil
           (cons (list :visit (fn-gnix-zero node) (cons 0 path) next-depth)
                 (cons (list :visit (fn-gnix-one node) (cons 1 path)
                             next-depth) tail)))))
     (t (mv :refused nil tasks))))))

(local
 (defthm fn-9p-ge-tree-unfolds
  (implies (consp node)
   (equal (fn-9p-ge-tree node path depth)
          (append (if (fn-9p-ge-entry node path depth)
                      (list (fn-9p-ge-entry node path depth)) nil)
                  (fn-9p-ge-tree (fn-gnix-zero node) (cons 0 path) (1+ (nfix depth)))
                  (fn-9p-ge-tree (fn-gnix-one node) (cons 1 path) (1+ (nfix depth))))))
  :hints (("Goal" :expand ((fn-9p-ge-tree node path depth))
                   :in-theory (disable fn-9p-ge-tree fn-9p-ge-entry)))))
(local
 (defthm fn-9p-ge-tree-of-atom
  (implies (not (consp node)) (equal (fn-9p-ge-tree node path depth) nil))
  :hints (("Goal" :expand ((fn-9p-ge-tree node path depth))
                   :in-theory (disable fn-9p-ge-tree fn-9p-ge-entry)))))

(local
 (defthm fn-9p-ge-append-associative
  (equal (append (append a b) c) (append a b c))
  :hints (("Goal" :induct (append a b) :in-theory (enable append)))))

(defthm fn-9p-ge-step-preserves-ordered-directory
 (equal (fn-9p-ge-remaining tasks)
        (append (if (equal (mv-nth 0 (fn-9p-ge-step tasks)) :group)
                    (list (mv-nth 1 (fn-9p-ge-step tasks))) nil)
                (fn-9p-ge-remaining (mv-nth 2 (fn-9p-ge-step tasks)))))
 :rule-classes nil
 :hints (("Goal" :in-theory
          (e/d (fn-9p-ge-step fn-9p-ge-remaining)
               (fn-9p-ge-tree fn-9p-ge-entry fn-gns-group-valuep))
          :do-not-induct t
          :expand ((fn-9p-ge-remaining tasks)))))
