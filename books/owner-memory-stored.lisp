; Exact stored-article maxima and the owner's paired totals/maximum cache.
(in-package "ACL2")
(include-book "charged-totals")
(include-book "defrecord")
(local (in-theory (disable (tau-system))))

(defun fn-adm-stored-article-most (records)
  (declare (xargs :guard t))
  (if (consp records)
      (max (if (fn-held-p (car records)) (nfix (fn-hf-octets (fn-held-facts (car records))))
             (if (fn-hstxa-p (car records))
                 (nfix (fn-hf-octets (fn-held-facts (fn-hstxa-held (car records))))) 0))
           (fn-adm-stored-article-most (cdr records)))
    0))

(defun fn-adm-stored-most-extend (cache records)
  (declare (xargs :guard t))
  (let ((records (true-list-fix records)))
    (if (and (consp cache) (natp (car cache)) (natp (cdr cache)) (<= (car cache) (len records)))
        (max (cdr cache) (fn-adm-stored-article-most (nthcdr (car cache) records)))
      (fn-adm-stored-article-most records))))

(defun fn-adm-stored-most-cache-validp (cache records)
  (declare (xargs :guard t))
  (let ((records (true-list-fix records)))
    (and (consp cache) (natp (car cache)) (natp (cdr cache)) (<= (car cache) (len records))
         (equal (cdr cache) (fn-adm-stored-article-most (take (car cache) records))))))

(fn-defrecord fn-adm-memory-cache
 :constructor (fn-adm-memory-cache-make totals most)
 :fields ((fn-adm-memory-cache-totals t) (fn-adm-memory-cache-most t)))


; The fold ignores an improper tail, exactly as true-list-fix does.
(defthm fn-adm-stored-article-most-is-natural
 (natp (fn-adm-stored-article-most records))
 :rule-classes :type-prescription)
(defthm fn-adm-stored-article-most-of-true-list-fix
 (equal (fn-adm-stored-article-most (true-list-fix records))
        (fn-adm-stored-article-most records)))
(local (in-theory (disable fn-held-p fn-hstxa-p fn-held-facts fn-hstxa-held fn-hf-octets)))
(local
 (defun pin-most-split-ind (k records)
  (declare (xargs :measure (nfix k)))
  (if (or (zp k) (atom records)) (list k records)
    (pin-most-split-ind (1- k) (cdr records)))))
(local
 (defthm pin-most-split
  (implies (and (natp k) (<= k (len records)))
   (equal (max (fn-adm-stored-article-most (take k records))
               (fn-adm-stored-article-most (nthcdr k records)))
          (fn-adm-stored-article-most records)))
  :hints (("Goal" :induct (pin-most-split-ind k records)
                  :in-theory (enable take nthcdr)))))
(local
 (defthm pin-most-take-append
  (implies (and (natp k) (<= k (len records)))
   (equal (take k (append records more)) (take k records)))
  :hints (("Goal" :induct (pin-most-split-ind k records) :in-theory (enable take)))))
(local
 (defthm pin-most-take-of-true-list-fix
  (equal (take k (true-list-fix records)) (take k records))
  :hints (("Goal" :induct (pin-most-split-ind k records) :in-theory (enable take)))))
(local (set-default-hints
 '((quote (:in-theory (disable fn-adm-stored-article-most)
          :use ((:instance pin-most-split (k (car cache))
                           (records (true-list-fix records)))))))))
(defthm fn-adm-stored-most-extend-of-a-valid-cache
  (implies (fn-adm-stored-most-cache-validp cache records)
           (equal (fn-adm-stored-most-extend cache records)
                  (fn-adm-stored-article-most records))))
(local (set-default-hints
 '((quote (:in-theory (disable fn-adm-stored-article-most))))))
(defthm fn-adm-stored-most-cache-valid-after-commit
  (implies (fn-adm-stored-most-cache-validp cache records)
           (fn-adm-stored-most-cache-validp cache (append records more))))
(local (set-default-hints nil))
(defthm fn-adm-stored-article-most-of-a-commit
  (equal (fn-adm-stored-article-most (append records (list row)))
         (max (fn-adm-stored-article-most records)
              (fn-adm-stored-article-most (list row)))))

(defthm fn-adm-stored-article-most-covers-held-member
 (implies (and (member-equal rec records) (fn-held-p rec))
  (<= (nfix (fn-hf-octets (fn-held-facts rec)))
      (fn-adm-stored-article-most records)))
 :rule-classes :linear
 :hints (("Goal" :induct (fn-adm-stored-article-most records)
                 :in-theory (disable fn-held-p fn-hstxa-p fn-held-facts fn-hstxa-held fn-hf-octets))))

(defthm fn-adm-stored-most-empty-cache-is-valid
 (fn-adm-stored-most-cache-validp '(0 . 0) records)
 :hints (("Goal" :in-theory (enable fn-adm-stored-most-cache-validp))))
(local
 (defthm pin-most-take-len
  (equal (take (len records) (true-list-fix records)) (true-list-fix records))
  :hints (("Goal" :induct (true-list-fix records) :in-theory (enable take true-list-fix)))))
(defthm fn-adm-stored-most-full-cache-is-valid
 (fn-adm-stored-most-cache-validp
   (cons (len records) (fn-adm-stored-article-most records)) records)
 :hints (("Goal" :in-theory (disable fn-adm-stored-article-most))))
