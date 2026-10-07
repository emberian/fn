(in-package "ACL2")
(include-book "def-loop-fixture-dep")

(defun fn-arf-changed-handles-loop (old new rev)
  (declare (xargs :guard (true-listp rev)))
  (cond ((or (atom old) (atom new)) (revappend rev nil))
        ((or (equal (car old) (car new))
             (not (fn-arf-row-handle (car old))))
         (fn-arf-changed-handles-loop (cdr old) (cdr new) rev))
        (t (fn-arf-changed-handles-loop (cdr old) (cdr new)
                                        (cons (fn-arf-row-handle (car old)) rev)))))

(defun fn-arf-changed-handles (old new)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (cond ((or (atom old) (atom new)) nil)
             ((or (equal (car old) (car new))
                  (not (fn-arf-row-handle (car old))))
              (fn-arf-changed-handles (cdr old) (cdr new)))
             (t (cons (fn-arf-row-handle (car old))
                      (fn-arf-changed-handles (cdr old) (cdr new)))))
       :exec (fn-arf-changed-handles-loop old new nil)))

(defthm fn-arf-changed-handles-loop-is-changed-handles
  (equal (fn-arf-changed-handles-loop old new rev)
         (revappend rev (fn-arf-changed-handles old new)))
  :hints (("Goal" :in-theory (disable fn-arf-row-handle))))

(verify-guards fn-arf-changed-handles
  :hints (("Goal" :in-theory (disable fn-arf-row-handle))))

