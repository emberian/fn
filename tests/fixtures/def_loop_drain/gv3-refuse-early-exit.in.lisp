(in-package "ACL2")
(include-book "def-loop-fixture-dep")

(defun fn-native-admin-carries-rows-loop (name hexes acc)
  (declare (xargs :guard (true-listp acc)))
  (if (consp hexes)
      (if (fn-native-admin-carries-hexp (car hexes))
          (fn-native-admin-carries-rows-loop
           name (cdr hexes) (cons (list name "carries-principal" (car hexes) 0) acc))
        :bad)
    (revappend acc nil)))

(defun fn-native-admin-carries-rows (name hexes)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp hexes)
           (let ((rest (fn-native-admin-carries-rows name (cdr hexes))))
             (if (and (fn-native-admin-carries-hexp (car hexes)) (listp rest))
                 (cons (list name "carries-principal" (car hexes) 0) rest)
               :bad))
         nil)
       :exec (fn-native-admin-carries-rows-loop name hexes nil)))

(local
 (defthm fn-native-admin-carries-rows-loop-is-revappend
   (equal (fn-native-admin-carries-rows-loop name hexes acc)
          (if (listp (fn-native-admin-carries-rows name hexes))
              (revappend acc (fn-native-admin-carries-rows name hexes))
            :bad))))

(verify-guards fn-native-admin-carries-rows
  ; The hex test stays closed: the guard needs only its truth value.
  :hints (("Goal" :in-theory (disable fn-native-admin-carries-hexp))))
