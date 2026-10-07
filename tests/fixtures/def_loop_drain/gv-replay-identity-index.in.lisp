(in-package "ACL2")
(include-book "def-loop-fixture-dep")

(defun fn-rii-kbuild-releases-loop (rev trie)
  (declare (xargs :guard t))
  (if (consp rev)
      (fn-rii-kbuild-releases-loop (cdr rev)
                                   (fn-rii-id-put (fn-retain-release-id (car rev)) trie))
    trie))

(defun fn-rii-kbuild-releases (releases)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp releases)
           (fn-rii-id-put (fn-retain-release-id (car releases))
                          (fn-rii-kbuild-releases (cdr releases)))
         nil)
       :exec (fn-rii-kbuild-releases-loop (fn-ag-rev-onto releases nil) nil)))

(defun fn-rii-kbuild-pins-loop (rev trie)
  (declare (xargs :guard t))
  (if (consp rev)
      (fn-rii-kbuild-pins-loop (cdr rev)
                               (fn-rii-id-put (fn-retain-obligation-id (car rev)) trie))
    trie))

(defun fn-rii-kbuild-pins (pins base)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp pins)
           (fn-rii-id-put (fn-retain-obligation-id (car pins))
                          (fn-rii-kbuild-pins (cdr pins) base))
         base)
       :exec (fn-rii-kbuild-pins-loop (fn-ag-rev-onto pins nil) base)))

(encapsulate ()
  (local
   (defthm fn-rii-kbuild-releases-loop-of-rev-onto
     (equal (fn-rii-kbuild-releases-loop (fn-ag-rev-onto xs zs) nil)
            (fn-rii-kbuild-releases-loop zs (fn-rii-kbuild-releases xs)))
     :hints (("Goal" :induct (fn-ag-rev-onto xs zs)
                     :in-theory (disable fn-rii-id-put fn-retain-release-id)))))
  (local
   (defthm fn-rii-kbuild-pins-loop-of-rev-onto
     (equal (fn-rii-kbuild-pins-loop (fn-ag-rev-onto xs zs) base)
            (fn-rii-kbuild-pins-loop zs (fn-rii-kbuild-pins xs base)))
     :hints (("Goal" :induct (fn-ag-rev-onto xs zs)
                     :in-theory (disable fn-rii-id-put fn-retain-obligation-id)))))
  (verify-guards fn-rii-kbuild-releases
    :hints (("Goal" :in-theory (disable fn-rii-id-put fn-retain-release-id fn-ag-rev-onto)
                    :use ((:instance fn-rii-kbuild-releases-loop-of-rev-onto
                                     (xs releases) (zs nil))))))
  (verify-guards fn-rii-kbuild-pins
    :hints (("Goal" :in-theory (disable fn-rii-id-put fn-retain-obligation-id fn-ag-rev-onto)
                    :use ((:instance fn-rii-kbuild-pins-loop-of-rev-onto
                                     (xs pins) (zs nil)))))))

(defun fn-rii-kbuild (retention)
  (declare (xargs :guard t))
  (fn-rii-kbuild-pins (fn-retain-pins retention)
                      (fn-rii-kbuild-releases (fn-retain-releases retention))))

(local
 (defthm fn-rii-id-hasp-of-kbuild-releases
   (implies (stringp x)
            (iff (fn-rii-id-hasp x (fn-rii-kbuild-releases releases))
                 (fn-rii-release-hasp x releases)))))

(local
 (defthm fn-rii-id-hasp-of-kbuild-pins
   (implies (stringp x)
            (iff (fn-rii-id-hasp x (fn-rii-kbuild-pins pins base))
                 (or (fn-rii-pin-hasp x pins) (fn-rii-id-hasp x base))))))
