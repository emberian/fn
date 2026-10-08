; Resumable accumulating row loops. The row can thread a concrete stobj;
; the library proves quantum composition once over its logical value.
(in-package "ACL2")

(encapsulate
 (((fn-dl-rn-row * * *) => (mv * * *))
  ((fn-dl-rn-ok) => *) ((fn-dl-rn-quantum) => *)
  ((fn-dl-rn-end * * *) => *))
 (local (defun fn-dl-rn-ok () nil))
 (local (defun fn-dl-rn-end (xs a s) (declare (ignore xs a s)) nil))
 (local (defun fn-dl-rn-quantum () 1))
 (local (defun fn-dl-rn-row (x a s) (declare (ignore x)) (mv nil a s)))
 (defthm fn-dl-rn-end-status
   (and (not (equal (fn-dl-rn-end xs a s) :done))
        (not (equal (fn-dl-rn-end xs a s) :more))))
 (defthm fn-dl-rn-positive-quantum (posp (fn-dl-rn-quantum)))
 (defthm fn-dl-rn-row-status
   (let ((v (mv-nth 0 (fn-dl-rn-row x a s))))
     (and (not (equal v :done)) (not (equal v :more))))))

(defthm fn-dl-rn-row-status-car
 (and (not (equal (car (fn-dl-rn-row xs a s)) :done))
      (not (equal (car (fn-dl-rn-row xs a s)) :more)))
 :hints (("Goal" :use ((:instance fn-dl-rn-row-status (x xs)))
          :in-theory (disable fn-dl-rn-row-status))))

(defun fn-dl-rn-all (xs a s)
 (declare (xargs :guard t))
 (if (atom xs) (mv (fn-dl-rn-end xs a s) a s)
   (mv-let (v a2 s) (fn-dl-rn-row xs a s)
     (if (equal v (fn-dl-rn-ok)) (fn-dl-rn-all (cdr xs) a2 s)
       (mv v a s)))))

(defun fn-dl-rn-run (k xs a s)
 (declare (xargs :guard (natp k)))
 (cond ((atom xs) (let ((v (fn-dl-rn-end xs a s)))
                     (if (equal v (fn-dl-rn-ok)) (mv :done nil a s)
                       (mv v xs a s))))
       ((zp k) (mv :more xs a s))
       (t (mv-let (v a2 s) (fn-dl-rn-row xs a s)
            (if (equal v (fn-dl-rn-ok))
                (fn-dl-rn-run (1- k) (cdr xs) a2 s)
              (mv v xs a s))))))

(defun fn-dl-rn-drive (fuel xs a s)
 (declare (xargs :guard (natp fuel)))
 (if (zp fuel) (mv '(:refused :fuel) a s)
   (mv-let (v rest a2 s) (fn-dl-rn-run (fn-dl-rn-quantum) xs a s)
     (cond ((equal v :done) (mv (fn-dl-rn-ok) a2 s))
           ((equal v :more) (fn-dl-rn-drive (1- fuel) rest a2 s))
           (t (mv v a2 s))))))

(defthm fn-dl-rn-run-rest-bound
 (<= (len (mv-nth 1 (fn-dl-rn-run k xs a s))) (len xs))
 :rule-classes :linear)

(defthm fn-dl-rn-run-progress
 (implies (and (posp k) (equal (mv-nth 0 (fn-dl-rn-run k xs a s)) :more))
          (< (len (mv-nth 1 (fn-dl-rn-run k xs a s))) (len xs)))
 :rule-classes :linear
 :hints (("Goal" :expand ((fn-dl-rn-run k xs a s))
          :use ((:instance fn-dl-rn-row-status (x xs)))
          :in-theory (disable fn-dl-rn-run fn-dl-rn-row-status))))

(defthm fn-dl-rn-run-composes
 (mv-let (v rest a2 s2) (fn-dl-rn-run k xs a s)
   (equal (fn-dl-rn-all xs a s)
          (cond ((equal v :done) (mv (fn-dl-rn-ok) a2 s2))
                ((equal v :more) (fn-dl-rn-all rest a2 s2))
                (t (mv v a2 s2)))))
 :rule-classes nil
 :hints (("Goal" :induct (fn-dl-rn-run k xs a s))))

(defthm fn-dl-rn-drive-is-all-when-fueled
 (implies (and (natp fuel) (< (len xs) fuel))
          (equal (fn-dl-rn-drive fuel xs a s) (fn-dl-rn-all xs a s)))
 :hints (("Goal" :induct (fn-dl-rn-drive fuel xs a s)
          :in-theory (disable fn-dl-rn-run fn-dl-rn-all))
         (and stable-under-simplificationp
              '(:use ((:instance fn-dl-rn-run-composes (k (fn-dl-rn-quantum)))
                      (:instance fn-dl-rn-run-progress (k (fn-dl-rn-quantum))))))))

(defthm fn-dl-rn-drive-is-all
 (equal (fn-dl-rn-drive (+ 1 (len xs)) xs a s) (fn-dl-rn-all xs a s))
 :hints (("Goal" :use ((:instance fn-dl-rn-drive-is-all-when-fueled (fuel (+ 1 (len xs)))))
          :in-theory (disable fn-dl-rn-drive fn-dl-rn-all)))
 :rule-classes nil)

(defthm fn-dl-rn-cons-equal
 (equal (equal (cons a b) (cons c d)) (and (equal a c) (equal b d))))

; :row is a term returning (mv VERDICT ACC [ST]); a refusal retains the
; old ACC and the returned ST. :success is the row/all success value.
; :end-status optionally refuses an improper terminal input by name; its
; default is :success. :done and :more are reserved run statuses. :quantum must be positive
; unconditionally, not only under the entry guard. Context formals stay fixed.
(defmacro def-loop/run (name formals &key over acc st row (success 'nil)
                            quantum (guard 't) guard-hints row-theory (end-status 'nil end-status-p))
 (let* ((xs (or over (car formals)))
        (end-status (if end-status-p end-status success))
        (all (intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-ALL") name))
        (run (intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-RUN") name))
        (drive (intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-DRIVE") name))
        (bridge (intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-DRIVE-IS-ALL") name))
        (preserves (intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-RUN-PRESERVES-GUARD") name))
        (all-shape (intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-ALL-SHAPE") name))
        (drive-shape (intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-DRIVE-SHAPE") name))
        (ss (or st 'dl-s))
        (outs (if st (list acc st) (list acc)))
        (outs2 (if st (list 'dl-a2 st) (list 'dl-a2)))
        (row-vars (cons 'dl-v outs2))
        (next (subst 'dl-a2 acc (subst `(cdr ,xs) xs formals)))
        (resume (subst 'dl-a2 acc (subst 'dl-rest xs formals)))
        (decl (and st `(:stobjs ,st)))
        (hints (and guard-hints `(:guard-hints ,guard-hints)))
        (wrap-row (if st row `(mv-let (dl-v dl-a2) ,row (mv dl-v dl-a2 ,ss))))
        (wrap-all (if st `(,all ,@formals)
                    `(mv-let (dl-v dl-a2) (,all ,@formals) (mv dl-v dl-a2 ,ss))))
        (wrap-run (if st `(,run dl-k ,@formals)
                    `(mv-let (dl-v dl-rest dl-a2) (,run dl-k ,@formals)
                       (mv dl-v dl-rest dl-a2 ,ss))))
        (wrap-drive (if st `(,drive dl-fuel ,@formals)
                      `(mv-let (dl-v dl-a2) (,drive dl-fuel ,@formals) (mv dl-v dl-a2 ,ss)))))
   (if (not (and (symbol-listp formals) (no-duplicatesp-eq formals)
                 (member-eq xs formals) (member-eq acc formals) (not (eq xs acc))
                 (or (not st) (and (member-eq st formals) (not (eq st xs)) (not (eq st acc))))
                 (not (intersectp-eq formals '(dl-k dl-fuel dl-v dl-rest dl-a2 dl-s)))
                 row quantum))
       '(assert-event nil :msg "def-loop :run requires distinct :over/:acc/optional :st formals, :row and :quantum; DL-* temporaries are reserved")
     `(encapsulate ()
        (defun ,all ,formals
          (declare (xargs :guard ,guard ,@decl ,@hints))
          (if (atom ,xs) (mv ,end-status ,@outs)
            (mv-let ,row-vars ,row
              (if (equal dl-v ,success) (,all ,@next) (mv dl-v ,@outs)))))
        (defun ,run (dl-k ,@formals)
          (declare (xargs :guard (and (natp dl-k) ,guard) ,@decl ,@hints))
          (cond ((atom ,xs) (let ((dl-v ,end-status))
                                (if (equal dl-v ,success) (mv :done nil ,@outs)
                                  (mv dl-v ,xs ,@outs))))
                ((zp dl-k) (mv :more ,xs ,@outs))
                (t (mv-let ,row-vars ,row
                     (if (equal dl-v ,success) (,run (1- dl-k) ,@next)
                       (mv dl-v ,xs ,@outs))))))
        ,@(and (not (eq guard t))
          `((local (defthm ,preserves
              (implies ,guard
                (mv-let (dl-v dl-rest ,@outs2) (,run dl-k ,@formals)
                  (declare (ignore dl-v))
                  (let ((,xs dl-rest) (,acc dl-a2))
                    (declare (ignorable ,xs ,acc)) ,guard)))
              :hints (("Goal" :induct (,run dl-k ,@formals)
                       :in-theory (disable ,(car row))))))))
        (defun ,drive (dl-fuel ,@formals)
          (declare (xargs :guard (and (natp dl-fuel) ,guard) ,@decl ,@hints))
          (if (zp dl-fuel) (mv '(:refused :fuel) ,@outs)
            (mv-let (dl-v dl-rest ,@outs2) (,run ,quantum ,@formals)
              (cond ((equal dl-v :done) (mv ,success ,@outs2))
                    ((equal dl-v :more) (,drive (1- dl-fuel) ,@resume))
                    (t (mv dl-v ,@outs2))))))
        ,@(and (not st)
          `((local (defthm ,all-shape
              (equal (list (mv-nth 0 (,all ,@formals)) (mv-nth 1 (,all ,@formals)))
                     (,all ,@formals))
              :rule-classes nil
              :hints (("Goal" :induct (,all ,@formals)
                       :in-theory (disable ,(car row))))))
            (local (defthm ,drive-shape
              (equal (list (mv-nth 0 (,drive dl-fuel ,@formals)) (mv-nth 1 (,drive dl-fuel ,@formals)))
                     (,drive dl-fuel ,@formals))
              :rule-classes nil
              :hints (("Goal" :induct (,drive dl-fuel ,@formals)
                       :in-theory (disable ,(car row) ,run)))))))
        (defthm ,bridge
          (equal (,drive (+ 1 (len ,xs)) ,@formals) (,all ,@formals))
          :rule-classes nil
          :hints (("Goal"
                   :use ((:instance
                          (:functional-instance fn-dl-rn-drive-is-all
                           (fn-dl-rn-ok (lambda () ,success))
                           (fn-dl-rn-end (lambda (,xs ,acc ,ss) ,end-status))
                           (fn-dl-rn-quantum (lambda () ,quantum))
                           (fn-dl-rn-row (lambda (,xs ,acc ,ss) ,wrap-row))
                           (fn-dl-rn-all (lambda (,xs ,acc ,ss) ,wrap-all))
                           (fn-dl-rn-run (lambda (dl-k ,xs ,acc ,ss) ,wrap-run))
                           (fn-dl-rn-drive (lambda (dl-fuel ,xs ,acc ,ss) ,wrap-drive)))
                          (xs ,xs) (a ,acc) (s ,(or st nil)))
                         ,@(and (not st)
                           `((:instance ,all-shape)
                             (:instance ,drive-shape (dl-fuel (+ 1 (len ,xs)))))))
                   :in-theory (union-theories
                               '(,all ,run ,drive ,(car row) ,@row-theory car-cons cdr-cons mv-nth fn-dl-rn-cons-equal
                                 zp natp posp len binary-+ <)
                               (theory 'minimal-theory)))))
        (table fn-generated ',name
               '(:def-loop :shape :run :all ,all :run ,run :drive ,drive :bridge ,bridge))))))

(in-theory (disable fn-dl-rn-cons-equal fn-dl-rn-all fn-dl-rn-run fn-dl-rn-drive
                    fn-dl-rn-positive-quantum fn-dl-rn-end-status fn-dl-rn-row-status
                    fn-dl-rn-row-status-car fn-dl-rn-run-rest-bound
                    fn-dl-rn-run-progress fn-dl-rn-drive-is-all-when-fueled))
