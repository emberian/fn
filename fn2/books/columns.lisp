; fn2 records/columns seed.  Declaration is recorded in the ACL2 world.
; Generated array storage is the executable representation.  The row/table
; views are non-executable, and resizing belongs only to the generated init.
(in-package "ACL2")
(include-book "declare")

(defthm fn2-columns-len-update-nth
  (implies (and (natp i) (< i (len xs)))
           (equal (len (update-nth i v xs)) (len xs))))

(defthm fn2-columns-nth-update-nth
  (equal (nth k (update-nth i v xs))
         (if (equal (nfix k) (nfix i)) v (nth k xs))))

(defthm fn2-columns-len-resize-list
  (equal (len (resize-list xs n default)) (nfix n)))

; One list template; each column instantiates it, without repeating induction.
(encapsulate (((fn2-columns-valuep *) => *))
 (local (defun fn2-columns-valuep (x) (natp x))))
(defun fn2-columns-valuesp (xs)
 (if (atom xs) (eq xs nil)
   (and (fn2-columns-valuep (car xs)) (fn2-columns-valuesp (cdr xs)))))
(defthm fn2-columns-valuesp-nth
 (implies (and (fn2-columns-valuesp xs) (natp i) (< i (len xs)))
          (fn2-columns-valuep (nth i xs))))
(defthm fn2-columns-valuesp-update
 (implies (and (fn2-columns-valuesp xs) (natp i) (< i (len xs))
               (fn2-columns-valuep v))
          (fn2-columns-valuesp (update-nth i v xs))))
(defthm fn2-columns-valuesp-resize
 (implies (and (fn2-columns-valuesp xs) (fn2-columns-valuep v))
          (fn2-columns-valuesp (resize-list xs n v))))

(encapsulate (((fn2-columns-slotp * *) => *))
 (local (defun fn2-columns-slotp (tag x) (declare (ignore tag)) (natp x))))
(defun fn2-columns-recordp (schema xs)
 (if (atom schema) t
   (and (fn2-columns-slotp (nfix (car schema)) (nth (car schema) xs))
        (fn2-columns-recordp (cdr schema) xs))))
(defthm fn2-columns-recordp-update
 (implies (and (fn2-columns-recordp schema xs)
               (natp i) (fn2-columns-slotp i v))
          (fn2-columns-recordp schema (update-nth i v xs))))

; Column lengths have one index-parametric update proof, just like types.
(defun fn2-columns-shapep (n rows xs)
  (if (zp n) t
    (and (fn2-columns-shapep (- n 1) rows xs)
         (equal (len (nth (- n 1) xs)) rows))))
(defthm fn2-columns-shapep-update
  (implies (and (fn2-columns-shapep n rows xs) (natp i)
                (or (<= (nfix n) i) (equal (len v) rows)))
           (fn2-columns-shapep n rows (update-nth i v xs))))
(in-theory (disable fn2-columns-shapep))

; Keep field replacement symbolic for the generic record theorem.
(in-theory (disable update-nth))

(defun fn2-columns-sym (name suffix)
  (declare (xargs :guard t :verify-guards nil))
  (intern-in-package-of-symbol
   (concatenate 'string (symbol-name name) suffix) name))

(defun fn2-columns-pre (prefix name)
  (declare (xargs :guard t :verify-guards nil))
  (intern-in-package-of-symbol
   (concatenate 'string prefix (symbol-name name)) name))

(defun fn2-columns-col-name (name col)
  (declare (xargs :guard t :verify-guards nil))
  (fn2-columns-sym name (concatenate 'string "-" (symbol-name col))))

(defun fn2-columns-width (kind)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((eq kind :u8) 8) ((eq kind :u16) 16)
        ((eq kind :u32) 32) ((eq kind :u60) 60)
        ((eq kind :u64) 64) ((eq kind :bool) 1) (t 8)))

(defun fn2-columns-fields (name cols)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom cols) nil
    (cons `(,(fn2-columns-sym (fn2-columns-col-name name (caar cols)) "$A")
            :type (array (unsigned-byte ,(fn2-columns-width (cadar cols))) (0))
            :initially 0 :resizable t)
          (fn2-columns-fields name (cdr cols)))))

(defun fn2-columns-enum-constants (name kws n)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom kws) nil
    (cons `(defconst ,(fn2-columns-pre "*" (fn2-columns-sym
                       (fn2-columns-col-name name (car kws)) "*")) ,n)
          (fn2-columns-enum-constants name (cdr kws) (+ 1 (nfix n))))))

(defun fn2-columns-enum-cases (kws n direction)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom kws) nil
    (cons (if direction `(,n ,(car kws)) `(,(car kws) ,n))
          (fn2-columns-enum-cases (cdr kws) (+ 1 (nfix n)) direction))))

(defun fn2-columns-enum-events (cols)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom cols) nil
    (let ((kind (cadar cols)))
      (append
       (if (and (consp kind) (eq (car kind) :enum))
           (let ((ename (cadr kind)) (kws (caddr kind)))
             (append
              (fn2-columns-enum-constants ename kws 0)
              `((defun ,(fn2-columns-sym ename "-CODE->KEYWORD") (code)
                  (declare (xargs :guard (unsigned-byte-p 8 code)))
                  (case code ,@(fn2-columns-enum-cases kws 0 t) (otherwise nil)))
                (defun ,(fn2-columns-sym ename "-KEYWORD->CODE") (keyword)
                  (declare (xargs :guard t))
                  (case keyword ,@(fn2-columns-enum-cases kws 0 nil)
                    (otherwise nil))))))
         nil)
       (fn2-columns-enum-events (cdr cols))))))

; Raw fields pass through verbatim.  Numeric fields additionally receive
; the specialized arithmetic/shape proof API; arbitrary raw fields do not.
(defun fn2-columns-field-spec (field)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom field) t
    (let ((entry (member-eq :type (cdr field))))
      (if entry (cadr entry) t))))

(defun fn2-columns-arrayp (field)
  (declare (xargs :guard t :verify-guards nil))
  (and (consp (fn2-columns-field-spec field))
       (eq (car (fn2-columns-field-spec field)) 'array)))

(defun fn2-columns-field-type (field)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn2-columns-arrayp field)
      (cadr (fn2-columns-field-spec field)) (fn2-columns-field-spec field)))

(defun fn2-columns-numeric-fieldp (field)
  (declare (xargs :guard t :verify-guards nil))
  (let ((type (fn2-columns-field-type field)))
    (and (consp type)
         (or (and (eq (car type) 'unsigned-byte) (posp (cadr type)))
        (and (eq (car type) 'integer) (natp (cadr type))
             (or (eq (caddr type) '*)
                 (and (integerp (caddr type)) (<= (cadr type) (caddr type)))))))))

(defun fn2-columns-type-form (type v)
  (declare (xargs :guard t :verify-guards nil))
  (if (eq (car type) 'unsigned-byte)
      `(unsigned-byte-p ,(cadr type) ,v)
    `(and (integerp ,v) (<= ,(cadr type) ,v)
          ,(if (eq (caddr type) '*) t `(<= ,v ,(caddr type))))))

(defun fn2-columns-type-limit (type)
  (declare (xargs :guard t :verify-guards nil))
  (if (eq (car type) 'unsigned-byte)
      (expt 2 (nfix (cadr type)))
    (if (integerp (caddr type)) (+ 1 (caddr type)) nil)))

; Unbounded extras and numeric extras reaching u64 require justification.
; Keep reasons in the registry, but never pass this DSL keyword to DEFSTOBJ.
(defun fn2-columns-extra-okp (fields)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom fields) (null fields)
    (let* ((field (car fields)) (why (and (consp field) (cadr (member-eq :why (cdr field)))))
           (limit (and (fn2-columns-numeric-fieldp field)
                       (fn2-columns-type-limit (fn2-columns-field-type field)))))
      (and (consp field)
           (or (and limit (<= limit (expt 2 63)))
               (and (stringp why) (< 0 (length why))))
           (fn2-columns-extra-okp (cdr fields))))))

(defun fn2-columns-without-why (options)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom options) nil
    (if (eq (car options) :why) (cddr options)
      (cons (car options) (cons (cadr options) (fn2-columns-without-why (cddr options)))))))

(defun fn2-columns-extra-specs (fields)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom fields) nil
    (cons (cons (caar fields) (fn2-columns-without-why (cdar fields)))
          (fn2-columns-extra-specs (cdr fields)))))

(defun fn2-columns-extra-reasons (fields)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom fields) nil
    (let ((why (cadr (member-eq :why (cdar fields)))))
      (append (and why (list (cons (caar fields) why)))
              (fn2-columns-extra-reasons (cdr fields))))))

(defun fn2-columns-array-facts (field)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((p (fn2-columns-sym (car field) "P"))
         (type (fn2-columns-field-type field))
         (fit (fn2-columns-type-form type 'v))
         (limit (fn2-columns-type-limit type))
         (subst `((fn2-columns-valuep (lambda (x) ,(fn2-columns-type-form type 'x)))
                  (fn2-columns-valuesp ,p)))
         (nth-hint `(("Goal" :use ((:functional-instance fn2-columns-valuesp-nth ,@subst))))))
    `((defthm ,(fn2-columns-sym p "-NTH-NATP")
        (implies (and (,p xs) (natp i) (< i (len xs))) (natp (nth i xs)))
        :rule-classes :type-prescription :hints ,nth-hint)
      ,@(if limit
            `((defthm ,(fn2-columns-sym p "-NTH-BOUND")
                (implies (and (,p xs) (natp i) (< i (len xs))) (< (nth i xs) ,limit))
                :rule-classes :linear :hints ,nth-hint)) nil)
      (defthm ,(fn2-columns-sym p "-OF-UPDATE-NTH")
        (implies (and (,p xs) (natp i) (< i (len xs)) ,fit) (,p (update-nth i v xs)))
        :hints (("Goal" :use ((:functional-instance fn2-columns-valuesp-update ,@subst)))))
      (defthm ,(fn2-columns-sym p "-OF-RESIZE-LIST")
        (implies (and (,p xs) ,fit) (,p (resize-list xs n v)))
        :hints (("Goal" :use ((:functional-instance fn2-columns-valuesp-resize ,@subst)))))
      (in-theory (disable ,p)))))

(defun fn2-columns-all-array-facts (fields)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom fields) nil
    (append (if (and (fn2-columns-arrayp (car fields))
                     (fn2-columns-numeric-fieldp (car fields)))
                (fn2-columns-array-facts (car fields)) nil)
            (fn2-columns-all-array-facts (cdr fields)))))

; These array-predicate facts match every NTH, independent of its field.
; Use them while deriving the typed accessor API, then keep them available
; only by explicit hint. The field-specific RAW-NTH facts remain enabled.
(defun fn2-columns-array-nth-runes (fields)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom fields) nil
    (append
     (if (and (fn2-columns-arrayp (car fields))
              (fn2-columns-numeric-fieldp (car fields)))
         (let ((p (fn2-columns-sym (caar fields) "P")))
           (append
            `((:type-prescription ,(fn2-columns-sym p "-NTH-NATP")))
            (and (fn2-columns-type-limit (fn2-columns-field-type (car fields)))
                 `((:linear ,(fn2-columns-sym p "-NTH-BOUND"))))))
       nil)
     (fn2-columns-array-nth-runes (cdr fields)))))

(defun fn2-columns-slot-cases (fields index)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom fields) nil
    (cons `(,index
            (and (,(fn2-columns-sym (caar fields) "P") x)
                 ,(if (and (fn2-columns-arrayp (car fields))
                           (not (cadr (member-eq :resizable (car fields)))))
                      `(equal (len x) ,(car (caddr (fn2-columns-field-spec (car fields))))) t)))
          (fn2-columns-slot-cases (cdr fields) (+ 1 (nfix index))))))

(defun fn2-columns-predicates (fields)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom fields) nil
    (cons (fn2-columns-sym (caar fields) "P") (fn2-columns-predicates (cdr fields)))))

(defun fn2-columns-record-events (name fields)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((p (fn2-columns-sym name "P"))
         (slotp (fn2-columns-sym name "-FIELD-P"))
         (recordp (fn2-columns-sym name "-RECORD-P"))
         (bridge (fn2-columns-sym name "-AS-RECORD"))
         (schema (strip-cars (fn2-columns-slot-cases fields 0))))
    `((defun ,slotp (tag x)
        (declare (xargs :verify-guards nil))
        (case tag ,@(fn2-columns-slot-cases fields 0) (otherwise t)))
      (defun ,recordp (schema xs)
        (declare (xargs :verify-guards nil))
        (if (atom schema) t
          (and (,slotp (nfix (car schema)) (nth (car schema) xs)) (,recordp (cdr schema) xs))))
      (local (defthm ,(fn2-columns-sym recordp "-UPDATE")
        (implies (and (,recordp schema xs) (natp i) (,slotp i v))
                 (,recordp schema (update-nth i v xs)))
        :hints (("Goal" :use ((:functional-instance fn2-columns-recordp-update
                               (fn2-columns-slotp ,slotp) (fn2-columns-recordp ,recordp)))))))
      (local (defthm ,bridge
        (equal (,p xs) (and (true-listp xs) (equal (len xs) ,(len fields))
                            (,recordp ',schema xs)))
        :hints (("Goal" :in-theory (disable ,@(fn2-columns-predicates fields))))))
      (defthm ,(fn2-columns-sym name "-UPDATE-FIELD-TYPE")
        (implies (and (,p xs) (natp i) (< i ,(len fields))
                      (,slotp i v)) (,p (update-nth i v xs)))
        :hints (("Goal" :in-theory (disable ,p ,recordp ,slotp))))
      (local (in-theory (disable ,bridge)))
      (in-theory (disable ,p ,recordp)))))

(defun fn2-columns-field-term (index name)
  (declare (xargs :guard t :verify-guards nil))
  (if (zp index) `(car ,name) `(nth ,index ,name)))

(defun fn2-columns-field-facts (name field index localp)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((p (fn2-columns-sym name "P")) (f (car field))
         (arrayp (fn2-columns-arrayp field))
         (fp (fn2-columns-sym f "P"))
         (read (if arrayp (fn2-columns-sym f "I") f))
         (write (fn2-columns-pre "UPDATE-" read))
         (resize (fn2-columns-pre "RESIZE-" f))
         (length (fn2-columns-sym f "-LENGTH"))
         (type (fn2-columns-field-type field))
         (fit (fn2-columns-type-form type 'v))
         (limit (fn2-columns-type-limit type))
         (readcall (if arrayp `(,read i ,name) `(,read ,name)))
         (writecall (if arrayp `(,write i v ,name) `(,write v ,name)))
         (bounds (if arrayp `((natp i) (< i (,length ,name))) nil)))
    `((defthm ,(fn2-columns-sym f "-FIELD-TYPE")
        (implies (,p ,name) (,fp ,(fn2-columns-field-term index name)))
        :rule-classes (:rewrite :forward-chaining)
        :hints (("Goal" :in-theory (enable ,p))))
      ,@(if arrayp
            (if (cadr (member-eq :resizable field)) nil
              `((defthm ,(fn2-columns-sym f "-FIXED-LENGTH")
                  (implies (,p ,name)
                           (equal (len (nth ,index ,name))
                                  ,(car (caddr (fn2-columns-field-spec field)))))
                  :rule-classes (:rewrite :forward-chaining)
                  :hints (("Goal" :in-theory (enable ,p))))))
          `((defthm ,(fn2-columns-sym f "-NTH-NATP")
              (implies (,p ,name) (natp (nth ,index ,name)))
              :rule-classes :type-prescription
              :hints (("Goal" :in-theory (enable ,p ,fp))))
            ,@(if limit
                  `((defthm ,(fn2-columns-sym f "-NTH-BOUND")
                      (implies (,p ,name) (< (nth ,index ,name) ,limit))
                      :rule-classes :linear
                      :hints (("Goal" :in-theory (enable ,p ,fp))))) nil)))
      ,@(if (and arrayp (not localp))
            `((progn (defthm ,(fn2-columns-sym f "-RAW-NTH-NATP")
                (implies (and (,p ,name) (natp i)
                              (< i ,(if (cadr (member-eq :resizable field))
                                        `(len (nth ,index ,name))
                                      (car (caddr (fn2-columns-field-spec field))))))
                         (natp (nth i (nth ,index ,name))))
                :rule-classes :type-prescription))
              ,@(if limit
                    `((progn (defthm ,(fn2-columns-sym f "-RAW-NTH-BOUND")
                        (implies (and (,p ,name) (natp i)
                                      (< i ,(if (cadr (member-eq :resizable field))
                                                `(len (nth ,index ,name))
                                              (car (caddr (fn2-columns-field-spec field))))))
                                 (< (nth i (nth ,index ,name)) ,limit))
                        :rule-classes :linear))) nil)) nil)
      (defthm ,(fn2-columns-sym read "-NATP")
        (implies (and (,p ,name) ,@bounds) (natp ,readcall))
        :rule-classes :type-prescription)
      ,@(if limit
            `((defthm ,(fn2-columns-sym read "-BOUND")
                (implies (and (,p ,name) ,@bounds) (< ,readcall ,limit))
                :rule-classes :linear)) nil)
      (defthm ,(fn2-columns-sym write "-NTH")
        (equal (nth k ,writecall)
               (if (equal (nfix k) ,index)
                   ,(if arrayp `(update-nth i v (nth ,index ,name)) 'v)
                 (nth k ,name))))
      (defthm ,(fn2-columns-sym write "-PRESERVES-TYPE")
        (implies (and (,p ,name) ,@bounds ,fit) (,p ,writecall)))
      ,@(if arrayp
            `((defthm ,(fn2-columns-sym write "-LENGTH")
                (implies (and (natp i) (< i (,length ,name)))
                         (equal (,length ,writecall) (,length ,name))))) nil)
      ,@(if (and arrayp (cadr (member-eq :resizable field)))
            `((defthm ,(fn2-columns-sym resize "-NTH")
                (equal (nth k (,resize n ,name))
                       (if (equal (nfix k) ,index)
                           (resize-list (nth ,index ,name) n
                                        ,(cadr (member-eq :initially field)))
                         (nth k ,name))))
              (defthm ,(fn2-columns-sym resize "-PRESERVES-TYPE")
                (implies (and (,p ,name) (natp n)) (,p (,resize n ,name))))
              (defthm ,(fn2-columns-sym resize "-LENGTH")
                (equal (,length (,resize n ,name)) (nfix n)))
              (in-theory (disable ,resize))) nil)
      (in-theory (disable ,write)))))

(defun fn2-columns-all-field-facts (name fields index localp)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom fields) nil
    (append (if (fn2-columns-numeric-fieldp (car fields))
                (fn2-columns-field-facts name (car fields) index localp) nil)
            (fn2-columns-all-field-facts name (cdr fields) (+ 1 (nfix index)) localp))))

(defun fn2-columns-wfp-conjuncts (name cols)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom cols) nil
    (cons `(equal (,(fn2-columns-sym
                    (fn2-columns-col-name name (caar cols)) "$A-LENGTH") ,name)
                  (,(fn2-columns-sym name "-ROWS") ,name))
          (fn2-columns-wfp-conjuncts name (cdr cols)))))

(defun fn2-columns-wfp-length-facts (name cols index)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom cols) nil
    (cons
     `(defthm ,(fn2-columns-sym (fn2-columns-col-name name (caar cols)) "-LENGTH-WHEN-WFP")
        (implies (,(fn2-columns-sym name "-WFP") ,name)
                 (equal (len ,(fn2-columns-field-term index name))
                        (,(fn2-columns-sym name "-ROWS") ,name)))
        :hints (("Goal" :in-theory (enable ,(fn2-columns-sym name "-WFP")))))
     (fn2-columns-wfp-length-facts name (cdr cols) (+ 1 (nfix index))))))

(defun fn2-columns-resize-bindings (name cols)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom cols) nil
    (cons `(,name (,(fn2-columns-pre "RESIZE-"
                       (fn2-columns-sym (fn2-columns-col-name name (caar cols)) "$A"))
                  n ,name))
          (fn2-columns-resize-bindings name (cdr cols)))))

(defun fn2-columns-shape-expansions (n)
  (declare (xargs :verify-guards nil))
  (if (zp n) nil
    (cons `(:free (rows xs) (fn2-columns-shapep ,n rows xs))
          (fn2-columns-shape-expansions (- n 1)))))

(defun fn2-columns-length-names (name cols)
  (declare (xargs :verify-guards nil))
  (if (atom cols) nil
    (cons (fn2-columns-sym (fn2-columns-col-name name (caar cols)) "$A-LENGTH")
          (fn2-columns-length-names name (cdr cols)))))

(defun fn2-columns-shape-events (name cols bound)
  (declare (xargs :verify-guards nil))
  (let ((count (len cols)) (wfp (fn2-columns-sym name "-WFP"))
        (rows (fn2-columns-sym name "-ROWS"))
        (bridge (fn2-columns-sym name "-WFP-AS-SHAPE")))
    `((local (defthm ,bridge
        (equal (,wfp ,name)
               (and (natp (,rows ,name)) (< (,rows ,name) ,bound)
                    (fn2-columns-shapep ,count (,rows ,name) ,name)))
        :hints (("Goal" :in-theory (union-theories
                          '(,wfp ,rows fn2-columns-shapep zp ,@(fn2-columns-length-names name cols))
                          (theory 'minimal-theory))
                        :expand ,(fn2-columns-shape-expansions count)))))
      (defthm ,(fn2-columns-sym name "-UPDATE-FIELD-WFP")
        (implies (and (,wfp ,name) (natp i) (not (equal i ,count))
                      (or (<= ,count i) (equal (len v) (,rows ,name))))
                 (,wfp (update-nth i v ,name)))
        :hints (("Goal" :in-theory (disable ,wfp))))
      (local (in-theory (disable ,bridge)))
      (in-theory (disable ,wfp)))))

(defun fn2-columns-wfp-write-facts (name fields column-fields)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom fields) nil
    (if (not (fn2-columns-numeric-fieldp (car fields)))
        (fn2-columns-wfp-write-facts name (cdr fields) column-fields)
      (let* ((f (caar fields)) (arrayp (fn2-columns-arrayp (car fields)))
           (wfp (fn2-columns-sym name "-WFP"))
           (read (if arrayp (fn2-columns-sym f "I") f))
           (write (fn2-columns-pre "UPDATE-" read))
           (length (fn2-columns-sym f "-LENGTH"))
           (call (if arrayp `(,write i v ,name) `(,write v ,name))))
      (append
       (if (equal f (fn2-columns-sym name "-ROWS")) nil
         `((defthm ,(fn2-columns-sym write "-PRESERVES-WFP")
             (implies (and (,wfp ,name)
                           ,@(if arrayp `((natp i) (< i (,length ,name))) nil))
                      (,wfp ,call))
             :hints (("Goal" :in-theory (enable ,write))))
           (defthm ,(fn2-columns-sym write "-ROWS")
             (equal (,(fn2-columns-sym name "-ROWS") ,call)
                    (,(fn2-columns-sym name "-ROWS") ,name)))))
       (if (and arrayp
                (cadr (member-eq :resizable (car fields)))
                (not (member-equal (car fields) column-fields)))
           `((defthm ,(fn2-columns-sym (fn2-columns-pre "RESIZE-" f) "-PRESERVES-WFP")
               (implies (,wfp ,name)
                        (,wfp (,(fn2-columns-pre "RESIZE-" f) n ,name)))
               :hints (("Goal" :in-theory (enable ,(fn2-columns-pre "RESIZE-" f)))))) nil)
       (fn2-columns-wfp-write-facts name (cdr fields) column-fields))))))

(defun fn2-columns-accessor-events (name cols index rows-index)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom cols) nil
    (let* ((read (fn2-columns-col-name name (caar cols)))
           (write (fn2-columns-col-name name
                    (fn2-columns-pre "SET-" (caar cols))))
           (raw (fn2-columns-sym read "$AI"))
           (raw-write (fn2-columns-pre "UPDATE-" raw))
           (rows (fn2-columns-sym name "-ROWS"))
           (wfp (fn2-columns-sym name "-WFP"))
           (p (fn2-columns-sym name "P"))
           (width (fn2-columns-width (cadar cols)))
           (guard `(and (natp i) (,wfp ,name) (< i (,rows ,name)))))
      (append
       `((defun ,read (i ,name)
           (declare (xargs :stobjs ,name :guard ,guard
                           :guard-hints (("Goal" :in-theory (disable ,wfp)))))
           (,raw i ,name))
         (defun ,write (i v ,name)
           (declare (xargs :stobjs ,name
                           :guard (and ,guard (unsigned-byte-p ,width v))
                           :guard-hints (("Goal" :in-theory (disable ,wfp)))))
           (,raw-write i v ,name))
         (defthm ,(fn2-columns-sym read "-NATP")
           (implies (and (,p ,name) ,guard) (natp (,read i ,name)))
           :rule-classes :type-prescription
           :hints (("Goal" :in-theory (disable ,wfp)
                          :use ((:instance ,(fn2-columns-sym read "$AP-NTH-NATP")
                                           (xs ,(fn2-columns-field-term index name)))))))
         (defthm ,(fn2-columns-sym read "-BOUND")
           (implies (and (,p ,name) ,guard) (< (,read i ,name) ,(expt 2 width)))
           :rule-classes :linear
           :hints (("Goal" :in-theory (disable ,wfp)
                          :use ((:instance ,(fn2-columns-sym read "$AP-NTH-BOUND")
                                           (xs ,(fn2-columns-field-term index name)))))))
         ; Guards simplify accessors to NTH before type inference.  These
         ; matching rules need no rewriting to relieve their hypotheses.
         (defthm ,(fn2-columns-sym read "-RAW-NTH-NATP")
           (implies (and (,p ,name) (,wfp ,name) (natp i)
                         (< i (nth ,rows-index ,name)))
                    (natp (nth i ,(fn2-columns-field-term index name))))
           :rule-classes :type-prescription
           :hints (("Goal" :in-theory (disable ,wfp ,p)
                          :use ((:instance ,(fn2-columns-sym read "$AP-NTH-NATP")
                                           (xs ,(fn2-columns-field-term index name)))))))
         (defthm ,(fn2-columns-sym read "-RAW-NTH-BOUND")
           (implies (and (,p ,name) (,wfp ,name) (natp i)
                         (< i (nth ,rows-index ,name)))
                    (< (nth i ,(fn2-columns-field-term index name)) ,(expt 2 width)))
           :rule-classes :linear
           :hints (("Goal" :in-theory (disable ,wfp ,p)
                          :use ((:instance ,(fn2-columns-sym read "$AP-NTH-BOUND")
                                           (xs ,(fn2-columns-field-term index name)))))))
         (defthm ,(fn2-columns-sym write "-PRESERVES-WFP")
           (implies ,guard (,wfp (,write i v ,name)))
           :hints (("Goal" :in-theory (disable ,wfp)
                          :use ((:instance ,(fn2-columns-sym raw-write "-PRESERVES-WFP"))))))
         (defthm ,(fn2-columns-sym write "-PRESERVES-TYPE")
           (implies (and (,p ,name) ,guard (unsigned-byte-p ,width v))
                    (,p (,write i v ,name)))
           :hints (("Goal" :in-theory (disable ,wfp)
                          :use ((:instance ,(fn2-columns-sym raw-write "-PRESERVES-TYPE"))))))
         (defthm ,(fn2-columns-sym write "-NTH")
           (equal (nth k (,write i v ,name)) (nth k (,raw-write i v ,name))))
         (defthm ,(fn2-columns-sym write "-ROWS")
           (equal (,rows (,write i v ,name)) (,rows ,name)))
         (in-theory (disable ,write))
         (assert-event (eq (symbol-class ',read (w state)) :common-lisp-compliant))
         (assert-event (eq (symbol-class ',write (w state)) :common-lisp-compliant)))
       (fn2-columns-accessor-events name (cdr cols) (+ 1 (nfix index)) rows-index)))))

(defun fn2-columns-row-terms (name cols)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom cols) nil
    (cons `(cons ',(caar cols) (,(fn2-columns-col-name name (caar cols)) i ,name))
          (fn2-columns-row-terms name (cdr cols)))))

(defun fn2-columns-specs (cols)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom cols) nil
    (cons (list (caar cols) (cadar cols)) (fn2-columns-specs (cdr cols)))))

(defun fn2-columns-events (name cols bound extras init-name)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((rows (fn2-columns-sym name "-ROWS"))
         (p (fn2-columns-sym name "P"))
         (wfp (fn2-columns-sym name "-WFP"))
         (init (or init-name (fn2-columns-sym name "-INIT")))
         (create (fn2-columns-pre "CREATE-" name))
         (row-view (fn2-columns-sym name "-ROW-VIEW"))
         (view-aux (fn2-columns-sym name "-VIEW-AUX"))
         (fields (append (fn2-columns-fields name cols)
                         `((,rows :type (integer 0 ,(- bound 1)) :initially 0))
                         (fn2-columns-extra-specs extras))))
    (fn2-declare (list :columns name)
      (list :columns (fn2-columns-specs cols)
            :column-reasons (fn2-columns-extra-reasons cols) :rows-bound bound
            :extra-fields (fn2-columns-extra-specs extras)
            :extra-field-reasons (fn2-columns-extra-reasons extras) :init-name init)
      nil
      `(; Plain numeric columns need only this DSL's proof theory. Raw extras
       ; retain incoming rules for their external nested-stobj constructors.
       ,@(if extras nil '((local (in-theory (theory 'fn2-columns-proof-theory)))))
       ,@(fn2-columns-enum-events cols)
       (defstobj ,name ,@fields :inline t)
       ,@(fn2-columns-all-array-facts fields)
       ,@(fn2-columns-record-events name fields)
       ,@(fn2-columns-all-field-facts name (take (len cols) fields) 0 t)
       ,@(fn2-columns-all-field-facts name (nthcdr (len cols) fields) (len cols) nil)
       (defthm ,(fn2-columns-sym create "-TYPE") (,p (,create))
         :hints (("Goal" :in-theory (enable ,p ,create))))
       (in-theory (disable ,p ,create))
       (defun ,wfp (,name)
         (declare (xargs :stobjs ,name))
         (and (natp (,rows ,name)) (< (,rows ,name) ,bound)
              ,@(fn2-columns-wfp-conjuncts name cols)))
       (defthm ,(fn2-columns-sym wfp "-FORWARD")
         (implies (,wfp ,name)
                  (and (natp (,rows ,name)) (< (,rows ,name) ,bound)))
         :rule-classes :forward-chaining
         :hints (("Goal" :in-theory (enable ,wfp))))
       ,@(fn2-columns-wfp-length-facts name cols 0)
       (defthm ,(fn2-columns-sym create "-WFP") (,wfp (,create))
         :hints (("Goal" :in-theory (enable ,create))))
       ,@(fn2-columns-shape-events name cols bound)
       (defun ,init (n ,name)
         (declare (xargs :stobjs ,name :guard (and (natp n) (< n ,bound))))
         (let* (,@(fn2-columns-resize-bindings name cols)
                (,name (,(fn2-columns-pre "UPDATE-" rows) n ,name)))
           ,name))
       (defthm ,(fn2-columns-sym init "-PRESERVES-TYPE")
         (implies (and (,p ,name) (natp n) (< n ,bound)) (,p (,init n ,name))))
       (defthm ,(fn2-columns-sym init "-WFP")
         (implies (and (natp n) (< n ,bound)) (,wfp (,init n ,name)))
         :hints (("Goal" :in-theory (enable ,wfp))))
       (defthm ,(fn2-columns-sym init "-NTH")
         (equal (nth k (,init n ,name))
                (nth k (let* (,@(fn2-columns-resize-bindings name cols)
                              (,name (,(fn2-columns-pre "UPDATE-" rows) n ,name)))
                         ,name))))
       (defthm ,(fn2-columns-sym init "-ROWS")
         (equal (,rows (,init n ,name)) n))
       ,@(fn2-columns-wfp-write-facts name fields (fn2-columns-fields name cols))
       ,@(fn2-columns-accessor-events name cols 0 (len cols))
       (defun-nx ,row-view (i ,name)
         (list ,@(fn2-columns-row-terms name cols)))
       (defun-nx ,view-aux (i n ,name)
         (declare (xargs :measure (nfix (- (nfix n) (nfix i)))))
         (if (or (not (natp i)) (not (natp n)) (>= i n)) nil
           (cons (,row-view i ,name) (,view-aux (+ 1 i) n ,name))))
       (defun-nx ,(fn2-columns-sym name "-VIEW") (,name)
         (,view-aux 0 (,rows ,name) ,name))
       (in-theory (disable ,wfp ,init ,@(fn2-columns-array-nth-runes fields)))
       (assert-event (eq (symbol-class ',init (w state)) :common-lisp-compliant))))))

(defun fn2-columns-keyword-listp (xs)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom xs) (null xs)
    (and (keywordp (car xs)) (fn2-columns-keyword-listp (cdr xs)))))

(defun fn2-columns-kindp (kind)
  (declare (xargs :guard t :verify-guards nil))
  (or (member-eq kind '(:u8 :u16 :u32 :u60 :u64 :bool))
      (and (true-listp kind) (equal (len kind) 3) (eq (car kind) :enum)
           (symbolp (cadr kind)) (cadr kind)
           (consp (caddr kind)) (fn2-columns-keyword-listp (caddr kind))
           (<= (len (caddr kind)) 256)
           (no-duplicatesp-equal (caddr kind)))))

(defun fn2-columns-declarationsp (cols)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom cols) (null cols)
    (and (true-listp (car cols))
         (or (and (equal (len (car cols)) 2) (not (eq (cadar cols) :u64)))
             (and (equal (len (car cols)) 4) (eq (caddar cols) :why)
                  (stringp (cadddr (car cols))) (< 0 (length (cadddr (car cols))))))
         (symbolp (caar cols)) (caar cols)
         (not (member-eq (caar cols) '(rows wfp init row-view view view-aux)))
         (fn2-columns-kindp (cadar cols))
         (fn2-columns-declarationsp (cdr cols)))))

(defun fn2-columns-field-names (fields)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom fields) nil
    (cons (if (consp (car fields)) (caar fields) (car fields))
          (fn2-columns-field-names (cdr fields)))))

(defmacro defcolumns (name columns &key (rows-bound '4294967296)
                          extra-fields init-name)
  (if (not (fn2-columns-extra-okp extra-fields))
      (er hard 'defcolumns "Unjustified unbounded or wide extra field in ~x0: non-finite numeric fields and numeric ranges reaching u64 require a nonempty :why string." name)
    (if (and (consp columns) (fn2-columns-declarationsp columns)
           (no-duplicatesp-equal (strip-cars columns))
           (integerp rows-bound) (< 0 rows-bound) (<= rows-bound (expt 2 60))
           (true-listp extra-fields)
           (no-duplicatesp-equal
            (fn2-columns-field-names (append (fn2-columns-fields name columns)
                               (list (list (fn2-columns-sym name "-ROWS")))
                               extra-fields)))
           (or (null init-name) (and (symbolp init-name) init-name)))
      (fn2-columns-events name columns rows-bound extra-fields init-name)
    (er hard 'defcolumns
        "Invalid defcolumns declaration for ~x0: use distinct column names, supported kinds, unique nonempty enums of at most 256 keywords, a positive rows bound at most 2^60, and a nonempty :why string for every :u64 column."
        name))))

; A fixed two-column representation: 120 bits by default, or 128 with u64.
; No combined bignum is constructed. Exhaustion leaves both limbs unchanged;
; callers retain the separate incarnation policy for any reusable identity.
(defmacro defwide-columns (name &key (limb-kind ':u60) why (rows-bound '4294967296))
  (if (not (member-eq limb-kind '(:u60 :u64)))
      (er hard 'defwide-columns "Pair limbs must be :u60 or justified :u64.")
    (let* ((hi (fn2-columns-sym name "-HI")) (lo (fn2-columns-sym name "-LO"))
           (sethi (fn2-columns-sym name "-SET-HI")) (setlo (fn2-columns-sym name "-SET-LO"))
           (compare (fn2-columns-sym name "-COMPARE")) (inc (fn2-columns-sym name "-INCREMENT"))
           (wfp (fn2-columns-sym name "-WFP")) (rows (fn2-columns-sym name "-ROWS"))
           (p (fn2-columns-sym name "P")) (limit (- (expt 2 (fn2-columns-width limb-kind)) 1))
           (guard `(and (,wfp ,name) (natp i) (< i (,rows ,name)))))
      `(progn
         (defcolumns ,name ((hi ,limb-kind ,@(and why `(:why ,why)))
                            (lo ,limb-kind ,@(and why `(:why ,why)))) :rows-bound ,rows-bound)
         (defun ,compare (i j ,name)
           (declare (xargs :stobjs ,name
                           :guard (and ,guard (natp j) (< j (,rows ,name)))))
           (let ((ahi (,hi i ,name)) (bhi (,hi j ,name))
                 (alo (,lo i ,name)) (blo (,lo j ,name)))
             (cond ((< ahi bhi) :lt) ((< bhi ahi) :gt)
                   ((< alo blo) :lt) ((< blo alo) :gt) (t :eq))))
         (defun ,inc (i ,name)
           (declare (xargs :stobjs ,name :guard ,guard))
           (let ((hi (,hi i ,name)) (lo (,lo i ,name)))
             (cond ((< lo ,limit)
                    (let ((,name (,setlo i (+ 1 lo) ,name))) (mv :ok ,name)))
                   ((< hi ,limit)
                    (let* ((,name (,sethi i (+ 1 hi) ,name)) (,name (,setlo i 0 ,name)))
                      (mv :ok ,name)))
                   (t (mv :exhausted ,name)))))
         (defthm ,(fn2-columns-sym inc "-TYPE")
           (implies (and (,p ,name) ,guard) (,p (mv-nth 1 (,inc i ,name)))))
         (defthm ,(fn2-columns-sym inc "-WFP")
           (implies ,guard (,wfp (mv-nth 1 (,inc i ,name)))))
         (defthm ,(fn2-columns-sym inc "-ROWS")
           (equal (nth 2 (mv-nth 1 (,inc i ,name))) (nth 2 ,name)))
         (assert-event (eq (symbol-class ',compare (w state)) :common-lisp-compliant))
         (assert-event (eq (symbol-class ',inc (w state)) :common-lisp-compliant))))))

; Freeze the generating book's theory, independent of the includer's world.
(make-event
 (let ((world (w state)))
   (value `(deftheory fn2-columns-proof-theory ',(current-theory :here)))))

; A small local instance exercises all kinds, enums and extra raw fields.
; No example storage or exported names are imposed on includers.
(local
 (defcolumns fn2-columns-example
   ((byte :u8) (short :u16) (word :u32) (gen :u60) (flag :bool)
    (phase (:enum fn2-columns-example-phase (:free :busy))))
   :rows-bound 32
   :extra-fields
   ((fn2-columns-example-bytes :type (array (unsigned-byte 8) (0))
                               :initially 0 :resizable t)
    (fn2-columns-example-count :type (integer 0 16) :initially 0)
    (fn2-columns-example-heads :initially 0 :type (array (unsigned-byte 32) (16)))
    (fn2-columns-example-metadata :initially nil :type t
     :why "Local DSL test: unrestricted metadata is never served.")
    (fn2-columns-example-objects :initially nil :type (array t (3))
     :why "Local DSL test: exercises object arrays, never served.")
    (fn2-columns-example-cache :type (hash-table equal) :initially nil
     :why "Local DSL test: exercises hash-table fields, never served.")
    (fn2-columns-example-bare :why "Local DSL test: exercises the default t field type, never served."))))

(local
 (defun fn2-columns-example-extra-reader (i fn2-columns-example)
   (declare (xargs :stobjs fn2-columns-example :guard (and (natp i) (< i 16))))
   (+ 1 (fn2-columns-example-headsi i fn2-columns-example))))

(local
 (defun fn2-columns-example-row-arithmetic (i fn2-columns-example)
   (declare (xargs :stobjs fn2-columns-example
                   :guard (and (fn2-columns-example-wfp fn2-columns-example)
                               (natp i) (< i (fn2-columns-example-rows fn2-columns-example)))))
   (+ (fn2-columns-example-rows fn2-columns-example)
      (fn2-columns-example-word i fn2-columns-example))))

(local
 (defun fn2-columns-example-test ()
   (declare (xargs :guard t))
   (with-local-stobj fn2-columns-example
     (mv-let (answer fn2-columns-example)
       (let* ((fn2-columns-example (fn2-columns-example-init 3 fn2-columns-example))
              (fn2-columns-example (fn2-columns-example-set-word 2 42 fn2-columns-example))
              (fn2-columns-example (fn2-columns-example-set-flag 1 1 fn2-columns-example)))
         (mv (and (equal (fn2-columns-example-word 2 fn2-columns-example) 42)
                  (equal (fn2-columns-example-flag 1 fn2-columns-example) 1)
                  (equal (fn2-columns-example-rows fn2-columns-example) 3))
             fn2-columns-example))
       answer))))

(local (assert-event (fn2-columns-example-test)))
(local (assert-event (equal (fn2-columns-example-phase-code->keyword 1) :busy)))
(local (assert-event (equal (fn2-columns-example-phase-keyword->code :free) 0)))
(local (assert-event (assoc-eq 'fn2-columns-example (reverse (fn2-decl-rows :columns (w state))))))
