; fn2 records/columns seed.  Declaration is recorded in the ACL2 world.
; Generated array storage is the executable representation.  The row/table
; views are non-executable, and resizing belongs only to the generated init.
(in-package "ACL2")
(include-book "operations")

(defthm fn2-columns-len-update-nth
  (implies (and (natp i) (< i (len xs)))
           (equal (len (update-nth i v xs)) (len xs))))



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
(local (in-theory (disable update-nth)))

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
        ((member-eq kind '(:u32 :link)) 32) ((eq kind :u60) 60)
        ((eq kind :u64) 64) ((eq kind :bool) 1) (t 8)))

(defun fn2-columns-fields (name cols)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom cols) nil
    (cons `(,(fn2-columns-sym (fn2-columns-col-name name (caar cols)) "$A")
            :type (array (unsigned-byte ,(fn2-columns-width (cadar cols))) (0))
            :initially ,(if (eq (cadar cols) :link) *fn2-none* 0) :resizable t)
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
              (cons `(defconst ,(fn2-columns-pre "*" (fn2-columns-sym ename "-COUNT*")) ,(len kws))
                    (fn2-columns-enum-constants ename kws 0))
              `((defun ,(fn2-columns-sym ename "-CODE->KEYWORD") (code)
                  (declare (xargs :guard (unsigned-byte-p 8 code)))
                  (case code ,@(fn2-columns-enum-cases kws 0 t) (otherwise nil)))
                (defun ,(fn2-columns-sym ename "-KEYWORD->CODE") (keyword)
                  (declare (xargs :guard t))
                  (case keyword ,@(fn2-columns-enum-cases kws 0 nil)
                    (otherwise nil))))))
         nil)
       (fn2-columns-enum-events (cdr cols))))))

; Guards carry enum cardinality; storage width alone admits unnamed tags.
(defun fn2-columns-fit (kind value)
  (declare (xargs :verify-guards nil))
  (if (consp kind)
      `(and (natp ,value) (< ,value ,(fn2-columns-pre "*" (fn2-columns-sym (cadr kind) "-COUNT*"))))
    `(unsigned-byte-p ,(fn2-columns-width kind) ,value)))
(defun fn2-columns-put-bindings (prefix object slot fields)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (cons `(,object (,(fn2-columns-col-name prefix (caar fields))
                    ,slot ,(cadar fields) ,object))
          (fn2-columns-put-bindings prefix object slot (cdr fields)))))
(defun fn2-columns-phase-formp (form constants)
  (declare (xargs :verify-guards nil))
  (or (member-eq form constants)
      (and (true-listp form) (equal (len form) 4) (eq (car form) 'if)
           (fn2-columns-phase-formp (caddr form) constants)
           (fn2-columns-phase-formp (cadddr form) constants))))
(defun fn2-columns-write-formp (name columns states fields)
  (declare (xargs :verify-guards nil))
  (let ((constants (strip-cars (strip-cdrs (fn2-columns-enum-constants
                                 (fn2-columns-sym name "-STATE") states 0)))))
    (and (doublet-listp fields) (no-duplicatesp-eq (strip-cars fields))
         (subsetp-eq (strip-cars fields) (strip-cars columns))
         (or (not states) (not (assoc-eq 'phase fields))
             (fn2-columns-phase-formp (cadr (assoc-eq 'phase fields)) constants)))))
(defun fn2-columns-put-expansion (name columns states slot fields)
  (declare (xargs :verify-guards nil))
  (if (fn2-columns-write-formp name columns states fields)
      `(let* ,(fn2-columns-put-bindings (fn2-columns-sym name "-SET") name slot fields) ,name)
    (er hard 'defcolumns "Invalid field list or cross-kind phase in ~x0 write: ~x1." name fields)))

; K7 shape/frame statements. Each instance names its actual call, hypotheses,
; result projections and observations; its leaf contracts discharge the proof.
(defun fn2-columns-preservation-facts (name call specs hyps hints)
  (declare (xargs :verify-guards nil))
  (if (atom specs) nil
    (let* ((spec (car specs)) (position (caddr spec))
           (result (if position `(mv-nth ,position ,call) call))
           (options (cdddr spec)) (frame (fn2-decl-get :frame options))
           (premise (if (member-eq :hyps options) (fn2-decl-get :hyps options) hyps))
           (fact-hints (if (member-eq :hints options) (fn2-decl-get :hints options) hints)))
      (cons `(defthm ,(fn2-columns-sym name (car spec))
               ,(if frame `(equal (,(cadr spec) ,result) (,(cadr spec) ,frame))
                  `(implies (and ,@premise) (,(cadr spec) ,result)))
               ,@(and fact-hints `(:hints ,fact-hints))
               ,@(and (member-eq :rule-classes options)
                      `(:rule-classes ,(fn2-decl-get :rule-classes options))))
            (fn2-columns-preservation-facts name call (cdr specs) hyps hints)))))
(defun fn2-columns-carrier-hyps (carriers)
  (declare (xargs :verify-guards nil))
  (if (atom carriers) nil
    (let* ((table (caar carriers)) (options (cddar carriers))
           (inv (or (fn2-decl-get :invariant options) (fn2-columns-sym table "-WFP"))))
      (append `((,(fn2-columns-sym table "P") ,table) (,inv ,table))
              (fn2-columns-carrier-hyps (cdr carriers))))))
(defun fn2-columns-carrier-specs (carriers)
  (declare (xargs :verify-guards nil))
  (if (atom carriers) nil
    (let* ((table (caar carriers)) (pos (cadar carriers)) (options (cddar carriers))
           (prefix (or (fn2-decl-get :prefix options) ""))
           (inv (or (fn2-decl-get :invariant options) (fn2-columns-sym table "-WFP")))
           (suffix (or (fn2-decl-get :suffix options) "-WFP")))
      (append `((,(concatenate 'string prefix "-TYPE") ,(fn2-columns-sym table "P") ,pos)
                (,(concatenate 'string prefix suffix) ,inv ,pos
                 :hints ,(fn2-decl-get :hints options)))
              (fn2-columns-carrier-specs (cdr carriers))))))
(defun fn2-columns-forward-facts (facts call)
  (declare (xargs :verify-guards nil))
  (if (atom facts) nil
    (cons (append (car facts) `(:rule-classes (:rewrite (:forward-chaining :trigger-terms (,call)))))
          (fn2-columns-forward-facts (cdr facts) call))))
(defun fn2-columns-preserves (table name args position hyps specs prefix rows disable hints wfp-type raw-rows carriers part forward)
  (declare (xargs :verify-guards nil))
  (let* ((p (fn2-columns-sym table "P")) (wfp (fn2-columns-sym table "-WFP"))
         (hyps (or hyps (and carriers (fn2-columns-carrier-hyps carriers)) `((,p ,table) (,wfp ,table))))
         (specs (or specs (and carriers (fn2-columns-carrier-specs carriers))
                    `((,(concatenate 'string prefix "-TYPE") ,p ,position)
                      (,(concatenate 'string prefix "-WFP") ,wfp ,position
                        ,@(and (not wfp-type) `(:hyps ((,wfp ,table)))))
                      ,@(and rows `((,(concatenate 'string prefix "-ROWS")
                                     ,(fn2-columns-sym table "-ROWS") ,position :frame ,table)))))))
    (let* ((call (cons name args)) (result (if position `(mv-nth ,position ,call) call))
           (facts (fn2-columns-preservation-facts name call specs hyps hints))
           (facts (if forward
                      (fn2-columns-forward-facts facts call) facts))
           (forms `(progn ,@facts
              ,@(and raw-rows
                `((defthm ,(fn2-columns-sym name (concatenate 'string prefix "-RAW-ROWS"))
                    (equal (nth ,(fn2-columns-pre "*" (fn2-columns-sym table "-ROWS*")) ,result)
                           (nth ,(fn2-columns-pre "*" (fn2-columns-sym table "-ROWS*")) ,table))
                    :hints (("Goal" :use ,(fn2-columns-sym name (concatenate 'string prefix "-ROWS")))))))
              ,@(and disable `((in-theory (disable ,name)))))))
      (if part (nth part forms) forms))))
(defun fn2-columns-preserves-macro (table)
  (declare (xargs :verify-guards nil))
  `(defmacro ,(fn2-columns-sym table "-PRESERVES")
     (name args &key position hyps specs (prefix '"-PRESERVES")
           (rows 't) (disable 't) hints (wfp-type 't) raw-rows carriers part forward)
     (fn2-columns-preserves ',table name args position hyps specs prefix rows disable hints wfp-type raw-rows carriers part forward)))

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

; Every representation escape documents why ordinary columns do not suffice.
(defun fn2-columns-unjustified-extra (fields)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (let ((why (cadr (member-eq :why (cdar fields)))))
      (if (and (stringp why) (< 0 (length why)))
          (fn2-columns-unjustified-extra (cdr fields)) (list (caar fields))))))
(defun fn2-columns-extra-okp (fields)
  (declare (xargs :verify-guards nil))
  (not (fn2-columns-unjustified-extra fields)))

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

(defun fn2-columns-local-facts (events)
  (declare (xargs :verify-guards nil))
  (if (atom events) nil
    (cons (if (eq (caar events) 'defthm) (list 'local (car events)) (car events))
          (fn2-columns-local-facts (cdr events)))))

(defun fn2-columns-all-array-facts (fields)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom fields) nil
    (append (if (and (fn2-columns-arrayp (car fields))
                     (fn2-columns-numeric-fieldp (car fields)))
                (fn2-columns-array-facts (car fields)) nil)
            (fn2-columns-all-array-facts (cdr fields)))))

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

(defun fn2-columns-init-nth (name cols index)
  (declare (xargs :verify-guards nil))
  (if (atom cols) `(if (equal (nfix k) ,index) n (nth k ,name))
    `(if (equal (nfix k) ,index) (resize-list (nth ,index ,name) n ,(if (eq (cadar cols) :link) *fn2-none* 0))
       ,(fn2-columns-init-nth name (cdr cols) (+ 1 (nfix index))))))

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
           (guard `(and (natp i) (,wfp ,name) (< i (,rows ,name))))
           (fit (fn2-columns-fit (cadar cols) 'v)))
      (append
       `((defun ,read (i ,name)
           (declare (xargs :stobjs ,name :guard ,guard
                           :guard-hints (("Goal" :in-theory (disable ,wfp)))))
           (,raw i ,name))
         (defun ,write (i v ,name)
           (declare (xargs :stobjs ,name
                           :guard (and ,guard ,fit)
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
           (equal (nth k (,write i v ,name))
                  (if (equal (nfix k) ,index)
                      (update-nth i v (nth ,index ,name)) (nth k ,name))))
         (defthm ,(fn2-columns-sym write "-ROWS")
           (equal (,rows (,write i v ,name)) (,rows ,name)))
         (in-theory (disable ,write)))
       (fn2-columns-accessor-events name (cdr cols) (+ 1 (nfix index)) rows-index)))))

(defun fn2-columns-accessor-names (name cols)
  (declare (xargs :verify-guards nil))
  (if (atom cols) nil
    (list* (fn2-columns-col-name name (caar cols))
           (fn2-columns-col-name name (fn2-columns-pre "SET-" (caar cols)))
           (fn2-columns-accessor-names name (cdr cols)))))

(defun fn2-columns-row-terms (name cols)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom cols) nil
    (cons `(cons ',(caar cols) (,(fn2-columns-col-name name (caar cols)) i ,name))
          (fn2-columns-row-terms name (cdr cols)))))

(defun fn2-columns-specs (cols)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom cols) nil
    (cons (list (caar cols) (cadar cols)) (fn2-columns-specs (cdr cols)))))

(defthm fn2-columns-countdown
  (implies (not (zp left)) (o< (nfix (- left 1)) (nfix left))) :rule-classes nil)
(defthm fn2-columns-count-op (o-p (nfix left)) :rule-classes nil)
; Test/reference specialization: the same column recipe supplies list snapshots
; and congruent copies. No extra reference carrier is allocated by declaration.
(defun fn2-columns-reference-fields (fields)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (cons (cons (fn2-columns-sym (caar fields) "-REF") (cdar fields))
          (fn2-columns-reference-fields (cdr fields)))))
(defun fn2-columns-traversals (name ref fields modes)
  (declare (xargs :verify-guards nil :measure (+ (* 4 (acl2-count fields)) (acl2-count modes))))
  (cond ((atom fields) nil)
        ((atom modes) (fn2-columns-traversals name ref (cdr fields) '(:copy :diff :snapshot)))
        (t (let* ((field (caar fields)) (mode (car modes))
                  (reader (fn2-columns-sym field "I"))
                  (writer (fn2-columns-pre "UPDATE-" reader))
                  (fn (fn2-columns-col-name field (if (eq mode :snapshot) :logical-snapshot mode)))
                  (snapshot (eq mode :snapshot)) (copy (eq mode :copy))
                  (args (if snapshot (list name) (list name ref)))
                  (again `(,fn (- left 1) (+ 1 (nfix i)) ,@args))
                  (body (cond (snapshot `(cons (,reader i ,name) ,again))
                              (copy `(let ((,ref (,writer i (,reader i ,name) ,ref))) ,again))
                              (t `(if (equal (,reader i ,name) (,reader i ,ref)) ,again
                                    (list ',field i (,reader i ,name) (,reader i ,ref)))))))
             (append
              (and (fn2-columns-arrayp (car fields))
                (list
                 (fn2-operation-events (list :columns name) fn (if snapshot name ref)
                   (if snapshot '(left i) (list 'left 'i name)) :infer nil :reference
                   `(declare (xargs :stobjs ,args :verify-guards nil :measure (nfix left)
                         :hints (("Goal" :in-theory (theory 'minimal-theory)
                            :use ((:instance fn2-columns-countdown) (:instance fn2-columns-count-op))))))
                   `((if (zp left) ,(and copy ref) ,body)) `((in-theory (disable ,fn))) nil)))
              (fn2-columns-traversals name ref fields (cdr modes)))))))
(defun fn2-columns-copy-bindings (name ref fields)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (let* ((field (caar fields)) (arrayp (fn2-columns-arrayp (car fields)))
           (length (fn2-columns-sym field "-LENGTH")))
      (append
       (and arrayp (cadr (member-eq :resizable (cdar fields)))
            `((,ref (,(fn2-columns-pre "RESIZE-" field) (,length ,name) ,ref))))
       `((,ref ,(if arrayp `(,(fn2-columns-sym field "-COPY") (,length ,name) 0 ,name ,ref)
                   `(,(fn2-columns-pre "UPDATE-" field) (,field ,name) ,ref))))
       (fn2-columns-copy-bindings name ref (cdr fields))))))
(defun fn2-columns-diff-terms (name ref fields skip)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (let* ((field (caar fields)) (arrayp (fn2-columns-arrayp (car fields)))
           (length (fn2-columns-sym field "-LENGTH")))
      (cons
       (if arrayp
           `(if (equal (,length ,name) (,length ,ref))
                ,(and (not (member-eq field skip))
                      `(,(fn2-columns-sym field "-DIFF") (,length ,name) 0 ,name ,ref))
              (list ',length))
         `(and (not (equal (,field ,name) (,field ,ref))) (list ',field)))
       (fn2-columns-diff-terms name ref (cdr fields) skip)))))
(defun fn2-columns-snapshot-calls (name fields)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (cons (if (fn2-columns-arrayp (car fields))
              `(,(fn2-columns-sym (caar fields) "-LOGICAL-SNAPSHOT")
                 (,(fn2-columns-sym (caar fields) "-LENGTH") ,name) 0 ,name)
            `(,(caar fields) ,name))
          (fn2-columns-snapshot-calls name (cdr fields)))))
; A flat numeric projection for allocation-free reference consumers. The
; consumer chooses a prefix, omitted scalars, and a proved word width.
(defun fn2-columns-projection-cases (name readers i rowp)
  (declare (xargs :verify-guards nil))
  (if (atom readers) nil
    (cons `(,i (,(car readers) ,@(if rowp '(slot) nil) ,name))
          (fn2-columns-projection-cases name (cdr readers) (+ 1 i) rowp))))
(defun fn2-columns-projection-readers (name cols)
  (declare (xargs :verify-guards nil))
  (if (atom cols) nil
    (cons (fn2-columns-col-name name (caar cols))
          (fn2-columns-projection-readers name (cdr cols)))))
(defun fn2-columns-projection-scalars (fields skip)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (if (or (fn2-columns-arrayp (car fields)) (member-eq (caar fields) skip))
        (fn2-columns-projection-scalars (cdr fields) skip)
      (cons (caar fields) (fn2-columns-projection-scalars (cdr fields) skip)))))
(defun fn2-columns-projection-events (name prefix cols extras skip width)
  (declare (xargs :verify-guards nil))
  (let* ((readers (fn2-columns-projection-readers name cols))
         (rows (fn2-columns-sym name "-ROWS"))
         (scalars (cons rows (fn2-columns-projection-scalars extras skip)))
         (p (fn2-columns-sym name "P")) (wfp (fn2-columns-sym name "-WFP"))
         (column-word (fn2-columns-sym prefix "-OP-COLUMN-WORD"))
         (scalar-word (fn2-columns-sym prefix "-OP-SCALAR-WORD"))
         (bound-suffix (concatenate 'string "-U" (coerce (explode-atom width 10) 'string)))
         (guard `(and (,wfp ,name) (natp slot) (< slot (,rows ,name)))))
    `((defconst ,(fn2-columns-pre "*" (fn2-columns-sym prefix "-NCOLS*")) ,(len readers))
       (defconst ,(fn2-columns-pre "*" (fn2-columns-sym prefix "-NSCALARS*")) ,(len scalars))
       ,(fn2-operation-events (list :columns name) column-word name '(column slot)
          :infer nil :reference `(declare (xargs :stobjs ,name :guard ,guard))
          `((case column ,@(fn2-columns-projection-cases name readers 0 t) (otherwise 0)))
          `((defthm ,(fn2-columns-sym column-word bound-suffix)
              (implies (and (,p ,name) (,wfp ,name) (natp slot) (< slot (,rows ,name)))
                       (unsigned-byte-p ,width (,column-word column slot ,name))))) nil)
       ,(fn2-operation-events (list :columns name) scalar-word name '(i)
          :infer nil :reference `(declare (xargs :stobjs ,name))
          `((case i ,@(fn2-columns-projection-cases name scalars 0 nil) (otherwise 0)))
          `((defthm ,(fn2-columns-sym scalar-word bound-suffix)
              (implies (,p ,name) (unsigned-byte-p ,width (,scalar-word i ,name))))) nil)
       (in-theory (disable ,column-word ,scalar-word)))))

(defun fn2-columns-reference-events (name ref fields)
  (declare (xargs :verify-guards nil))
  (append (list (fn2-declare (list :operation-set ref) '(:role :reference)
                   (list (list :declaration (list :columns name))
                         (list :function (fn2-columns-sym name "-LOGICAL-SNAPSHOT") :at :reference))
                   `((defstobj ,ref ,@(fn2-columns-reference-fields fields) :congruent-to ,name))))
    (fn2-columns-traversals name ref fields '(:copy :diff :snapshot))
    (list (fn2-operation-events (list :columns name) (fn2-columns-sym name "-LOGICAL-SNAPSHOT")
      name nil :infer nil :reference `(declare (xargs :stobjs ,name :verify-guards nil))
      `((list ,@(fn2-columns-snapshot-calls name fields))) nil nil))))

(defun fn2-columns-record-readers (name cols index)
  (declare (xargs :verify-guards nil))
  (if (atom cols) nil
    (cons `(defun ,(fn2-columns-col-name (fn2-columns-sym name "-RECORD") (caar cols)) (record)
             (declare (xargs :guard t)) (nth ,index (true-list-fix record)))
          (fn2-columns-record-readers name (cdr cols) (+ 1 (nfix index))))))

(defun fn2-columns-events (name cols bound extras init-name put-policy)
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
            :extra-field-reasons (fn2-columns-extra-reasons extras) :init-name init :put-policy put-policy)
      nil
      `(; Plain numeric columns need only this DSL's proof theory. Raw extras
       ; retain incoming rules for their external nested-stobj constructors.
       ,@(if extras nil '((local (in-theory (theory 'fn2-columns-proof-theory)))))
       (local (in-theory (disable update-nth)))
       ,@(fn2-columns-enum-events cols)
       (defstobj ,name ,@fields :inline t)
       ,@(fn2-columns-local-facts (fn2-columns-all-array-facts fields))
       ,@(fn2-columns-record-events name fields)
       ,@(fn2-columns-local-facts (fn2-columns-all-field-facts name (take (len cols) fields) 0 t))
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
                ,(fn2-columns-init-nth name cols 0)))
       (defthm ,(fn2-columns-sym init "-ROWS")
         (equal (,rows (,init n ,name)) n))
       ,@(fn2-columns-wfp-write-facts name fields (fn2-columns-fields name cols))
       ,@(fn2-columns-accessor-events name cols 0 (len cols))
       (defmacro ,(fn2-columns-sym name "-PUT") (slot &rest fields)
         (fn2-columns-put-expansion ',name ',cols ',put-policy slot fields))
       ,(fn2-columns-preserves-macro name)
       (defmacro ,(fn2-columns-sym name "-COPY") (source &optional target)
         (if target `(let* ,(fn2-columns-copy-bindings source target ',fields) ,target)
           (list ',(fn2-columns-sym name "-LOGICAL-SNAPSHOT") source)))
       (defmacro ,(fn2-columns-sym name "-DIFF") (source target &key skip)
         (cons 'or (fn2-columns-diff-terms source target ',fields skip)))
       (defun ,(fn2-columns-sym name "-ROW-SNAPSHOT") (i ,name)
         (declare (xargs :stobjs ,name :guard (and (,wfp ,name) (natp i) (< i (,rows ,name)))) (ignorable i ,name))
         (list ,@(strip-cars (strip-cdrs (strip-cdrs (fn2-columns-row-terms name cols))))))
       ,@(fn2-columns-record-readers name cols 0)
       (defun-nx ,row-view (i ,name)
         (declare (ignorable i ,name))
         (list ,@(fn2-columns-row-terms name cols)))
       (defun-nx ,view-aux (i n ,name)
         (declare (xargs :measure (nfix (- (nfix n) (nfix i)))))
         (if (or (not (natp i)) (not (natp n)) (>= i n)) nil
           (cons (,row-view i ,name) (,view-aux (+ 1 i) n ,name))))
       (defun-nx ,(fn2-columns-sym name "-VIEW") (,name)
         (,view-aux 0 (,rows ,name) ,name))
       (in-theory (disable ,wfp ,init))
       (assert-event (fn2-assert-compliant-p
                      '(,init ,@(fn2-columns-accessor-names name cols)) (w state)))))))

(defun fn2-columns-keyword-listp (xs)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom xs) (null xs)
    (and (keywordp (car xs)) (fn2-columns-keyword-listp (cdr xs)))))

(defun fn2-columns-kindp (kind)
  (declare (xargs :guard t :verify-guards nil))
  (or (member-eq kind '(:u8 :u16 :u32 :u60 :u64 :bool :link))
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

(defun fn2-columns-constants (form world)
  (declare (xargs :verify-guards nil))
  (if (consp form)
      (cons (fn2-columns-constants (car form) world) (fn2-columns-constants (cdr form) world))
    (let ((value (and (symbolp form) (getpropc form 'const nil world))))
      (if value (unquote value) form))))

(defmacro defcolumns (name columns &key (rows-bound '4294967296)
                          extra-fields init-name put-policy)
  (if (not (fn2-columns-extra-okp extra-fields))
      `(make-event (er soft 'defcolumns "Extra field ~x0 of ~x1 requires a nonempty :why."
                      ',(car (fn2-columns-unjustified-extra extra-fields)) ',name))
    (if (and (true-listp columns) (fn2-columns-declarationsp columns)
           (no-duplicatesp-equal (strip-cars columns))
           (integerp rows-bound) (< 0 rows-bound) (<= rows-bound (expt 2 60))
           (true-listp extra-fields)
           (no-duplicatesp-equal
            (fn2-columns-field-names (append (fn2-columns-fields name columns)
                               (list (list (fn2-columns-sym name "-ROWS")))
                               extra-fields)))
           (or (null init-name) (and (symbolp init-name) init-name)))
      `(make-event (value (fn2-columns-events ',name ',columns ,rows-bound
        (fn2-columns-constants ',extra-fields (w state)) ',init-name ',put-policy)))
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
         (fn2-defoperation (:columns ,name) :declaration (order)
         (defun ,compare (i j ,name)
           (declare (xargs :stobjs ,name
                           :guard (and ,guard (natp j) (< j (,rows ,name)))))
           (let ((ahi (,hi i ,name)) (bhi (,hi j ,name))
                 (alo (,lo i ,name)) (blo (,lo j ,name)))
             (cond ((< ahi bhi) :lt) ((< bhi ahi) :gt)
                   ((< alo blo) :lt) ((< blo alo) :gt) (t :eq)))))
         (fn2-defoperation (:columns ,name) :declaration (code ,name)
         (defun ,inc (i ,name)
           (declare (xargs :stobjs ,name :guard ,guard))
           (let ((hi (,hi i ,name)) (lo (,lo i ,name)))
             (cond ((< lo ,limit)
                    (let ((,name (,setlo i (+ 1 lo) ,name))) (mv :ok ,name)))
                   ((< hi ,limit)
                    (let* ((,name (,sethi i (+ 1 hi) ,name)) (,name (,setlo i 0 ,name)))
                      (mv :ok ,name)))
                   (t (mv :exhausted ,name))))))
         (defthm ,(fn2-columns-sym inc "-TYPE")
           (implies (and (,p ,name) ,guard) (,p (mv-nth 1 (,inc i ,name)))))
         (defthm ,(fn2-columns-sym inc "-WFP")
           (implies ,guard (,wfp (mv-nth 1 (,inc i ,name)))))
         (defthm ,(fn2-columns-sym inc "-ROWS")
           (equal (nth 2 (mv-nth 1 (,inc i ,name))) (nth 2 ,name)))
         (assert-event (fn2-assert-compliant-p '(,compare ,inc) (w state)))))))

; Freeze the generating book's theory, independent of the includer's world.
(make-event
 (let ((world (w state)))
   (value `(deftheory fn2-columns-proof-theory ',(current-theory :here)))))
