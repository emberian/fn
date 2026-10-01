; fn prototype (lane proto-adt, 2026-09-27): `defadt', a sequence-of-products
; ADT declared at the ADT level and backed by typed columns and one octet
; pool.  NOT on a served path; no host calls it.
;
;   (defadt NAME (FIELD KIND) ...)
;
; KIND is :u8 :u32 :u64 :bool :octets, (:nat B), or (:enum OBJ ...).
; The logical value of the abstract stobj NAME is a true list of records,
; each the true list of its field values (books/proto/adt-lib.lisp).  The
; macro emits, per instance:
;   the foundation NAME$c: one typed resizable array per scalar field, an
;     (offset, length) pair of arrays per :octets field, the pool, count, fill;
;   the executable operations over it (count, get-FIELD, append, set-FIELD);
;   the logical operations (len, nth, append, update-nth of a field);
;   the correspondence NAME$corr = (adt-corr '<schema> c a);
;   BRIDGES, each an equality between an instance function and the library
;     operation at the constant schema: array recognizers and the two pool
;     loops by :functional-instance of the library's constrained shapes, the
;     rest by unfolding (theory adt-instance-unfold);
;   the defabsstobj obligations, obtained from ACL2 itself
;     (defabsstobj-missing-events) and each proved by one uniform hint that
;     opens the instance's logical definitions and its bridges: the library's
;     adt-corr-* theorems, universally quantified over the schema, close them;
;   the defabsstobj event, and the "-is-" theorems stating each export's
;     logical meaning.
; No step is written per type.

(in-package "ACL2")
(include-book "adt-lib")

(program)

; A generated name lives in the package of the symbol it is derived from
; (as defstobj's own CREATE-/UPDATE-/RESIZE- names do), so an instance in
; another package gets its names there and two instances of one spelling
; in two packages never collide; a string base has no package of its own
; and names the generator's (deputy-1 2026-10-01, after Codex t10).
(defun adt-sym (base suffix)
  (intern-in-package-of-symbol
   (concatenate 'string (if (stringp base) base (symbol-name base)) suffix)
   (if (symbolp base) base 'adt-sym)))

(defun adt-sym3 (a mid b)
  (intern-in-package-of-symbol
   (concatenate 'string (symbol-name a) mid (symbol-name b)) a))

; PREFIX before the symbol's name, in the symbol's package.
(defun adt-sym-pre (prefix sym)
  (intern-in-package-of-symbol (concatenate 'string prefix (symbol-name sym)) sym))

(defun adt-norm-kind (k)
  (if (keywordp k) (list k) k))

(defun adt-norm-fields (fields)
  (if (endp fields)
      nil
    (cons (list (car (car fields)) (adt-norm-kind (cadr (car fields))))
          (adt-norm-fields (cdr fields)))))

(defun adt-ctype-decl (ct)
  (case (car ct)
    (:ub `(unsigned-byte ,(cadr ct)))
    (:range `(integer 0 ,(cadr ct)))
    (otherwise '(integer 0 *))))

; The columns: (colname ctype) in layout order.
(defun adt-columns (name fields)
  (if (endp fields)
      nil
    (let* ((f (car (car fields))) (k (cadr (car fields))))
      (if (eq (car k) :octets)
          (list* (list (adt-sym3 name "$C-" (adt-sym f "-OFF")) '(:nat))
                 (list (adt-sym3 name "$C-" (adt-sym f "-LEN")) '(:nat))
                 (adt-columns name (cdr fields)))
        (cons (list (adt-sym3 name "$C-" f) (adt-ctype k))
              (adt-columns name (cdr fields)))))))

(defun adt-stobj-fields (cols)
  (if (endp cols)
      nil
    (cons `(,(car (car cols)) :type (array ,(adt-ctype-decl (cadr (car cols))) (0))
            :initially 0 :resizable t)
          (adt-stobj-fields (cdr cols)))))

; Per column: its put function, recognizer bridge.
(defun adt-col-events (name cols ci)
  (if (endp cols)
      nil
    (let* ((cname (car (car cols)))
           (ct (cadr (car cols)))
           (st (adt-sym name "$C"))
           (put (adt-sym cname "-PUT"))
           (len (adt-sym cname "-LENGTH"))
           (rsz (adt-sym-pre "RESIZE-" cname))
           (upd (adt-sym-pre "UPDATE-" (adt-sym cname "I")))
           (recog (adt-sym cname "P")))
      (append
       `((defthm ,(adt-sym recog "-IS")
           (equal (,recog x) (adt-all-elt-p ',ct x))
           :hints (("Goal" :in-theory (enable adt-elt-p)
                    :use ((:functional-instance adt-g-colp-is-all-elt-p
                                                (adt-g-ct (lambda () ',ct))
                                                (adt-g-colp ,recog))))))
         (defun ,put (n x ,st)
           (declare (xargs :stobjs ,st
                           :guard (and (natp n) (adt-elt-p ',ct x))
                           :guard-hints (("Goal" :in-theory (enable ,(adt-sym name "$CP") adt-elt-p)))))
           (let ((,st (if (< n (,len ,st)) ,st (,rsz (* 2 (+ 1 n)) ,st))))
             (,upd n x ,st)))
         (defthm ,(adt-sym put "-BRIDGE")
           (equal (,put n x c) (update-nth ,ci (adt-col-put (nth ,ci c) n x) c))
           :hints (("Goal" :in-theory (enable ,put adt-col-put adt-col-room))))
         (in-theory (disable ,put)))
       (adt-col-events name (cdr cols) (+ 1 ci))))))

(defun adt-recog-bridges (cols)
  (if (endp cols) nil
    (cons (adt-sym (adt-sym (car (car cols)) "P") "-IS") (adt-recog-bridges (cdr cols)))))

; Per field: put-field, get-field, get-okp, set, their logical twins.
(defun adt-field-events (name fields j ci p)
  (if (endp fields)
      nil
    (let* ((f (car (car fields)))
           (k (cadr (car fields)))
           (st (adt-sym name "$C"))
           (octp (eq (car k) :octets))
           (w (if octp 2 1))
           (cbase (adt-sym3 name "$C-" f))
           (putf (adt-sym3 name "$C-PUT-FIELD-" f))
           (getf (adt-sym3 name "$C-GET-" f))
           (okp (adt-sym getf "-OKP"))
           (setf (adt-sym3 name "$C-SET-" f))
           (schema (adt-sym3 '* (symbol-name name) '-schema*))
           (ghints `(("Goal" :in-theory (e/d (,(adt-sym name "$CP") adt-elt-p)
                                              (,(adt-sym name "$CP-IS-SHAPE")))))))
      (append
       (if octp
           (let ((off (adt-sym cbase "-OFF")) (lenc (adt-sym cbase "-LEN")))
             `((defun ,putf (n v ,st)
                 (declare (xargs :stobjs ,st
                                 :guard (and (natp n) (adt-octetsp v))
                                 :guard-hints ,ghints))
                 (let* ((o (,(adt-sym name "$C-FILL") ,st))
                        (,st (,(adt-sym name "$C-POOL-PUSH") v ,st))
                        (,st (,(adt-sym off "-PUT") n o ,st)))
                   (,(adt-sym lenc "-PUT") n (len v) ,st)))
               (defun ,okp (i ,st)
                 (declare (xargs :stobjs ,st :guard (natp i) :guard-hints ,ghints))
                 (and (< i (,(adt-sym off "-LENGTH") ,st))
                      (< i (,(adt-sym lenc "-LENGTH") ,st))
                      (<= (+ (,(adt-sym off "I") i ,st) (,(adt-sym lenc "I") i ,st))
                          (,(adt-sym name "$C-POOL-LENGTH") ,st))))
               (defun ,getf (i ,st)
                 (declare (xargs :stobjs ,st :guard (and (natp i) (,okp i ,st))
                                 :guard-hints ,ghints))
                 (,(adt-sym name "$C-POOLR") (,(adt-sym off "I") i ,st)
                  (,(adt-sym lenc "I") i ,st) nil ,st))))
         (let ((put (adt-sym cbase "-PUT")))
           `((defun ,putf (n v ,st)
               (declare (xargs :stobjs ,st
                               :guard (and (natp n) (adt-val-okp ',k v))
                               :guard-hints (("Goal" :in-theory (e/d (,(adt-sym name "$CP")
                                                                        adt-elt-p adt-val-okp
                                                                        adt-enc adt-ctype)
                                                                       (,(adt-sym name "$CP-IS-SHAPE")))))))
               (,put n (adt-enc ',k v) ,st))
             (defun ,okp (i ,st)
               (declare (xargs :stobjs ,st :guard (natp i)))
               (< i (,(adt-sym cbase "-LENGTH") ,st)))
             (defun ,getf (i ,st)
               (declare (xargs :stobjs ,st :guard (and (natp i) (,okp i ,st))))
               (adt-dec ',k (,(adt-sym cbase "I") i ,st))))))
       `((defthm ,(adt-sym putf "-BRIDGE")
           (equal (,putf n v c) (adt-put-field ',k ,ci ,p n v c))
           :hints (("Goal" :in-theory (enable ,putf adt-put-field))))
         (defthm ,(adt-sym okp "-BRIDGE")
           (equal (,okp i c) (adt-get-okp ,schema ,j i c))
           :hints (("Goal" :in-theory (enable ,okp adt-instance-unfold))))
         (defthm ,(adt-sym getf "-BRIDGE")
           (equal (,getf i c) (adt-get-c ,schema ,j i c))
           :hints (("Goal" :in-theory (enable ,getf adt-instance-unfold))))
         (defun ,setf (i v ,st)
           (declare (xargs :stobjs ,st
                           :guard (and (natp i) (adt-val-okp ',k v))
                           :guard-hints (("Goal" :in-theory (enable adt-val-okp)))))
           (,putf i v ,st))
         (defthm ,(adt-sym setf "-BRIDGE")
           (equal (,setf i v c) (adt-set-c ,schema ,j i v c))
           :hints (("Goal" :in-theory (enable ,setf adt-instance-unfold))))
         (in-theory (disable ,putf ,okp ,getf ,setf)))
       (adt-field-events name (cdr fields) (+ 1 j) (+ w ci) p)))))

; The logical twins of a sequence's field accessors (plain defadt only).
(defun adt-field-logic-events (name fields j)
  (if (endp fields)
      nil
    (let* ((f (car (car fields)))
           (k (cadr (car fields)))
           (agetf (adt-sym3 name "$A-GET-" f))
           (asetf (adt-sym3 name "$A-SET-" f))
           (ap (adt-sym name "$AP")))
      (append
       `((defun ,agetf (i ,(adt-sym name "$A"))
           (declare (xargs :guard (and (,ap ,(adt-sym name "$A")) (natp i)
                                       (< i (,(adt-sym name "$A-COUNT") ,(adt-sym name "$A"))))))
           (nth ,j (nth i ,(adt-sym name "$A"))))
         (defun ,asetf (i v ,(adt-sym name "$A"))
           (declare (xargs :guard (and (,ap ,(adt-sym name "$A")) (natp i)
                                       (< i (,(adt-sym name "$A-COUNT") ,(adt-sym name "$A")))
                                       (adt-val-okp ',k v))))
           (adt-set-a ,j i v ,(adt-sym name "$A"))))
       (adt-field-logic-events name (cdr fields) (+ 1 j))))))

(defun adt-append-body (name fields recv st)
  (if (endp fields)
      nil
    (cons `(,st (,(adt-sym3 name "$C-PUT-FIELD-" (car (car fields))) n (car ,recv) ,st))
          (adt-append-body name (cdr fields) `(cdr ,recv) st))))

(defun adt-exports (name fields)
  (if (endp fields)
      nil
    (let ((f (car (car fields))))
      (list* `(,(adt-sym3 name "-GET-" f) :logic ,(adt-sym3 name "$A-GET-" f)
               :exec ,(adt-sym3 name "$C-GET-" f))
             `(,(adt-sym3 name "-SET-" f) :logic ,(adt-sym3 name "$A-SET-" f)
               :exec ,(adt-sym3 name "$C-SET-" f) :protect t)
             (adt-exports name (cdr fields))))))

(defun adt-logic-names (name fields)
  (if (endp fields)
      nil
    (list* (adt-sym3 name "$A-GET-" (car (car fields)))
           (adt-sym3 name "$A-SET-" (car (car fields)))
           (adt-logic-names name (cdr fields)))))

(defun adt-is-thms (name fields j)
  (if (endp fields)
      nil
    (let ((f (car (car fields))))
      (list* `(defthm ,(adt-sym3 name "-GET-" (adt-sym f "-IS-NTH"))
                (equal (,(adt-sym3 name "-GET-" f) i ,name) (nth ,j (nth i ,name)))
                :hints (("Goal" :in-theory (enable ,(adt-sym3 name "$A-GET-" f)))))
             `(defthm ,(adt-sym3 name "-SET-" (adt-sym f "-IS-UPDATE-NTH"))
                (equal (,(adt-sym3 name "-SET-" f) i v ,name)
                       (update-nth i (update-nth ,j v (nth i ,name)) ,name))
                :hints (("Goal" :in-theory (enable ,(adt-sym3 name "$A-SET-" f) adt-set-a))))
             (adt-is-thms name (cdr fields) (+ 1 j))))))

(defun adt-schema-of (fields)
  (if (endp fields) nil (cons (cadr (car fields)) (adt-schema-of (cdr fields)))))

(defun adt-obligation-thms (missing hints wrld)
  (if (endp missing)
      nil
    (cons `(defthm ,(car (car missing))
             ,(untranslate (cadr (car missing)) t wrld)
             :rule-classes nil
             :hints ,hints)
          (adt-obligation-thms (cdr missing) hints wrld))))

; The foundation and its executables, shared by `defadt' and `defadt-keyed'
; (books/proto/adt-keyed.lisp): FIELDS are the normalized physical fields,
; SCHEMA-CONST names the physical schema, EXTRA are further defstobj fields
; above the fill, N the stobj's field count.
(defun adt-foundation-events (name fields schema-const extra n)
  (let* ((schema (adt-schema-of fields))
         (cols (adt-columns name fields))
         (p (len cols))
         (st (adt-sym name "$C"))
         (pool (adt-sym name "$C-POOL"))
         (poolw (adt-sym name "$C-POOLW"))
         (poolr (adt-sym name "$C-POOLR"))
         (push (adt-sym name "$C-POOL-PUSH"))
         (cp (adt-sym name "$CP")))
    `((defconst ,schema-const ',schema)
      (defthm ,(adt-sym name "-SCHEMA-OK")
        (and (adt-schemap ,schema-const) (equal (adt-ncols ,schema-const) ,p))
        :rule-classes nil)
      (defstobj ,st
        ,@(adt-stobj-fields cols)
        (,pool :type (array (unsigned-byte 8) (0)) :initially 0 :resizable t)
        (,(adt-sym name "$C-COUNT") :type (integer 0 *) :initially 0)
        (,(adt-sym name "$C-FILL") :type (integer 0 *) :initially 0)
        ,@extra
        :inline t)
      ; The pool: recognizer, write loop, read loop, push.
      (defthm ,(adt-sym pool "P-IS")
        (equal (,(adt-sym pool "P") x) (adt-all-elt-p '(:ub 8) x))
        :hints (("Goal" :in-theory (enable adt-elt-p)
                 :use ((:functional-instance adt-g-colp-is-all-elt-p
                                             (adt-g-ct (lambda () '(:ub 8)))
                                             (adt-g-colp ,(adt-sym pool "P")))))))
      (defun ,poolw (i bytes ,st)
        (declare (xargs :stobjs ,st
                        :guard (and (natp i) (adt-octetsp bytes)
                                    (<= (+ i (len bytes)) (,(adt-sym pool "-LENGTH") ,st)))
                        :guard-hints (("Goal" :in-theory (enable ,cp adt-elt-p)))))
        (if (atom bytes)
            ,st
          (let ((,st (,(adt-sym-pre "UPDATE-" (adt-sym pool "I"))
                      i (car bytes) ,st)))
            (,poolw (+ 1 i) (cdr bytes) ,st))))
      (defthm ,(adt-sym poolw "-BRIDGE")
        (equal (,poolw i bytes c) (adt-poolw ,p i bytes c))
        :hints (("Goal" :use ((:functional-instance adt-g-poolw-is-poolw
                                                    (adt-g-p (lambda () ,p))
                                                    (adt-g-poolw ,poolw))))))
      (defun ,poolr (off n acc ,st)
        (declare (xargs :stobjs ,st
                        :guard (and (natp off) (natp n)
                                    (<= (+ off n) (,(adt-sym pool "-LENGTH") ,st)))))
        (if (zp n)
            acc
          (,poolr off (+ -1 n) (cons (,(adt-sym pool "I") (+ off (+ -1 n)) ,st) acc) ,st)))
      (defthm ,(adt-sym poolr "-BRIDGE")
        (equal (,poolr off n acc c) (adt-poolr ,p off n acc c))
        :hints (("Goal" :use ((:functional-instance adt-g-poolr-is-poolr
                                                    (adt-g-q (lambda () ,p))
                                                    (adt-g-poolr ,poolr))))))
      (defun ,push (bytes ,st)
        (declare (xargs :stobjs ,st
                        :guard (adt-octetsp bytes)
                        :guard-hints (("Goal" :in-theory (enable ,cp adt-elt-p)))))
        (let* ((fl (,(adt-sym name "$C-FILL") ,st))
               (need (+ fl (len bytes)))
               (,st (if (<= need (,(adt-sym pool "-LENGTH") ,st))
                        ,st
                      (,(adt-sym-pre "RESIZE-" pool)
                       (max need (* 2 (,(adt-sym pool "-LENGTH") ,st))) ,st)))
               (,st (,poolw fl bytes ,st)))
          (,(adt-sym-pre "UPDATE-" (adt-sym name "$C-FILL")) need ,st)))
      (defthm ,(adt-sym push "-BRIDGE")
        (equal (,push bytes c) (adt-pool-push ,p bytes c))
        :hints (("Goal" :in-theory (enable ,push adt-pool-push adt-pool-room))))
      (in-theory (disable ,poolw ,poolr ,push))
      ,@(adt-col-events name cols 0)
      ; The recognizer IS the library's shape at this field count.
      (defthm ,(adt-sym cp "-IS-SHAPE")
        (equal (,cp c) (and (adt-shape-p ,schema-const c) (equal (len c) ,n)))
        :hints (("Goal" :in-theory (enable ,cp adt-instance-unfold))))
      ,@(adt-field-events name fields 0 0 p)
      (defun ,(adt-sym name "$C-COUNT-OF") (,st)
        (declare (xargs :stobjs ,st))
        (,(adt-sym name "$C-COUNT") ,st))
      (defthm ,(adt-sym name "$C-COUNT-OF-BRIDGE")
        (equal (,(adt-sym name "$C-COUNT-OF") c) (adt-count-c ,schema-const c))
        :hints (("Goal" :in-theory (enable ,(adt-sym name "$C-COUNT-OF") adt-instance-unfold))))
      (defun ,(adt-sym name "$C-APPEND") (rec ,st)
        (declare (xargs :stobjs ,st
                        :guard (adt-rec-p ,schema-const rec)
                        :guard-hints (("Goal" :in-theory (e/d (,cp adt-rec-p-open adt-schema-fns-of-atom)
                                                             (,(adt-sym cp "-IS-SHAPE")))))))
        (let* ((n (,(adt-sym name "$C-COUNT") ,st))
               ,@(adt-append-body name fields 'rec st))
          (,(adt-sym-pre "UPDATE-" (adt-sym name "$C-COUNT")) (+ 1 n) ,st)))
      (defthm ,(adt-sym name "$C-APPEND-BRIDGE")
        (equal (,(adt-sym name "$C-APPEND") rec c) (adt-append-c ,schema-const rec c))
        :hints (("Goal" :in-theory (enable ,(adt-sym name "$C-APPEND") adt-instance-unfold))))
      (in-theory (disable ,(adt-sym name "$C-COUNT-OF") ,(adt-sym name "$C-APPEND"))))))

(defun defadt-fn (name fields0)
  (let* ((fields (adt-norm-fields fields0))
         (schema-const (adt-sym3 '* (symbol-name name) '-schema*))
         (cols (adt-columns name fields))
         (p (len cols))
         (st (adt-sym name "$C"))
         (a (adt-sym name "$A"))
         (ap (adt-sym name "$AP"))
         (corr (adt-sym name "$CORR"))
         (count-of (adt-sym name "$C-COUNT-OF"))
         (append-c (adt-sym name "$C-APPEND"))
         (append-a (adt-sym name "$A-APPEND"))
         (count-a (adt-sym name "$A-COUNT"))
         (create-a (adt-sym-pre "CREATE-" a))
         (create-c (adt-sym-pre "CREATE-" st))
         (recog (adt-sym name "P"))
         (defabs
           `(defabsstobj ,name
              :foundation ,st
              :recognizer (,recog :logic ,ap :exec ,(adt-sym name "$CP"))
              :creator (,(adt-sym-pre "CREATE-" name) :logic ,create-a :exec ,create-c)
              :corr-fn ,corr
              :corr-fn-exists t
              :exports ((,(adt-sym name "-COUNT") :logic ,count-a :exec ,count-of)
                        (,(adt-sym name "-APPEND") :logic ,append-a :exec ,append-c :protect t)
                        ,@(adt-exports name fields))))
         (ob-hints `(("Goal" :in-theory (enable ,corr ,ap ,create-a ,count-a ,append-a
                                                 ,@(adt-logic-names name fields))))))
    `(encapsulate
       ()
       ; The proofs below reason about the stobj's logical image through the
       ; library's list lemmas; nth, update-nth and resize-list stay closed.
       (local (in-theory (disable nth update-nth resize-list)))
       ,@(adt-foundation-events name fields schema-const nil (+ 3 p))
       ; The executable creator is the library's canonical empty image.
       (defthm ,(adt-sym create-c "-IS-CANONICAL-EMPTY")
         (equal (,create-c) (adt-empty-c ,schema-const))
         :hints (("Goal" :in-theory (enable adt-empty-c))))
       ; The logical side.
       (defun ,ap (,a)
         (declare (xargs :guard t))
         (adt-seq-p ,schema-const ,a))
       (defun ,create-a ()
         (declare (xargs :guard t))
         nil)
       (defun ,count-a (,a)
         (declare (xargs :guard (,ap ,a)))
         (len ,a))
       (defun ,append-a (rec ,a)
         (declare (xargs :guard (and (,ap ,a) (adt-rec-p ,schema-const rec))))
         (append ,a (list rec)))
       ,@(adt-field-logic-events name fields 0)
       (defun ,corr (c a)
         (declare (xargs :guard t :verify-guards nil))
         (adt-corr ,schema-const c a))
       ; The defabsstobj obligations, as ACL2 states them, each by one hint.
       (make-event
        (er-let* ((missing (defabsstobj-missing-events ,@(cdr defabs))))
          (value (cons 'progn (adt-obligation-thms missing ',ob-hints (w state))))))
       ,defabs
       (defthm ,(adt-sym name "-COUNT-IS-LEN")
         (equal (,(adt-sym name "-COUNT") ,name) (len ,name))
         :hints (("Goal" :in-theory (enable ,count-a))))
       (defthm ,(adt-sym name "-APPEND-IS-APPEND")
         (equal (,(adt-sym name "-APPEND") rec ,name) (append ,name (list rec)))
         :hints (("Goal" :in-theory (enable ,append-a))))
       (defthm ,(adt-sym recog "-IS-SEQ-P")
         (equal (,recog x) (adt-seq-p ,schema-const x))
         :hints (("Goal" :in-theory (enable ,ap))))
       ,@(adt-is-thms name fields 0))))

(defmacro defadt (name &rest fields)
  (defadt-fn name fields))

(logic)
