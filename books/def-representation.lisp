; fn: `def-representation' --- an abstract stobj from one declaration of
; its schema, promoted from the prototype `defadt' (books/proto/adt.lisp,
; lane proto-adt 2026-09-27) for stage 1 of
; planning/design-store-representation-2026-10-01.md.
;
;   (def-representation NAME (FIELD KIND) ...
;     [:scalar t] [:generic t] [:invariant PRED :invariant-lemmas (L ...)]
;     [:write-once t] [:paged nil])
;
; KIND is :u8 :u32 :u64 :bool :octets, (:nat B) or (:enum OBJ ...).  What
; `defadt' already generates, this generates (the foundation of typed
; columns and one octet pool, the executables, the bridges by functional
; instance and by unfolding, the obligations obtained from ACL2 itself by
; `defabsstobj-missing-events' and closed by one uniform hint, the
; `defabsstobj', the `-is-' meaning of each export); the prototype's
; generator function is reused, not copied.  Added here:
;
;   * the ATTACHMENT CHECK at expansion.  ACL2 refuses an abstract stobj
;     whose recognizer or correspondence has an attached ancestor
;     (:DOC stobj-attachment-restrictions); the tree learned that when the
;     catalog's recognizer reached `fn-digest' (books/catalog.lisp,
;     2026-09-27) and no book could include it beside crypto-attach.  Here
;     the ancestors of what the recognizer and correspondence will call
;     (the library's `adt-corr' and `adt-seq-p', and the :invariant) are
;     checked in the world BEFORE anything is generated, with
;     `canonical-ancestors-lst' and `attached-fns', the functions ACL2's
;     own check uses, and a reachable attachment is refused by name.
;   * `:invariant PRED', a unary predicate over the logical sequence
;     conjoined into the recognizer.  Its preservation is content, not
;     ceremony: the instance is refused unless `:invariant-lemmas' names
;     theorems already in the world, which the uniform hint enables for the
;     `{preserved}' obligations (PRED of the empty sequence, of an append
;     of a well-formed record, of a field update).
;   * `:scalar t', for a one-field schema: the logical value is the list of
;     the field's values (`adt-scalar-seq-p'), not of one-element records,
;     so a buffer of payloads has the arena's logical view
;     (books/payload-arena.lisp: `fn-arn-payload-listp', `len', `nth',
;     `append').  The exports are NAME-count, NAME-get, NAME-set,
;     NAME-append.
;   * `:generic t': the columnar instance is emitted as NAME-cols, then
;     `(attach-stobj NAME NAME-cols)', then NAME itself as an ATTACHABLE
;     generic over a LIST foundation (one field holding the logical value,
;     every :exec a total list operation from
;     books/def-representation-lib.lisp), with the same :logic functions
;     and the same export skeleton, so that a book certified against NAME
;     is included unchanged under the attachment (the pattern of
;     books/payload-arena.lisp and payload-arena-attach.lisp, generated).
;   * `:write-once t' (lane paged-catalog-4, Codex r21 F1): no :octets or
;     :tree field has a set export, so the pool is written only by an
;     append; NAME$C-FILL-IS-LOAD-OF-{CREATE,APPEND,APPEND-T,SET-F,CLEAR},
;     one per writing export, say the pool's fill is `adt-load' of the
;     logical sequence (the sum of its records' octets) in every reachable
;     foundation: the pool is bounded by the live records, never by the
;     history of their writes.
;
; Every generated name is derived from NAME (`NAME$c', `NAME$a', `NAME$ap',
; `NAME$corr', `NAME-count', `NAME-get-FIELD', ...; `NAME$l' for the list
; foundation) and the instance is recorded in the world table
; `fn-generated'.  Malformed input is refused at expansion with a soft
; error naming the check.  Nothing of the library is left enabled by an
; instance beyond what `defadt' leaves.

(in-package "ACL2")
(include-book "proto/adt")
(include-book "def-representation-lib")
(include-book "def-representation-paged")

(program)

; -----------------------------------------------------------------------------
; The scalar instance: one field, the logical value is the list of values.
; The foundation and its executables are the prototype's (one record of one
; field); only the logical side and the correspondence differ, and the
; obligations are closed by the library's wrap lemmas.

; (rep-scalar-events is below the paged foundation, which it may use.)

; -----------------------------------------------------------------------------
; The generic over a list foundation, attached to the columnar instance.
; IMPL is the columnar instance's name (NAME-cols); its logical functions
; are the generic's.  EXPORTS are (export-name logic-fn exec-kind . args)
; rows computed from the schema: the exec of each is a total list
; operation over the one field.

(defun rep-l-field-execs (l items upd fields j)
  (if (endp fields)
      nil
    (let ((f (car (car fields))))
      (list* `(defun ,(adt-sym3 l "-GET-" f) (i ,l)
                (declare (xargs :stobjs ,l))
                (adt-l-nth ,j (adt-l-nth i (,items ,l))))
             `(defun ,(adt-sym3 l "-SET-" f) (i v ,l)
                (declare (xargs :stobjs ,l))
                (,upd (adt-l-update-nth i (adt-l-update-nth ,j v (adt-l-nth i (,items ,l)))
                                        (,items ,l))
                      ,l))
             (rep-l-field-execs l items upd (cdr fields) (+ 1 j))))))

(defun rep-l-exec-events (name fields scalar)
  ; The :exec functions of the list foundation, each :guard t.
  (let* ((l (adt-sym name "$L"))
         (items (adt-sym l "-ITEMS"))
         (upd (adt-sym-pre "UPDATE-" items)))
    (append
     `((defun ,(adt-sym l "-COUNT") (,l)
         (declare (xargs :stobjs ,l))
         (len (,items ,l)))
       (defun ,(adt-sym l "-APPEND") (rec ,l)
         (declare (xargs :stobjs ,l))
         (,upd (adt-l-snoc (,items ,l) rec) ,l))
       (defun ,(adt-sym l "-CLEAR") (,l)
         (declare (xargs :stobjs ,l))
         (,upd nil ,l)))
     (if scalar
         `((defun ,(adt-sym l "-GET") (i ,l)
             (declare (xargs :stobjs ,l))
             (adt-l-nth i (,items ,l)))
           (defun ,(adt-sym l "-SET") (i v ,l)
             (declare (xargs :stobjs ,l))
             (,upd (adt-l-update-nth i v (,items ,l)) ,l)))
       (rep-l-field-execs l items upd fields 0)))))


(defun rep-generic-field-exports (name impl l fields)
  (if (endp fields)
      nil
    (let ((f (car (car fields))))
      (list* `(,(adt-sym3 name "-GET-" f) :logic ,(adt-sym3 impl "$A-GET-" f)
               :exec ,(adt-sym3 l "-GET-" f))
             `(,(adt-sym3 name "-SET-" f) :logic ,(adt-sym3 impl "$A-SET-" f)
               :exec ,(adt-sym3 l "-SET-" f) :protect t)
             (rep-generic-field-exports name impl l (cdr fields))))))

(defun rep-generic-exports (name impl fields scalar)
  ; In the implementation's order: `attach-stobj' matches the two export
  ; lists positionally.
  (let ((l (adt-sym name "$L")))
    (if scalar
        `((,(adt-sym name "-COUNT") :logic ,(adt-sym impl "$A-COUNT") :exec ,(adt-sym l "-COUNT"))
          (,(adt-sym name "-GET") :logic ,(adt-sym impl "$A-GET") :exec ,(adt-sym l "-GET"))
          (,(adt-sym name "-SET") :logic ,(adt-sym impl "$A-SET") :exec ,(adt-sym l "-SET")
           :protect t)
          (,(adt-sym name "-APPEND") :logic ,(adt-sym impl "$A-APPEND") :exec ,(adt-sym l "-APPEND")
           :protect t)
          (,(adt-sym name "-CLEAR") :logic ,(adt-sym impl "$A-CLEAR") :exec ,(adt-sym l "-CLEAR")
           :protect t))
      `((,(adt-sym name "-COUNT") :logic ,(adt-sym impl "$A-COUNT") :exec ,(adt-sym l "-COUNT"))
        (,(adt-sym name "-APPEND") :logic ,(adt-sym impl "$A-APPEND") :exec ,(adt-sym l "-APPEND")
         :protect t)
        ,@(rep-generic-field-exports name impl l fields)
        (,(adt-sym name "-CLEAR") :logic ,(adt-sym impl "$A-CLEAR") :exec ,(adt-sym l "-CLEAR")
         :protect t)))))


(defun rep-logic-names (impl fields scalar)
  (if scalar
      (list (adt-sym impl "$A-GET") (adt-sym impl "$A-SET"))
    (adt-logic-names impl fields)))

(defun rep-generic-events (name impl fields scalar)
  (let* ((l (adt-sym name "$L"))
         (items (adt-sym l "-ITEMS"))
         (lp (adt-sym l "P"))
         (lcorr (adt-sym name "$LCORR"))
         (ap (adt-sym impl "$AP"))
         (create-a (adt-sym-pre "CREATE-" (adt-sym impl "$A")))
         (create-l (adt-sym-pre "CREATE-" l))
         (recog (adt-sym name "P"))
         (execs (rep-l-exec-events name fields scalar))
         (exec-names (strip-cadrs execs))
         (defabs
           `(defabsstobj ,name
              :foundation ,l
              :recognizer (,recog :logic ,ap :exec ,lp)
              :creator (,(adt-sym-pre "CREATE-" name) :logic ,create-a :exec ,create-l)
              :corr-fn ,lcorr
              :exports ,(rep-generic-exports name impl fields scalar)
              :attachable t))
         (ob-hints `(("Goal" :in-theory (enable ,lcorr ,ap ,create-a ,create-l
                                                 ,(adt-sym impl "$A-COUNT") ,(adt-sym impl "$A-APPEND")
                                                 ,(adt-sym impl "$A-CLEAR")
                                                 ,@(rep-logic-names impl fields scalar)
                                                 ,@exec-names ,items
                                                 adt-set-a adt-scalar-seq-p)))))
    `((defstobj ,l (,items :type t :initially nil) :inline t)
      (defun ,lcorr (,l a)
        (declare (xargs :stobjs ,l :verify-guards nil))
        (and (,ap a) (equal (,items ,l) a)))
      ,@execs
      (encapsulate
        ()
        (local (in-theory (disable nth update-nth)))
        (make-event
         (er-let* ((missing (defabsstobj-missing-events ,@(cdr defabs))))
           (value (cons 'progn (adt-obligation-thms missing ',ob-hints (w state)))))))
      (attach-stobj ,name ,impl)
      ,defabs)))

; -----------------------------------------------------------------------------
; THE PAGED FOUNDATION (lane gate-b, 2026-10-01; D27).  A sequence instance
; is backed by fixed pages (books/def-representation-paged.lisp): a row page
; stobj NAME$PG (one typed array per column, *adt-pg-rows* entries once in
; use), a pool page stobj NAME$PP (*adt-pg-octets* octets), and NAME$C, the
; two page tables, the count, the fill and the pages in use.  Every
; executable unfolds to the library's paged operation (its bridge, by
; definition); the correspondence is `adt-pg-corr', and the obligations are
; closed by the library's adt-pg-corr-* theorems by one uniform hint.  The
; logical side, the exports and their -IS- meanings are the columnar
; instance's, unchanged.

(defun adt-pg-num (i) (coerce (explode-atom i 10) 'string))

(defun adt-pg-pcols (name fields)
  ; the page's columns: (colname ctype) in layout order
  (if (endp fields)
      nil
    (let* ((f (car (car fields))) (k (cadr (car fields))))
      (if (eq (car k) :octets)
          (list* (list (adt-sym3 name "$PG-" (adt-sym f "-OFF")) '(:nat))
                 (list (adt-sym3 name "$PG-" (adt-sym f "-LEN")) '(:nat))
                 (adt-pg-pcols name (cdr fields)))
        (cons (list (adt-sym3 name "$PG-" f) (adt-ctype k))
              (adt-pg-pcols name (cdr fields)))))))

(defun adt-pg-fresh-body (cols pg r)
  (if (endp cols)
      nil
    (list* `(,pg (,(adt-sym-pre "RESIZE-" (car (car cols))) 0 ,pg))
           `(,pg (,(adt-sym-pre "RESIZE-" (car (car cols))) ,r ,pg))
           (adt-pg-fresh-body (cdr cols) pg r))))

(defun adt-pg-col-events (name cols ci)
  ; per column: the row put and the row get, each the library's at CI
  (if (endp cols)
      nil
    (let* ((cname (car (car cols)))
           (ct (cadr (car cols)))
           (st (adt-sym name "$C"))
           (pg (adt-sym name "$PG"))
           (tp (adt-sym name "$TP"))
           (tpp (adt-sym name "$TP-PAGES"))
           (rows (adt-sym name "$C-ROWS"))
           (put (adt-sym name (concatenate 'string "$C-RPUT" (adt-pg-num ci))))
           (get (adt-sym name (concatenate 'string "$C-RGET" (adt-pg-num ci)))))
      (list*
       `(defun ,put (n x ,st)
          (declare (xargs :stobjs ,st :guard (and (natp n) (adt-elt-p ',ct x))
                          :guard-hints (("Goal" :in-theory (e/d (adt-elt-p) (floor mod))
                                         :use ((:instance adt-pg-floor-mod-guard-facts (r *adt-pg-rows*))
                                               (:instance adt-pg-mod-below (r *adt-pg-rows*))
                                               (:instance adt-pg-floor-mod-guard-facts (n (floor n *adt-pg-rows*)) (r *adt-pg-tpages*))
                                               (:instance adt-pg-mod-below (n (floor n *adt-pg-rows*)) (r *adt-pg-tpages*)))))))
          (let* ((k (floor n *adt-pg-rows*)) (j (mod n *adt-pg-rows*))
                 (jt (floor k *adt-pg-tpages*)) (it (mod k *adt-pg-tpages*)))
            (if (< jt (,(adt-sym rows "-LENGTH") ,st))
                (stobj-let ((,tp (,(adt-sym rows "I") jt ,st)))
                           (,tp)
                           (if (< it (,(adt-sym tpp "-LENGTH") ,tp))
                               (stobj-let ((,pg (,(adt-sym tpp "I") it ,tp)))
                                          (,pg)
                                          (if (< j (,(adt-sym cname "-LENGTH") ,pg))
                                              (,(adt-sym-pre "UPDATE-" (adt-sym cname "I")) j x ,pg)
                                            ,pg)
                                          ,tp)
                             ,tp)
                           ,st)
              ,st)))
       `(defthm ,(adt-sym put "-UNFOLDS")
          (equal (,put n x c) (adt-pg-rput ,ci n x *adt-pg-rows* c))
          :hints (("Goal" :in-theory (enable ,put adt-pg-rput))))
       `(defun ,get (n ,st)
          (declare (xargs :stobjs ,st :guard (natp n)
                          :guard-hints (("Goal" :in-theory (disable floor mod)
                                         :use ((:instance adt-pg-floor-mod-guard-facts (r *adt-pg-rows*))
                                               (:instance adt-pg-mod-below (r *adt-pg-rows*))
                                               (:instance adt-pg-floor-mod-guard-facts (n (floor n *adt-pg-rows*)) (r *adt-pg-tpages*))
                                               (:instance adt-pg-mod-below (n (floor n *adt-pg-rows*)) (r *adt-pg-tpages*)))))))
          (let* ((k (floor n *adt-pg-rows*)) (j (mod n *adt-pg-rows*))
                 (jt (floor k *adt-pg-tpages*)) (it (mod k *adt-pg-tpages*)))
            (if (< jt (,(adt-sym rows "-LENGTH") ,st))
                (stobj-let ((,tp (,(adt-sym rows "I") jt ,st)))
                           (v)
                           (if (< it (,(adt-sym tpp "-LENGTH") ,tp))
                               (stobj-let ((,pg (,(adt-sym tpp "I") it ,tp)))
                                          (v)
                                          (if (< j (,(adt-sym cname "-LENGTH") ,pg))
                                              (,(adt-sym cname "I") j ,pg)
                                            0)
                                          v)
                             0)
                           v)
              0)))
       `(defthm ,(adt-sym get "-UNFOLDS")
          (equal (,get n c) (adt-pg-rget ,ci n *adt-pg-rows* c))
          :hints (("Goal" :in-theory (enable ,get adt-pg-rget))))
       `(in-theory (disable ,put ,get))
       (adt-pg-col-events name (cdr cols) (+ 1 ci))))))

(defun adt-pg-load-terms (fields recv)
  (if (endp fields)
      nil
    (if (eq (car (cadr (car fields))) :octets)
        (cons `(len (car ,recv)) (adt-pg-load-terms (cdr fields) `(cdr ,recv)))
      (adt-pg-load-terms (cdr fields) `(cdr ,recv)))))

(defun adt-pg-field-events (name fields j ci schema)
  ; per field: put, get, set, each bridged to the library's paged operation
  (if (endp fields)
      nil
    (let* ((f (car (car fields)))
           (k (cadr (car fields)))
           (st (adt-sym name "$C"))
           (octp (eq (car k) :octets))
           (putf (adt-sym3 name "$C-PUT-FIELD-" f))
           (getf (adt-sym3 name "$C-GET-" f))
           (setf (adt-sym3 name "$C-SET-" f))
           (rput0 (adt-sym name (concatenate 'string "$C-RPUT" (adt-pg-num ci))))
           (rput1 (adt-sym name (concatenate 'string "$C-RPUT" (adt-pg-num (+ 1 ci)))))
           (rget0 (adt-sym name (concatenate 'string "$C-RGET" (adt-pg-num ci))))
           (rget1 (adt-sym name (concatenate 'string "$C-RGET" (adt-pg-num (+ 1 ci))))))
      (append
       (if octp
           `((defun ,putf (n v ,st)
               (declare (xargs :stobjs ,st :guard (and (natp n) (adt-octetsp v))
                               :guard-hints (("Goal" :in-theory (enable adt-elt-p)))))
               (let* ((o (,(adt-sym name "$C-FILL") ,st))
                      (,st (,(adt-sym name "$C-POOLW") o v ,st))
                      (,st (,(adt-sym-pre "UPDATE-" (adt-sym name "$C-FILL")) (+ o (len v)) ,st))
                      (,st (,rput0 n o ,st)))
                 (,rput1 n (len v) ,st)))
             (defun ,getf (i ,st)
               (declare (xargs :stobjs ,st :guard (natp i)))
               (,(adt-sym name "$C-POOLR") (,rget0 i ,st) (,rget1 i ,st) nil ,st))
             (defun ,setf (i v ,st)
               (declare (xargs :stobjs ,st :guard (and (natp i) (adt-val-okp ',k v))
                               :guard-hints (("Goal" :in-theory (enable adt-val-okp)))))
               (let ((,st (,(adt-sym name "$C-POOLROOM") (+ (,(adt-sym name "$C-FILL") ,st) (len v)) ,st)))
                 (,putf i v ,st))))
         `((defun ,putf (n v ,st)
             (declare (xargs :stobjs ,st :guard (and (natp n) (adt-val-okp ',k v))
                             :guard-hints (("Goal" :in-theory (enable adt-elt-p adt-val-okp adt-enc adt-ctype)))))
             (,rput0 n (adt-enc ',k v) ,st))
           (defun ,getf (i ,st)
             (declare (xargs :stobjs ,st :guard (natp i)))
             (adt-dec ',k (,rget0 i ,st)))
           (defun ,setf (i v ,st)
             (declare (xargs :stobjs ,st :guard (and (natp i) (adt-val-okp ',k v))))
             (,putf i v ,st))))
       `((defthm ,(adt-sym putf "-UNFOLDS")
           (equal (,putf n v c) (adt-pg-put-field ',k ,ci n v *adt-pg-rows* *adt-pg-octets* c))
           :hints (("Goal" :in-theory (enable ,putf adt-pg-put-field))))
         (defthm ,(adt-sym getf "-UNFOLDS")
           (equal (,getf i c) (adt-pg-get-c ,schema ,j i *adt-pg-rows* *adt-pg-octets* c))
           :hints (("Goal" :in-theory (enable ,getf adt-pg-get-c adt-pg-get-fields adt-pg-get-field))))
         (defthm ,(adt-sym setf "-UNFOLDS")
           (equal (,setf i v c)
                  (adt-pg-set-c ,schema ,j i v *adt-pg-rows* *adt-pg-octets* (,(adt-sym-pre "CREATE-" (adt-sym name "$PP"))) c))
           :hints (("Goal" :in-theory (enable ,setf adt-pg-set-c adt-pg-set-fields adt-pg-set-room))))
         (in-theory (disable ,putf ,getf ,setf)))
       (adt-pg-field-events name (cdr fields) (+ 1 j) (+ (if octp 2 1) ci) schema)))))

(defun adt-pg-append-body (name fields recv st)
  (if (endp fields)
      nil
    (cons `(,st (,(adt-sym3 name "$C-PUT-FIELD-" (car (car fields))) n (car ,recv) ,st))
          (adt-pg-append-body name (cdr fields) `(cdr ,recv) st))))

(defun adt-pg-putf-bridges (name fields)
  (if (endp fields)
      nil
    (cons (adt-sym (adt-sym3 name "$C-PUT-FIELD-" (car (car fields))) "-UNFOLDS")
          (adt-pg-putf-bridges name (cdr fields)))))

(defun adt-pg-foundation-events (name fields schema-const)
  (let* ((schema (adt-schema-of fields))
         (pcols (adt-pg-pcols name fields))
         (p (len pcols))
         (st (adt-sym name "$C"))
         (pg (adt-sym name "$PG"))
         (pp (adt-sym name "$PP"))
         (ppb (adt-sym name "$PP-BYTES"))
         (tp (adt-sym name "$TP"))
         (tpp (adt-sym name "$TP-PAGES"))
         (pt (adt-sym name "$PT"))
         (ptp (adt-sym name "$PT-PAGES"))
         (tready (adt-sym name "$TP-READY"))
         (ptready (adt-sym name "$PT-READY"))
         (rows (adt-sym name "$C-ROWS"))
         (ppages (adt-sym name "$C-PPAGES"))
         (cnt (adt-sym name "$C-COUNT"))
         (fillf (adt-sym name "$C-FILL"))
         (np (adt-sym name "$C-NP"))
         (nq (adt-sym name "$C-NQ"))
         (dpg `(,(adt-sym-pre "CREATE-" pg)))
         (dpp `(,(adt-sym-pre "CREATE-" pp)))
         (fresh (adt-sym name "$PG-FRESH"))
         (pfresh (adt-sym name "$PP-FRESH"))
         (addrow (adt-sym name "$C-ADDROW"))
         (addpool (adt-sym name "$C-ADDPOOL"))
         (rowroom (adt-sym name "$C-ROWROOM"))
         (poolroom (adt-sym name "$C-POOLROOM"))
         (pput (adt-sym name "$C-PPUT"))
         (pget (adt-sym name "$C-PGET"))
         (poolw (adt-sym name "$C-POOLW"))
         (poolr (adt-sym name "$C-POOLR"))
         (count-of (adt-sym name "$C-COUNT-OF"))
         (append-c (adt-sym name "$C-APPEND"))
         (clear-c (adt-sym name "$C-CLEAR")))
    `((defconst ,schema-const ',schema)
      (defthm ,(adt-sym name "-SCHEMA-OK")
        (and (adt-schemap ,schema-const) (equal (adt-ncols ,schema-const) ,p))
        :rule-classes nil)
      (defstobj ,pg ,@(adt-stobj-fields pcols) :inline t)
      (defstobj ,pp (,ppb :type (array (unsigned-byte 8) (0)) :initially 0 :resizable t) :inline t)
      ; A table page: *adt-pg-tpages* pages once ready (the two-level table,
      ; books/def-representation-paged.lisp section 4b).
      (defstobj ,tp (,tpp :type (array ,pg (0)) :resizable t) :inline t)
      (defstobj ,pt (,ptp :type (array ,pp (0)) :resizable t) :inline t)
      (defstobj ,st
        (,rows :type (array ,tp (0)) :resizable t)
        (,ppages :type (array ,pt (0)) :resizable t)
        (,cnt :type (integer 0 *) :initially 0)
        (,fillf :type (integer 0 *) :initially 0)
        (,np :type (integer 0 *) :initially 0)
        (,nq :type (integer 0 *) :initially 0)
        :inline t)
      (defthm ,(adt-sym-pre "CREATE-" (adt-sym st "-IS-EMPTY"))
        (equal (,(adt-sym-pre "CREATE-" st)) '(nil nil 0 0 0 0)))
      ; A page made ready: each column emptied, then R zeros.
      (defun ,fresh (,pg)
        (declare (xargs :stobjs ,pg))
        (let* (,@(adt-pg-fresh-body pcols pg '*adt-pg-rows*)) ,pg))
      (defthm ,(adt-sym fresh "-UNFOLDS")
        (equal (,fresh pg) (adt-pg-fresh 0 ,p *adt-pg-rows* pg))
        :hints (("Goal" :in-theory (enable ,fresh adt-pg-fresh))))
      (defun ,pfresh (,pp)
        (declare (xargs :stobjs ,pp))
        (let* ((,pp (,(adt-sym-pre "RESIZE-" ppb) 0 ,pp))
               (,pp (,(adt-sym-pre "RESIZE-" ppb) *adt-pg-octets* ,pp)))
          ,pp))
      (defthm ,(adt-sym pfresh "-UNFOLDS")
        (equal (,pfresh pp) (adt-pg-fresh 0 1 *adt-pg-octets* pp))
        :hints (("Goal" :in-theory (enable ,pfresh adt-pg-fresh))))
      (in-theory (disable ,fresh ,pfresh))
      ; A table page made ready: its pages emptied, then T fresh headers.
      (defun ,tready (,tp)
        (declare (xargs :stobjs ,tp))
        (let* ((,tp (,(adt-sym-pre "RESIZE-" tpp) 0 ,tp))
               (,tp (,(adt-sym-pre "RESIZE-" tpp) *adt-pg-tpages* ,tp)))
          ,tp))
      (defthm ,(adt-sym tready "-UNFOLDS")
        (equal (,tready tp) (adt-pg-tready ,dpg tp))
        :hints (("Goal" :in-theory (enable ,tready adt-pg-tready))))
      (defun ,ptready (,pt)
        (declare (xargs :stobjs ,pt))
        (let* ((,pt (,(adt-sym-pre "RESIZE-" ptp) 0 ,pt))
               (,pt (,(adt-sym-pre "RESIZE-" ptp) *adt-pg-tpages* ,pt)))
          ,pt))
      (defthm ,(adt-sym ptready "-UNFOLDS")
        (equal (,ptready pt) (adt-pg-tready ,dpp pt))
        :hints (("Goal" :in-theory (enable ,ptready adt-pg-tready))))
      (in-theory (disable ,tready ,ptready))
      (defun ,addrow (,st)
        (declare (xargs :stobjs ,st
                        :guard-hints (("Goal" :in-theory (disable floor mod)
                                       :use ((:instance adt-pg-floor-mod-guard-facts (n (nth 4 ,st)) (r *adt-pg-tpages*))
                                             (:instance adt-pg-mod-below (n (nth 4 ,st)) (r *adt-pg-tpages*)))))))
        (let* ((k (,np ,st)) (jt (floor k *adt-pg-tpages*)) (it (mod k *adt-pg-tpages*))
               (,st (if (and (equal it 0) (<= (,(adt-sym rows "-LENGTH") ,st) jt))
                        (,(adt-sym-pre "RESIZE-" rows) (max *adt-pg-dir-reserve* (* 2 jt)) ,st)
                      ,st))
               (,st (if (and (equal it 0) (< jt (,(adt-sym rows "-LENGTH") ,st)))
                        (stobj-let ((,tp (,(adt-sym rows "I") jt ,st)))
                                   (,tp)
                                   (,tready ,tp)
                                   ,st)
                      ,st))
               (,st (if (< jt (,(adt-sym rows "-LENGTH") ,st))
                        (stobj-let ((,tp (,(adt-sym rows "I") jt ,st)))
                                   (,tp)
                                   (if (< it (,(adt-sym tpp "-LENGTH") ,tp))
                                       (stobj-let ((,pg (,(adt-sym tpp "I") it ,tp)))
                                                  (,pg)
                                                  (,fresh ,pg)
                                                  ,tp)
                                     ,tp)
                                   ,st)
                      ,st)))
          (,(adt-sym-pre "UPDATE-" np) (+ 1 k) ,st)))
      (defthm ,(adt-sym addrow "-UNFOLDS")
        (equal (,addrow c) (adt-pg-addrow ,p *adt-pg-rows* ,dpg c))
        :hints (("Goal" :in-theory (e/d (,addrow adt-pg-addrow adt-pg-cdadd ,(adt-sym tready "-UNFOLDS")
                                         ,(adt-sym fresh "-UNFOLDS"))
                                        (floor mod (:executable-counterpart force))))))
      (defun ,addpool (,st)
        (declare (xargs :stobjs ,st
                        :guard-hints (("Goal" :in-theory (disable floor mod)
                                       :use ((:instance adt-pg-floor-mod-guard-facts (n (nth 5 ,st)) (r *adt-pg-tpages*))
                                             (:instance adt-pg-mod-below (n (nth 5 ,st)) (r *adt-pg-tpages*)))))))
        (let* ((k (,nq ,st)) (jt (floor k *adt-pg-tpages*)) (it (mod k *adt-pg-tpages*))
               (,st (if (and (equal it 0) (<= (,(adt-sym ppages "-LENGTH") ,st) jt))
                        (,(adt-sym-pre "RESIZE-" ppages) (max *adt-pg-dir-reserve* (* 2 jt)) ,st)
                      ,st))
               (,st (if (and (equal it 0) (< jt (,(adt-sym ppages "-LENGTH") ,st)))
                        (stobj-let ((,pt (,(adt-sym ppages "I") jt ,st)))
                                   (,pt)
                                   (,ptready ,pt)
                                   ,st)
                      ,st))
               (,st (if (< jt (,(adt-sym ppages "-LENGTH") ,st))
                        (stobj-let ((,pt (,(adt-sym ppages "I") jt ,st)))
                                   (,pt)
                                   (if (< it (,(adt-sym ptp "-LENGTH") ,pt))
                                       (stobj-let ((,pp (,(adt-sym ptp "I") it ,pt)))
                                                  (,pp)
                                                  (,pfresh ,pp)
                                                  ,pt)
                                     ,pt)
                                   ,st)
                      ,st)))
          (,(adt-sym-pre "UPDATE-" nq) (+ 1 k) ,st)))
      (defthm ,(adt-sym addpool "-UNFOLDS")
        (equal (,addpool c) (adt-pg-addpool *adt-pg-octets* ,dpp c))
        :hints (("Goal" :in-theory (e/d (,addpool adt-pg-addpool adt-pg-cdadd ,(adt-sym ptready "-UNFOLDS")
                                         ,(adt-sym pfresh "-UNFOLDS"))
                                        (floor mod (:executable-counterpart force))))))
      (in-theory (disable ,addrow ,addpool))
      (defun ,rowroom (,st)
        (declare (xargs :stobjs ,st))
        (if (< (,cnt ,st) (* *adt-pg-rows* (,np ,st))) ,st (,addrow ,st)))
      (defthm ,(adt-sym rowroom "-UNFOLDS")
        (equal (,rowroom c) (adt-pg-rowroom ,p *adt-pg-rows* ,dpg c))
        :hints (("Goal" :in-theory (enable ,rowroom adt-pg-rowroom))))
      (defun ,poolroom (need ,st)
        (declare (xargs :stobjs ,st
                        :measure (nfix (- (nfix need) (* *adt-pg-octets* (nfix (nth 5 ,st)))))
                        :hints (("Goal" :in-theory (enable ,(adt-sym addpool "-UNFOLDS"))))))
        (if (and (natp (,nq ,st)) (natp need) (< (* *adt-pg-octets* (,nq ,st)) need))
            (let ((,st (,addpool ,st))) (,poolroom need ,st))
          ,st))
      (defthm ,(adt-sym poolroom "-BRIDGE")
        (equal (,poolroom need c) (adt-pg-poolroom *adt-pg-octets* ,dpp need c))
        :hints (("Goal" :induct (,poolroom need c)
                 :in-theory (enable ,poolroom adt-pg-poolroom))))
      (in-theory (disable ,rowroom ,poolroom))
      ; The pool: an octet put and get at a position, the write and read loops.
      (defun ,pput (i b ,st)
        (declare (xargs :stobjs ,st :guard (and (natp i) (unsigned-byte-p 8 b))
                        :guard-hints (("Goal" :in-theory (disable floor mod)
                                       :use ((:instance adt-pg-floor-mod-guard-facts (n i) (r *adt-pg-octets*))
                                             (:instance adt-pg-mod-below (n i) (r *adt-pg-octets*))
                                             (:instance adt-pg-floor-mod-guard-facts (n (floor i *adt-pg-octets*)) (r *adt-pg-tpages*))
                                             (:instance adt-pg-mod-below (n (floor i *adt-pg-octets*)) (r *adt-pg-tpages*)))))))
        (let* ((k (floor i *adt-pg-octets*)) (j (mod i *adt-pg-octets*))
               (jt (floor k *adt-pg-tpages*)) (it (mod k *adt-pg-tpages*)))
          (if (< jt (,(adt-sym ppages "-LENGTH") ,st))
              (stobj-let ((,pt (,(adt-sym ppages "I") jt ,st)))
                         (,pt)
                         (if (< it (,(adt-sym ptp "-LENGTH") ,pt))
                             (stobj-let ((,pp (,(adt-sym ptp "I") it ,pt)))
                                        (,pp)
                                        (if (< j (,(adt-sym ppb "-LENGTH") ,pp))
                                            (,(adt-sym-pre "UPDATE-" (adt-sym ppb "I")) j b ,pp)
                                          ,pp)
                                        ,pt)
                           ,pt)
                         ,st)
            ,st)))
      (defthm ,(adt-sym pput "-UNFOLDS")
        (equal (,pput i b c) (adt-pg-pput i b *adt-pg-octets* c))
        :hints (("Goal" :in-theory (enable ,pput adt-pg-pput))))
      (defun ,pget (i ,st)
        (declare (xargs :stobjs ,st :guard (natp i)
                        :guard-hints (("Goal" :in-theory (disable floor mod)
                                       :use ((:instance adt-pg-floor-mod-guard-facts (n i) (r *adt-pg-octets*))
                                             (:instance adt-pg-mod-below (n i) (r *adt-pg-octets*))
                                             (:instance adt-pg-floor-mod-guard-facts (n (floor i *adt-pg-octets*)) (r *adt-pg-tpages*))
                                             (:instance adt-pg-mod-below (n (floor i *adt-pg-octets*)) (r *adt-pg-tpages*)))))))
        (let* ((k (floor i *adt-pg-octets*)) (j (mod i *adt-pg-octets*))
               (jt (floor k *adt-pg-tpages*)) (it (mod k *adt-pg-tpages*)))
          (if (< jt (,(adt-sym ppages "-LENGTH") ,st))
              (stobj-let ((,pt (,(adt-sym ppages "I") jt ,st)))
                         (v)
                         (if (< it (,(adt-sym ptp "-LENGTH") ,pt))
                             (stobj-let ((,pp (,(adt-sym ptp "I") it ,pt)))
                                        (v)
                                        (if (< j (,(adt-sym ppb "-LENGTH") ,pp))
                                            (,(adt-sym ppb "I") j ,pp)
                                          0)
                                        v)
                           0)
                         v)
            0)))
      (defthm ,(adt-sym pget "-UNFOLDS")
        (equal (,pget i c) (adt-pg-pget i *adt-pg-octets* c))
        :hints (("Goal" :in-theory (enable ,pget adt-pg-pget))))
      (in-theory (disable ,pput ,pget))
      (defun ,poolw (i bytes ,st)
        (declare (xargs :stobjs ,st :guard (and (natp i) (adt-octetsp bytes))))
        (if (atom bytes)
            ,st
          (let ((,st (,pput i (car bytes) ,st)))
            (,poolw (+ 1 i) (cdr bytes) ,st))))
      (defthm ,(adt-sym poolw "-BRIDGE")
        (equal (,poolw i bytes c) (adt-pg-poolw i bytes *adt-pg-octets* c))
        :hints (("Goal" :induct (,poolw i bytes c)
                 :in-theory (enable ,poolw adt-pg-poolw))))
      (defun ,poolr (off n acc ,st)
        (declare (xargs :stobjs ,st :guard (true-listp acc)))
        (if (or (not (posp n)) (not (natp off)))
            acc
          (,poolr off (+ -1 n) (cons (,pget (+ off (+ -1 n)) ,st) acc) ,st)))
      (defthm ,(adt-sym poolr "-BRIDGE")
        (equal (,poolr off n acc c) (adt-pg-poolr off n acc *adt-pg-octets* c))
        :hints (("Goal" :induct (,poolr off n acc c)
                 :in-theory (enable ,poolr adt-pg-poolr))))
      (in-theory (disable ,poolw ,poolr))
      ,@(adt-pg-col-events name pcols 0)
      ,@(adt-pg-field-events name fields 0 0 schema-const)
      (defun ,count-of (,st)
        (declare (xargs :stobjs ,st))
        (,cnt ,st))
      (defun ,append-c (rec ,st)
        (declare (xargs :stobjs ,st
                        :guard (adt-rec-p ,schema-const rec)
                        :guard-hints (("Goal" :in-theory (enable adt-rec-p-open adt-schema-fns-of-atom)))))
        (let* ((,st (,rowroom ,st))
               (,st (,poolroom (+ (,fillf ,st) ,@(adt-pg-load-terms fields 'rec)) ,st))
               (n (,cnt ,st))
               ,@(adt-pg-append-body name fields 'rec st))
          (,(adt-sym-pre "UPDATE-" cnt) (+ 1 n) ,st)))
      (defthm ,(adt-sym append-c "-UNFOLDS")
        (equal (,append-c rec c)
               (adt-pg-append-c ,schema-const rec *adt-pg-rows* *adt-pg-octets* ,dpg ,dpp c))
        :hints (("Goal" :in-theory (enable ,append-c adt-pg-append-c adt-pg-append-room adt-pg-append-at
                                           adt-pg-append-fields adt-rec-load
                                           ,@(adt-pg-putf-bridges name fields)))))
      ; The clear releases the pages: both tables emptied, the counters 0.
      (defun ,clear-c (,st)
        (declare (xargs :stobjs ,st))
        (let* ((,st (,(adt-sym-pre "RESIZE-" rows) 0 ,st))
               (,st (,(adt-sym-pre "RESIZE-" ppages) 0 ,st))
               (,st (,(adt-sym-pre "UPDATE-" cnt) 0 ,st))
               (,st (,(adt-sym-pre "UPDATE-" fillf) 0 ,st))
               (,st (,(adt-sym-pre "UPDATE-" np) 0 ,st)))
          (,(adt-sym-pre "UPDATE-" nq) 0 ,st)))
      (defthm ,(adt-sym clear-c "-UNFOLDS")
        (equal (,clear-c c) (adt-pg-clear-c c))
        :hints (("Goal" :in-theory (enable ,clear-c adt-pg-clear-c resize-list))))
      (in-theory (disable ,count-of ,append-c ,clear-c)))))


; The fill-is-load theorems of a write-once paged instance, over the flat
; view (books/def-representation-paged.lisp, adt-pg-fill-is-load-*).
(defun adt-pg-once-set-thms (name fields schema-const)
  (cond ((endp fields) nil)
        ((eq (car (cadr (car fields))) :octets)
         (adt-pg-once-set-thms name (cdr fields) schema-const))
        (t (cons `(defthm ,(adt-sym3 name "$C-FILL-IS-LOAD-OF-SET-" (car (car fields)))
                    (implies (and (,(adt-sym name "$CORR") c a)
                                  (adt-fill-is-load ,schema-const (adt-pg-flat ,schema-const c) a)
                                  (natp i) (< i (len a)))
                             (adt-fill-is-load ,schema-const
                                               (adt-pg-flat ,schema-const
                                                            (,(adt-sym3 name "$C-SET-" (car (car fields))) i v c))
                                               (,(adt-sym3 name "$A-SET-" (car (car fields))) i v a)))
                    :hints (("Goal" :in-theory (enable ,(adt-sym name "$CORR")
                                                       ,(adt-sym3 name "$A-SET-" (car (car fields)))))))
                 (adt-pg-once-set-thms name (cdr fields) schema-const)))))

(defun adt-pg-once-events (name fields trees schema-const)
  (let ((st (adt-sym name "$C")) (a (adt-sym name "$A")) (corr (adt-sym name "$CORR")))
    `((defthm ,(adt-sym name "$C-FILL-IS-LOAD-OF-CREATE")
        (adt-fill-is-load ,schema-const (adt-pg-flat ,schema-const (,(adt-sym-pre "CREATE-" st)))
                          (,(adt-sym-pre "CREATE-" a)))
        :hints (("Goal" :in-theory (enable ,(adt-sym-pre "CREATE-" a)))))
      (defthm ,(adt-sym name "$C-FILL-IS-LOAD-OF-APPEND")
        (implies (and (,corr c a) (adt-fill-is-load ,schema-const (adt-pg-flat ,schema-const c) a))
                 (adt-fill-is-load ,schema-const (adt-pg-flat ,schema-const (,(adt-sym name "$C-APPEND") rec c))
                                   (,(adt-sym name "$A-APPEND") rec a)))
        :hints (("Goal" :in-theory (e/d (,corr ,(adt-sym name "$A-APPEND"))
                                        (adt-pg-append-c-is-room-then-append)))))
      ,@(and trees
             `((defthm ,(adt-sym name "$C-FILL-IS-LOAD-OF-APPEND-T")
                 (implies (and (,corr c a)
                               (adt-fill-is-load ,schema-const (adt-pg-flat ,schema-const c) a)
                               ,@(adt-tree-okp-terms fields trees 0))
                          (adt-fill-is-load ,schema-const (adt-pg-flat ,schema-const (,(adt-sym name "$C-APPEND-T") rec c))
                                            (,(adt-sym name "$A-APPEND-T") rec a)))
                 :hints (("Goal" :in-theory (e/d (,corr ,(adt-sym name "$A-APPEND-T") ,(adt-sym name "$A-APPEND"))
                                                 (,(adt-sym name "$C-APPEND") ,(adt-sym name "$C-APPEND-T")
                                                  ,(adt-sym name "$C-FILL-IS-LOAD-OF-APPEND")))
                          :use ((:instance ,(adt-sym name "$C-APPEND-T-IS-APPEND"))
                                (:instance ,(adt-sym name "$C-FILL-IS-LOAD-OF-APPEND")
                                           (rec (,(adt-sym name "-TREE-ENC") rec)))))))))
      ,@(adt-pg-once-set-thms name fields schema-const)
      (defthm ,(adt-sym name "$C-FILL-IS-LOAD-OF-CLEAR")
        (adt-fill-is-load ,schema-const (adt-pg-flat ,schema-const (,(adt-sym name "$C-CLEAR") c))
                          (,(adt-sym name "$A-CLEAR") a))
        :hints (("Goal" :in-theory (enable ,(adt-sym name "$A-CLEAR") adt-pg-clear-c)))))))

; The scalar instance (its comment is at the top of this file).
(defun rep-scalar-events (name fields invariant invariant-lemmas paged)
  (let* ((kind (cadr (car fields)))
         (schema-const (adt-sym-const name "-SCHEMA*"))
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
         (get-a (adt-sym name "$A-GET"))
         (set-a (adt-sym name "$A-SET"))
         (get-c (adt-sym3 name "$C-GET-" (car (car fields))))
         (set-c (adt-sym3 name "$C-SET-" (car (car fields))))
         (create-a (adt-sym-pre "CREATE-" a))
         (create-c (adt-sym-pre "CREATE-" st))
         (recog (adt-sym name "P"))
         (append-c1 (adt-sym name "$C-APPEND1"))
         (clear-a (adt-sym name "$A-CLEAR"))
         (clear-c (adt-sym name "$C-CLEAR"))
         (defabs
           `(defabsstobj ,name
              :foundation ,st
              :recognizer (,recog :logic ,ap :exec ,(adt-sym name "$CP"))
              :creator (,(adt-sym-pre "CREATE-" name) :logic ,create-a :exec ,create-c)
              :corr-fn ,corr
              :corr-fn-exists t
              :exports ((,(adt-sym name "-COUNT") :logic ,count-a :exec ,count-of)
                        (,(adt-sym name "-GET") :logic ,get-a :exec ,get-c)
                        (,(adt-sym name "-SET") :logic ,set-a :exec ,set-c :protect t)
                        (,(adt-sym name "-APPEND") :logic ,append-a :exec ,append-c1 :protect t)
                        (,(adt-sym name "-CLEAR") :logic ,clear-a :exec ,clear-c :protect t))))
         (ob-hints `(("Goal" :in-theory (enable ,corr ,ap ,create-a ,count-a ,append-a ,get-a ,set-a
                                                 ,clear-a ,append-c1 adt-scalar-seq-p adt-val-okp
                                                 ,@(and paged (list count-of))
                                                 ,@invariant-lemmas)))))
    `(encapsulate
       ()
       (local (in-theory (disable nth update-nth resize-list)))
       ; Paged (lane gate-b-2): the paged foundation, the same logical side.
       ,@(if paged
             (adt-pg-foundation-events name fields schema-const)
           `(,@(adt-foundation-events name fields schema-const nil (+ 3 p))
             (defthm ,(adt-sym create-c "-IS-CANONICAL-EMPTY")
               (equal (,create-c) (adt-empty-c ,schema-const))
               :hints (("Goal" :in-theory (enable adt-empty-c))))))
       ; The one-record append, over the field value.
       (defun ,append-c1 (v ,st)
         (declare (xargs :stobjs ,st :guard (adt-val-okp ',kind v)
                         :guard-hints (("Goal" :in-theory (enable adt-rec-p-of-list1)))))
         (,append-c (list v) ,st))
       ; The logical side: the list of values.
       (defun ,ap (,a)
         (declare (xargs :guard t))
         (and (adt-scalar-seq-p ',kind ,a)
              ,@(if invariant `((,invariant ,a)) nil)))
       (defun ,create-a ()
         (declare (xargs :guard t))
         nil)
       (defun ,count-a (,a)
         (declare (xargs :guard (,ap ,a)))
         (len ,a))
       (defun ,get-a (i ,a)
         (declare (xargs :guard (and (,ap ,a) (natp i) (< i (,count-a ,a)))))
         (nth i ,a))
       (defun ,set-a (i v ,a)
         (declare (xargs :guard (and (,ap ,a) (natp i) (< i (,count-a ,a)) (adt-val-okp ',kind v))))
         (update-nth i v ,a))
       (defun ,append-a (v ,a)
         (declare (xargs :guard (and (,ap ,a) (adt-val-okp ',kind v))))
         (append ,a (list v)))
       (defun ,clear-a (,a)
         (declare (xargs :guard (,ap ,a)) (ignore ,a))
         nil)
       (defun ,corr (c a)
         (declare (xargs :guard t :verify-guards nil))
         ,(if paged
              `(adt-pg-corr ,schema-const *adt-pg-rows* *adt-pg-octets* c (adt-wrap1 a))
            `(adt-corr ,schema-const c (adt-wrap1 a))))
       (make-event
        (er-let* ((missing (defabsstobj-missing-events ,@(cdr defabs))))
          (value (cons 'progn (adt-obligation-thms missing ',ob-hints (w state))))))
       ,defabs
       (defthm ,(adt-sym name "-COUNT-IS-LEN")
         (equal (,(adt-sym name "-COUNT") ,name) (len ,name))
         :hints (("Goal" :in-theory (enable ,count-a))))
       (defthm ,(adt-sym name "-GET-IS-NTH")
         (equal (,(adt-sym name "-GET") i ,name) (nth i ,name))
         :hints (("Goal" :in-theory (enable ,get-a))))
       (defthm ,(adt-sym name "-SET-IS-UPDATE-NTH")
         (equal (,(adt-sym name "-SET") i v ,name) (update-nth i v ,name))
         :hints (("Goal" :in-theory (enable ,set-a))))
       (defthm ,(adt-sym name "-APPEND-IS-APPEND")
         (equal (,(adt-sym name "-APPEND") v ,name) (append ,name (list v)))
         :hints (("Goal" :in-theory (enable ,append-a))))
       (defthm ,(adt-sym name "-CLEAR-IS-NIL")
         (equal (,(adt-sym name "-CLEAR") ,name) nil)
         :hints (("Goal" :in-theory (enable ,clear-a))))
       (defthm ,(adt-sym recog "-IS-SCALAR-SEQ-P")
         (equal (,recog x) (and (adt-scalar-seq-p ',kind x)
                                ,@(if invariant `((,invariant x)) nil)))
         :hints (("Goal" :in-theory (enable ,ap)))))))

; The paged sequence instance: `defadt-fn-trees-once''s skeleton over the
; paged foundation.  Its logical side, exports and -IS- theorems are the
; columnar instance's (the same generator functions).

; A paged instance with :tree fields (books/def-representation-tree.lisp):
; the checked put of one octet at the fill (NAME$C-POOL-PUT, bridged to
; `adt-pg-cput'), the walk over it (the columnar instance's six writers,
; `adt-tree-walk-defuns', whose meaning is the generic writer's by
; functional instance), each tree field's put (offset at the fill, the walk,
; the length; bridged to `adt-pg-put-tree'), and NAME$C-APPEND-T (bridged
; to `adt-pg-append-t-c'), which is NAME$C-APPEND of the encoded record by
; the library's `adt-pg-append-t-c-is-append-c'.

(defun adt-pg-tree-mask (fields trees)
  (if (endp fields)
      nil
    (cons (if (member-eq (car (car fields)) trees) t nil)
          (adt-pg-tree-mask (cdr fields) trees))))

(defun adt-pg-tree-fn-alist (name)
  ; the generic writer of books/def-representation-tree-walk.lisp -> this instance's
  (list (cons 'adt-h-put (adt-sym name "$C-POOL-PUT"))
        (cons 'adt-h-puts '(lambda (bytes c) (adt-pg-cputs bytes *adt-pg-octets* c)))
        (cons 'adt-h-tw-digits (adt-sym name "$C-TW-DIGITS"))
        (cons 'adt-h-tw-chars (adt-sym name "$C-TW-CHARS"))
        (cons 'adt-h-tw-bytes (adt-sym name "$C-TW-BYTES"))
        (cons 'adt-h-tw-ops (adt-sym name "$C-TW-OPS"))
        (cons 'adt-h-tw-atom (adt-sym name "$C-TW-ATOM"))
        (cons 'adt-h-tw-tree (adt-sym name "$C-TW-TREE"))))

(defun adt-pg-tree-load-terms (fields trees recv)
  (cond ((endp fields) nil)
        ((member-eq (car (car fields)) trees)
         (cons `(adt-tree-plen (car ,recv) 0) (adt-pg-tree-load-terms (cdr fields) trees `(cdr ,recv))))
        ((eq (car (cadr (car fields))) :octets)
         (cons `(len (car ,recv)) (adt-pg-tree-load-terms (cdr fields) trees `(cdr ,recv))))
        (t (adt-pg-tree-load-terms (cdr fields) trees `(cdr ,recv)))))

(defun adt-pg-tree-field-events (name fields trees ci)
  ; each tree field's put, bridged to `adt-pg-put-tree' at its columns
  (if (endp fields)
      nil
    (let* ((f (car (car fields)))
           (octp (eq (car (cadr (car fields))) :octets))
           (rest (adt-pg-tree-field-events name (cdr fields) trees (+ (if octp 2 1) ci))))
      (if (member-eq f trees)
          (let* ((st (adt-sym name "$C"))
                 (putt (adt-sym (adt-sym3 name "$C-PUT-FIELD-" f) "-TREE"))
                 (rput0 (adt-sym name (concatenate 'string "$C-RPUT" (adt-pg-num ci))))
                 (rput1 (adt-sym name (concatenate 'string "$C-RPUT" (adt-pg-num (+ 1 ci))))))
            (list* `(defun ,putt (n x ,st)
                      (declare (xargs :stobjs ,st :guard (and (natp n) (adt-tree-okp x))
                                      :guard-hints (("Goal" :in-theory (enable adt-elt-p)))))
                      (let* ((o (,(adt-sym name "$C-FILL") ,st))
                             (,st (,(adt-sym name "$C-TW-TREE") x 0 ,st))
                             (,st (,rput0 n o ,st)))
                        (,rput1 n (adt-tree-plen x 0) ,st)))
                   `(defthm ,(adt-sym putt "-UNFOLDS")
                      (equal (,putt n x c) (adt-pg-put-tree ,ci n x *adt-pg-rows* *adt-pg-octets* c))
                      :hints (("Goal" :in-theory (enable ,putt adt-pg-put-tree
                                                         ,(adt-sym name "$C-TW-TREE-IS-CPUTS")))))
                   `(in-theory (disable ,putt))
                   rest))
        rest))))

(defun adt-pg-tree-putt-bridges (name fields trees)
  (cond ((endp fields) nil)
        ((member-eq (car (car fields)) trees)
         (cons (adt-sym (adt-sym (adt-sym3 name "$C-PUT-FIELD-" (car (car fields))) "-TREE") "-UNFOLDS")
               (adt-pg-tree-putt-bridges name (cdr fields) trees)))
        (t (adt-pg-tree-putt-bridges name (cdr fields) trees))))

(defun adt-pg-tree-exec-events (name fields trees schema-const)
  (let* ((st (adt-sym name "$C"))
         (put (adt-sym name "$C-POOL-PUT"))
         (fillf (adt-sym name "$C-FILL"))
         (tree (adt-sym name "$C-TW-TREE"))
         (enc (adt-sym name "-TREE-ENC"))
         (append-t (adt-sym name "$C-APPEND-T"))
         (append-c (adt-sym name "$C-APPEND"))
         (mask (adt-pg-tree-mask fields trees))
         (dpg `(,(adt-sym-pre "CREATE-" (adt-sym name "$PG"))))
         (dpp `(,(adt-sym-pre "CREATE-" (adt-sym name "$PP"))))
         (walk (strip-cdrs (cddr (adt-pg-tree-fn-alist name))))
         (okps (adt-tree-okp-terms fields trees 0)))
    (append
     `((defun ,put (b ,st)
         (declare (xargs :stobjs ,st))
         (let ((fl (,fillf ,st)))
           (if (and (unsigned-byte-p 8 b) (natp fl) (< fl (* *adt-pg-octets* (,(adt-sym name "$C-NQ") ,st))))
               (let ((,st (,(adt-sym name "$C-PPUT") fl b ,st)))
                 (,(adt-sym-pre "UPDATE-" fillf) (+ 1 fl) ,st))
             ,st)))
       (defthm ,(adt-sym put "-UNFOLDS")
         (equal (,put b c) (adt-pg-cput b *adt-pg-octets* c))
         :hints (("Goal" :in-theory (enable ,put adt-pg-cput))))
       (in-theory (disable ,put))
       ,@(adt-tree-walk-defuns name put st)
       ,@(pairlis$ (make-list (len walk) :initial-element 'verify-guards)
                   (pairlis$ walk (make-list (len walk) :initial-element
                                             '(:hints (("Goal" :in-theory (disable floor)))))))
       (defthm ,(adt-sym tree "-IS-CPUTS")
         (equal (,tree x n c)
                (adt-pg-cputs (append (fn-scc-program x) (fn-scc-repeat (nfix n) *fn-scc-op-cons*))
                              *adt-pg-octets* c))
         :hints (("Goal" :in-theory (enable ,@walk ,(adt-sym put "-UNFOLDS") adt-pg-cputs)
                  :use ((:functional-instance adt-h-tw-tree-is-puts
                                              ,@(pairlis$ (strip-cars (adt-pg-tree-fn-alist name))
                                                          (pairlis$ (strip-cdrs (adt-pg-tree-fn-alist name)) nil)))))))
       (in-theory (disable ,@walk)))
     (adt-pg-tree-field-events name fields trees 0)
     `((defun ,enc (rec)
         (declare (xargs :guard (and (true-listp rec) ,@okps)
                         :guard-hints (("Goal" :in-theory (enable adt-tree-okp-is-sccb-treep)))))
         (list ,@(adt-tree-enc-terms fields trees 0)))
       (defthm ,(adt-sym enc "-IS-TMASK-ENC")
         (equal (,enc rec) (adt-pg-tmask-enc ',mask rec))
         :hints (("Goal" :in-theory (enable ,enc adt-pg-tmask-enc))))
       (defun ,append-t (rec ,st)
         (declare (xargs :stobjs ,st
                         :guard (and (true-listp rec) ,@okps (adt-rec-p ,schema-const (,enc rec)))
                         :guard-hints (("Goal" :in-theory (enable ,enc adt-rec-p-open adt-schema-fns-of-atom)))))
         (let* ((,st (,(adt-sym name "$C-ROWROOM") ,st))
                (,st (,(adt-sym name "$C-POOLROOM") (+ (,fillf ,st) ,@(adt-pg-tree-load-terms fields trees 'rec)) ,st))
                (n (,(adt-sym name "$C-COUNT") ,st))
                ,@(adt-append-t-body name fields trees 'rec st))
           (,(adt-sym-pre "UPDATE-" (adt-sym name "$C-COUNT")) (+ 1 n) ,st)))
       (defthm ,(adt-sym append-t "-UNFOLDS")
         (equal (,append-t rec c)
                (adt-pg-append-t-c ,schema-const ',mask rec *adt-pg-rows* *adt-pg-octets* ,dpg ,dpp c))
         :hints (("Goal" :in-theory (enable ,append-t adt-pg-append-t-c adt-pg-append-room
                                            adt-pg-append-fields-t adt-pg-tmask-enc adt-rec-load
                                            ,@(adt-pg-putf-bridges name fields)
                                            ,@(adt-pg-tree-putt-bridges name fields trees)))))
       (defthm ,(adt-sym append-t "-IS-APPEND")
         (implies (and (adt-pg-corr ,schema-const *adt-pg-rows* *adt-pg-octets* c a) ,@okps)
                  (equal (,append-t rec c) (,append-c (,enc rec) c)))
         :hints (("Goal" :in-theory (e/d (,(adt-sym append-t "-UNFOLDS") ,(adt-sym append-c "-UNFOLDS")
                                          ,(adt-sym enc "-IS-TMASK-ENC") adt-tree-okp-is-sccb-treep
                                          adt-pg-tmask-okp adt-pg-tmask-kinds-okp)
                                         (,append-t ,append-c ,enc adt-pg-tmask-enc))
                  :use ((:instance adt-pg-append-t-c-is-append-c
                                   (s ,schema-const) (mask ',mask) (r *adt-pg-rows*) (q *adt-pg-octets*)
                                   (d ,dpg) (dp ,dpp))))))
       (in-theory (disable ,append-t ,enc ,(adt-sym append-t "-UNFOLDS") ,(adt-sym enc "-IS-TMASK-ENC")))))))

(defun adt-pg-tree-logic-events (name trees fields schema-const)
  (let ((a (adt-sym name "$A")) (okps (adt-tree-okp-terms fields trees 0)))
    `((defun ,(adt-sym name "$A-APPEND-T") (rec ,a)
        (declare (xargs :guard (and (,(adt-sym name "$AP") ,a) (true-listp rec) ,@okps
                                    (adt-rec-p ,schema-const (,(adt-sym name "-TREE-ENC") rec)))))
        (append ,a (list (,(adt-sym name "-TREE-ENC") rec)))))))

(defun rep-pg-seq-events (name fields0 trees once)
  (let* ((fields (adt-norm-fields fields0))
         (schema-const (adt-sym-const name "-SCHEMA*"))
         (st (adt-sym name "$C"))
         (a (adt-sym name "$A"))
         (ap (adt-sym name "$AP"))
         (corr (adt-sym name "$CORR"))
         (count-of (adt-sym name "$C-COUNT-OF"))
         (append-c (adt-sym name "$C-APPEND"))
         (append-a (adt-sym name "$A-APPEND"))
         (count-a (adt-sym name "$A-COUNT"))
         (clear-a (adt-sym name "$A-CLEAR"))
         (clear-c (adt-sym name "$C-CLEAR"))
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
                        ,@(and trees
                               `((,(adt-sym name "-APPEND-T") :logic ,(adt-sym name "$A-APPEND-T")
                                  :exec ,(adt-sym name "$C-APPEND-T") :protect t)))
                        ,@(adt-exports-once name fields once)
                        (,(adt-sym name "-CLEAR") :logic ,clear-a :exec ,clear-c :protect t))))
         (ob-hints `(("Goal" :in-theory (enable ,corr ,ap ,create-a ,count-a ,append-a ,clear-a ,count-of
                                                 ,@(and trees (list (adt-sym name "$A-APPEND-T")))
                                                 ,@(adt-logic-names name fields))))))
    `(encapsulate
       ()
       (local (in-theory (disable nth update-nth resize-list)))
       ,@(adt-pg-foundation-events name fields schema-const)
       ,@(and trees (adt-pg-tree-exec-events name fields trees schema-const))
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
       (defun ,clear-a (,a)
         (declare (xargs :guard (,ap ,a)) (ignore ,a))
         nil)
       ,@(adt-field-logic-events name fields 0)
       ,@(and trees (adt-pg-tree-logic-events name trees fields schema-const))
       (defun ,corr (c a)
         (declare (xargs :guard t :verify-guards nil))
         (adt-pg-corr ,schema-const *adt-pg-rows* *adt-pg-octets* c a))
       ,@(and once (adt-pg-once-events name fields trees schema-const))
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
       ,@(and trees
              `((defthm ,(adt-sym name "-APPEND-T-IS-APPEND")
                  (equal (,(adt-sym name "-APPEND-T") rec ,name)
                         (append ,name (list (,(adt-sym name "-TREE-ENC") rec))))
                  :hints (("Goal" :in-theory (enable ,(adt-sym name "$A-APPEND-T")))))
                (defthm ,(adt-sym name "-TREE-ENC-IS-LIST")
                  (equal (,(adt-sym name "-TREE-ENC") rec)
                         (list ,@(adt-tree-enc-terms fields trees 0)))
                  :hints (("Goal" :in-theory (enable ,(adt-sym name "-TREE-ENC")))))))
       (defthm ,(adt-sym recog "-IS-SEQ-P")
         (equal (,recog x) (adt-seq-p ,schema-const x))
         :hints (("Goal" :in-theory (enable ,ap))))
       (defthm ,(adt-sym name "-CLEAR-IS-NIL")
         (equal (,(adt-sym name "-CLEAR") ,name) nil)
         :hints (("Goal" :in-theory (enable ,clear-a))))
       ,@(adt-is-thms-once name fields 0 once))))

; -----------------------------------------------------------------------------
; The attachment check and the form.

(defun rep-attached-ancestors (fns wrld)
  ; The functions among the ancestors of FNS (the functions the recognizer
  ; and correspondence will call) that have an attachment: what
  ; `defabsstobj' would refuse, found before anything is generated.
  (attached-fns (canonical-ancestors-lst fns wrld) wrld))

(defun rep-theorem-names-p (names wrld)
  (cond ((atom names) (null names))
        ((and (symbolp (car names)) (getpropc (car names) 'theorem nil wrld))
         (rep-theorem-names-p (cdr names) wrld))
        (t nil)))

; Every generated name is interned in NAME's package by construction:
; adt-sym and adt-sym3 follow their base symbol's package and adt-sym-pre
; the symbol it prefixes (books/proto/adt.lisp), so an instance in another
; package gets its foundation, exports and lemmas there, and the same
; spelling in two packages never collides.  (Codex t10 found the names
; interned in ACL2 and relocated them by a double expansion and a diff;
; deputy-1 2026-10-01 put the rule where the names are made.)
; A `(F :tree)' field is an :octets field (the schema and the logical value
; are unchanged) with the extra export NAME-APPEND-T (books/proto/adt.lisp,
; `adt-tree-exec-events'; books/def-representation-tree.lisp).
(defun rep-tree-names (fields0)
  (cond ((atom fields0) nil)
        ((eq (cadr (car fields0)) :tree)
         (cons (car (car fields0)) (rep-tree-names (cdr fields0))))
        (t (rep-tree-names (cdr fields0)))))

(defun rep-untree (fields0)
  (cond ((atom fields0) nil)
        ((eq (cadr (car fields0)) :tree)
         (cons (list (car (car fields0)) :octets) (rep-untree (cdr fields0))))
        (t (cons (car fields0) (rep-untree (cdr fields0))))))

(defun rep-instance-events (name fields1 scalar generic invariant invariant-lemmas once paged)
  (let* ((trees (rep-tree-names fields1))
         (fields0 (rep-untree fields1))
         (fields (adt-norm-fields fields0))
         (impl (if generic (adt-sym name "-COLS") name))
         (paged (if paged t nil))
         (instance (cond (scalar (rep-scalar-events impl fields invariant invariant-lemmas paged))
                         (paged (rep-pg-seq-events impl fields0 trees once))
                         (t (defadt-fn-trees-once impl fields0 trees once)))))
    `(progn
       ,instance
       ,@(if generic (rep-generic-events name impl fields scalar) nil)
       (table fn-generated ',name
              '(:def-representation :scalar ,scalar :generic ,generic
                :implementation ,impl :invariant ,invariant :trees ,trees
                :write-once ,once :paged ,paged)))))

(defun def-representation-fn (name fields0 scalar generic invariant invariant-lemmas once paged state)
  (declare (xargs :stobjs state))
  (let* ((wrld (w state))
         (ctx 'def-representation)
         (trees (rep-tree-names fields0))
         (fields (adt-norm-fields (rep-untree fields0)))
         (roots (append '(adt-corr adt-seq-p adt-scalar-seq-p)
                        (if invariant (list invariant) nil)))
         (attached (and (symbol-listp roots) (rep-attached-ancestors roots wrld))))
    (cond
     ((not (and (symbolp name) name))
      (er soft ctx "the name must be a non-nil symbol; ~x0 is not." name))
     ((or (atom fields) (not (adt-schemap (adt-schema-of fields))))
      (er soft ctx "~x0: the fields must be a non-empty list of (FIELD KIND) with KIND one of :u8 :u32 :u64 :bool :octets (:nat B) (:enum ...); ~x1 is not." name fields0))
     ((and trees (or scalar generic))
      (er soft ctx "~x0: a :tree field is supported without :scalar and :generic in this stage." name))
     ((and trees (not (function-symbolp 'adt-pg-append-t-c wrld)))
      (er soft ctx "~x0: a :tree field needs books/def-representation-tree.lisp included first (the writer and its theorems)." name))
     ((and scalar (not (equal (len fields) 1)))
      (er soft ctx "~x0: :scalar t needs exactly one field; ~x1 were given." name (len fields)))
     ((and invariant (not (and (symbolp invariant) (function-symbolp invariant wrld)
                                (equal (arity invariant wrld) 1))))
      (er soft ctx "~x0: :invariant ~x1 must be a unary function in the world." name invariant))
     (attached
      (er soft ctx "~x0: the recognizer or correspondence would reach ~&1, which ~#1~[has~/have~] an attachment; ACL2 refuses such an abstract stobj (:DOC stobj-attachment-restrictions).  Carry that part of the invariant beside the stobj (def-carried), not in it." name attached))
     ((and invariant (not (and invariant-lemmas (rep-theorem-names-p invariant-lemmas wrld))))
      (er soft ctx "~x0: :invariant ~x1 needs :invariant-lemmas naming theorems already proved (of the empty sequence, of an append, of a field update); ~x2 does not." name invariant invariant-lemmas))
     ((and once (or scalar generic))
      (er soft ctx "~x0: :write-once is supported without :scalar and :generic in this stage." name))
     ((not (booleanp once))
      (er soft ctx "~x0: :write-once takes t or nil; ~x1 is neither." name once))
     ((not (member-eq paged '(t nil :default)))
      (er soft ctx "~x0: :paged takes t or nil; ~x1 is neither." name paged))
     ((and invariant (not scalar))
      (er soft ctx "~x0: :invariant is supported with :scalar t in this stage." name))
     (t
      (value (rep-instance-events name fields0 scalar generic invariant invariant-lemmas once
                                  (not (eq paged nil))))))))

(defun rep-fields-of (args)
  (if (or (endp args) (keywordp (car args)))
      nil
    (cons (car args) (rep-fields-of (cdr args)))))

(defmacro def-representation (name &rest args)
  ; Fields come first; the keyword options after them.
  (let* ((fields (rep-fields-of args))
         (opts (nthcdr (len fields) args)))
    `(make-event
      (def-representation-fn ',name ',fields
        ',(cadr (assoc-keyword :scalar opts))
        ',(cadr (assoc-keyword :generic opts))
        ',(cadr (assoc-keyword :invariant opts))
        ',(cadr (assoc-keyword :invariant-lemmas opts))
        ',(cadr (assoc-keyword :write-once opts))
        ',(if (assoc-keyword :paged opts) (cadr (assoc-keyword :paged opts)) :default)
        state))))


(logic)
