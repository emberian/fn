; Additive same-parse size provenance for the resident checkpoint reader.
; This does not bound the existing whole-run summary source lift or fund
; the temporary annotation graph. Those are explicit producer obligations.
(in-package "ACL2")
(include-book "store-checkpoint-tables-reader")
(include-book "store-tree-size")
(local (include-book "arithmetic/top" :dir :system))

(defun fn-scsr-car (x)
  (declare (xargs :guard t))
  (if (consp x) (car x) nil))
(defun fn-scsr-cdr (x)
  (declare (xargs :guard t))
  (if (consp x) (cdr x) nil))

(defun fn-scsr-info-root (info)
  (declare (xargs :guard t))
  (if (consp info) (car info) nil))
(defun fn-scsr-info-leaf (carry)
  (declare (xargs :guard t))
  (list carry))
(defun fn-scsr-info-pair (a d)
  (declare (xargs :guard (and (fn-scs-carryp (fn-scsr-info-root a))
                              (fn-scs-carryp (fn-scsr-info-root d)))))
  (cons (fn-scs-cons (fn-scsr-info-root a) (fn-scsr-info-root d))
        (cons a d)))

(defun fn-scsr-pair-info (a d)
  (declare (xargs :guard t))
  (if (and (fn-scs-carryp (fn-scsr-info-root a))
           (fn-scs-carryp (fn-scsr-info-root d)))
      (fn-scsr-info-pair a d)
    nil))

; STEP constructs the actual retained value exactly once. The octet payload
; length comes from its successful consumed boundary minus its original
; prefix width cell, never a second READ-NAT or walk over the allocated leaf.
(defun fn-scsr-step (i end stack infos fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp end) (< i end)
                              (<= end (fn-octets-len fn-octets)))
                  :verify-guards nil))
  (let ((next (fn-sccr-step i end stack fn-octets))
        (op (fn-sccr-cell i fn-octets)))
    (if (not (consp next))
        (mv next nil)
      (if (equal op *fn-scc-op-cons*)
          (mv next (cons (fn-scsr-pair-info (fn-scsr-car (fn-scsr-cdr infos)) (fn-scsr-car infos))
                         (fn-scsr-cdr (fn-scsr-cdr infos))))
        (let* ((value (fn-scsr-car (fn-scsr-car next)))
               (carry
                (if (equal op *fn-scc-op-octets*)
                    (and (< (+ 1 i) end)
                         (natp (cdr next))
                         (let ((n (- (cdr next) (+ 2 i (fn-sccr-cell (+ 1 i) fn-octets)))))
                           (and (natp n) (fn-scs-octets n))))
                  (and (or (integerp value) (characterp value)
                           (stringp value) (symbolp value))
                       (fn-scs-atom value)))))
          (mv next (cons (and carry (fn-scsr-info-leaf carry)) infos)))))))

(verify-guards fn-scsr-step
 :hints (("Goal" :do-not-induct t :use fn-sccr-step-advances
          :in-theory (disable fn-sccr-step-advances fn-sccr-step))))

(defthm fn-scsr-step-result-is-existing-by-definition
  (equal (mv-nth 0 (fn-scsr-step i end stack infos fn-octets))
         (fn-sccr-step i end stack fn-octets))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-scsr-step))))

(local (defthm fn-scsr-slice-length
 (implies (and (natp i) (natp n) (<= i n))
  (equal (len (fn-oct-slice-list i n fn-octets)) (- n i)))
 :hints (("Goal" :induct (fn-oct-slice-list i n fn-octets)
          :in-theory (enable fn-oct-slice-list)))))
(local (defthm fn-scsr-read-nat-end-by-definition
 (implies (fn-sccr-read-nat i end fn-octets)
  (equal (cdr (fn-sccr-read-nat i end fn-octets))
         (+ 1 i (fn-sccr-cell i fn-octets))))
 :hints (("Goal" :in-theory (enable fn-sccr-read-nat)))))
(defthm fn-scsr-octet-consumed-length
 (implies (and (fn-octets-p fn-octets) (natp i) (natp end) (< i end)
               (<= end (len fn-octets))
               (equal (fn-sccr-cell i fn-octets) *fn-scc-op-octets*)
               (consp (fn-sccr-step i end stack fn-octets)))
  (equal (- (cdr (fn-sccr-step i end stack fn-octets))
            (+ 2 i (fn-sccr-cell (+ 1 i) fn-octets)))
         (len (car (car (fn-sccr-step i end stack fn-octets))))))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-sccr-read-nat-facts (i (+ 1 i))))
          :in-theory (e/d (fn-sccr-step)
                           (fn-sccr-read-nat fn-sccr-read-string
                            fn-sccr-cell fn-scc-le-value fn-scc-intern)))))

(local (defthm fn-scsr-slice-octet-listp
 (implies (and (fn-octets-p fn-octets) (natp i) (natp n) (<= i n)
               (<= n (len fn-octets)))
          (fn-scc-octet-listp (fn-oct-slice-list i n fn-octets)))
 :hints (("Goal" :induct (fn-oct-slice-list i n fn-octets)
          :in-theory (e/d (fn-oct-slice-list fn-scc-octet-listp
                             fn-scc-octetp fn-octets-get)
                           (fn-oct-slice-list-is-take-nthcdr))))))
(local (defthm fn-scsr-slice-canonical-size
 (implies (and (fn-octets-p fn-octets) (natp a) (natp n)
               (<= (+ a n) (len fn-octets)))
  (equal (fn-scs-octets n)
         (fn-scs-summary (fn-oct-slice-list a (+ a n) fn-octets))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-scs-octets-establishes-canonical-size
                                 (xs (fn-oct-slice-list a (+ a n) fn-octets))))
          :in-theory (disable fn-oct-slice-list-is-take-nthcdr
                              fn-oct-slice-list fn-scs-octets fn-scs-summary)))))

(defthm fn-scsr-octet-carry-is-actual-canonical-size
 (implies (and (fn-octets-p fn-octets) (natp i) (natp end) (< i end)
               (<= end (len fn-octets))
               (equal (fn-sccr-cell i fn-octets) *fn-scc-op-octets*)
               (consp (fn-sccr-step i end stack fn-octets)))
  (equal (fn-scsr-info-root (car (mv-nth 1 (fn-scsr-step i end stack infos fn-octets))))
         (fn-scs-summary (car (car (fn-sccr-step i end stack fn-octets))))))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-scsr-octet-consumed-length)
                (:instance fn-sccr-read-nat-facts (i (+ 1 i)))
                (:instance fn-scsr-slice-canonical-size
                           (a (+ 2 i (fn-sccr-cell (+ 1 i) fn-octets)))
                           (n (car (fn-sccr-read-nat (+ 1 i) end fn-octets)))))
          :in-theory (e/d (fn-scsr-step fn-scsr-info-root fn-scsr-info-leaf
                            fn-scsr-car fn-sccr-step)
                           (fn-sccr-read-nat fn-sccr-read-string fn-sccr-cell
                            fn-scc-le-value fn-scc-intern fn-scs-octets
                            fn-scs-summary fn-oct-slice-list-is-take-nthcdr)))))

(defun fn-scsr-info-provenancep (info x)
 (declare (xargs :measure (acl2-count x) :verify-guards nil))
 (if (not (fn-scs-carryp (fn-scsr-info-root info))) t
   (and (equal (fn-scsr-info-root info) (fn-scs-summary x))
        (if (consp (fn-scsr-cdr info))
            (let ((a (fn-scsr-car (fn-scsr-cdr info)))
                  (d (fn-scsr-cdr (fn-scsr-cdr info))))
              (and (consp x)
                   (fn-scs-carryp (fn-scsr-info-root a))
                   (fn-scs-carryp (fn-scsr-info-root d))
                   (fn-scsr-info-provenancep a (car x))
                   (fn-scsr-info-provenancep d (cdr x))))
          t))))

(defun fn-scsr-stack-provenancep (infos stack)
 (declare (xargs :verify-guards nil))
 (if (consp stack)
     (and (consp infos) (fn-scsr-info-provenancep (car infos) (car stack))
          (fn-scsr-stack-provenancep (cdr infos) (cdr stack)))
   (null infos)))

(local (defthm fn-scsr-provenance-valid-root
 (implies (and (fn-scsr-info-provenancep info x)
               (fn-scs-carryp (fn-scsr-info-root info)))
          (equal (fn-scsr-info-root info) (fn-scs-summary x)))
 :hints (("Goal" :expand ((fn-scsr-info-provenancep info x))))))

(local (defthm fn-scsr-pair-info-preserves-provenance
 (implies (and (fn-scsr-info-provenancep a x)
               (fn-scsr-info-provenancep d y))
          (fn-scsr-info-provenancep (fn-scsr-pair-info a d) (cons x y)))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-scsr-provenance-valid-root (info a))
                (:instance fn-scsr-provenance-valid-root (info d) (x y))
                (:instance fn-scs-cons-preserves-canonical-size
                           (a (fn-scsr-info-root a)) (d (fn-scsr-info-root d))))
          :expand ((fn-scsr-info-provenancep (fn-scsr-pair-info a d) (cons x y))
                   (fn-scsr-info-provenancep (list* (fn-scs-summary (cons x y)) a d)
                                           (cons x y))
                   (fn-scsr-info-provenancep nil (cons x y)))
          :in-theory (e/d (fn-scsr-pair-info fn-scsr-info-pair fn-scsr-info-root
                           fn-scsr-car fn-scsr-cdr)
                          (fn-scsr-info-provenancep fn-scs-summary))))))

(local (defthm fn-scsr-supported-scalar-summary
 (implies (or (integerp x) (characterp x) (stringp x) (symbolp x))
          (equal (fn-scs-atom x) (fn-scs-summary x)))
 :hints (("Goal" :use fn-scs-atom-establishes-summary))))

(defthm fn-scsr-step-preserves-partial-provenance
 (implies (and (fn-octets-p fn-octets) (natp i) (natp end) (< i end)
               (<= end (len fn-octets))
               (fn-scsr-stack-provenancep infos stack)
               (consp (fn-sccr-step i end stack fn-octets)))
          (fn-scsr-stack-provenancep
           (mv-nth 1 (fn-scsr-step i end stack infos fn-octets))
           (car (fn-sccr-step i end stack fn-octets))))
 :hints (("Goal" :do-not-induct t
          :use (fn-scsr-octet-carry-is-actual-canonical-size
                (:instance fn-scsr-pair-info-preserves-provenance
                           (a (cadr infos)) (d (car infos))
                           (x (cadr stack)) (y (car stack))))
          :expand ((fn-scsr-stack-provenancep infos stack)
                   (fn-scsr-stack-provenancep (cdr infos) (cdr stack)))
          :in-theory (e/d (fn-scsr-step fn-sccr-step fn-scsr-stack-provenancep
                            fn-scsr-info-leaf fn-scsr-info-provenancep
                            fn-scsr-info-root fn-scsr-car fn-scsr-cdr)
                           (fn-scs-summary fn-scs-atom fn-scs-octets
                            fn-sccr-read-nat fn-sccr-read-string fn-sccr-cell
                            fn-scc-intern fn-scsr-pair-info
                            fn-oct-slice-list-is-take-nthcdr)))))

; The original reference lookup projects an article/composite payload from
; the raw P row. Its annotation must follow that same fixed field selection.
; Walk at most the literal field index (4 or 6), never the selected payload.
(defun fn-scsr-info-field (n info)
 (declare (xargs :guard (natp n) :measure (nfix n)))
 (if (and (fn-scs-carryp (fn-scsr-info-root info))
          (consp (fn-scsr-cdr info)))
     (if (zp n) (fn-scsr-car (fn-scsr-cdr info))
       (fn-scsr-info-field (1- n) (fn-scsr-cdr (fn-scsr-cdr info))))
   nil))
(defun fn-scsr-payload-info (value info)
 (declare (xargs :guard t))
 (cond ((not (consp value)) nil)
       ((stringp (fn-sco-at 3 value)) (fn-scsr-info-field 4 info))
       ((consp (fn-sco-at 6 value)) (fn-scsr-info-field 6 info))
       (t info)))

(defun fn-sctsr-step (i end stack infos table info-table fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp end) (< i end)
                              (<= end (fn-octets-len fn-octets)))
                  :verify-guards nil))
  (if (equal (fn-sccr-cell i fn-octets) *fn-sct-op-ref*)
      (let ((n (fn-sccr-read-nat (+ 1 i) end fn-octets)))
        (if (not n)
            (mv nil nil)
          (let* ((raw (fn-cei-get (car n) table))
                 (v (fn-sct-payload-of raw)))
            (if (not v) (mv :dangling nil)
              (mv (cons (cons v stack) (cdr n))
                  (cons (fn-scsr-payload-info raw (fn-cei-get (car n) info-table))
                        infos))))))
    (fn-scsr-step i end stack infos fn-octets)))

(defthm fn-sctsr-step-result-is-existing-by-definition
  (equal (mv-nth 0 (fn-sctsr-step i end stack infos table info-table fn-octets))
         (fn-sctr-step i end stack table fn-octets))
  :rule-classes nil
  :hints (("Goal" :use fn-scsr-step-result-is-existing-by-definition
           :in-theory (enable fn-sctsr-step fn-sctr-step fn-sct-ref-get))))

(local (defthm fn-sctsr-step-projection-rewrite
  (equal (mv-nth 0 (fn-sctsr-step i end stack infos table info-table fn-octets))
         (fn-sctr-step i end stack table fn-octets))
  :hints (("Goal" :use fn-sctsr-step-result-is-existing-by-definition))))

; Work remains the existing finite source region; this run is not the new
; bounded/yielding summary source lift. Its metadata is allocated beside the
; actual retained decoder stack and must be admitted before consumption.
(defun fn-sctsr-run (i end stack infos table info-table fn-octets)
  (declare (xargs :stobjs fn-octets :verify-guards nil
                  :guard (and (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets)))
                  :measure (nfix (- end i))
                  :hints (("Goal"
                           :use ((:instance fn-sctsr-step-result-is-existing-by-definition))
                           :in-theory (disable fn-sctsr-step)))))
  (if (or (not (natp i)) (not (natp end)) (>= i end))
      (mv stack infos)
    (mv-let (next next-infos)
      (fn-sctsr-step i end stack infos table info-table fn-octets)
      (cond ((eq next :dangling) (mv :dangling nil))
            ((and (consp next)
                  (mbt (and (natp (cdr next)) (< i (cdr next)) (<= (cdr next) end))))
             (fn-sctsr-run (cdr next) end (car next) next-infos table info-table fn-octets))
            (t (mv :refused nil))))))

(defthm fn-sctsr-run-result-is-existing-by-definition
  (equal (mv-nth 0 (fn-sctsr-run i end stack infos table info-table fn-octets))
         (fn-sctr-run i end stack table fn-octets))
  :rule-classes nil
  :hints (("Goal" :induct (fn-sctsr-run i end stack infos table info-table fn-octets)
           :in-theory (e/d (fn-sctsr-run fn-sctr-run) (fn-sctsr-step fn-sctr-step)))))

(defun fn-sctsr-decode-rows (start end table info-table fn-octets)
  (declare (xargs :stobjs fn-octets :verify-guards nil
                  :guard (and (natp start) (natp end) (<= start end)
                              (<= end (fn-octets-len fn-octets)))))
  (mv-let (st infos) (fn-sctsr-run start end nil nil table info-table fn-octets)
    (cond ((true-listp st) (mv (list :ok (reverse st)) (reverse infos)))
          ((eq st :dangling) (mv (list :refused :ref) nil))
          (t (mv (list :refused :tree) nil)))))

(defthm fn-sctsr-decode-rows-result-is-existing-by-definition
  (equal (mv-nth 0 (fn-sctsr-decode-rows start end table info-table fn-octets))
         (fn-sctr-decode-rows start end table fn-octets))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-sctsr-run-result-is-existing-by-definition
                                   (i start) (stack nil) (infos nil)))
           :in-theory (e/d (fn-sctsr-decode-rows fn-sctr-decode-rows)
                           (fn-sctsr-run fn-sctr-run)))))

(defun fn-scsr-info-index-aux (infos ordinal trie)
  (declare (xargs :guard (natp ordinal)))
  (if (consp infos)
      (fn-scsr-info-index-aux
       (cdr infos) (1+ ordinal)
       (if (fn-cp-uintp ordinal)
           (fn-cei-put-digits (fn-cbor-u32-bytes ordinal) (car infos) trie)
         trie))
    (list trie nil ordinal)))
(defun fn-scsr-info-index (infos)
  (declare (xargs :guard t))
  (fn-scsr-info-index-aux infos 0 nil))

; P annotations are inserted under the same ordinal keys as actual P values.
; References reuse them; they never rebuild or inspect the referenced graph.
; F and E keep their original decoder, while P and R use the sized decoder.
(defun fn-sctsr-decode-programs (fa fb pa pb ea eb ra rb fn-octets)
  (declare (xargs :stobjs fn-octets :verify-guards nil
                  :guard (and (natp fa) (natp fb) (<= fa fb) (<= fb (fn-octets-len fn-octets))
                              (natp pa) (natp pb) (<= pa pb) (<= pb (fn-octets-len fn-octets))
                              (natp ea) (natp eb) (<= ea eb) (<= eb (fn-octets-len fn-octets))
                              (natp ra) (natp rb) (<= ra rb) (<= rb (fn-octets-len fn-octets)))))
  (let ((f (fn-sctr-decode-rows fa fb nil fn-octets)))
    (if (not (eq (car f) :ok)) (mv f nil nil)
      (let ((frows (cadr f)))
        (if (not (and (consp frows) (null (cdr frows)) (fn-sct-f-rowp (car frows))))
            (mv (list :refused :f-row) nil nil)
          (let* ((frow (car frows)) (s (cadr frow)))
            (mv-let (p pinfos) (fn-sctsr-decode-rows pa pb nil nil fn-octets)
              (if (not (eq (car p) :ok)) (mv p nil nil)
                (if (not (equal (len (cadr p)) s)) (mv (list :refused :close) nil nil)
                  (let* ((table (fn-cei-build (cadr p)))
                         (info-table (fn-scsr-info-index pinfos))
                         (e (fn-sctr-decode-rows ea eb table fn-octets)))
                    (if (not (eq (car e) :ok)) (mv e nil nil)
                      (if (not (equal (len (cadr e)) s)) (mv (list :refused :close) nil nil)
                        (mv-let (r rinfos) (fn-sctsr-decode-rows ra rb table info-table fn-octets)
                          (if (not (eq (car r) :ok)) (mv r nil nil)
                            (if (not (equal (len (cadr r)) 4)) (mv (list :refused :close) nil nil)
                              (mv (list :ok (list frow (cadr p) (cadr e) (cadr r)))
                                  (fn-scsr-car (fn-scsr-cdr rinfos))
                                  (list :summary-region ra rb :R 1)))))))))))))))))

(local (defthm fn-sctsr-decode-rows-projection-rewrite
 (equal (mv-nth 0 (fn-sctsr-decode-rows start end table info-table fn-octets))
        (fn-sctr-decode-rows start end table fn-octets))
 :hints (("Goal" :use fn-sctsr-decode-rows-result-is-existing-by-definition))))
(defthm fn-sctsr-decode-programs-result-is-existing-by-definition
 (equal (mv-nth 0 (fn-sctsr-decode-programs fa fb pa pb ea eb ra rb fn-octets))
        (fn-sctr-decode-programs fa fb pa pb ea eb ra rb fn-octets))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-sctsr-decode-programs fn-sctr-decode-programs)
                                 (fn-sctsr-decode-rows fn-sctr-decode-rows
                                  fn-cei-build fn-sct-f-rowp)))))
(verify-guards fn-sctsr-step
 :hints (("Goal" :use ((:instance fn-sccr-read-nat-facts (i (+ 1 i))))
          :in-theory (disable fn-sccr-read-nat-facts fn-sccr-read-nat fn-sccr-step))))
(verify-guards fn-sctsr-run
 :hints (("Goal" :use (fn-sctsr-step-result-is-existing-by-definition
                       fn-sctr-step-advances)
          :in-theory (disable fn-sctsr-step fn-sctr-step))))

(defun fn-scsr-select-fields (n info)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      (mv nil (and (consp info) (null (cdr info))
                   (equal (fn-scsr-info-root info) (fn-scs-atom nil))))
    (if (and (consp info) (consp (cdr info))
             (fn-scs-carryp (fn-scsr-info-root (cadr info))))
        (mv-let (fields usable)
          (fn-scsr-select-fields (1- n) (cddr info))
          (mv (cons (fn-scsr-info-root (cadr info)) fields) usable))
      (mv nil nil))))
(defun fn-sctsr-original-context-carries (info)
  (declare (xargs :guard t))
  (mv-let (fields usable) (fn-scsr-select-fields 6 info)
    (if (and usable (fn-scs-carryp (fn-scsr-info-root info)))
        (mv :ready (fn-scsr-info-root info) fields)
      (mv :unavailable nil nil))))

(local (defun fn-scsr-select-provenance-ind (n info x)
 (declare (xargs :measure (nfix n)))
 (if (zp n) (list info x)
   (fn-scsr-select-provenance-ind (1- n) (fn-scsr-cdr (fn-scsr-cdr info)) (cdr x)))))
(defthm fn-scsr-select-fields-preserves-provenance
 (implies (and (natp n) (true-listp x) (equal (len x) n)
               (fn-scsr-info-provenancep info x)
               (fn-scs-carryp (fn-scsr-info-root info))
               (mv-nth 1 (fn-scsr-select-fields n info)))
          (fn-scs-correspondsp (mv-nth 0 (fn-scsr-select-fields n info)) x))
 :hints (("Goal" :induct (fn-scsr-select-provenance-ind n info x)
          :in-theory (e/d (fn-scsr-select-fields fn-scsr-info-provenancep
                           fn-scsr-info-root fn-scsr-car fn-scsr-cdr
                           fn-scs-correspondsp)
                          (fn-scs-summary fn-scs-atom fn-scs-carryp)))))

(defthm fn-sctsr-original-context-ready-has-exact-carries
 (implies (and (true-listp ctx) (equal (len ctx) 6)
               (fn-scsr-info-provenancep info ctx)
               (equal (mv-nth 0 (fn-sctsr-original-context-carries info)) :ready))
          (and (equal (mv-nth 1 (fn-sctsr-original-context-carries info))
                      (fn-scs-summary ctx))
               (fn-scs-correspondsp
                (mv-nth 2 (fn-sctsr-original-context-carries info)) ctx)))
 :hints (("Goal" :use ((:instance fn-scsr-select-fields-preserves-provenance
                         (n 6) (x ctx))
                       (:instance fn-scsr-provenance-valid-root (x ctx)))
          :in-theory (e/d (fn-sctsr-original-context-carries)
                          (fn-scsr-select-fields fn-scsr-info-provenancep
                           fn-scsr-select-fields-preserves-provenance
                           fn-scsr-provenance-valid-root fn-scs-correspondsp
                           fn-scs-summary fn-scs-carryp fn-scsr-info-root)))))

(defthm fn-scsr-info-field-preserves-provenance
 (implies (and (natp n) (fn-scsr-info-provenancep info x))
          (fn-scsr-info-provenancep (fn-scsr-info-field n info) (nth n x)))
 :hints (("Goal" :induct (fn-scsr-select-provenance-ind n info x)
          :in-theory (e/d (fn-scsr-info-field fn-scsr-info-provenancep
                           fn-scsr-info-root fn-scsr-car fn-scsr-cdr nth)
                          (fn-scs-summary fn-scs-carryp fn-scs-atom)))))

(local (defthm fn-sctsr-step-infos-true-listp
 (implies (true-listp infos)
          (true-listp (mv-nth 1 (fn-sctsr-step i end stack infos table info-table fn-octets))))
 :hints (("Goal" :in-theory (e/d (fn-sctsr-step fn-scsr-step fn-scsr-cdr)
                                (fn-sccr-step fn-sccr-read-nat fn-sccr-cell
                                 fn-sct-ref-get fn-cei-get fn-scsr-pair-info
                                 fn-scsr-info-leaf fn-scs-octets fn-scs-atom))))))
(local (defthm fn-sctsr-run-infos-true-listp
 (implies (true-listp infos)
          (true-listp (mv-nth 1 (fn-sctsr-run i end stack infos table info-table fn-octets))))
 :hints (("Goal" :induct (fn-sctsr-run i end stack infos table info-table fn-octets)
          :in-theory (e/d (fn-sctsr-run) (fn-sctsr-step))))))
(verify-guards fn-sctsr-decode-rows)
(verify-guards fn-sctsr-decode-programs)

(defun fn-sctsr-load (plan fn-octets)
  (declare (xargs :stobjs fn-octets :guard t :verify-guards nil))
  (let ((start (if (consp plan) (fn-sccr-at 1 (car plan)) 0)))
    (if (not (fn-sccr-planp plan start fn-octets))
        (mv (list :refused :layout) nil nil)
      (let ((h (and (consp plan) (fn-scc-parse-header (fn-sccr-at 0 (car plan))))))
        (if (not h) (mv (list :refused :header) nil nil)
          (let* ((s (nth 3 h)) (f (fn-sctr-next-run plan s fn-octets)))
            (if (not (eq (car f) :ok)) (mv f nil nil)
              (let ((p (fn-sctr-next-run (nth 3 f) s fn-octets)))
                (if (not (eq (car p) :ok)) (mv p nil nil)
                  (let ((e (fn-sctr-next-run (nth 3 p) s fn-octets)))
                    (if (not (eq (car e) :ok)) (mv e nil nil)
                      (let ((r (fn-sctr-next-run (nth 3 e) s fn-octets)))
                        (if (not (eq (car r) :ok)) (mv r nil nil)
                          (if (consp (nth 3 r)) (mv (list :refused :trailing) nil nil)
                            (mv-let (tables info region)
                              (fn-sctsr-decode-programs
                               (nth 1 f) (nth 2 f) (nth 1 p) (nth 2 p)
                               (nth 1 e) (nth 2 e) (nth 1 r) (nth 2 r) fn-octets)
                              (if (not (eq (car tables) :ok)) (mv tables nil nil)
                                (if (not (equal (fn-sco-at 1 (fn-sct-tables-f (cadr tables))) s))
                                    (mv (list :refused :close) nil nil)
                                  (mv tables info region)))))))))))))))))

)
(local (defthm fn-sctsr-decode-programs-projection-rewrite
 (equal (mv-nth 0 (fn-sctsr-decode-programs fa fb pa pb ea eb ra rb fn-octets))
        (fn-sctr-decode-programs fa fb pa pb ea eb ra rb fn-octets))
 :hints (("Goal" :use fn-sctsr-decode-programs-result-is-existing-by-definition))))
; The unchanged tables reader exports NEXT-RUN shape and RESTP facts.
; Its first-frame lemma is local, so expose only the needed local guard fact.
(local (defthm fn-sctsr-planp-first-frame-for-guards
 (implies (and (fn-sccr-planp plan pos fn-octets) (consp plan))
          (and (true-listp (car plan)) (consp (car plan))
               (fn-scc-octet-listp (car (car plan)))
               (fn-scc-octet-listp (fn-sccr-at 0 (car plan)))))
 :hints (("Goal" :expand ((fn-sccr-planp plan pos fn-octets))
          :in-theory (enable fn-sccr-framep)))))
(verify-guards fn-sctsr-load
 :hints (("Goal" :in-theory (disable fn-sctr-next-run fn-sctr-restp
                                    fn-scc-parse-header fn-sccr-planp fn-sccr-framep))))

(defthm fn-sctsr-load-result-is-existing-by-definition
 (equal (mv-nth 0 (fn-sctsr-load plan fn-octets)) (fn-sct-load plan fn-octets))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-sctsr-load fn-sct-load)
                                 (fn-sctsr-decode-programs fn-sctr-decode-programs
                                  fn-sctr-next-run fn-sccr-planp fn-scc-parse-header
                                  fn-sct-tables-f fn-sco-at)))))

(defthm fn-sctsr-load-existing-result-true-listp
 (true-listp (mv-nth 0 (fn-sctsr-load plan fn-octets)))
 :hints (("Goal" :use fn-sctsr-load-result-is-existing-by-definition
          :in-theory (e/d (fn-sct-load fn-sctr-next-run fn-sctr-run-decode fn-sctr-decode-programs)
                          (fn-sctsr-load fn-sccr-planp fn-scc-parse-header fn-sccr-join
                           fn-sctr-decode-rows fn-cei-build fn-sct-f-rowp)))))

(defthm fn-scsr-payload-info-preserves-provenance
 (implies (and (fn-scsr-info-provenancep info value)
               (fn-sct-payload-of value))
          (fn-scsr-info-provenancep (fn-scsr-payload-info value info)
                                   (fn-sct-payload-of value)))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-scsr-info-field-preserves-provenance (n 4) (x value))
                (:instance fn-scsr-info-field-preserves-provenance (n 6) (x value)))
          :in-theory (e/d (fn-scsr-payload-info fn-sct-payload-of
                           fn-sct-octets-or-nil fn-sco-at)
                          (fn-scsr-info-field fn-scsr-info-provenancep
                           fn-scsr-info-field-preserves-provenance
                           fn-scc-octets-valuep)))))

(defthm fn-sctsr-step-preserves-partial-provenance
 (implies
  (and (fn-octets-p fn-octets) (natp i) (natp end) (< i end)
       (<= end (len fn-octets)) (fn-scsr-stack-provenancep infos stack)
       (implies (equal (fn-sccr-cell i fn-octets) *fn-sct-op-ref*)
         (let ((ordinal (car (fn-sccr-read-nat (+ 1 i) end fn-octets))))
          (fn-scsr-info-provenancep (fn-cei-get ordinal info-table)
                                    (fn-cei-get ordinal table))))
       (consp (fn-sctr-step i end stack table fn-octets)))
  (fn-scsr-stack-provenancep
   (mv-nth 1 (fn-sctsr-step i end stack infos table info-table fn-octets))
   (car (fn-sctr-step i end stack table fn-octets))))
 :hints (("Goal" :do-not-induct t
          :use (fn-scsr-step-preserves-partial-provenance
                (:instance fn-scsr-payload-info-preserves-provenance
                 (value (fn-cei-get (car (fn-sccr-read-nat (+ 1 i) end fn-octets)) table))
                 (info (fn-cei-get (car (fn-sccr-read-nat (+ 1 i) end fn-octets)) info-table))))
          :in-theory (e/d (fn-sctsr-step fn-sctr-step fn-sct-ref-get
                           fn-scsr-stack-provenancep)
                          (fn-scsr-step fn-sccr-step fn-sccr-read-nat
                           fn-sccr-cell fn-cei-get fn-sct-payload-of
                           fn-scsr-payload-info fn-scsr-info-provenancep
                           fn-scsr-payload-info-preserves-provenance
                           fn-scsr-step-preserves-partial-provenance)))))

(local (defthm fn-scsr-info-index-aux-has-existing-sequence-trie
 (equal (car (fn-scsr-info-index-aux infos ordinal (fn-cei-sequence-trie index)))
        (fn-cei-sequence-trie (fn-cei-build-aux infos ordinal index)))
 :hints (("Goal" :induct (fn-cei-build-aux infos ordinal index)
          :in-theory (e/d (fn-scsr-info-index-aux fn-cei-build-aux
                           fn-cei-put fn-cei-sequence-trie)
                          (fn-cei-msgid-add fn-cei-put-digits fn-cp-uintp
                           fn-cbor-u32-bytes fn-cei-count fn-cei-msgid-trie))))))

(defthm fn-scsr-info-index-lookup-is-row
 (implies (and (true-listp infos)
               (<= (len infos) (1+ *fn-cbor-max-uint*)) (fn-cp-uintp ordinal))
          (equal (fn-cei-get ordinal (fn-scsr-info-index infos))
                 (if (< ordinal (len infos)) (nth ordinal infos) nil)))
 :hints (("Goal" :use ((:instance fn-cei-get-of-build-is-committed-event
                                  (events infos) (sequence ordinal))
                       (:instance fn-scsr-info-index-aux-has-existing-sequence-trie
                                  (ordinal 0) (index nil)))
          :in-theory (e/d (fn-scsr-info-index fn-cei-build fn-cei-get
                           fn-cei-sequence-trie)
                          (fn-scsr-info-index-aux fn-cei-build-aux fn-cei-get-digits
                           fn-cei-get-of-build-is-committed-event fn-cei-get-of-build-aux
                           fn-scsr-info-index-aux-has-existing-sequence-trie)))))

(local (defun fn-scsr-nth-provenance-ind (n infos rows)
 (declare (xargs :measure (nfix n)))
 (if (zp n) (list infos rows)
  (fn-scsr-nth-provenance-ind (1- n) (cdr infos) (cdr rows)))))

(local (defthm fn-scsr-stack-provenance-nth
 (implies (and (natp n) (fn-scsr-stack-provenancep infos rows))
          (fn-scsr-info-provenancep (nth n infos) (nth n rows)))
 :hints (("Goal" :induct (fn-scsr-nth-provenance-ind n infos rows)
          :in-theory (e/d (fn-scsr-stack-provenancep fn-scsr-info-provenancep
                           fn-scsr-info-root nth)
                          (fn-scs-summary fn-scs-carryp))))) )

(local (defthm fn-scsr-stack-provenance-list-shape
 (implies (and (true-listp rows) (fn-scsr-stack-provenancep infos rows))
          (and (true-listp infos) (equal (len infos) (len rows))))
 :hints (("Goal" :induct (fn-scsr-stack-provenancep infos rows)
          :in-theory (enable fn-scsr-stack-provenancep)))))

(defthm fn-scsr-built-dictionary-preserves-provenance
 (implies (and (true-listp rows) (fn-scsr-stack-provenancep infos rows)
               (<= (len rows) (1+ *fn-cbor-max-uint*)))
          (fn-scsr-info-provenancep
           (fn-cei-get ordinal (fn-scsr-info-index infos))
           (fn-cei-get ordinal (fn-cei-build rows))))
 :hints (("Goal" :do-not-induct t :cases ((fn-cp-uintp ordinal))
          :use (fn-scsr-stack-provenance-list-shape
                (:instance fn-scsr-stack-provenance-nth (n ordinal))
                (:instance fn-scsr-info-index-lookup-is-row)
                (:instance fn-cei-get-of-build-is-committed-event
                            (events rows) (sequence ordinal)))
          :in-theory (e/d (fn-cei-get)
                          (fn-cei-get-digits fn-scsr-info-index fn-cei-build
                           fn-scsr-info-provenancep fn-scsr-info-root
                           fn-scsr-stack-provenance-nth fn-scsr-stack-provenance-list-shape
                           fn-scsr-info-index-lookup-is-row
                           fn-cei-get-of-build-is-committed-event
                           fn-scsr-stack-provenancep fn-scs-summary fn-scs-carryp)))))

(local (defthm fn-scsr-get-is-sequence-trie-lookup
 (implies (equal (fn-cei-sequence-trie a) (fn-cei-sequence-trie b))
          (equal (fn-cei-get ordinal a) (fn-cei-get ordinal b)))
 :hints (("Goal" :in-theory (e/d (fn-cei-get) (fn-cei-get-digits fn-cei-sequence-trie))))))

(local (in-theory (disable fn-scsr-get-is-sequence-trie-lookup)))

(defthm fn-scsr-dictionary-trie-preserves-provenance
 (implies (and (true-listp rows) (fn-scsr-stack-provenancep row-infos rows)
               (<= (len rows) (1+ *fn-cbor-max-uint*))
               (equal table (fn-cei-build rows))
               (equal (fn-cei-sequence-trie info-table)
                      (fn-cei-sequence-trie (fn-scsr-info-index row-infos))))
          (fn-scsr-info-provenancep (fn-cei-get ordinal info-table)
                                    (fn-cei-get ordinal table)))
 :hints (("Goal" :use ((:instance fn-scsr-built-dictionary-preserves-provenance (infos row-infos))
                       (:instance fn-scsr-get-is-sequence-trie-lookup
                        (a info-table) (b (fn-scsr-info-index row-infos))))
          :in-theory (disable fn-scsr-info-provenancep fn-cei-get fn-cei-build
                              fn-scsr-info-index fn-cei-sequence-trie
                              fn-scsr-get-is-sequence-trie-lookup
                              fn-scsr-built-dictionary-preserves-provenance))))

(defthm fn-sctsr-run-preserves-partial-provenance
 (implies
  (and (fn-octets-p fn-octets) (natp i) (natp end) (<= i end)
       (<= end (len fn-octets)) (fn-scsr-stack-provenancep infos stack)
       (true-listp rows) (fn-scsr-stack-provenancep row-infos rows)
       (<= (len rows) (1+ *fn-cbor-max-uint*))
       (equal table (fn-cei-build rows))
       (equal (fn-cei-sequence-trie info-table)
              (fn-cei-sequence-trie (fn-scsr-info-index row-infos)))
       (true-listp (mv-nth 0 (fn-sctsr-run i end stack infos table info-table fn-octets))))
  (fn-scsr-stack-provenancep
   (mv-nth 1 (fn-sctsr-run i end stack infos table info-table fn-octets))
   (mv-nth 0 (fn-sctsr-run i end stack infos table info-table fn-octets))))
 :rule-classes nil
 :hints (("Goal" :induct (fn-sctsr-run i end stack infos table info-table fn-octets)
          :in-theory (e/d (fn-sctsr-run)
                          (fn-sctsr-step fn-sctr-step fn-cei-build fn-scsr-info-index
                           fn-scsr-get-is-sequence-trie-lookup fn-cei-sequence-trie
                           fn-scsr-stack-provenancep fn-scsr-info-provenancep fn-cei-get
                           fn-cp-uintp fn-sctsr-step-preserves-partial-provenance
                           fn-scsr-dictionary-trie-preserves-provenance)))
         ("Subgoal *1/3" :use
          ((:instance fn-sctsr-step-preserves-partial-provenance)
           (:instance fn-scsr-dictionary-trie-preserves-provenance
                        (ordinal (car (fn-sccr-read-nat (+ 1 i) end fn-octets))))))))

(local (defun fn-scsr-reverse-provenance-ind (infos rows ai ar)
 (if (consp rows)
     (fn-scsr-reverse-provenance-ind (cdr infos) (cdr rows)
                                    (cons (car infos) ai) (cons (car rows) ar))
   (list ai ar))))

(local (defthm fn-scsr-provenance-of-revappend
 (implies (and (fn-scsr-stack-provenancep infos rows)
               (fn-scsr-stack-provenancep ai ar))
          (fn-scsr-stack-provenancep (revappend infos ai) (revappend rows ar)))
 :hints (("Goal" :induct (fn-scsr-reverse-provenance-ind infos rows ai ar)
          :in-theory (enable fn-scsr-stack-provenancep revappend)))))

(local (defthm fn-scsr-provenance-of-reverse
 (implies (and (true-listp rows) (fn-scsr-stack-provenancep infos rows))
          (fn-scsr-stack-provenancep (reverse infos) (reverse rows)))
 :hints (("Goal" :use ((:instance fn-scsr-provenance-of-revappend (ai nil) (ar nil)))
          :in-theory (e/d (reverse) (fn-scsr-provenance-of-revappend
                                    fn-scsr-stack-provenancep))))))

(defthm fn-sctsr-decode-rows-preserves-partial-provenance
 (implies
  (and (fn-octets-p fn-octets) (natp start) (natp end) (<= start end)
       (<= end (len fn-octets))
       (true-listp rows) (fn-scsr-stack-provenancep row-infos rows)
       (<= (len rows) (1+ *fn-cbor-max-uint*))
       (equal table (fn-cei-build rows))
       (equal (fn-cei-sequence-trie info-table)
              (fn-cei-sequence-trie (fn-scsr-info-index row-infos)))
       (equal (car (mv-nth 0 (fn-sctsr-decode-rows start end table info-table fn-octets))) :ok))
  (fn-scsr-stack-provenancep
   (mv-nth 1 (fn-sctsr-decode-rows start end table info-table fn-octets))
   (cadr (mv-nth 0 (fn-sctsr-decode-rows start end table info-table fn-octets)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-sctsr-run-preserves-partial-provenance
                            (i start) (stack nil) (infos nil))
                (:instance fn-scsr-provenance-of-reverse
                  (infos (mv-nth 1 (fn-sctsr-run start end nil nil table info-table fn-octets)))
                  (rows (mv-nth 0 (fn-sctsr-run start end nil nil table info-table fn-octets)))))
          :in-theory (e/d (fn-sctsr-decode-rows)
                          (fn-sctsr-run fn-sctr-run fn-scsr-get-is-sequence-trie-lookup fn-cei-sequence-trie
                           fn-scsr-provenance-of-reverse fn-scsr-stack-provenancep)))))

(local (defthm fn-sctsr-decode-rows-ok-list-shape
 (implies (equal (car (mv-nth 0 (fn-sctsr-decode-rows start end table info-table fn-octets))) :ok)
          (true-listp (cadr (mv-nth 0 (fn-sctsr-decode-rows start end table info-table fn-octets)))))
 :hints (("Goal" :in-theory (e/d (fn-sctsr-decode-rows fn-sctr-decode-rows)
                                (fn-sctsr-run fn-sctr-run))))))

(local (defthm fn-scsr-nth-one-is-cadr
 (equal (nth 1 x) (cadr x))
 :hints (("Goal" :expand ((nth 1 x) (nth 0 (cdr x)))))))

(defthm fn-sctsr-decode-programs-original-context-provenance
 (implies
  (and (fn-octets-p fn-octets)
       (natp fa) (natp fb) (<= fa fb) (<= fb (len fn-octets))
       (natp pa) (natp pb) (<= pa pb) (<= pb (len fn-octets))
       (natp ea) (natp eb) (<= ea eb) (<= eb (len fn-octets))
       (natp ra) (natp rb) (<= ra rb) (<= rb (len fn-octets))
       (equal (car (mv-nth 0 (fn-sctsr-decode-programs fa fb pa pb ea eb ra rb fn-octets))) :ok)
       (<= (fn-sco-at 1 (fn-sct-tables-f
            (cadr (mv-nth 0 (fn-sctsr-decode-programs fa fb pa pb ea eb ra rb fn-octets)))))
           (1+ *fn-cbor-max-uint*)))
  (fn-scsr-info-provenancep
   (mv-nth 1 (fn-sctsr-decode-programs fa fb pa pb ea eb ra rb fn-octets))
   (cadr (nth 3 (cadr (mv-nth 0 (fn-sctsr-decode-programs fa fb pa pb ea eb ra rb fn-octets)))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-sctsr-decode-rows-ok-list-shape
                   (start pa) (end pb) (table nil) (info-table nil))
                (:instance fn-sctsr-decode-rows-preserves-partial-provenance
                  (start pa) (end pb) (rows nil) (row-infos nil) (table nil) (info-table nil))
                (:instance fn-sctsr-decode-rows-preserves-partial-provenance
                  (start ra) (end rb)
                  (rows (cadr (mv-nth 0 (fn-sctsr-decode-rows pa pb nil nil fn-octets))))
                  (row-infos (mv-nth 1 (fn-sctsr-decode-rows pa pb nil nil fn-octets)))
                  (table (fn-cei-build (cadr (mv-nth 0 (fn-sctsr-decode-rows pa pb nil nil fn-octets)))))
                  (info-table (fn-scsr-info-index (mv-nth 1 (fn-sctsr-decode-rows pa pb nil nil fn-octets)))))
                (:instance fn-scsr-stack-provenance-nth
                  (n 1)
                  (infos (mv-nth 1
                    (fn-sctsr-decode-rows ra rb
                     (fn-cei-build (cadr (mv-nth 0 (fn-sctsr-decode-rows pa pb nil nil fn-octets))))
                     (fn-scsr-info-index (mv-nth 1 (fn-sctsr-decode-rows pa pb nil nil fn-octets))) fn-octets)))
                  (rows (cadr (mv-nth 0
                    (fn-sctsr-decode-rows ra rb
                     (fn-cei-build (cadr (mv-nth 0 (fn-sctsr-decode-rows pa pb nil nil fn-octets))))
                     (fn-scsr-info-index (mv-nth 1 (fn-sctsr-decode-rows pa pb nil nil fn-octets))) fn-octets))))))
          :in-theory (e/d (fn-sctsr-decode-programs fn-scsr-car fn-scsr-cdr fn-sco-at fn-sct-tables-f)
                          (fn-sctsr-decode-rows fn-sctr-decode-rows fn-cei-build
                           fn-sct-log-positionp fn-sctsr-decode-rows-ok-list-shape
                           fn-scsr-info-index fn-scsr-stack-provenancep
                           fn-scsr-info-provenancep fn-scsr-stack-provenance-nth
                           fn-scsr-get-is-sequence-trie-lookup fn-cei-sequence-trie
                           fn-sctsr-decode-rows-projection-rewrite
                           fn-sctsr-decode-programs-projection-rewrite)))))

(defthm fn-sctsr-decode-programs-success-region
 (implies (equal (car (mv-nth 0 (fn-sctsr-decode-programs fa fb pa pb ea eb ra rb fn-octets))) :ok)
          (equal (mv-nth 2 (fn-sctsr-decode-programs fa fb pa pb ea eb ra rb fn-octets))
                 (list :summary-region ra rb :R 1)))
 :hints (("Goal" :in-theory (e/d (fn-sctsr-decode-programs)
                      (fn-sctsr-decode-rows fn-sctr-decode-rows fn-cei-build fn-scsr-info-index
                       fn-sct-f-rowp fn-scsr-car fn-scsr-cdr
                       fn-sctsr-decode-programs-projection-rewrite)))))
(defthm fn-sctsr-load-refusal-has-no-region
 (implies (not (equal (car (mv-nth 0 (fn-sctsr-load plan fn-octets))) :ok))
          (equal (mv-nth 2 (fn-sctsr-load plan fn-octets)) nil))
 :hints (("Goal" :in-theory (e/d (fn-sctsr-load fn-sctsr-decode-programs)
                      (fn-sctsr-decode-rows fn-sctr-decode-rows fn-cei-build fn-scsr-info-index
                       fn-sct-f-rowp fn-scsr-car fn-scsr-cdr fn-sccr-planp fn-scc-parse-header
                       fn-sctr-next-run fn-sct-tables-f fn-sco-at
                       fn-sctsr-decode-programs-projection-rewrite)))))

(in-theory (disable fn-scsr-info-root fn-scsr-info-leaf fn-scsr-info-pair
                    fn-scsr-pair-info fn-scsr-step fn-sctsr-step
                    fn-scsr-info-field fn-scsr-payload-info
                    fn-sctsr-run fn-sctsr-decode-rows fn-sctsr-decode-programs
                    fn-scsr-info-index-aux fn-scsr-info-index
                    fn-scsr-select-fields fn-sctsr-original-context-carries
                    fn-sctsr-load fn-scsr-car fn-scsr-cdr))
