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

(defun fn-sctsr-step (i end stack infos table info-table fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp end) (< i end)
                              (<= end (fn-octets-len fn-octets)))
                  :verify-guards nil))
  (if (equal (fn-sccr-cell i fn-octets) *fn-sct-op-ref*)
      (let ((n (fn-sccr-read-nat (+ 1 i) end fn-octets)))
        (if (not n)
            (mv nil nil)
          (let ((v (fn-sct-ref-get (car n) table)))
            (if (not v) (mv :dangling nil)
              (mv (cons (cons v stack) (cdr n))
                  (cons (fn-cei-get (car n) info-table) infos))))))
    (fn-scsr-step i end stack infos fn-octets)))

(defthm fn-sctsr-step-result-is-existing-by-definition
  (equal (mv-nth 0 (fn-sctsr-step i end stack infos table info-table fn-octets))
         (fn-sctr-step i end stack table fn-octets))
  :rule-classes nil
  :hints (("Goal" :use fn-scsr-step-result-is-existing-by-definition
           :in-theory (enable fn-sctsr-step fn-sctr-step))))

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
    (if (not (eq (car f) :ok)) (mv f nil)
      (let ((frows (cadr f)))
        (if (not (and (consp frows) (null (cdr frows)) (fn-sct-f-rowp (car frows))))
            (mv (list :refused :f-row) nil)
          (let* ((frow (car frows)) (s (cadr frow)))
            (mv-let (p pinfos) (fn-sctsr-decode-rows pa pb nil nil fn-octets)
              (if (not (eq (car p) :ok)) (mv p nil)
                (if (not (equal (len (cadr p)) s)) (mv (list :refused :close) nil)
                  (let* ((table (fn-cei-build (cadr p)))
                         (info-table (fn-scsr-info-index pinfos))
                         (e (fn-sctr-decode-rows ea eb table fn-octets)))
                    (if (not (eq (car e) :ok)) (mv e nil)
                      (if (not (equal (len (cadr e)) s)) (mv (list :refused :close) nil)
                        (mv-let (r rinfos) (fn-sctsr-decode-rows ra rb table info-table fn-octets)
                          (if (not (eq (car r) :ok)) (mv r nil)
                            (if (not (equal (len (cadr r)) 4)) (mv (list :refused :close) nil)
                              (mv (list :ok (list frow (cadr p) (cadr e) (cadr r)))
                                  (fn-scsr-car (fn-scsr-cdr rinfos))))))))))))))))))

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
        (mv (list :refused :layout) nil)
      (let ((h (and (consp plan) (fn-scc-parse-header (fn-sccr-at 0 (car plan))))))
        (if (not h) (mv (list :refused :header) nil)
          (let* ((s (nth 3 h)) (f (fn-sctr-next-run plan s fn-octets)))
            (if (not (eq (car f) :ok)) (mv f nil)
              (let ((p (fn-sctr-next-run (nth 3 f) s fn-octets)))
                (if (not (eq (car p) :ok)) (mv p nil)
                  (let ((e (fn-sctr-next-run (nth 3 p) s fn-octets)))
                    (if (not (eq (car e) :ok)) (mv e nil)
                      (let ((r (fn-sctr-next-run (nth 3 e) s fn-octets)))
                        (if (not (eq (car r) :ok)) (mv r nil)
                          (if (consp (nth 3 r)) (mv (list :refused :trailing) nil)
                            (mv-let (tables info)
                              (fn-sctsr-decode-programs
                               (nth 1 f) (nth 2 f) (nth 1 p) (nth 2 p)
                               (nth 1 e) (nth 2 e) (nth 1 r) (nth 2 r) fn-octets)
                              (if (not (eq (car tables) :ok)) (mv tables nil)
                                (if (not (equal (fn-sco-at 1 (fn-sct-tables-f (cadr tables))) s))
                                    (mv (list :refused :close) nil)
                                  (mv tables info)))))))))))))))))

)
(local (defthm fn-sctsr-decode-programs-projection-rewrite
 (equal (mv-nth 0 (fn-sctsr-decode-programs fa fb pa pb ea eb ra rb fn-octets))
        (fn-sctr-decode-programs fa fb pa pb ea eb ra rb fn-octets))
 :hints (("Goal" :use fn-sctsr-decode-programs-result-is-existing-by-definition))))
(defthm fn-sctsr-load-result-is-existing-by-definition
 (equal (mv-nth 0 (fn-sctsr-load plan fn-octets)) (fn-sct-load plan fn-octets))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-sctsr-load fn-sct-load)
                                 (fn-sctsr-decode-programs fn-sctr-decode-programs
                                  fn-sctr-next-run fn-sccr-planp fn-scc-parse-header
                                  fn-sct-tables-f fn-sco-at)))))

(in-theory (disable fn-scsr-info-root fn-scsr-info-leaf fn-scsr-info-pair
                    fn-scsr-pair-info fn-scsr-step fn-sctsr-step
                    fn-sctsr-run fn-sctsr-decode-rows fn-sctsr-decode-programs
                    fn-scsr-info-index-aux fn-scsr-info-index
                    fn-scsr-select-fields fn-sctsr-original-context-carries
                    fn-sctsr-load fn-scsr-car fn-scsr-cdr))
