; The admission list identifies each transaction workspace by its index.
; Recording the owner of every installed transaction lets the next fresh
; index distinguish its write even when a batch reuses an old row.
(in-package "ACL2")
(include-book "commit-admission-member-proof")
(fn2-book-layer :b)

(defun fn2-ctp-recorded-member-owners-p (rows admissions)
 (declare (xargs :verify-guards nil))
 (if (atom rows) t
  (let ((row (car rows)))
   (and (or (not (equal (car row) *fn2-commit-member-kind-txn*))
            (assoc-equal (- (nth 5 row) 3) admissions))
        (fn2-ctp-recorded-member-owners-p (cdr rows) admissions)))))

(defthm fn2-ctp-recorded-owner-of-member
 (implies (and (fn2-ctp-recorded-member-owners-p rows admissions)
               (member-equal row rows)
               (equal (car row) *fn2-commit-member-kind-txn*))
          (assoc-equal (- (nth 5 row) 3) admissions))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-ctp-recorded-member-owners-p rows admissions)
          :in-theory (disable assoc-equal))))

(defthm fn2-ctp-observed-range-contains-member
 (implies (and (natp i) (natp start) (natp count) (<= start i) (< i (+ start count)))
          (member-equal (fn2-ctp-member-fields i fn2-commit-member)
                        (fn2-ctp-member-fields-range start count fn2-commit-member)))
 :hints (("Goal" :induct (fn2-ctp-member-fields-range start count fn2-commit-member)
          :in-theory (disable fn2-ctp-member-fields))))

(defthm fn2-ctp-fresh-index-differs-from-member
 (implies (and (natp i) (not (assoc-equal i admissions))
               (natp r) (< r *fn2-commit-member-count*)
               (fn2-ctp-recorded-member-owners-p
                (fn2-ctp-member-fields-range 0 *fn2-commit-member-count* fn2-commit-member)
                admissions))
          (not (equal (fn2-ctp-member-fields r fn2-commit-member)
                      (list *fn2-commit-member-kind-txn* slot gen len 9 (+ 3 i) 5 event settled))))
 :hints (("Goal" :use ((:instance fn2-ctp-recorded-owner-of-member
                         (rows (fn2-ctp-member-fields-range 0 *fn2-commit-member-count* fn2-commit-member))
                         (row (fn2-ctp-member-fields r fn2-commit-member)))
                       (:instance fn2-ctp-observed-range-contains-member
                         (i r) (start 0) (count *fn2-commit-member-count*)))
          :in-theory (disable assoc-equal fn2-ctp-recorded-member-owners-p
                              fn2-ctp-member-fields fn2-ctp-member-fields-range
                              fn2-ctp-observed-range-contains-member))))

(defthm fn2-ctp-known-admission-stays-known
 (implies (assoc-equal i admissions) (assoc-equal i (append admissions new))))

(defthm fn2-ctp-appended-owner-is-known
 (implies (natp i) (assoc-equal i (append admissions (list (cons i entry)))))
 :hints (("Goal" :induct (len admissions))))

(defthm fn2-ctp-recorded-member-owners-grow
 (implies (fn2-ctp-recorded-member-owners-p rows admissions)
          (fn2-ctp-recorded-member-owners-p rows (append admissions new)))
 :hints (("Goal" :induct (fn2-ctp-recorded-member-owners-p rows admissions)
          :in-theory (disable assoc-equal))))

(defthm fn2-ctp-install-keeps-recorded-member-owners
 (let ((after (fn2-commit-member-put r (kind *fn2-commit-member-kind-txn*)
               (slot slot) (gen gen) (len len) (okind 9) (oslot oslot) (ogen 5)
               (entries 0) (entry-bytes 0) (schema 0) (event event) (settled settled))))
  (implies (and (natp r) (natp start) (< r (fn2-commit-member-rows fn2-commit-member))
                (assoc-equal (- oslot 3) admissions)
                (fn2-ctp-recorded-member-owners-p
                 (fn2-ctp-member-fields-range start count fn2-commit-member) admissions))
           (fn2-ctp-recorded-member-owners-p (fn2-ctp-member-fields-range start count after)
                                             admissions)))
 :hints (("Goal" :induct (fn2-ctp-member-fields-range start count fn2-commit-member)
          :in-theory (disable assoc-equal fn2-ctp-member-fields fn2-commit-member-rows))))

(defthm fn2-ctp-fresh-member-install-is-total
 (b* ((oslot (+ 3 i)) (admission (list i :ok batch event t records))
      ((mv code settled &) (fn2-cs-reserve 9 oslot 5 fn2-commit-settled))
      (after (fn2-commit-member-put r (kind *fn2-commit-member-kind-txn*)
              (slot slot) (gen gen) (len len) (okind 9) (oslot oslot) (ogen 5)
              (entries 0) (entry-bytes 0) (schema 0) (event event) (settled settled)))
      (before-rows (fn2-ctp-member-fields-range 0 *fn2-commit-member-count* fn2-commit-member))
      (after-rows (fn2-ctp-member-fields-range 0 *fn2-commit-member-count* after)))
  (implies (and (natp i) (not (assoc-equal i admissions))
                (fn2-ctp-recorded-member-owners-p before-rows admissions)
                (unsigned-byte-p 32 (fn2-commit-settled-rows fn2-commit-settled))
                (< 0 (fn2-cs-free-count 0 0 fn2-commit-settled))
                (unsigned-byte-p 32 oslot) (natp r) (< r *fn2-commit-member-count*)
                (< r (fn2-commit-member-rows fn2-commit-member)))
           (and (eq code :ok)
                (fn2-ctp-totalp code slot gen len oslot
                                (cons before-rows before-rest) (cons after-rows after-rest))
                (fn2-ctp-recorded-member-owners-p after-rows
                                                  (append admissions (list admission))))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-ctp-reserved-member-admission-observation
                                  (oslot (+ 3 i)))
                       (:instance fn2-ctp-fresh-index-differs-from-member
                                  (settled (mv-nth 1 (fn2-cs-reserve 9 (+ 3 i) 5 fn2-commit-settled)))))
          :in-theory (disable fn2-cs-reserve fn2-cs-free-count fn2-commit-settled-rows
                              fn2-ctp-totalp fn2-ctp-member-fields fn2-ctp-member-fields-range
                              fn2-commit-member-rows assoc-equal fn2-ctp-recorded-member-owners-p))))

; A keyed start can reuse a row formerly occupied by a transaction.
(defthm fn2-ctp-member-fields-of-keyed-write
 (let ((after (fn2-commit-member-put r (kind *fn2-commit-member-kind-keyed-mutation*)
               (slot 0) (gen 0) (len 0) (okind okind) (oslot oslot) (ogen ogen)
               (entries 0) (entry-bytes 0) (schema 0) (event event) (settled settled))))
  (implies (and (natp i) (natp r) (< r (fn2-commit-member-rows fn2-commit-member)))
           (equal (fn2-ctp-member-fields i after)
                  (if (equal i r)
                      (list *fn2-commit-member-kind-keyed-mutation* 0 0 0 okind oslot ogen event settled)
                    (fn2-ctp-member-fields i fn2-commit-member)))))
 :hints (("Goal" :in-theory (e/d (fn2-ctp-member-fields-from-snapshot)
                                 (fn2-ctp-member-fields fn2-commit-member-rows
                                  fn2-commit-member-row-snapshot)))))

(defthm fn2-ctp-keyed-write-preserves-recorded-owners
 (let ((after (fn2-commit-member-put r (kind *fn2-commit-member-kind-keyed-mutation*)
               (slot 0) (gen 0) (len 0) (okind okind) (oslot oslot) (ogen ogen)
               (entries 0) (entry-bytes 0) (schema 0) (event event) (settled settled))))
  (implies (and (natp r) (natp start) (< r (fn2-commit-member-rows fn2-commit-member))
                (fn2-ctp-recorded-member-owners-p
                 (fn2-ctp-member-fields-range start count fn2-commit-member) admissions))
           (fn2-ctp-recorded-member-owners-p (fn2-ctp-member-fields-range start count after)
                                             admissions)))
 :hints (("Goal" :induct (fn2-ctp-member-fields-range start count fn2-commit-member)
          :in-theory (disable assoc-equal fn2-ctp-member-fields fn2-commit-member-rows))))

; The empty admission list covers every row of the initialized table.
(local (include-book "std/lists/resize-list" :dir :system))
(local
 (defthm fn2-ctp-member-fields-kind
  (equal (car (fn2-ctp-member-fields i fn2-commit-member))
         (and (< (nfix i) (fn2-commit-member-rows fn2-commit-member))
              (fn2-commit-member-kind i fn2-commit-member)))
  :hints (("Goal" :in-theory '(fn2-ctp-member-fields car-cons (:e car))))))

(local
 (defthm fn2-ctp-member-kind-after-init
  (implies (and (natp i) (natp n) (< i n))
           (equal (fn2-commit-member-kind i (fn2-commit-member-init n fn2-commit-member))
                  *fn2-commit-member-kind-none*))
  :hints (("Goal" :in-theory
           (union-theories '(fn2-commit-member-kind fn2-commit-member-kind$ai
                             fn2-commit-member-init-nth nth-of-resize-list
                             natp nfix (:e nfix) (:e equal) (:e len))
                           (theory 'minimal-theory))))))

(defthm fn2-ctp-initial-member-owners-recorded
 (implies (and (natp start) (natp n))
          (fn2-ctp-recorded-member-owners-p
           (fn2-ctp-member-fields-range start count (fn2-commit-member-init n fn2-commit-member))
           nil))
 :hints (("Goal" :induct (fn2-ctp-member-fields-range start count fn2-commit-member)
          :in-theory (disable fn2-ctp-member-fields fn2-commit-member-init
                              fn2-commit-member-kind fn2-commit-member-rows))))
