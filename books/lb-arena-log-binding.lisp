; Arena/log binding over the actual catalog writers and sealed append.
(in-package "ACL2")
(include-book "lb-log-handle-allocation")
(include-book "served-columns")

(local (defthm fn-lbal-row-entry-depends-on-key
 (implies (and (equal (fn-record-sequence a) (fn-record-sequence b)) (equal (fn-record-payload a) (fn-record-payload b)))
 (equal (fn-lb-log-model-row-entry a log) (fn-lb-log-model-row-entry b log)))
 :hints (("Goal" :induct (fn-lb-log-model-row-entry a log)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-model-row-entry))))))

(local (defthm fn-lbal-payload-depends-on-key
 (implies (and (equal (fn-record-sequence a) (fn-record-sequence b)) (equal (fn-record-payload a) (fn-record-payload b)))
 (equal (fn-lb-log-payload a log) (fn-lb-log-payload b log)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-lbal-row-entry-depends-on-key)) :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-payload))))))

(local (defthm fn-lbal-binding-member
 (implies (and (fn-lb-arena-is-log fn-arena rows log) (natp i) (< i (len rows)))
 (equal (fn-nntp-payload-bytes (fn-record-payload (nth i rows)) fn-arena) (fn-lb-log-payload (nth i rows) log)))
 :hints (("Goal" :induct (nth i rows) :in-theory (union-theories (theory 'ground-zero) '(fn-lb-arena-is-log nth natp zp len))))))

(local (defthm fn-lbal-binding-of-update-same-key
 (implies (and (fn-lb-arena-is-log fn-arena rows log) (natp i) (< i (len rows))
 (equal (fn-record-sequence new) (fn-record-sequence (nth i rows)))
 (equal (fn-record-payload new) (fn-record-payload (nth i rows))))
 (fn-lb-arena-is-log fn-arena (update-nth i new rows) log))
 :hints (("Goal" :induct (nth i rows)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-arena-is-log update-nth nth natp zp len)))
 ("Subgoal *1/1" :use ((:instance fn-lbal-payload-depends-on-key (a new) (b (nth i rows)))))
 ("Subgoal *1/2" :use ((:instance fn-lbal-payload-depends-on-key (a new) (b (nth i rows)))))
 ("Subgoal *1/3" :use ((:instance fn-lbal-payload-depends-on-key (a new) (b (nth i rows))))))))

(local (defthm fn-lbal-withdrawn-row-key-fields
 (and (equal (fn-record-sequence (fn-held-with-withdrawn h withdrawn)) (fn-record-sequence h))
      (equal (fn-record-payload (fn-held-with-withdrawn h withdrawn)) (fn-record-payload h)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-held-with-withdrawn fn-held-make fn-record-sequence fn-record-payload fn-cbor-ag-car fn-cbor-ag-cdr))))))

(local (defthm fn-lbal-reference-withdraw-binding
 (implies (and (fn-lb-arena-is-log fn-arena rows log) (natp target))
 (fn-lb-arena-is-log fn-arena (fn-cat$a-withdraw target by rows) log))
 :hints (("Goal" :do-not-induct t :cases ((< target (len rows)))
 :use ((:instance fn-lbal-binding-of-update-same-key (i target) (new (fn-held-with-withdrawn (nth target rows) (cons (len rows) by)))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-cat$a-withdraw fn-cat-mark-withdrawn fn-lbal-withdrawn-row-key-fields))))))

(local (defthm fn-lbal-reference-redecide-binding
 (implies (and (fn-lb-arena-is-log fn-arena rows log) (natp seq) (< seq (len rows)))
 (fn-lb-arena-is-log fn-arena (fn-cat$a-redecide seq context rows) log))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbal-binding-of-update-same-key (i seq) (new (fn-held-with-context (nth seq rows) context)))
       (:instance fn-held-with-context-fields (h (nth seq rows)) (ctx context)))
 :in-theory (union-theories (theory 'ground-zero) '(fn-cat$a-redecide))))))

(local (defthm fn-lbal-row-entry-in-append
 (implies (natp handle)
 (equal (fn-lb-log-model-row-entry-in sequence handle (append entries tail))
 (or (fn-lb-log-model-row-entry-in sequence handle entries) (fn-lb-log-model-row-entry-in sequence handle tail))))
 :hints (("Goal" :induct (fn-lb-log-model-row-entry-in sequence handle entries)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-model-row-entry-in binary-append nth natp))))))

(local (defthm fn-lbal-last-appended-entry
 (equal (car (last (append entries (list entry)))) entry)
 :hints (("Goal" :induct (append entries (list entry)) :in-theory (union-theories (theory 'ground-zero) '(binary-append last))))))

(local (defthm fn-lbal-segment-append-row-entry
 (implies (natp handle)
 (equal (fn-lb-log-model-row-entry-in sequence handle (caddr (fn-lb-log-model-append-to-segment row payload segment)))
 (or (fn-lb-log-model-row-entry-in sequence handle (caddr segment))
     (and (equal sequence (fn-record-sequence row)) (equal handle (fn-record-payload row))
          (car (last (caddr (fn-lb-log-model-append-to-segment row payload segment))))))))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-append-to-segment fn-lbal-row-entry-in-append fn-lbal-last-appended-entry fn-lb-log-model-row-entry-in nth))))))

(local (defthm fn-lbal-segment-new-entry-is-present
 (consp (car (last (caddr (fn-lb-log-model-append-to-segment row payload segment)))))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-model-append-to-segment fn-lbal-last-appended-entry))))))

(local (defthm fn-lbal-segment-new-entry-payload
 (equal (nth 6 (car (last (caddr (fn-lb-log-model-append-to-segment row payload segment))))) payload)
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-model-append-to-segment fn-lbal-last-appended-entry nth))))))

(local (defthm fn-lbal-log-payload-of-cons
 (equal (fn-lb-log-payload query (cons segment log))
 (let ((entry (fn-lb-log-model-row-entry-in (fn-record-sequence query) (fn-record-payload query) (caddr segment))))
 (if entry (nth 6 entry) (fn-lb-log-payload query log))))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-payload fn-lb-log-model-row-entry))))))

(local (defthm fn-lbal-log-payload-of-atom
 (implies (atom log) (equal (fn-lb-log-payload query log) nil))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-payload fn-lb-log-model-row-entry nth))))))

(local (defthm fn-lbal-row-entry-in-nil
 (equal (fn-lb-log-model-row-entry-in sequence handle nil) nil)
 :hints (("Goal" :in-theory '(fn-lb-log-model-row-entry-in)))))





; Binding preservation does not require catalog row types, including nil-key shadow cases.
(local (defthm fn-lbwr-entry-append-preserves-observation
 (implies
  (and (equal (let ((old (fn-lb-log-model-row-entry-in sequence handle entries)))
                (if old (nth 6 old) fallback)) expected)
       (implies (fn-lb-log-model-row-entry-in sequence handle tail)
         (equal (nth 6 (fn-lb-log-model-row-entry-in sequence handle tail)) expected)))
  (equal (let ((entry (fn-lb-log-model-row-entry-in sequence handle (append entries tail))))
            (if entry (nth 6 entry) fallback)) expected))
 :rule-classes nil
 :hints (("Goal" :induct (fn-lb-log-model-row-entry-in sequence handle entries)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-row-entry-in binary-append nth))))))

(local (defthm fn-lbwr-appended-directory
 (equal (caddr (fn-lb-log-model-append-to-segment row payload segment))
        (append (caddr segment)
          (list (car (last (caddr (fn-lb-log-model-append-to-segment row payload segment)))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-append-to-segment fn-lbal-last-appended-entry))))))

(local (defthm fn-lbwr-appended-key-and-payload
 (let ((entry (car (last (caddr (fn-lb-log-model-append-to-segment row payload segment))))))
  (and (equal (nth 5 entry) (fn-record-payload row))
       (equal (nth 6 entry) payload) (equal (nth 8 entry) (fn-record-sequence row))))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-append-to-segment fn-lbal-last-appended-entry nth))))))

(local (defthm fn-lbwr-segment-append-preserves-observation
 (implies
  (and (equal (let ((old (fn-lb-log-model-row-entry-in sequence handle (caddr segment))))
                (if old (nth 6 old) fallback)) expected)
       (implies (and (equal sequence (fn-record-sequence row))
                     (equal handle (fn-record-payload row))) (equal payload expected)))
  (equal (let ((entry (fn-lb-log-model-row-entry-in sequence handle
                       (caddr (fn-lb-log-model-append-to-segment row payload segment)))))
            (if entry (nth 6 entry) fallback)) expected))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbwr-appended-directory)
       (:instance fn-lbwr-entry-append-preserves-observation
         (entries (caddr segment))
         (tail (list (car (last (caddr (fn-lb-log-model-append-to-segment row payload segment))))))))
 :expand ((fn-lb-log-model-row-entry-in sequence handle
            (list (car (last (caddr (fn-lb-log-model-append-to-segment row payload segment)))))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbal-row-entry-in-nil fn-lbwr-appended-key-and-payload (:executable-counterpart fn-lb-log-model-row-entry-in)))))))

(local (defthm fn-lbwr-log-append-preserves-observation
 (implies (and (equal (fn-lb-log-payload query log) expected)
               (implies (equal (fn-record-payload query) (fn-record-payload row))
                        (equal payload expected)))
 (equal (fn-lb-log-payload query (fn-lb-log-model-append row payload target log)) expected))
 :rule-classes nil
 :hints (("Goal" :induct (fn-lb-log-model-append row payload target log)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-append fn-lbal-log-payload-of-cons fn-lbal-log-payload-of-atom
   fn-lbal-row-entry-in-nil)))
 ("Subgoal *1/1"  :use ((:instance fn-lbwr-segment-append-preserves-observation
          (sequence (fn-record-sequence query)) (handle (fn-record-payload query))
          (segment (car log)) (fallback (fn-lb-log-payload query (cdr log))))
       (:instance fn-lbwr-segment-append-preserves-observation
          (sequence (fn-record-sequence query)) (handle (fn-record-payload query))
          (segment (list target nil nil)) (fallback nil))))
 ("Subgoal *1/2"  :use ((:instance fn-lbwr-segment-append-preserves-observation
          (sequence (fn-record-sequence query)) (handle (fn-record-payload query))
          (segment (car log)) (fallback (fn-lb-log-payload query (cdr log))))
       (:instance fn-lbwr-segment-append-preserves-observation
          (sequence (fn-record-sequence query)) (handle (fn-record-payload query))
          (segment (list target nil nil)) (fallback nil))))
 ("Subgoal *1/3"  :use ((:instance fn-lbwr-segment-append-preserves-observation
          (sequence (fn-record-sequence query)) (handle (fn-record-payload query))
          (segment (car log)) (fallback (fn-lb-log-payload query (cdr log))))
       (:instance fn-lbwr-segment-append-preserves-observation
          (sequence (fn-record-sequence query)) (handle (fn-record-payload query))
          (segment (list target nil nil)) (fallback nil))))
)))

(local (defthm fn-lbwr-single-row-append-binding
 (implies
  (equal (fn-nntp-payload-bytes (fn-record-payload query) fn-arena)
         (fn-lb-log-payload query log))
  (equal (fn-lb-log-payload query
           (fn-lb-log-model-append row (fn-nntp-payload-bytes (fn-record-payload row) fn-arena) target log))
         (fn-nntp-payload-bytes (fn-record-payload query) fn-arena)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbwr-log-append-preserves-observation
        (expected (fn-nntp-payload-bytes (fn-record-payload query) fn-arena))
        (payload (fn-nntp-payload-bytes (fn-record-payload row) fn-arena))))
 :in-theory (theory 'ground-zero)))))

(defthm fn-lb-arena-is-log-of-append
 (implies (fn-lb-arena-is-log fn-arena rows log)
 (fn-lb-arena-is-log fn-arena rows
  (fn-lb-log-model-append row (fn-nntp-payload-bytes (fn-record-payload row) fn-arena) target log)))
 :hints (("Goal" :induct (fn-lb-arena-is-log fn-arena rows log)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-arena-is-log fn-lbwr-single-row-append-binding)))))

(defthm fn-lb-arena-is-log-of-withdraw
 (implies (and (fn-lb-arena-is-log fn-arena rows log) (natp target))
 (fn-lb-arena-is-log fn-arena (fn-cat-withdraw target by rows) log))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbal-reference-withdraw-binding))
 :in-theory (union-theories (theory 'ground-zero) '(fn-cat-withdraw)))))

(defthm fn-lb-arena-is-log-of-redecide
 (implies (and (fn-lb-arena-is-log fn-arena rows log) (natp seq) (< seq (len rows)))
 (fn-lb-arena-is-log fn-arena (fn-cat-redecide seq context rows) log))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbal-reference-redecide-binding))
 :in-theory (union-theories (theory 'ground-zero) '(fn-cat-redecide)))))

(local (defthm fn-lbal-binding-of-row-append
 (implies (and (fn-lb-arena-is-log fn-arena rows log)
 (equal (fn-nntp-payload-bytes (fn-record-payload new) fn-arena) (fn-lb-log-payload new log)))
 (fn-lb-arena-is-log fn-arena (append rows (list new)) log))
 :hints (("Goal" :induct (fn-lb-arena-is-log fn-arena rows log)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-arena-is-log binary-append))))))

(local (defthm fn-lbal-assigned-key-fields
 (and (equal (fn-record-sequence (fn-cat-assign h rows)) (fn-record-sequence h))
      (equal (fn-record-payload (fn-cat-assign h rows)) (fn-record-payload h)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-cat-assign fn-held-with-numbers fn-held-make fn-record-sequence fn-record-payload fn-cbor-ag-car fn-cbor-ag-cdr))))))

(local (defthm fn-lbal-catalog-commit-ready-binding
 (implies (and (fn-lb-arena-is-log fn-arena rows log)
 (equal (fn-nntp-payload-bytes (fn-record-payload h) fn-arena) (fn-lb-log-payload h log)))
 (fn-lb-arena-is-log fn-arena (fn-cat-commit h rows) log))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbal-binding-of-row-append (new (fn-cat-assign h rows)))
       (:instance fn-lbal-payload-depends-on-key (a (fn-cat-assign h rows)) (b h)))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-cat-commit fn-cat$a-commit fn-lbal-assigned-key-fields))))))

(local (defthm fn-lbal-segment-new-entry-truth
 (iff (car (last (caddr (fn-lb-log-model-append-to-segment row payload segment)))) t)
 :hints (("Goal" :use ((:instance fn-lbal-segment-new-entry-is-present)) :in-theory (theory 'ground-zero)))))

(defthm fn-lb-log-append-binds-fresh-row
 (implies (and (natp (fn-record-payload row)) (not (fn-lb-log-model-row-entry row log)))
 (equal (fn-lb-log-payload row (fn-lb-log-model-append row payload target log)) payload))
 :hints (("Goal" :induct (fn-lb-log-model-append row payload target log)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-append fn-lb-log-model-row-entry fn-lbal-log-payload-of-cons fn-lbal-log-payload-of-atom
 fn-lbal-segment-append-row-entry fn-lbal-segment-new-entry-is-present fn-lbal-segment-new-entry-truth fn-lbal-segment-new-entry-payload fn-lbal-row-entry-in-nil)))))

(local (defthm fn-lbal-payload-bytes-survive-seal
 (implies (and (natp h) (< h (fn-arena-count fn-arena)))
 (equal (fn-nntp-payload-bytes h (fn-arena-seal-list payload fn-arena)) (fn-nntp-payload-bytes h fn-arena)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-arena-seal-list-keeps-nth-below (xs payload)))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-nntp-payload-bytes fn-arena-payload-is-nth fn-arena-count-is-len fn-arena-seal-list-len))))))

(local (defthm fn-lbal-binding-of-seal-list
 (implies (and (fn-lb-arena-is-log fn-arena rows log) (fn-scol-handles-below rows (fn-arena-count fn-arena)))
 (fn-lb-arena-is-log (fn-arena-seal-list payload fn-arena) rows log))
 :hints (("Goal" :induct (fn-lb-arena-is-log fn-arena rows log)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-arena-is-log fn-scol-handles-below fn-lbal-payload-bytes-survive-seal fn-arena-count-is-len nfix))))))

(local (defthm fn-lbal-nth-append-at-length
 (equal (nth (len a) (append a (list x))) x)
 :hints (("Goal" :induct (len a) :in-theory (union-theories (theory 'ground-zero) '(nth len zp binary-append))))))

(local (defthm fn-lbal-new-seal-payload
 (equal (fn-nntp-payload-bytes (fn-arena-count fn-arena) (fn-arena-seal-list payload fn-arena)) payload)
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-arena-seal-new-handle (xs payload)))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-nntp-payload-bytes fn-arena-seal-count fn-arena-count-is-len))))))



(defthm fn-lb-arena-is-log-of-commit
 (implies (and
 (fn-lb-arena-is-log fn-arena rows log)
 (fn-scol-handles-below rows (fn-arena-count fn-arena))
 (equal (fn-record-payload h) (fn-arena-count fn-arena))
 (not (fn-lb-log-model-row-entry h log)))
 (let* ((arena (fn-arena-seal-list payload fn-arena))
        (log2 (fn-lb-log-model-append (fn-cat-assign h rows) payload target log)))
 (fn-lb-arena-is-log arena (fn-cat-commit h rows) log2)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbal-binding-of-seal-list)
       (:instance fn-lbal-new-seal-payload)
       (:instance fn-lbal-assigned-key-fields)
       (:instance fn-lbal-row-entry-depends-on-key (a (fn-cat-assign h rows)) (b h))
       (:instance fn-lbal-payload-depends-on-key (a (fn-cat-assign h rows)) (b h)
        (log (fn-lb-log-model-append (fn-cat-assign h rows) payload target log)))
       (:instance fn-lb-log-append-binds-fresh-row (row (fn-cat-assign h rows)))
       (:instance fn-lb-arena-is-log-of-append
        (fn-arena (fn-arena-seal-list payload fn-arena)) (row (fn-cat-assign h rows)))
       (:instance fn-lbal-catalog-commit-ready-binding
        (fn-arena (fn-arena-seal-list payload fn-arena))
        (log (fn-lb-log-model-append (fn-cat-assign h rows) payload target log))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-arena-count-is-len natp)))))

(defthm fn-lb-arena-is-log-of-allocated-commit
 (implies (and
 (fn-lb-arena-is-log fn-arena rows log)
 (fn-scol-handles-below rows (fn-arena-count fn-arena))
 (equal (fn-record-payload h) (fn-arena-count fn-arena))
 (fn-lb-log-handles-below log (fn-arena-count fn-arena)))
 (let* ((arena (fn-arena-seal-list payload fn-arena))
        (log2 (fn-lb-log-model-append (fn-cat-assign h rows) payload target log)))
 (fn-lb-arena-is-log arena (fn-cat-commit h rows) log2)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lb-arena-is-log-of-commit)
       (:instance fn-lb-log-handles-below-gives-fresh-key (row h) (n (fn-arena-count fn-arena))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-arena-count-is-len nfix natp)))))
