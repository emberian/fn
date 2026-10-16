; Fresh append carries the whole served invariant over an existing resident row.
(in-package "ACL2")
(include-book "../../books/catalog-columns-append-resolved-preservation")
(include-book "lb-column-read-cost-teeth")
(defun fn-lbsa-log ()
 (declare (xargs :guard t :verify-guards nil))
 (fn-lb-log-model-append (fn-lbcc-test-decided-row) *fn-lbr13-payload* 1 nil))
(defun fn-lbsa-incoming ()
 (declare (xargs :guard t :verify-guards nil))
 (update-nth 0 1 (fn-lbcc-test-decided-row)))
(defthm fn-lbsa-fixture-domains
 (and (fn-lbc-p (create-fn-lbc))
      (fn-held-listp (list (fn-lbcc-test-decided-row)))
      (fn-lbc-rows-log-guardp (list (fn-lbcc-test-decided-row)) (fn-lbsa-log))
      (fn-lb-log-layoutp (fn-lbsa-log))
      (fn-lb-log-model-segsp (fn-lbsa-log))
      (fn-lb-log-rows-sourcep (list (fn-lbcc-test-decided-row)) (fn-lbsa-log)))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  (set-difference-theories
   (union-theories (executable-counterpart-theory :here)
    '(fn-lb-log-rows-sourcep fn-lb-log-row-sourcep fn-lb-log-model-next-range fn-lbc-p create-fn-lbc create-fn-dmap fn-dmap$ap create-fn-dmap$a fn-lbc-number-storep))
   '((:executable-counterpart fn-lb-log-model-next-range)
     (:executable-counterpart fn-lb-log-rows-sourcep) (:executable-counterpart fn-lb-log-row-sourcep)))))))
(defthm fn-lbsa-fixture-served-invariant
 (fn-lb-served-log-invp (fn-lbsa-log) '(nil nil) (fn-lbcc-test-one-state)
  (list (fn-lbcc-test-decided-row)))
 :rule-classes nil
 :hints (("Goal" :use (fn-lbsa-fixture-domains
  (:instance fn-lb-served-log-invp-of-open-rebuild
   (rows (list (fn-lbcc-test-decided-row))) (log (fn-lbsa-log))
   (fn-lb-vmap '(nil nil)) (fn-lbc (create-fn-lbc))))
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbcc-test-one-state fn-lbcc-test-model-columns fn-lbsa-log
     fn-lb-verified-invp fn-lb-verified-entries-invp fn-lb-vmap-index-covers nth)))))
(defthm fn-lbsa-fixture-column-type
 (fn-lbc-p (fn-lbcc-test-one-state))
 :rule-classes nil
 :hints (("Goal" :use (fn-lbsa-fixture-domains
  (:instance fn-lbc-p-of-open-rebuild
   (rows (list (fn-lbcc-test-decided-row))) (log (fn-lbsa-log)) (fn-lbc (create-fn-lbc))))
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbcc-test-one-state fn-lbcc-test-model-columns fn-lbsa-log
     fn-held-listp-implies-cat-rowsp fn-cat$ap)))))
(defthm fn-lbsa-fixture-fresh-append-domains
 (and (fn-lb-catalog-distinct-log-keyp (fn-lbsa-incoming) (list (fn-lbcc-test-decided-row))))
 :rule-classes nil
 :hints (("Goal" :in-theory (set-difference-theories
  (union-theories (theory 'ground-zero)
   (union-theories (executable-counterpart-theory :here) '(fn-lb-catalog-distinct-log-keyp)))
  '((:executable-counterpart fn-lb-catalog-distinct-log-keyp))))))
(defthm fn-lbsa-append-whole-positive
 (and (fn-lb-served-log-invp (fn-lbsa-log) '(nil nil) (fn-lbcc-test-one-state) (list (fn-lbcc-test-decided-row)))
      (fn-lb-catalog-distinct-log-keyp (fn-lbsa-incoming) (list (fn-lbcc-test-decided-row)))
      (fn-cat-rowp (fn-lbsa-incoming)) (fn-cbor-octet-listp *fn-lbr13-payload*) (unsigned-byte-p 64 2)
      (fn-lb-served-log-invp (fn-lb-log-model-append (fn-lbsa-incoming) *fn-lbr13-payload* 2 (fn-lbsa-log))
       '(nil nil) (fn-lbcc-test-one-state) (list (fn-lbcc-test-decided-row))))
 :rule-classes nil
 :hints (("Goal" :use (fn-lbsa-fixture-served-invariant fn-lbsa-fixture-column-type
  fn-lbsa-fixture-domains fn-lbsa-fixture-fresh-append-domains
  (:instance fn-lb-served-log-invp-of-append (log (fn-lbsa-log)) (fn-lb-vmap-v '(nil nil))
   (fn-lbc-v (fn-lbcc-test-one-state)) (rows (list (fn-lbcc-test-decided-row)))
   (row (fn-lbsa-incoming)) (payload *fn-lbr13-payload*) (target 2)))
  :in-theory (union-theories (theory 'ground-zero)
   (union-theories (executable-counterpart-theory :here) '(fn-held-listp-implies-cat-rowsp))))))

(defun fn-lbsa-overwrite-after-append (row payload target log)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((post (fn-lb-log-model-append row payload target log)) (segment (car post)))
  (cons (update-nth 1 (update-nth 0 255 (cadr segment)) segment) (cdr post))))
(defun fn-lbsa-corrupt-pre-log ()
 (declare (xargs :guard t :verify-guards nil))
 (let* ((log (fn-lbsa-log)) (segment (car log)))
  (list (update-nth 1 (update-nth 0 255 (cadr segment)) segment))))
(local (defthm fn-lbsa-invp-gives-first-auth-by-definition
 (implies (fn-lb-served-log-invp log vm cols (cons old rest))
  (fn-arx-entry-ok
   (fn-lb-entry-octets (fn-loc-segment (fn-lbc-loc0 0 cols) (fn-lbc-loc1 0 cols))
                      (fn-loc-offset (fn-lbc-loc0 0 cols) (fn-lbc-loc1 0 cols)) log)
   (fn-lb-entry-protected-len (fn-loc-segment (fn-lbc-loc0 0 cols) (fn-lbc-loc1 0 cols))
                            (fn-loc-offset (fn-lbc-loc0 0 cols) (fn-lbc-loc1 0 cols)) log)))
 :hints (("Goal" :do-not-induct t
  :expand ((fn-lbc-rows-corr 0 (cons old rest) 0 cols log))
  :in-theory (union-theories (theory 'ground-zero) '(fn-lb-served-log-invp fn-lbc-corr fn-lbc-row-corr))))))
(local (defthm fn-lbsa-invp-gives-segsp-by-definition
 (implies (fn-lb-served-log-invp log vm cols rows) (fn-lb-log-model-segsp log))
 :hints (("Goal" :in-theory '(fn-lb-served-log-invp fn-lbc-corr)))))
(defthm fn-lbsa-fault-corrupts-old-entry
 (not (fn-arx-entry-ok
  (fn-lb-entry-octets 1 6 (fn-lbsa-overwrite-after-append (fn-lbsa-incoming) *fn-lbr13-payload* 2 (fn-lbsa-log)))
  (fn-lb-entry-protected-len 1 6 (fn-lbsa-overwrite-after-append (fn-lbsa-incoming) *fn-lbr13-payload* 2 (fn-lbsa-log)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) (executable-counterpart-theory :here)))))
(defthm fn-lbsa-overwrite-falsifies-served-invariant
 (not (fn-lb-served-log-invp
  (fn-lbsa-overwrite-after-append (fn-lbsa-incoming) *fn-lbr13-payload* 2 (fn-lbsa-log))
  '(nil nil) (fn-lbcc-test-one-state) (list (fn-lbcc-test-decided-row))))
 :rule-classes nil
 :hints (("Goal" :use (fn-lbsa-fault-corrupts-old-entry fn-lbcc-test-head-positive
  (:instance fn-lbsa-invp-gives-first-auth-by-definition
   (log (fn-lbsa-overwrite-after-append (fn-lbsa-incoming) *fn-lbr13-payload* 2 (fn-lbsa-log)))
   (vm '(nil nil)) (cols (fn-lbcc-test-one-state)) (old (fn-lbcc-test-decided-row)) (rest nil)))
  :in-theory (theory 'ground-zero))))

; BEGIN generated append domain-removal facts
(defthm fn-lbsa-row-type-log-is-not-recognized
 (not (fn-lb-log-model-segsp (fn-lb-log-model-append (update-nth 4 -1 (fn-lbsa-incoming)) *fn-lbr13-payload* 2 (fn-lbsa-log)))) :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) (executable-counterpart-theory :here)))))
(defthm fn-lbsa-row-type-post-invariant-fails
 (not (fn-lb-served-log-invp (fn-lb-log-model-append (update-nth 4 -1 (fn-lbsa-incoming)) *fn-lbr13-payload* 2 (fn-lbsa-log)) '(nil nil) (fn-lbcc-test-one-state) (list (fn-lbcc-test-decided-row))))
 :rule-classes nil
 :hints (("Goal" :use (fn-lbsa-row-type-log-is-not-recognized
  (:instance fn-lbsa-invp-gives-segsp-by-definition (log (fn-lb-log-model-append (update-nth 4 -1 (fn-lbsa-incoming)) *fn-lbr13-payload* 2 (fn-lbsa-log))) (vm '(nil nil)) (cols (fn-lbcc-test-one-state)) (rows (list (fn-lbcc-test-decided-row)))))
  :in-theory (theory 'ground-zero))))
(defthm fn-lbsa-payload-type-log-is-not-recognized
 (not (fn-lb-log-model-segsp (fn-lb-log-model-append (fn-lbsa-incoming) '(999) 2 (fn-lbsa-log)))) :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) (executable-counterpart-theory :here)))))
(defthm fn-lbsa-payload-type-post-invariant-fails
 (not (fn-lb-served-log-invp (fn-lb-log-model-append (fn-lbsa-incoming) '(999) 2 (fn-lbsa-log)) '(nil nil) (fn-lbcc-test-one-state) (list (fn-lbcc-test-decided-row))))
 :rule-classes nil
 :hints (("Goal" :use (fn-lbsa-payload-type-log-is-not-recognized
  (:instance fn-lbsa-invp-gives-segsp-by-definition (log (fn-lb-log-model-append (fn-lbsa-incoming) '(999) 2 (fn-lbsa-log))) (vm '(nil nil)) (cols (fn-lbcc-test-one-state)) (rows (list (fn-lbcc-test-decided-row)))))
  :in-theory (theory 'ground-zero))))
(defthm fn-lbsa-segment-type-log-is-not-recognized
 (not (fn-lb-log-model-segsp (fn-lb-log-model-append (fn-lbsa-incoming) *fn-lbr13-payload* -1 (fn-lbsa-log)))) :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) (executable-counterpart-theory :here)))))
(defthm fn-lbsa-segment-type-post-invariant-fails
 (not (fn-lb-served-log-invp (fn-lb-log-model-append (fn-lbsa-incoming) *fn-lbr13-payload* -1 (fn-lbsa-log)) '(nil nil) (fn-lbcc-test-one-state) (list (fn-lbcc-test-decided-row))))
 :rule-classes nil
 :hints (("Goal" :use (fn-lbsa-segment-type-log-is-not-recognized
  (:instance fn-lbsa-invp-gives-segsp-by-definition (log (fn-lb-log-model-append (fn-lbsa-incoming) *fn-lbr13-payload* -1 (fn-lbsa-log))) (vm '(nil nil)) (cols (fn-lbcc-test-one-state)) (rows (list (fn-lbcc-test-decided-row)))))
  :in-theory (theory 'ground-zero))))

(defthm fn-lbsa-bad-pre-and-post-entry
 (and (not (fn-arx-entry-ok (fn-lb-entry-octets 1 6 (fn-lbsa-corrupt-pre-log)) (fn-lb-entry-protected-len 1 6 (fn-lbsa-corrupt-pre-log))))
      (not (fn-arx-entry-ok
       (fn-lb-entry-octets 1 6 (fn-lb-log-model-append (fn-lbsa-incoming) *fn-lbr13-payload* 2 (fn-lbsa-corrupt-pre-log)))
       (fn-lb-entry-protected-len 1 6 (fn-lb-log-model-append (fn-lbsa-incoming) *fn-lbr13-payload* 2 (fn-lbsa-corrupt-pre-log))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) (executable-counterpart-theory :here)))))
(defthm fn-lbsa-bad-pre-and-post-invariant
 (and (not (fn-lb-served-log-invp (fn-lbsa-corrupt-pre-log) '(nil nil) (fn-lbcc-test-one-state) (list (fn-lbcc-test-decided-row))))
      (not (fn-lb-served-log-invp
       (fn-lb-log-model-append (fn-lbsa-incoming) *fn-lbr13-payload* 2 (fn-lbsa-corrupt-pre-log))
       '(nil nil) (fn-lbcc-test-one-state) (list (fn-lbcc-test-decided-row)))))
 :rule-classes nil
 :hints (("Goal" :use (fn-lbsa-bad-pre-and-post-entry fn-lbcc-test-head-positive
  (:instance fn-lbsa-invp-gives-first-auth-by-definition
   (log (fn-lbsa-corrupt-pre-log)) (vm '(nil nil)) (cols (fn-lbcc-test-one-state)) (old (fn-lbcc-test-decided-row)) (rest nil))
  (:instance fn-lbsa-invp-gives-first-auth-by-definition
   (log (fn-lb-log-model-append (fn-lbsa-incoming) *fn-lbr13-payload* 2 (fn-lbsa-corrupt-pre-log)))
   (vm '(nil nil)) (cols (fn-lbcc-test-one-state)) (old (fn-lbcc-test-decided-row)) (rest nil)))
  :in-theory (theory 'ground-zero))))

(defun fn-lbsa-shadow-base-log ()
 (declare (xargs :guard t :verify-guards nil))
 (cons '(0 nil nil) (fn-lbsa-log)))
(defun-nx fn-lbsa-shadow-base-columns ()
 (fn-lbcc-test-model-columns (list (fn-lbcc-test-decided-row)) (fn-lbsa-shadow-base-log)))
(defthm fn-lbsa-shadow-base-domains
 (and (fn-lbc-rows-log-guardp (list (fn-lbcc-test-decided-row)) (fn-lbsa-shadow-base-log))
      (fn-lb-log-layoutp (fn-lbsa-shadow-base-log))
      (fn-lb-log-model-segsp (fn-lbsa-shadow-base-log))
      (fn-lb-log-rows-sourcep (list (fn-lbcc-test-decided-row)) (fn-lbsa-shadow-base-log)))
 :rule-classes nil
 :hints (("Goal" :in-theory (set-difference-theories
  (union-theories (theory 'ground-zero) (union-theories (executable-counterpart-theory :here)
   '(fn-lb-log-rows-sourcep fn-lb-log-row-sourcep fn-lb-log-model-next-range)))
  '((:executable-counterpart fn-lb-log-model-next-range) (:executable-counterpart fn-lb-log-rows-sourcep)
    (:executable-counterpart fn-lb-log-row-sourcep))))))
(defthm fn-lbsa-shadow-base-served-invariant
 (fn-lb-served-log-invp (fn-lbsa-shadow-base-log) '(nil nil) (fn-lbsa-shadow-base-columns)
  (list (fn-lbcc-test-decided-row)))
 :rule-classes nil
 :hints (("Goal" :use (fn-lbsa-fixture-domains fn-lbsa-shadow-base-domains
  (:instance fn-lb-served-log-invp-of-open-rebuild
   (rows (list (fn-lbcc-test-decided-row))) (log (fn-lbsa-shadow-base-log))
   (fn-lb-vmap '(nil nil)) (fn-lbc (create-fn-lbc))))
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbsa-shadow-base-columns fn-lbcc-test-model-columns
     fn-lb-verified-invp fn-lb-verified-entries-invp fn-lb-vmap-index-covers nth)))))
(local (defthm fn-lbsa-invp-gives-first-head-by-definition
 (implies (fn-lb-served-log-invp log vm cols (cons old rest))
  (equal (fn-lbc-value 0 :head-length cols)
         (len (fn-nntp-stuffed-section :head (fn-lb-log-payload old log)))))
 :hints (("Goal" :do-not-induct t
  :expand ((fn-lbc-rows-corr 0 (cons old rest) 0 cols log))
  :in-theory (union-theories (theory 'ground-zero) '(fn-lb-served-log-invp fn-lbc-corr fn-lbc-row-corr))))))
(defthm fn-lbsa-shadow-observations
 (and (equal (fn-lb-log-payload (fn-lbcc-test-decided-row) (fn-lbsa-shadow-base-log)) *fn-lbr13-payload*)
      (equal (len (fn-nntp-stuffed-section :head *fn-lbr13-payload*)) 12)
      (equal (fn-lb-log-payload (fn-lbcc-test-decided-row)
       (fn-lb-log-model-append (fn-lbcc-test-decided-row) nil 0 (fn-lbsa-shadow-base-log))) nil)
      (fn-lb-log-model-segsp (fn-lb-log-model-append (fn-lbcc-test-decided-row) nil 0 (fn-lbsa-shadow-base-log))))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) (executable-counterpart-theory :here)))))
(defthm fn-lbsa-shadow-base-head-length
 (equal (fn-lbc-value 0 :head-length (fn-lbsa-shadow-base-columns)) 12)
 :rule-classes nil
 :hints (("Goal" :use (fn-lbsa-shadow-base-served-invariant fn-lbsa-shadow-observations
  (:instance fn-lbsa-invp-gives-first-head-by-definition
   (log (fn-lbsa-shadow-base-log)) (vm '(nil nil)) (cols (fn-lbsa-shadow-base-columns))
   (old (fn-lbcc-test-decided-row)) (rest nil)))
  :in-theory (theory 'ground-zero))))
(defthm fn-lbsa-duplicate-key-shadow-falsifies-post-invariant
 (not (fn-lb-served-log-invp
  (fn-lb-log-model-append (fn-lbcc-test-decided-row) nil 0 (fn-lbsa-shadow-base-log))
  '(nil nil) (fn-lbsa-shadow-base-columns) (list (fn-lbcc-test-decided-row))))
 :rule-classes nil
 :hints (("Goal" :use (fn-lbsa-shadow-base-head-length fn-lbsa-shadow-observations
  (:instance fn-lbsa-invp-gives-first-head-by-definition
   (log (fn-lb-log-model-append (fn-lbcc-test-decided-row) nil 0 (fn-lbsa-shadow-base-log)))
   (vm '(nil nil)) (cols (fn-lbsa-shadow-base-columns)) (old (fn-lbcc-test-decided-row)) (rest nil)))
  :in-theory (union-theories (theory 'ground-zero) '((:executable-counterpart fn-nntp-stuffed-section) (:executable-counterpart len))))))

; BEGIN final served-append teeth
(defthm fn-lbsa-remove-invariant-whole-witness
 (and (fn-lb-catalog-distinct-log-keyp (fn-lbsa-incoming) (list (fn-lbcc-test-decided-row))) (fn-cat-rowp (fn-lbsa-incoming)) (fn-cbor-octet-listp *fn-lbr13-payload*) (unsigned-byte-p 64 2) (not (fn-lb-served-log-invp (fn-lbsa-corrupt-pre-log) '(nil nil) (fn-lbcc-test-one-state) (list (fn-lbcc-test-decided-row)))) (not (fn-lb-served-log-invp (fn-lb-log-model-append (fn-lbsa-incoming) *fn-lbr13-payload* 2 (fn-lbsa-corrupt-pre-log)) '(nil nil) (fn-lbcc-test-one-state) (list (fn-lbcc-test-decided-row))))) :rule-classes nil
 :hints (("Goal" :use (fn-lbsa-append-whole-positive fn-lbsa-bad-pre-and-post-invariant)
  :in-theory (set-difference-theories
   (union-theories (theory 'ground-zero) (union-theories (executable-counterpart-theory :here)
    '(fn-lb-catalog-distinct-log-keyp)))
   '((:executable-counterpart fn-lb-catalog-distinct-log-keyp))))))
(defthm fn-lbsa-remove-fresh-key-whole-witness
 (and (fn-lb-served-log-invp (fn-lbsa-shadow-base-log) '(nil nil) (fn-lbsa-shadow-base-columns) (list (fn-lbcc-test-decided-row))) (fn-cat-rowp (fn-lbcc-test-decided-row)) (fn-cbor-octet-listp nil) (unsigned-byte-p 64 0) (not (fn-lb-catalog-distinct-log-keyp (fn-lbcc-test-decided-row) (list (fn-lbcc-test-decided-row)))) (not (fn-lb-served-log-invp (fn-lb-log-model-append (fn-lbcc-test-decided-row) nil 0 (fn-lbsa-shadow-base-log)) '(nil nil) (fn-lbsa-shadow-base-columns) (list (fn-lbcc-test-decided-row))))) :rule-classes nil
 :hints (("Goal" :use (fn-lbsa-append-whole-positive fn-lbsa-shadow-base-served-invariant fn-lbsa-duplicate-key-shadow-falsifies-post-invariant)
  :in-theory (set-difference-theories
   (union-theories (theory 'ground-zero) (union-theories (executable-counterpart-theory :here)
    '(fn-lb-catalog-distinct-log-keyp)))
   '((:executable-counterpart fn-lb-catalog-distinct-log-keyp))))))
(defthm fn-lbsa-remove-row-type-whole-witness
 (and (fn-lb-served-log-invp (fn-lbsa-log) '(nil nil) (fn-lbcc-test-one-state) (list (fn-lbcc-test-decided-row))) (fn-lb-catalog-distinct-log-keyp (update-nth 4 -1 (fn-lbsa-incoming)) (list (fn-lbcc-test-decided-row))) (fn-cbor-octet-listp *fn-lbr13-payload*) (unsigned-byte-p 64 2) (not (fn-cat-rowp (update-nth 4 -1 (fn-lbsa-incoming)))) (not (fn-lb-served-log-invp (fn-lb-log-model-append (update-nth 4 -1 (fn-lbsa-incoming)) *fn-lbr13-payload* 2 (fn-lbsa-log)) '(nil nil) (fn-lbcc-test-one-state) (list (fn-lbcc-test-decided-row))))) :rule-classes nil
 :hints (("Goal" :use (fn-lbsa-append-whole-positive fn-lbsa-row-type-post-invariant-fails)
  :in-theory (set-difference-theories
   (union-theories (theory 'ground-zero) (union-theories (executable-counterpart-theory :here)
    '(fn-lb-catalog-distinct-log-keyp)))
   '((:executable-counterpart fn-lb-catalog-distinct-log-keyp))))))
(defthm fn-lbsa-remove-octets-whole-witness
 (and (fn-lb-served-log-invp (fn-lbsa-log) '(nil nil) (fn-lbcc-test-one-state) (list (fn-lbcc-test-decided-row))) (fn-lb-catalog-distinct-log-keyp (fn-lbsa-incoming) (list (fn-lbcc-test-decided-row))) (fn-cat-rowp (fn-lbsa-incoming)) (unsigned-byte-p 64 2) (not (fn-cbor-octet-listp '(999))) (not (fn-lb-served-log-invp (fn-lb-log-model-append (fn-lbsa-incoming) '(999) 2 (fn-lbsa-log)) '(nil nil) (fn-lbcc-test-one-state) (list (fn-lbcc-test-decided-row))))) :rule-classes nil
 :hints (("Goal" :use (fn-lbsa-append-whole-positive fn-lbsa-payload-type-post-invariant-fails)
  :in-theory (set-difference-theories
   (union-theories (theory 'ground-zero) (union-theories (executable-counterpart-theory :here)
    '(fn-lb-catalog-distinct-log-keyp)))
   '((:executable-counterpart fn-lb-catalog-distinct-log-keyp))))))
(defthm fn-lbsa-remove-segment-whole-witness
 (and (fn-lb-served-log-invp (fn-lbsa-log) '(nil nil) (fn-lbcc-test-one-state) (list (fn-lbcc-test-decided-row))) (fn-lb-catalog-distinct-log-keyp (fn-lbsa-incoming) (list (fn-lbcc-test-decided-row))) (fn-cat-rowp (fn-lbsa-incoming)) (fn-cbor-octet-listp *fn-lbr13-payload*) (not (unsigned-byte-p 64 -1)) (not (fn-lb-served-log-invp (fn-lb-log-model-append (fn-lbsa-incoming) *fn-lbr13-payload* -1 (fn-lbsa-log)) '(nil nil) (fn-lbcc-test-one-state) (list (fn-lbcc-test-decided-row))))) :rule-classes nil
 :hints (("Goal" :use (fn-lbsa-append-whole-positive fn-lbsa-segment-type-post-invariant-fails)
  :in-theory (set-difference-theories
   (union-theories (theory 'ground-zero) (union-theories (executable-counterpart-theory :here)
    '(fn-lb-catalog-distinct-log-keyp)))
   '((:executable-counterpart fn-lb-catalog-distinct-log-keyp))))))
(defthm fn-lbsa-overwrite-whole-witness
 (and (fn-lb-served-log-invp (fn-lbsa-log) '(nil nil) (fn-lbcc-test-one-state) (list (fn-lbcc-test-decided-row))) (fn-lb-catalog-distinct-log-keyp (fn-lbsa-incoming) (list (fn-lbcc-test-decided-row))) (fn-cat-rowp (fn-lbsa-incoming)) (fn-cbor-octet-listp *fn-lbr13-payload*) (unsigned-byte-p 64 2) (fn-lb-served-log-invp (fn-lb-log-model-append (fn-lbsa-incoming) *fn-lbr13-payload* 2 (fn-lbsa-log)) '(nil nil) (fn-lbcc-test-one-state) (list (fn-lbcc-test-decided-row))) (not (fn-lb-served-log-invp (fn-lbsa-overwrite-after-append (fn-lbsa-incoming) *fn-lbr13-payload* 2 (fn-lbsa-log)) '(nil nil) (fn-lbcc-test-one-state) (list (fn-lbcc-test-decided-row))))) :rule-classes nil
 :hints (("Goal" :use (fn-lbsa-append-whole-positive fn-lbsa-overwrite-falsifies-served-invariant)
  :in-theory (theory 'ground-zero))))
(defteeth fn-lb-served-log-invp-of-append
 :claim (((invariant (fn-lb-served-log-invp log fn-lb-vmap-v fn-lbc-v rows)) (fresh-key (fn-lb-catalog-distinct-log-keyp row rows)) (row-type (fn-cat-rowp row)) (octets (fn-cbor-octet-listp payload)) (segment (unsigned-byte-p 64 target))) (fn-lb-served-log-invp (fn-lb-log-model-append row payload target log) fn-lb-vmap-v fn-lbc-v rows))
 :subject fn-lb-log-model-append :witness ((log (fn-lbsa-log)) (fn-lb-vmap-v '(nil nil)) (fn-lbc-v (fn-lbcc-test-one-state)) (rows (list (fn-lbcc-test-decided-row))) (row (fn-lbsa-incoming)) (payload *fn-lbr13-payload*) (target 2))
 :witness-lemma fn-lbsa-append-whole-positive
 :breaks (
 (invariant ((log (fn-lbsa-corrupt-pre-log)) (fn-lb-vmap-v '(nil nil)) (fn-lbc-v (fn-lbcc-test-one-state)) (rows (list (fn-lbcc-test-decided-row))) (row (fn-lbsa-incoming)) (payload *fn-lbr13-payload*) (target 2)) :lemma fn-lbsa-remove-invariant-whole-witness)
 (fresh-key ((log (fn-lbsa-shadow-base-log)) (fn-lb-vmap-v '(nil nil)) (fn-lbc-v (fn-lbsa-shadow-base-columns)) (rows (list (fn-lbcc-test-decided-row))) (row (fn-lbcc-test-decided-row)) (payload nil) (target 0)) :lemma fn-lbsa-remove-fresh-key-whole-witness)
 (row-type ((log (fn-lbsa-log)) (fn-lb-vmap-v '(nil nil)) (fn-lbc-v (fn-lbcc-test-one-state)) (rows (list (fn-lbcc-test-decided-row))) (row (update-nth 4 -1 (fn-lbsa-incoming))) (payload *fn-lbr13-payload*) (target 2)) :lemma fn-lbsa-remove-row-type-whole-witness :logical "The removed incoming type premise is deliberately false; this is a logical domain boundary witness")
 (octets ((log (fn-lbsa-log)) (fn-lb-vmap-v '(nil nil)) (fn-lbc-v (fn-lbcc-test-one-state)) (rows (list (fn-lbcc-test-decided-row))) (row (fn-lbsa-incoming)) (payload '(999)) (target 2)) :lemma fn-lbsa-remove-octets-whole-witness :logical "The removed incoming type premise is deliberately false; this is a logical domain boundary witness")
 (segment ((log (fn-lbsa-log)) (fn-lb-vmap-v '(nil nil)) (fn-lbc-v (fn-lbcc-test-one-state)) (rows (list (fn-lbcc-test-decided-row))) (row (fn-lbsa-incoming)) (payload *fn-lbr13-payload*) (target -1)) :lemma fn-lbsa-remove-segment-whole-witness :logical "The removed incoming type premise is deliberately false; this is a logical domain boundary witness")
)
 :mutations ((overwrite-old-entry (:conclusion (fn-lb-served-log-invp (fn-lbsa-overwrite-after-append row payload target log) fn-lb-vmap-v fn-lbc-v rows)) ((log (fn-lbsa-log)) (fn-lb-vmap-v '(nil nil)) (fn-lbc-v (fn-lbcc-test-one-state)) (rows (list (fn-lbcc-test-decided-row))) (row (fn-lbsa-incoming)) (payload *fn-lbr13-payload*) (target 2))
  :fault "Append overwrites byte zero of a previously authenticated entry" :lemma fn-lbsa-overwrite-whole-witness)))

(defun fn-lbsa-native-append-controls ()
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-lbc
  (mv-let (ok fn-lbc)
   (let* ((row (fn-lbcc-test-decided-row)) (log (fn-lbsa-log))
          (fn-lbc (fn-lbc-open-rebuild (list row) log fn-lbc))
          (good (fn-lb-log-model-append (fn-lbsa-incoming) *fn-lbr13-payload* 2 log))
          (bad (fn-lbsa-overwrite-after-append (fn-lbsa-incoming) *fn-lbr13-payload* 2 log))
          (append-ok (and (equal (fn-lbc-count fn-lbc) 1)
           (fn-arx-entry-ok (fn-lb-entry-octets 1 6 log) (fn-lb-entry-protected-len 1 6 log))
           (fn-arx-entry-ok (fn-lb-entry-octets 1 6 good) (fn-lb-entry-protected-len 1 6 good))
           (not (fn-arx-entry-ok (fn-lb-entry-octets 1 6 bad) (fn-lb-entry-protected-len 1 6 bad)))))
          (shadow-base (fn-lbsa-shadow-base-log))
          (fn-lbc (fn-lbc-open-rebuild (list row) shadow-base fn-lbc))
          (shadow (fn-lb-log-model-append row nil 0 shadow-base)))
    (mv (and append-ok (equal (fn-lbc-value 0 :head-length fn-lbc) 12)
     (equal (fn-lb-log-payload row shadow-base) *fn-lbr13-payload*)
     (equal (fn-lb-log-payload row shadow) nil) (fn-lb-log-model-segsp shadow)) fn-lbc)) ok)))
(with-guard-checking-event t (assert-event (fn-lbsa-native-append-controls)))
