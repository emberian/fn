; Logical names keep the wide fixture compact; these builders never execute.
(in-package "ACL2")
(include-book "lb-recognizer-repair-fixtures")
(include-book "../../books/catalog-columns-native-open-invariant")

(defun-nx fn-lbr13-wide-empty () (update-nth *fn-lbc-overview-store* (make-list-ac 18446744073709551616 '(0) nil) (create-fn-lbc)))

(defun-nx fn-lbr13-single-log () (fn-lb-log-model-append (fn-lbr13-held) *fn-lbr13-payload* 1 nil))

(local (defthm fn-lbr1-single-log-agreement
 (fn-lb-retained-payloads-agreep (list (fn-lbr13-held)) (fn-lbr13-single-log))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-retained-payloads-agreep fn-lb-log-row-copies-agreep fn-lb-log-entries-payload-agreep
 fn-lbr13-single-log (:executable-counterpart fn-lbr13-held)
 (:executable-counterpart fn-record-sequence) (:executable-counterpart fn-record-payload)
 (:executable-counterpart fn-lb-log-model-append) (:executable-counterpart fn-lb-log-payload) nth))))))


(defun-nx fn-lbr13-wide-row-write () (fn-lbc-append-row (fn-lbr13-held) (fn-lbr13-single-log) (fn-lbr13-wide-empty)))

(defun-nx fn-lbr13-wide-indexed-write () (fn-lbr13-finish-single-row (fn-lbr13-held) (fn-lbr13-wide-row-write)))

(defun-nx fn-lbr13-clamped-row-write () (fn-lbr13-clamp-append-row (fn-lbr13-held) (fn-lbr13-single-log) (fn-lbr13-wide-empty)))

(defun-nx fn-lbr13-clamped-indexed-write () (fn-lbr13-finish-single-row (fn-lbr13-held) (fn-lbr13-clamped-row-write)))

(defthm fn-lbr13-render-nov-of-finish-single-row
   (equal (fn-lbc-render-nov i (fn-lbr13-finish-single-row row fn-lbc))
          (fn-lbc-render-nov i fn-lbc))
   :hints (("Goal" :do-not-induct t
    :in-theory (union-theories (theory 'ground-zero)
     '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-finish-single-row fn-lbc-render-nov-of-index-slots
       fn-lbc-render-nov-of-reserve-slots fn-lbc-render-nov-of-summary-groups-update
       fn-lbc-render-nov-of-rebuild-summaries fn-lbc-render-nov-of-number-put-row)))))

(defthm fn-lbr13-count-of-finish-single-row
   (equal (fn-lbc-count (fn-lbr13-finish-single-row row fn-lbc))
          (fn-lbc-count fn-lbc))
   :hints (("Goal" :do-not-induct t
    :in-theory (union-theories (theory 'ground-zero)
     '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-finish-single-row fn-lbc-count-of-index-slots
       fn-lbc-count-of-reserve-slots fn-lbc-count-of-summary-groups-update
       fn-lbc-count-of-rebuild-summaries fn-lbc-count-of-number-put-row)))))

(defthm fn-lbr13-directory-length-of-finish-single-row
   (equal (len (nth *fn-lbc-directory-store* (fn-lbr13-finish-single-row row fn-lbc)))
          (len (nth *fn-lbc-directory-store* fn-lbc)))
   :hints (("Goal" :do-not-induct t
    :in-theory (union-theories (theory 'ground-zero)
     '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-finish-single-row fn-lbwf-index-slots-field fn-lbwf-reserve-slots-field
       fn-lbwf-rebuild-summaries-field fn-lbwf-number-put-row-field
       update-fn-lbc-summary-groups fn-dm-nth-update-nth
       (:executable-counterpart member-equal) (:executable-counterpart natp)
       (:executable-counterpart equal) (:executable-counterpart nfix))))))

(in-theory (disable fn-lbr13-wide-empty (:executable-counterpart fn-lbr13-wide-empty) fn-lbr13-single-log (:executable-counterpart fn-lbr13-single-log) fn-lbr13-wide-row-write (:executable-counterpart fn-lbr13-wide-row-write) fn-lbr13-wide-indexed-write (:executable-counterpart fn-lbr13-wide-indexed-write) fn-lbr13-clamped-row-write (:executable-counterpart fn-lbr13-clamped-row-write) fn-lbr13-clamped-indexed-write (:executable-counterpart fn-lbr13-clamped-indexed-write)))

; BEGIN proved initial-state interface
(local (in-theory (disable (tau-system))))

(local (defun fn-lbr13-fixture-runes (runes)
 (declare (xargs :guard t :verify-guards t))
 (if (consp runes)
  (let* ((r (car runes)) (sym (ec-call (car (ec-call (cdr r)))))
         (name (if (symbolp sym) (symbol-name sym) "")))
   (if (and (member-eq (ec-call (car r)) '(:definition :rewrite :type-prescription))
            (equal (subseq name 0 (min 9 (length name))) "FN-LBR13-"))
       (cons r (fn-lbr13-fixture-runes (cdr runes)))
     (fn-lbr13-fixture-runes (cdr runes)))) nil)))

(local
 (defthm fn-lbr13-repeat-zero
  (equal (make-list-ac 0 item acc) acc)
  :hints (("Goal" :in-theory (enable make-list-ac)))))

(local
 (defthm fn-lbr13-repeat-three
  (equal (make-list-ac 3 item acc) (cons item (cons item (cons item acc))))
  :hints
  (("Goal"
    :expand ((make-list-ac 3 item acc)
             (make-list-ac 2 item (cons item acc))
             (make-list-ac 1 item (cons item (cons item acc))))
    :in-theory (enable make-list-ac)))))

(local (defun fn-lbr13-column-runes (runes kind)
 (declare (xargs :guard t :verify-guards t))
 (if (consp runes)
  (let* ((r (car runes)) (sym (ec-call (car (ec-call (cdr r)))))
         (name (if (symbolp sym) (symbol-name sym) "")))
   (if (and (equal (ec-call (car r)) kind)
            (or (equal (subseq name 0 (min 7 (length name))) "FN-LBC-")
                (equal (subseq name 0 (min 9 (length name))) "FN-LBR13-")
                (equal (subseq name 0 (min 6 (length name))) "FN-LB-")
                (equal (subseq name 0 (min 8 (length name))) "FN-DMAP-")
                (equal (subseq name 0 (min 9 (length name))) "FN-ARENA-")
                (equal sym 'create-fn-arena)
                (equal sym 'create-fn-lbc)))
       (cons r (fn-lbr13-column-runes (cdr runes) kind))
     (fn-lbr13-column-runes (cdr runes) kind))) nil))
)

(local (defthm fn-lbr13-repeat-true-list
 (implies (and (natp n) (true-listp acc))
          (true-listp (make-list-ac n item acc)))
 :hints (("Goal" :induct (make-list-ac n item acc)))))

(local (defthm fn-lbr13-repeat-length
 (implies (natp n)
          (equal (len (make-list-ac n item acc)) (+ n (len acc))))
 :hints (("Goal" :induct (make-list-ac n item acc)))))

(local (defthm fn-lbr13-repeat-schema
 (implies (and (natp n) (adt-rec-p schema item) (adt-seq-p schema acc))
          (adt-seq-p schema (make-list-ac n item acc)))
 :hints (("Goal" :induct (make-list-ac n item acc)
                  :in-theory (enable make-list-ac adt-seq-p)))))

(local (defthm fn-lbr13-repeat-consp
 (implies (and (natp n) (or (posp n) (consp acc)))
          (consp (make-list-ac n item acc)))
 :hints (("Goal" :induct (make-list-ac n item acc)))))

(local (defthm fn-lbr13-repeat-car
 (implies (and (natp n)
              (or (posp n) (and (consp acc) (equal (car acc) item))))
          (equal (car (make-list-ac n item acc)) item))
 :hints (("Goal" :induct (make-list-ac n item acc)))))

(local (in-theory (disable make-list-ac (:executable-counterpart make-list-ac))))

(local (defthm fn-lbr13-repeat-first-after-append
 (implies (posp n)
          (equal (car (append (make-list-ac n item nil) tail)) item))
 :hints (("Goal" :do-not-induct t
                  :use ((:instance fn-lbr13-repeat-consp (acc nil))
                        (:instance fn-lbr13-repeat-car (acc nil)))
                  :expand ((binary-append (make-list-ac n item nil) tail))))))

(defthm fn-lbr13-wide-empty-p
(fn-lbc-p (fn-lbr13-wide-empty))
 :hints (("Goal" :do-not-induct t
 :expand ((fn-lbr13-wide-empty)) :in-theory (set-difference-theories (union-theories (current-theory :here)
 (fn-lbr13-column-runes (current-theory :here) :definition))
 (append '((tau-system) (:definition make-list-ac) (:executable-counterpart make-list-ac))
 (fn-lbr13-column-runes (current-theory :here) :executable-counterpart))))))

(defthm fn-lbr13-wide-empty-count
(equal (fn-lbc-count (fn-lbr13-wide-empty)) 0)
 :hints (("Goal" :do-not-induct t
 :expand ((fn-lbr13-wide-empty)) :in-theory (set-difference-theories (union-theories (current-theory :here)
 (fn-lbr13-column-runes (current-theory :here) :definition))
 (append '((tau-system) (:definition make-list-ac) (:executable-counterpart make-list-ac))
 (fn-lbr13-column-runes (current-theory :here) :executable-counterpart))))))

(defthm fn-lbr13-wide-empty-directory-count
(equal (fn-lbc-directory-count (nth *fn-lbc-directory-store* (fn-lbr13-wide-empty))) 0)
 :hints (("Goal" :do-not-induct t
 :expand ((fn-lbr13-wide-empty)) :in-theory (set-difference-theories (union-theories (current-theory :here)
 (fn-lbr13-column-runes (current-theory :here) :definition))
 (append '((tau-system) (:definition make-list-ac) (:executable-counterpart make-list-ac))
 (fn-lbr13-column-runes (current-theory :here) :executable-counterpart))))))

(defthm fn-lbr13-wide-empty-pool-layout
(fn-lb-columns-pool-layoutp (fn-lbr13-wide-empty))
 :hints (("Goal" :do-not-induct t
 :expand ((fn-lbr13-wide-empty)) :in-theory (set-difference-theories (union-theories (current-theory :here)
 (fn-lbr13-column-runes (current-theory :here) :definition))
 (append '((tau-system) (:definition make-list-ac) (:executable-counterpart make-list-ac))
 (fn-lbr13-column-runes (current-theory :here) :executable-counterpart))))))

(defthm fn-lbr13-wide-empty-directory-alignment
(fn-lb-columns-directory-alignedp (fn-lbr13-wide-empty))
 :hints (("Goal" :do-not-induct t
 :expand ((fn-lbr13-wide-empty)) :in-theory (set-difference-theories (union-theories (current-theory :here)
 (fn-lbr13-column-runes (current-theory :here) :definition))
 (append '((tau-system) (:definition make-list-ac) (:executable-counterpart make-list-ac))
 (fn-lbr13-column-runes (current-theory :here) :executable-counterpart))))))

(defthm fn-lbr13-wide-empty-escape-domain
(fn-lbc-escape-cellsp 0 (fn-lbr13-wide-empty))
 :hints (("Goal" :do-not-induct t
 :expand ((fn-lbr13-wide-empty)) :in-theory (set-difference-theories (union-theories (current-theory :here)
 (fn-lbr13-column-runes (current-theory :here) :definition))
 (append '((tau-system) (:definition make-list-ac) (:executable-counterpart make-list-ac))
 (fn-lbr13-column-runes (current-theory :here) :executable-counterpart))))))

; BEGIN proved log interface
(defthm fn-lbr13-single-log-segsp
 (fn-lb-log-model-segsp (fn-lbr13-single-log))
 :hints (("Goal" :do-not-induct t
 :expand ((fn-lbr13-single-log))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lb-log-append-preserves-type fn-lb-log-model-append-preserves-layout
 fn-lb-log-append-fresh-row-entry fn-lb-log-append-fresh-row-segment
 fn-lb-log-row-sourcep-of-fresh-append
 fn-lb-log-model-row-entry fn-lb-log-model-row-segment fn-lb-log-model-segment
 fn-lb-log-model-segsp fn-lb-log-layoutp
 fn-lb-log-next-entry-payload-by-definition fn-lb-log-next-entry-served-offset-by-definition
 fn-lb-log-next-entry-served-length-by-definition
 fn-lb-log-model-next-range fn-lbc-row-log-guardp
 (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-cat-rowp)
 (:executable-counterpart fn-cbor-octet-listp) (:executable-counterpart fn-record-payload)
 (:executable-counterpart fn-lb-log-model-pre) (:executable-counterpart fn-rcl-tombstonep)
 (:executable-counterpart fn-la-payload-wire))))))

(defthm fn-lbr13-single-log-layout
 (fn-lb-log-layoutp (fn-lbr13-single-log))
 :hints (("Goal" :do-not-induct t
 :expand ((fn-lbr13-single-log))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lb-log-append-preserves-type fn-lb-log-model-append-preserves-layout
 fn-lb-log-append-fresh-row-entry fn-lb-log-append-fresh-row-segment
 fn-lb-log-row-sourcep-of-fresh-append
 fn-lb-log-model-row-entry fn-lb-log-model-row-segment fn-lb-log-model-segment
 fn-lb-log-model-segsp fn-lb-log-layoutp
 fn-lb-log-next-entry-payload-by-definition fn-lb-log-next-entry-served-offset-by-definition
 fn-lb-log-next-entry-served-length-by-definition
 fn-lb-log-model-next-range fn-lbc-row-log-guardp
 (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-cat-rowp)
 (:executable-counterpart fn-cbor-octet-listp) (:executable-counterpart fn-record-payload)
 (:executable-counterpart fn-lb-log-model-pre) (:executable-counterpart fn-rcl-tombstonep)
 (:executable-counterpart fn-la-payload-wire))))))

(defthm fn-lbr13-single-log-payload
 (equal (nth 6 (fn-lb-log-model-row-entry (fn-lbr13-held) (fn-lbr13-single-log))) *fn-lbr13-payload*)
 :hints (("Goal" :do-not-induct t
 :expand ((fn-lbr13-single-log))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lb-log-append-preserves-type fn-lb-log-model-append-preserves-layout
 fn-lb-log-append-fresh-row-entry fn-lb-log-append-fresh-row-segment
 fn-lb-log-row-sourcep-of-fresh-append
 fn-lb-log-model-row-entry fn-lb-log-model-row-segment fn-lb-log-model-segment
 fn-lb-log-model-segsp fn-lb-log-layoutp
 fn-lb-log-next-entry-payload-by-definition fn-lb-log-next-entry-served-offset-by-definition
 fn-lb-log-next-entry-served-length-by-definition
 fn-lb-log-model-next-range fn-lbc-row-log-guardp
 (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-cat-rowp)
 (:executable-counterpart fn-cbor-octet-listp) (:executable-counterpart fn-record-payload)
 (:executable-counterpart fn-lb-log-model-pre) (:executable-counterpart fn-rcl-tombstonep)
 (:executable-counterpart fn-la-payload-wire))))))

(defthm fn-lbr13-single-log-segment
 (equal (fn-lb-log-model-row-segment (fn-lbr13-held) (fn-lbr13-single-log)) 1)
 :hints (("Goal" :do-not-induct t
 :expand ((fn-lbr13-single-log))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lb-log-append-preserves-type fn-lb-log-model-append-preserves-layout
 fn-lb-log-append-fresh-row-entry fn-lb-log-append-fresh-row-segment
 fn-lb-log-row-sourcep-of-fresh-append
 fn-lb-log-model-row-entry fn-lb-log-model-row-segment fn-lb-log-model-segment
 fn-lb-log-model-segsp fn-lb-log-layoutp
 fn-lb-log-next-entry-payload-by-definition fn-lb-log-next-entry-served-offset-by-definition
 fn-lb-log-next-entry-served-length-by-definition
 fn-lb-log-model-next-range fn-lbc-row-log-guardp
 (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-cat-rowp)
 (:executable-counterpart fn-cbor-octet-listp) (:executable-counterpart fn-record-payload)
 (:executable-counterpart fn-lb-log-model-pre) (:executable-counterpart fn-rcl-tombstonep)
 (:executable-counterpart fn-la-payload-wire))))))

(defthm fn-lbr13-single-log-row-profile
 (fn-lbc-row-log-guardp (fn-lbr13-held) (fn-lbr13-single-log))
 :hints (("Goal" :do-not-induct t
 :expand ((fn-lbr13-single-log))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lb-log-append-preserves-type fn-lb-log-model-append-preserves-layout
 fn-lb-log-append-fresh-row-entry fn-lb-log-append-fresh-row-segment
 fn-lb-log-row-sourcep-of-fresh-append
 fn-lb-log-model-row-entry fn-lb-log-model-row-segment fn-lb-log-model-segment
 fn-lb-log-model-segsp fn-lb-log-layoutp
 fn-lb-log-next-entry-payload-by-definition fn-lb-log-next-entry-served-offset-by-definition
 fn-lb-log-next-entry-served-length-by-definition
 fn-lb-log-model-next-range fn-lbc-row-log-guardp
 (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-cat-rowp)
 (:executable-counterpart fn-cbor-octet-listp) (:executable-counterpart fn-record-payload)
 (:executable-counterpart fn-lb-log-model-pre) (:executable-counterpart fn-rcl-tombstonep)
 (:executable-counterpart fn-la-payload-wire))))))

(defthm fn-lbr13-single-log-row-source
 (fn-lb-log-row-sourcep (fn-lbr13-held) (fn-lbr13-single-log))
 :hints (("Goal" :do-not-induct t
 :expand ((fn-lbr13-single-log))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lb-log-append-preserves-type fn-lb-log-model-append-preserves-layout
 fn-lb-log-append-fresh-row-entry fn-lb-log-append-fresh-row-segment
 fn-lb-log-row-sourcep-of-fresh-append
 fn-lb-log-model-row-entry fn-lb-log-model-row-segment fn-lb-log-model-segment
 fn-lb-log-model-segsp fn-lb-log-layoutp
 fn-lb-log-next-entry-payload-by-definition fn-lb-log-next-entry-served-offset-by-definition
 fn-lb-log-next-entry-served-length-by-definition
 fn-lb-log-model-next-range fn-lbc-row-log-guardp
 (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-cat-rowp)
 (:executable-counterpart fn-cbor-octet-listp) (:executable-counterpart fn-record-payload)
 (:executable-counterpart fn-lb-log-model-pre) (:executable-counterpart fn-rcl-tombstonep)
 (:executable-counterpart fn-la-payload-wire))))))

; BEGIN proved actual wide row write
(defthm fn-lbr13-wide-row-write-p
 (fn-lbc-p (fn-lbr13-wide-row-write))
 :hints (("Goal" :do-not-induct t
 :expand ((fn-lbr13-wide-row-write))
 :use ((:instance fn-lbr13-wide-empty-p) (:instance fn-lbr13-wide-empty-count) (:instance fn-lbr13-wide-empty-directory-count) (:instance fn-lbr13-wide-empty-pool-layout) (:instance fn-lbr13-wide-empty-directory-alignment) (:instance fn-lbr13-single-log-segsp) (:instance fn-lbr13-single-log-layout) (:instance fn-lbr13-single-log-payload) (:instance fn-lbr13-single-log-row-profile) (:instance fn-lbr13-single-log-row-source) (:instance fn-lbc-render-nov-of-append-row-new (row (fn-lbr13-held)) (log (fn-lbr13-single-log)) (fn-lbc (fn-lbr13-wide-empty))) (:instance fn-lbc-row-corr-from-row-source (row (fn-lbr13-held)) (log (fn-lbr13-single-log)) (fn-lbc (fn-lbr13-wide-empty))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbc-p-of-append-row fn-lbc-count-of-append-row fn-lbc-append-row-directory-count
 fn-lbc-directory-count-is-len fn-lbr13-wide-empty-count
 fn-lbr13-wide-empty-p
 fn-lbr13-wide-empty-pool-layout fn-lbr13-wide-empty-directory-alignment
 fn-lbr13-single-log-segsp fn-lbr13-single-log-layout fn-lbr13-single-log-payload
 fn-lbr13-single-log-row-profile fn-lbr13-single-log-row-source
 (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-cat-rowp)
 (:executable-counterpart fn-record-stamp) (:executable-counterpart fn-hnov-of))))))

(defthm fn-lbr13-wide-row-write-count
 (equal (fn-lbc-count (fn-lbr13-wide-row-write)) 1)
 :hints (("Goal" :do-not-induct t
 :expand ((fn-lbr13-wide-row-write))
 :use ((:instance fn-lbr13-wide-empty-p) (:instance fn-lbr13-wide-empty-count) (:instance fn-lbr13-wide-empty-directory-count) (:instance fn-lbr13-wide-empty-pool-layout) (:instance fn-lbr13-wide-empty-directory-alignment) (:instance fn-lbr13-single-log-segsp) (:instance fn-lbr13-single-log-layout) (:instance fn-lbr13-single-log-payload) (:instance fn-lbr13-single-log-row-profile) (:instance fn-lbr13-single-log-row-source) (:instance fn-lbc-render-nov-of-append-row-new (row (fn-lbr13-held)) (log (fn-lbr13-single-log)) (fn-lbc (fn-lbr13-wide-empty))) (:instance fn-lbc-row-corr-from-row-source (row (fn-lbr13-held)) (log (fn-lbr13-single-log)) (fn-lbc (fn-lbr13-wide-empty))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbc-p-of-append-row fn-lbc-count-of-append-row fn-lbc-append-row-directory-count
 fn-lbc-directory-count-is-len fn-lbr13-wide-empty-count
 fn-lbr13-wide-empty-p
 fn-lbr13-wide-empty-pool-layout fn-lbr13-wide-empty-directory-alignment
 fn-lbr13-single-log-segsp fn-lbr13-single-log-layout fn-lbr13-single-log-payload
 fn-lbr13-single-log-row-profile fn-lbr13-single-log-row-source
 (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-cat-rowp)
 (:executable-counterpart fn-record-stamp) (:executable-counterpart fn-hnov-of))))))

(defthm fn-lbr13-wide-row-write-directory-count
 (equal (fn-lbc-directory-count (nth *fn-lbc-directory-store* (fn-lbr13-wide-row-write))) 1)
 :hints (("Goal" :do-not-induct t
 :expand ((fn-lbr13-wide-row-write))
 :use ((:instance fn-lbr13-wide-empty-p) (:instance fn-lbr13-wide-empty-count) (:instance fn-lbr13-wide-empty-directory-count) (:instance fn-lbr13-wide-empty-pool-layout) (:instance fn-lbr13-wide-empty-directory-alignment) (:instance fn-lbr13-single-log-segsp) (:instance fn-lbr13-single-log-layout) (:instance fn-lbr13-single-log-payload) (:instance fn-lbr13-single-log-row-profile) (:instance fn-lbr13-single-log-row-source) (:instance fn-lbc-render-nov-of-append-row-new (row (fn-lbr13-held)) (log (fn-lbr13-single-log)) (fn-lbc (fn-lbr13-wide-empty))) (:instance fn-lbc-row-corr-from-row-source (row (fn-lbr13-held)) (log (fn-lbr13-single-log)) (fn-lbc (fn-lbr13-wide-empty))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbc-p-of-append-row fn-lbc-count-of-append-row fn-lbc-append-row-directory-count
 fn-lbc-directory-count-is-len fn-lbr13-wide-empty-count
 fn-lbr13-wide-empty-p
 fn-lbr13-wide-empty-pool-layout fn-lbr13-wide-empty-directory-alignment
 fn-lbr13-single-log-segsp fn-lbr13-single-log-layout fn-lbr13-single-log-payload
 fn-lbr13-single-log-row-profile fn-lbr13-single-log-row-source
 (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-cat-rowp)
 (:executable-counterpart fn-record-stamp) (:executable-counterpart fn-hnov-of))))))

(defthm fn-lbr13-wide-row-write-render
 (equal (fn-lbc-render-nov 0 (fn-lbr13-wide-row-write)) (fn-hnov-of *fn-lbr13-payload*))
 :hints (("Goal" :do-not-induct t
 :expand ((fn-lbr13-wide-row-write))
 :use ((:instance fn-lbr13-wide-empty-p) (:instance fn-lbr13-wide-empty-count) (:instance fn-lbr13-wide-empty-directory-count) (:instance fn-lbr13-wide-empty-pool-layout) (:instance fn-lbr13-wide-empty-directory-alignment) (:instance fn-lbr13-single-log-segsp) (:instance fn-lbr13-single-log-layout) (:instance fn-lbr13-single-log-payload) (:instance fn-lbr13-single-log-row-profile) (:instance fn-lbr13-single-log-row-source) (:instance fn-lbc-render-nov-of-append-row-new (row (fn-lbr13-held)) (log (fn-lbr13-single-log)) (fn-lbc (fn-lbr13-wide-empty))) (:instance fn-lbc-row-corr-from-row-source (row (fn-lbr13-held)) (log (fn-lbr13-single-log)) (fn-lbc (fn-lbr13-wide-empty))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbc-p-of-append-row fn-lbc-count-of-append-row fn-lbc-append-row-directory-count
 fn-lbc-directory-count-is-len fn-lbr13-wide-empty-count
 fn-lbr13-wide-empty-p
 fn-lbr13-wide-empty-pool-layout fn-lbr13-wide-empty-directory-alignment
 fn-lbr13-single-log-segsp fn-lbr13-single-log-layout fn-lbr13-single-log-payload
 fn-lbr13-single-log-row-profile fn-lbr13-single-log-row-source
 (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-cat-rowp)
 (:executable-counterpart fn-record-stamp) (:executable-counterpart fn-hnov-of))))))

(defthm fn-lbr13-wide-row-write-row-corr
 (fn-lbc-row-corr 0 (fn-lbr13-held) 5 (fn-lbr13-wide-row-write) (fn-lbr13-single-log))
 :hints (("Goal" :do-not-induct t
 :expand ((fn-lbr13-wide-row-write))
 :use ((:instance fn-lbr13-wide-empty-p) (:instance fn-lbr13-wide-empty-count) (:instance fn-lbr13-wide-empty-directory-count) (:instance fn-lbr13-wide-empty-pool-layout) (:instance fn-lbr13-wide-empty-directory-alignment) (:instance fn-lbr13-single-log-segsp) (:instance fn-lbr13-single-log-layout) (:instance fn-lbr13-single-log-payload) (:instance fn-lbr13-single-log-row-profile) (:instance fn-lbr13-single-log-row-source) (:instance fn-lbc-render-nov-of-append-row-new (row (fn-lbr13-held)) (log (fn-lbr13-single-log)) (fn-lbc (fn-lbr13-wide-empty))) (:instance fn-lbc-row-corr-from-row-source (row (fn-lbr13-held)) (log (fn-lbr13-single-log)) (fn-lbc (fn-lbr13-wide-empty))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbc-p-of-append-row fn-lbc-count-of-append-row fn-lbc-append-row-directory-count
 fn-lbc-directory-count-is-len fn-lbr13-wide-empty-count
 fn-lbr13-wide-empty-p
 fn-lbr13-wide-empty-pool-layout fn-lbr13-wide-empty-directory-alignment
 fn-lbr13-single-log-segsp fn-lbr13-single-log-layout fn-lbr13-single-log-payload
 fn-lbr13-single-log-row-profile fn-lbr13-single-log-row-source
 (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-cat-rowp)
 (:executable-counterpart fn-record-stamp) (:executable-counterpart fn-hnov-of))))))

; BEGIN proved indexing-tail interface
(defthm fn-lbr13-p-of-finish-single-row
 (implies (fn-lbc-p fn-lbc) (fn-lbc-p (fn-lbr13-finish-single-row row fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-finish-single-row fn-lbc-p-of-number-put-row fn-lbc-p-of-rebuild-summaries
 fn-lbc-p-of-update-summary-groups fn-lbc-p-of-reserve-slots fn-lbc-p-of-index-slots)))))

(defthm fn-lbr13-row-corr-of-finish-single-row
 (implies (and (fn-lbc-p fn-lbc) (natp i) (< i (fn-lbc-count fn-lbc)))
 (equal (fn-lbc-row-corr i old pm (fn-lbr13-finish-single-row row fn-lbc) log)
        (fn-lbc-row-corr i old pm fn-lbc log)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-finish-single-row fn-lbc-row-corr-of-number-put-row
 fn-lbc-row-corr-of-rebuild-summaries fn-lbc-row-corr-of-summary-groups-update
 fn-lbc-row-corr-of-reserve-slots fn-lbc-row-corr-of-index-slots
 fn-lbc-p-of-number-put-row fn-lbc-p-of-rebuild-summaries
 fn-lbc-p-of-update-summary-groups fn-lbc-p-of-reserve-slots
 fn-lbc-count-of-number-put-row fn-lbc-count-of-rebuild-summaries
 fn-lbc-count-of-summary-groups-update fn-lbc-count-of-reserve-slots)))))

(defthm fn-lbr13-wide-indexed-write-p
(fn-lbc-p (fn-lbr13-wide-indexed-write))
 :hints (("Goal" :do-not-induct t
 :expand ((fn-lbr13-wide-indexed-write))
 :use ((:instance fn-lbr13-wide-row-write-directory-count))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-p-of-finish-single-row fn-lbr13-count-of-finish-single-row
 fn-lbr13-directory-length-of-finish-single-row fn-lbr13-render-nov-of-finish-single-row
 fn-lbr13-row-corr-of-finish-single-row fn-lbr13-wide-row-write-p
 fn-lbr13-wide-row-write-count fn-lbr13-wide-row-write-render fn-lbr13-wide-row-write-row-corr
 fn-lbc-directory-count-is-len)))))

(defthm fn-lbr13-wide-indexed-write-count
(equal (fn-lbc-count (fn-lbr13-wide-indexed-write)) 1)
 :hints (("Goal" :do-not-induct t
 :expand ((fn-lbr13-wide-indexed-write))
 :use ((:instance fn-lbr13-wide-row-write-directory-count))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-p-of-finish-single-row fn-lbr13-count-of-finish-single-row
 fn-lbr13-directory-length-of-finish-single-row fn-lbr13-render-nov-of-finish-single-row
 fn-lbr13-row-corr-of-finish-single-row fn-lbr13-wide-row-write-p
 fn-lbr13-wide-row-write-count fn-lbr13-wide-row-write-render fn-lbr13-wide-row-write-row-corr
 fn-lbc-directory-count-is-len)))))

(defthm fn-lbr13-wide-indexed-write-directory-count
(equal (fn-lbc-directory-count (nth *fn-lbc-directory-store* (fn-lbr13-wide-indexed-write))) 1)
 :hints (("Goal" :do-not-induct t
 :expand ((fn-lbr13-wide-indexed-write))
 :use ((:instance fn-lbr13-wide-row-write-directory-count))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-p-of-finish-single-row fn-lbr13-count-of-finish-single-row
 fn-lbr13-directory-length-of-finish-single-row fn-lbr13-render-nov-of-finish-single-row
 fn-lbr13-row-corr-of-finish-single-row fn-lbr13-wide-row-write-p
 fn-lbr13-wide-row-write-count fn-lbr13-wide-row-write-render fn-lbr13-wide-row-write-row-corr
 fn-lbc-directory-count-is-len)))))

(defthm fn-lbr13-wide-indexed-write-render
(equal (fn-lbc-render-nov 0 (fn-lbr13-wide-indexed-write)) (fn-hnov-of *fn-lbr13-payload*))
 :hints (("Goal" :do-not-induct t
 :expand ((fn-lbr13-wide-indexed-write))
 :use ((:instance fn-lbr13-wide-row-write-directory-count))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-p-of-finish-single-row fn-lbr13-count-of-finish-single-row
 fn-lbr13-directory-length-of-finish-single-row fn-lbr13-render-nov-of-finish-single-row
 fn-lbr13-row-corr-of-finish-single-row fn-lbr13-wide-row-write-p
 fn-lbr13-wide-row-write-count fn-lbr13-wide-row-write-render fn-lbr13-wide-row-write-row-corr
 fn-lbc-directory-count-is-len)))))

(defthm fn-lbr13-wide-indexed-write-row-corr
(fn-lbc-row-corr 0 (fn-lbr13-held) 5 (fn-lbr13-wide-indexed-write) (fn-lbr13-single-log))
 :hints (("Goal" :do-not-induct t
 :expand ((fn-lbr13-wide-indexed-write))
 :use ((:instance fn-lbr13-wide-row-write-directory-count))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-p-of-finish-single-row fn-lbr13-count-of-finish-single-row
 fn-lbr13-directory-length-of-finish-single-row fn-lbr13-render-nov-of-finish-single-row
 fn-lbr13-row-corr-of-finish-single-row fn-lbr13-wide-row-write-p
 fn-lbr13-wide-row-write-count fn-lbr13-wide-row-write-render fn-lbr13-wide-row-write-row-corr
 fn-lbc-directory-count-is-len)))))

; BEGIN indexed-correspondence-components
(defthm fn-lbr13-summary-groups-of-finish-single-row
   (equal (fn-lbc-summary-groups (fn-lbr13-finish-single-row row fn-lbc))
          (fn-lbc-row-group-keys (list row)))
   :hints (("Goal" :do-not-induct t
    :in-theory (union-theories (theory 'ground-zero)
     '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-finish-single-row fn-lbc-summary-groups
       fn-lbwf-index-slots-field fn-lbwf-reserve-slots-field
       update-fn-lbc-summary-groups fn-dm-nth-update-nth
       (:executable-counterpart member-equal) (:executable-counterpart natp)
       (:executable-counterpart equal) (:executable-counterpart nfix))))))

(defthm fn-lbr13-wide-indexed-write-summary-groups
   (equal (fn-lbc-summary-groups (fn-lbr13-wide-indexed-write))
          (fn-lbc-row-group-keys (list (fn-lbr13-held))))
   :hints (("Goal" :expand ((fn-lbr13-wide-indexed-write))
    :in-theory (union-theories (theory 'ground-zero)
     '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-summary-groups-of-finish-single-row)))))

(defthm fn-lbr13-wide-indexed-write-rows-corr
   (fn-lbc-rows-corr 0 (list (fn-lbr13-held)) 0
                    (fn-lbr13-wide-indexed-write) (fn-lbr13-single-log))
   :hints (("Goal" :do-not-induct t
    :use ((:instance fn-lbr13-wide-indexed-write-row-corr))
    :in-theory (union-theories (theory 'ground-zero)
     '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbc-rows-corr (:executable-counterpart fn-lbr13-held)
       (:executable-counterpart fn-record-stamp))))))

; BEGIN clean-corr-square
(local (defthm fn-lbr13-clear-create-unfolds
 (equal (fn-lbc-clear-columns (create-fn-lbc)) (create-fn-lbc))
 :hints (("Goal" :do-not-induct t
 :in-theory (e/d (fn-lbc-clear-columns create-fn-lbc create-fn-dmap
 fn-lbc-rowwords-clear-is-nil fn-lbc-msgid-octets-clear-is-nil
 fn-lbc-overview-octets-clear-is-nil fn-lbc-msgid-slots-clear-is-nil
 fn-lbc-directory-clear-is-nil fn-lbc-memberships-clear-is-nil fn-lbc-nov-clear-is-nil
 fn-lbc-escape-store-clear update-fn-lbc-slot-escape-keys update-fn-lbc-summary-groups fn-dmap-clear)
 ((:executable-counterpart fn-lbc-clear-columns) (:executable-counterpart create-fn-lbc)))))))

(local (defthm fn-lbr13-rebuild-one-row-unfolds
 (equal (fn-lbc-rebuild-rows (list row) log fn-lbc)
        (fn-lbc-number-put-row (fn-held-numbers row) (fn-lbc-count fn-lbc)
                              (fn-lbc-append-row row log fn-lbc)))
 :hints (("Goal" :do-not-induct t
 :expand ((fn-lbc-rebuild-rows (list row) log fn-lbc)
          (:free (state) (fn-lbc-rebuild-rows nil log state)))
 :in-theory (union-theories (theory 'minimal-theory) '(car-cons cdr-cons (:executable-counterpart consp)))))))

(local (defthm fn-lbr13-clean-single-write-is-open-rebuild
 (equal (fn-lbr13-finish-single-row row (fn-lbc-append-row row log (create-fn-lbc)))
        (fn-lbc-open-rebuild (list row) log (create-fn-lbc)))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbr13-clear-create-unfolds))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-finish-single-row fn-lbc-open-rebuild fn-lbr13-clear-create-unfolds
 fn-lbr13-rebuild-one-row-unfolds fn-lbc-count fn-lbc-row-store
 fn-lbc-rowwords-count-is-len create-fn-lbc create-fn-dmap
 (:executable-counterpart create-fn-dmap$a)))))))

(defthm fn-lbr13-clean-single-write-corr
 (fn-lbc-corr
 (fn-lbr13-finish-single-row (fn-lbr13-held)
  (fn-lbc-append-row (fn-lbr13-held) (fn-lbr13-single-log) (create-fn-lbc)))
 (list (fn-lbr13-held)) (fn-lbr13-single-log))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbr13-clean-single-write-is-open-rebuild (row (fn-lbr13-held)) (log (fn-lbr13-single-log)))
       (:instance fn-lbc-corr-of-open-rebuild
        (rows (list (fn-lbr13-held))) (log (fn-lbr13-single-log)) (fn-lbc (create-fn-lbc)))
       (:instance fn-lbr13-single-log-row-source)
       (:instance fn-lbr13-single-log-row-profile))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-clean-single-write-is-open-rebuild
 fn-cat-rowsp fn-lbc-rows-log-guardp fn-lb-log-rows-sourcep
 fn-lbr13-single-log-layout fn-lbr13-single-log-segsp
 create-fn-lbc create-fn-dmap
 (:executable-counterpart create-fn-dmap$a) (:executable-counterpart fn-lbc-p)
 (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-cat-rowp))))))

; BEGIN wide-number-store
(local (in-theory (disable (tau-system))))

(local (defthm fn-lbr13-wide-empty-number-store
 (equal (nth 3 (fn-lbr13-wide-empty)) (nth 3 (create-fn-lbc)))
 :hints (("Goal" :expand ((fn-lbr13-wide-empty)) :in-theory
 (union-theories (theory 'minimal-theory) '(fn-dm-nth-update-nth (:executable-counterpart equal) (:executable-counterpart natp) (:executable-counterpart nfix)))))))

(local (defthm fn-lbr13-wide-row-number-store
 (equal (nth 3 (fn-lbr13-wide-row-write)) (nth 3 (create-fn-lbc)))
 :hints (("Goal" :expand ((fn-lbr13-wide-row-write)) :in-theory
 (union-theories (theory 'minimal-theory) '(fn-lbwf-append-row-field
 fn-lbr13-wide-empty-number-store (:executable-counterpart natp) (:executable-counterpart member-equal)))))))

(local (defthm fn-lbr13-single-finish-number-store-congruence
 (implies (equal (nth 3 a) (nth 3 b))
 (equal (nth 3 (fn-lbr13-finish-single-row (fn-lbr13-held) a))
        (nth 3 (fn-lbr13-finish-single-row (fn-lbr13-held) b))))
 :hints (("Goal" :do-not-induct t :in-theory
 (union-theories (theory 'ground-zero)
 '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-finish-single-row fn-lbc-number-put-row fn-lbc-number-put-row-seen
 fn-lbc-number-put-first fn-lbc-number-store update-fn-lbc-number-store
 fn-lbc-rebuild-summaries fn-lbc-summary-put fn-lbc-row-group-keys fn-lbc-number-group-keys
 fn-lbwf-index-slots-field fn-lbwf-reserve-slots-field update-fn-lbc-summary-groups
 fn-dm-nth-update-nth
 (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-held-numbers)
 (:executable-counterpart fn-cat$a-group-live-count) (:executable-counterpart fn-cat$a-group-live-low)
 (:executable-counterpart fn-cat$a-group-live-high) (:executable-counterpart fn-cat$a-group-next)))))))

(defthm fn-lbr13-wide-indexed-number-store
 (equal (nth 3 (fn-lbr13-wide-indexed-write))
 (nth 3 (fn-lbr13-finish-single-row (fn-lbr13-held)
 (fn-lbc-append-row (fn-lbr13-held) (fn-lbr13-single-log) (create-fn-lbc)))))
 :hints (("Goal" :expand ((fn-lbr13-wide-indexed-write))
 :use ((:instance fn-lbr13-single-finish-number-store-congruence
 (a (fn-lbr13-wide-row-write))
 (b (fn-lbc-append-row (fn-lbr13-held) (fn-lbr13-single-log) (create-fn-lbc)))))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbr13-wide-row-number-store
 fn-lbwf-append-row-field (:executable-counterpart natp) (:executable-counterpart member-equal))))))

; BEGIN payload-log-facts
(defun-nx fn-lbr13-fresh-log () (fn-lb-log-model-append (fn-lbr13-held) *fn-lbr13-payload* 2 nil))

(defun-nx fn-lbr13-good-log () (append (fn-lbr13-single-log) (fn-lbr13-fresh-log)))

(defun-nx fn-lbr13-after-log () (fn-lb-log-model-recycle 1 (fn-lbr13-good-log)))

(local (defthm fn-lbr1-retained-log-agreement
 (fn-lb-retained-payloads-agreep (list (fn-lbr13-held)) (fn-lbr13-good-log))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-retained-payloads-agreep fn-lb-log-row-copies-agreep fn-lb-log-entries-payload-agreep
 fn-lbr13-single-log fn-lbr13-fresh-log fn-lbr13-good-log binary-append
 (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-record-sequence)
 (:executable-counterpart fn-record-payload) (:executable-counterpart fn-lb-log-model-append)
 (:executable-counterpart fn-lb-log-payload) nth))))))

(in-theory (disable fn-lbr13-fresh-log (:executable-counterpart fn-lbr13-fresh-log) fn-lbr13-good-log (:executable-counterpart fn-lbr13-good-log) fn-lbr13-after-log (:executable-counterpart fn-lbr13-after-log)))

(defthm fn-lbr13-fresh-segsp
 (fn-lb-log-model-segsp (fn-lbr13-fresh-log))
 :hints (("Goal" :do-not-induct t :in-theory
 (union-theories (theory 'ground-zero)
 '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-fresh-log fn-lbr13-good-log fn-lbr13-after-log fn-lbr13-single-log
 (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-lbr13-shadow-log)
 (:executable-counterpart fn-lbr13-old-log-model-segsp)
 (:executable-counterpart fn-lb-log-model-segsp) (:executable-counterpart fn-lb-log-model-append)
 (:executable-counterpart fn-lb-log-model-recycle))))))

(defthm fn-lbr13-good-segsp
 (fn-lb-log-model-segsp (fn-lbr13-good-log))
 :hints (("Goal" :do-not-induct t :in-theory
 (union-theories (theory 'ground-zero)
 '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-fresh-log fn-lbr13-good-log fn-lbr13-after-log fn-lbr13-single-log
 (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-lbr13-shadow-log)
 (:executable-counterpart fn-lbr13-old-log-model-segsp)
 (:executable-counterpart fn-lb-log-model-segsp) (:executable-counterpart fn-lb-log-model-append)
 (:executable-counterpart fn-lb-log-model-recycle))))))

(defthm fn-lbr13-after-is-fresh
 (equal (fn-lbr13-after-log) (fn-lbr13-fresh-log))
 :hints (("Goal" :do-not-induct t :in-theory
 (union-theories (theory 'ground-zero)
 '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-fresh-log fn-lbr13-good-log fn-lbr13-after-log fn-lbr13-single-log
 (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-lbr13-shadow-log)
 (:executable-counterpart fn-lbr13-old-log-model-segsp)
 (:executable-counterpart fn-lb-log-model-segsp) (:executable-counterpart fn-lb-log-model-append)
 (:executable-counterpart fn-lb-log-model-recycle))))))

(defthm fn-lbr13-bad-segsp-refused
 (not (fn-lb-log-model-segsp (fn-lbr13-shadow-log)))
 :hints (("Goal" :do-not-induct t :in-theory
 (union-theories (theory 'ground-zero)
 '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-fresh-log fn-lbr13-good-log fn-lbr13-after-log fn-lbr13-single-log
 (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-lbr13-shadow-log)
 (:executable-counterpart fn-lbr13-old-log-model-segsp)
 (:executable-counterpart fn-lb-log-model-segsp) (:executable-counterpart fn-lb-log-model-append)
 (:executable-counterpart fn-lb-log-model-recycle))))))

(defthm fn-lbr13-bad-old-segsp-accepted
 (fn-lbr13-old-log-model-segsp (fn-lbr13-shadow-log))
 :hints (("Goal" :do-not-induct t :in-theory
 (union-theories (theory 'ground-zero)
 '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-fresh-log fn-lbr13-good-log fn-lbr13-after-log fn-lbr13-single-log
 (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-lbr13-shadow-log)
 (:executable-counterpart fn-lbr13-old-log-model-segsp)
 (:executable-counterpart fn-lb-log-model-segsp) (:executable-counterpart fn-lb-log-model-append)
 (:executable-counterpart fn-lb-log-model-recycle))))))

; BEGIN wide-table-corr
(local (in-theory (disable (tau-system))))

(local (defthm fn-lbr13-number-keys-store-congruence
 (implies (equal (nth 3 a) (nth 3 b))
 (equal (fn-lbc-number-keys-covered numbers rows a) (fn-lbc-number-keys-covered numbers rows b)))
 :rule-classes nil
 :hints (("Goal" :induct (fn-lbc-number-keys-covered numbers rows a) :in-theory
 (union-theories (theory 'minimal-theory) '(fn-lbc-number-keys-covered fn-lbc-number-get fn-lbc-number-store))))))

(local (defthm fn-lbr13-number-rows-store-congruence
 (implies (equal (nth 3 a) (nth 3 b))
 (equal (fn-lbc-number-rows-covered rest rows a) (fn-lbc-number-rows-covered rest rows b)))
 :rule-classes nil
 :hints (("Goal" :induct (fn-lbc-number-rows-covered rest rows a)
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-number-rows-covered)))
 ("Subgoal *1/3" :use ((:instance fn-lbr13-number-keys-store-congruence (numbers (fn-held-numbers (car rest))))))
 ("Subgoal *1/2" :use ((:instance fn-lbr13-number-keys-store-congruence (numbers (fn-held-numbers (car rest))))))
 ("Subgoal *1/1" :use ((:instance fn-lbr13-number-keys-store-congruence (numbers (fn-held-numbers (car rest)))))))))

(local (defthm fn-lbr13-summaries-store-congruence
 (implies (equal (nth 3 a) (nth 3 b))
 (equal (fn-lbc-summaries-corr groups rows a) (fn-lbc-summaries-corr groups rows b)))
 :rule-classes nil
 :hints (("Goal" :induct (fn-lbc-summaries-corr groups rows a) :in-theory
 (union-theories (theory 'minimal-theory) '(fn-lbc-summaries-corr fn-lbc-live-summary fn-lbc-summary-word fn-lbc-number-store))))))

(local (defthm fn-lbr13-tables-store-congruence
 (implies (equal (nth 3 a) (nth 3 b))
 (equal (fn-lbc-tables-corr a rows) (fn-lbc-tables-corr b rows)))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-tables-corr))))))

(local (defthm fn-lbr13-corr-implies-tables
 (implies (fn-lbc-corr fn-lbc rows log) (fn-lbc-tables-corr fn-lbc rows))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-corr))))))

(defthm fn-lbr13-wide-indexed-write-tables-corr
 (fn-lbc-tables-corr (fn-lbr13-wide-indexed-write) (list (fn-lbr13-held)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbr13-tables-store-congruence
  (a (fn-lbr13-wide-indexed-write)) (b (fn-lbr13-finish-single-row (fn-lbr13-held) (fn-lbc-append-row (fn-lbr13-held) (fn-lbr13-single-log) (create-fn-lbc))))
  (rows (list (fn-lbr13-held))))
 (:instance fn-lbr13-corr-implies-tables (fn-lbc (fn-lbr13-finish-single-row (fn-lbr13-held) (fn-lbc-append-row (fn-lbr13-held) (fn-lbr13-single-log) (create-fn-lbc))))
 (rows (list (fn-lbr13-held))) (log (fn-lbr13-single-log)))
 (:instance fn-lbr13-clean-single-write-corr))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbr13-wide-indexed-number-store)))))

(local (defthm fn-lbr13-corr-implies-number-rows
 (implies (fn-lbc-corr fn-lbc rows log) (fn-lbc-number-rows-covered rows rows fn-lbc))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-corr))))))

(defthm fn-lbr13-wide-indexed-write-number-rows-corr
 (fn-lbc-number-rows-covered (list (fn-lbr13-held)) (list (fn-lbr13-held)) (fn-lbr13-wide-indexed-write))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbr13-number-rows-store-congruence
  (a (fn-lbr13-wide-indexed-write)) (b (fn-lbr13-finish-single-row (fn-lbr13-held) (fn-lbc-append-row (fn-lbr13-held) (fn-lbr13-single-log) (create-fn-lbc))))
  (rows (list (fn-lbr13-held))) (rest (list (fn-lbr13-held))))
 (:instance fn-lbr13-corr-implies-number-rows (fn-lbc (fn-lbr13-finish-single-row (fn-lbr13-held) (fn-lbc-append-row (fn-lbr13-held) (fn-lbr13-single-log) (create-fn-lbc))))
 (rows (list (fn-lbr13-held))) (log (fn-lbr13-single-log)))
 (:instance fn-lbr13-clean-single-write-corr))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbr13-wide-indexed-number-store)))))

(local (defthm fn-lbr13-corr-implies-summaries
 (implies (fn-lbc-corr fn-lbc rows log) (fn-lbc-summaries-corr (fn-lbc-row-group-keys rows) rows fn-lbc))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-corr))))))

(defthm fn-lbr13-wide-indexed-write-summaries-corr
 (fn-lbc-summaries-corr (fn-lbc-row-group-keys (list (fn-lbr13-held))) (list (fn-lbr13-held)) (fn-lbr13-wide-indexed-write))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbr13-summaries-store-congruence
  (a (fn-lbr13-wide-indexed-write)) (b (fn-lbr13-finish-single-row (fn-lbr13-held) (fn-lbc-append-row (fn-lbr13-held) (fn-lbr13-single-log) (create-fn-lbc))))
  (rows (list (fn-lbr13-held))) (groups (fn-lbc-row-group-keys (list (fn-lbr13-held)))))
 (:instance fn-lbr13-corr-implies-summaries (fn-lbc (fn-lbr13-finish-single-row (fn-lbr13-held) (fn-lbc-append-row (fn-lbr13-held) (fn-lbr13-single-log) (create-fn-lbc))))
 (rows (list (fn-lbr13-held))) (log (fn-lbr13-single-log)))
 (:instance fn-lbr13-clean-single-write-corr))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbr13-wide-indexed-number-store)))))

; BEGIN wide-slots-corr
(defun-nx fn-lbr13-wide-preindex ()
 (let* ((rows (list (fn-lbr13-held)))
        (fn-lbc (fn-lbc-number-put-row (fn-held-numbers (fn-lbr13-held)) 0 (fn-lbr13-wide-row-write)))
        (groups (fn-lbc-row-group-keys rows))
        (fn-lbc (fn-lbc-rebuild-summaries groups rows fn-lbc))
        (fn-lbc (update-fn-lbc-summary-groups groups fn-lbc)))
 (fn-lbc-reserve-slots (+ 1 (* 2 (len rows))) fn-lbc)))

(in-theory (disable fn-lbr13-wide-preindex (:executable-counterpart fn-lbr13-wide-preindex)))

(local
 (defthm fn-lbr13-slot-list-three
  (equal (make-list-ac 3 item acc) (cons item (cons item (cons item acc))))
  :hints
  (("Goal"
    :expand ((make-list-ac 3 item acc)
             (make-list-ac 2 item (cons item acc))
             (make-list-ac 1 item (cons item (cons item acc))))
    :in-theory (enable make-list-ac)))))

(local (defthm fn-lbr13-wide-indexed-by-preindex
 (equal (fn-lbr13-wide-indexed-write) (fn-lbc-index-slots 0 1 (fn-lbr13-wide-preindex)))
 :hints (("Goal" :do-not-induct t :in-theory (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-wide-indexed-write fn-lbr13-finish-single-row fn-lbr13-wide-preindex len)) '((:executable-counterpart make-list-ac)))))))

(local (defthm fn-lbr13-wide-row-empty-slot-store
 (equal (fn-lb-slot-store-model (fn-lbr13-wide-row-write)) nil)
 :hints (("Goal" :do-not-induct t :in-theory (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lb-slot-store-model-of-append-row fn-lbr13-wide-row-write fn-lbr13-wide-empty fn-lb-slot-store-model fn-dm-nth-update-nth create-fn-lbc create-fn-dmap)) '((:executable-counterpart make-list-ac)))))))

(local (defthm fn-lbr13-wide-preindex-raw-store
 (equal (fn-lb-slot-store-model (fn-lbr13-wide-preindex)) (fn-lb-zero-slot-records 3))
 :hints (("Goal" :do-not-induct t :in-theory (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-wide-preindex fn-lb-slot-store-model-of-reserve-slots fn-lb-slot-store-model-of-summary-groups-update fn-lb-slot-store-model-of-rebuild-summaries fn-lb-slot-store-model-of-number-put-row fn-lbr13-wide-row-empty-slot-store binary-append true-listp natp len)) '((:executable-counterpart make-list-ac)))))))

(local (defthm fn-lbr13-wide-preindex-capacity
 (equal (fn-lbc-slot-count (fn-lbr13-wide-preindex)) 3)
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbr13-wide-preindex-raw-store)) :in-theory (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbc-slot-count-by-store fn-lb-slot-store-model fn-lb-zero-slot-records-length nfix)) '((:executable-counterpart make-list-ac)))))))

(local (defthm fn-lbr13-wide-empty-owner-keys
 (equal (fn-lbc-slot-escape-keys (fn-lbr13-wide-empty)) nil)
 :hints (("Goal" :do-not-induct t :in-theory (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-wide-empty fn-lbc-slot-escape-keys fn-dm-nth-update-nth create-fn-lbc create-fn-dmap (:executable-counterpart create-fn-dmap$a))) '((:executable-counterpart make-list-ac)))))))

(local (defthm fn-lbr13-wide-row-owner-keys
 (equal (fn-lbc-slot-escape-keys (fn-lbr13-wide-row-write)) nil)
 :hints (("Goal" :do-not-induct t :in-theory (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-wide-row-write fn-lbc-slot-escape-keys-of-append-row fn-lbr13-wide-empty-owner-keys)) '((:executable-counterpart make-list-ac)))))))

(local (defthm fn-lbr13-wide-row-empty-slot-owner
 (equal (fn-lbc-escape 0 :msgid-slot (fn-lbr13-wide-row-write)) nil)
 :hints (("Goal" :do-not-induct t :in-theory (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-wide-row-write fn-lbc-slot-escape-of-append-row fn-lbr13-wide-empty-count)) '((:executable-counterpart make-list-ac)))))))

(local (defthm fn-lbr13-wide-preindex-owner-keys
 (equal (fn-lbc-slot-escape-keys (fn-lbr13-wide-preindex)) nil)
 :hints (("Goal" :do-not-induct t :in-theory (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-wide-preindex fn-lbc-slot-escape-keys-of-reserve-slots fn-lbc-slot-escape-keys-of-summary-groups-update fn-lbc-slot-escape-keys-of-rebuild-summaries fn-lbc-slot-escape-keys-of-number-put-row fn-lbr13-wide-row-owner-keys)) '((:executable-counterpart make-list-ac)))))))

(local (defthm fn-lbr13-wide-preindex-empty-owner
 (equal (fn-lbc-escape 0 :msgid-slot (fn-lbr13-wide-preindex)) nil)
 :hints (("Goal" :do-not-induct t :in-theory (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-wide-preindex fn-lbc-escape-of-reserve-slots fn-lbc-escape-of-summary-groups-update fn-lbc-escape-of-rebuild-summaries fn-lbc-escape-of-number-put-row fn-lbr13-wide-row-empty-slot-owner)) '((:executable-counterpart make-list-ac)))))))

(local (defthm fn-lbr13-wide-preindex-row-corr
 (fn-lbc-row-corr 0 (fn-lbr13-held) 5 (fn-lbr13-wide-preindex) (fn-lbr13-single-log))
 :hints (("Goal" :do-not-induct t :in-theory (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-wide-preindex fn-lbc-row-corr-of-reserve-slots fn-lbc-row-corr-of-summary-groups-update fn-lbc-row-corr-of-rebuild-summaries fn-lbc-row-corr-of-number-put-row fn-lbr13-wide-row-write-p fn-lbr13-wide-row-write-count fn-lbr13-wide-row-write-row-corr fn-lbc-p-of-number-put-row fn-lbc-p-of-rebuild-summaries fn-lbc-p-of-update-summary-groups fn-lbc-count-of-number-put-row fn-lbc-count-of-rebuild-summaries fn-lbc-count-of-summary-groups-update)) '((:executable-counterpart make-list-ac)))))))

(local (defthm fn-lbr13-wide-preindex-row-hash
 (fn-lb-slot-row-hashesp (list (fn-lbr13-held)) 0 (fn-lbr13-wide-preindex))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbr13-wide-preindex-row-corr)) :in-theory (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lb-slot-row-hashesp fn-lbc-row-corr nfix)) '((:executable-counterpart make-list-ac)))))))

(defthm fn-lbr13-wide-indexed-write-slots-corr
 (fn-lbc-slots-corr (fn-lbr13-wide-indexed-write) (list (fn-lbr13-held)))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-index-slots-refines-canonical (i 0) (table '(0 0 0)) (rows (list (fn-lbr13-held))) (fn-lbc (fn-lbr13-wide-preindex))) (:instance fn-lbc-slot-cells-corr-of-zero-records (fn-lbc (fn-lbr13-wide-preindex)) (capacity 3) (n 3)) (:instance fn-lbr13-wide-preindex-raw-store)) :in-theory (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-slot-list-three fn-lbc-slots-corr fn-lbr13-wide-indexed-by-preindex fn-lbr13-wide-preindex-capacity fn-lbr13-wide-preindex-owner-keys fn-lbr13-wide-preindex-empty-owner fn-lbr13-wide-preindex-row-hash fn-lbc-slot-count-of-index-slots fn-lb-slot-owner-keys-below fn-lb-unindexed-slotsp natp posp len)) '((:executable-counterpart make-list-ac))))))

; BEGIN wide-full-corr
(defthm fn-lbr13-wide-indexed-write-corr
 (fn-lbc-corr (fn-lbr13-wide-indexed-write) (list (fn-lbr13-held)) (fn-lbr13-single-log))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbc-corr fn-lbr13-wide-indexed-write-count
 fn-lbr13-wide-indexed-write-directory-count fn-lbr13-single-log-segsp
 fn-lbr13-wide-indexed-write-summary-groups fn-lbr13-wide-indexed-write-rows-corr
 fn-lbr13-wide-indexed-write-tables-corr fn-lbr13-wide-indexed-write-number-rows-corr
 fn-lbr13-wide-indexed-write-slots-corr fn-lbr13-wide-indexed-write-summaries-corr
 (:executable-counterpart len) len)))))

; BEGIN directory-full-control
(local (defun fn-lbr13-directory-control-runes (runes kind)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp runes)
  (let* ((r (car runes)) (sym (cadr r))
         (name (if (symbolp sym) (symbol-name sym) "")))
   (if (and (equal (car r) kind)
            (or (equal (subseq name 0 (min 7 (length name))) "FN-LBC-")
                (equal (subseq name 0 (min 9 (length name))) "FN-LBR13-")
                (equal (subseq name 0 (min 6 (length name))) "FN-LB-")
                (equal (subseq name 0 (min 8 (length name))) "FN-DMAP-")
                (equal sym 'create-fn-lbc)))
       (cons r (fn-lbr13-directory-control-runes (cdr runes) kind))
     (fn-lbr13-directory-control-runes (cdr runes) kind))) nil)))

(defthm fn-lbr13-corr-directory-equality (implies (fn-lbc-corr fn-lbc rows log) (equal (len (nth *fn-lbc-directory-store* fn-lbc)) (fn-lbc-count fn-lbc))) :hints (("Goal" :do-not-induct t :in-theory (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbc-corr fn-lbc-directory-count-is-len)) '((:executable-counterpart make-list-ac))))))

(defthm fn-lbr13-empty-corr-any-log (implies (fn-lb-log-model-segsp log) (fn-lbc-corr (create-fn-lbc) nil log)) :hints (("Goal" :do-not-induct t :in-theory (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbc-corr create-fn-lbc create-fn-dmap (:executable-counterpart create-fn-dmap$a) fn-lbc-count fn-lbc-row-store fn-lbc-rowwords-count-is-len fn-lbc-directory-count-is-len fn-lbc-summary-groups fn-lbc-row-group-keys fn-lbc-rows-corr fn-lbc-tables-corr fn-lbc-number-cells-corr fn-lbc-summary-cells-corr fn-lbc-number-rows-covered fn-lbc-slots-corr fn-lbc-slot-count-by-store fn-lbc-slot-cells-corr fn-lbc-summaries-corr fn-lbc-canonical-slots-from)) '((:executable-counterpart make-list-ac))))))

(defthm fn-lbr13-stray-directory-properties (let ((fn-lbc (fn-lbr13-extra-directory (create-fn-lbc)))) (and (fn-lbc-p fn-lbc) (equal (fn-lbc-count fn-lbc) 0) (equal (len (nth *fn-lbc-directory-store* fn-lbc)) 1) (fn-lbr13-old-corr fn-lbc nil log) (not (fn-lbc-corr fn-lbc nil log)))) :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero) (append '((:executable-counterpart adt-seq-p) (:executable-counterpart adt-rec-p) (:executable-counterpart fn-dmapp) update-fn-lbc-directory-store fn-lbc-directory-store create-fn-dmap (:executable-counterpart create-fn-dmap$a)) (fn-lbr13-directory-control-runes (universal-theory :here) :definition))))))

(defthm fn-lbr13-stray-writer-refused (not (fn-lbc-corr (fn-lbr13-finish-single-row (fn-lbr13-held) (fn-lbc-append-row (fn-lbr13-held) (fn-lbr13-single-log) (fn-lbr13-extra-directory (create-fn-lbc)))) (list (fn-lbr13-held)) (fn-lbr13-single-log))) :hints (("Goal" :do-not-induct t :use ((:instance fn-lbr13-corr-directory-equality (fn-lbc (fn-lbr13-finish-single-row (fn-lbr13-held) (fn-lbc-append-row (fn-lbr13-held) (fn-lbr13-single-log) (fn-lbr13-extra-directory (create-fn-lbc))))) (rows (list (fn-lbr13-held))) (log (fn-lbr13-single-log))) (:instance fn-lbr13-stray-directory-properties (log (fn-lbr13-single-log)))) :in-theory (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-directory-length-of-finish-single-row fn-lbr13-count-of-finish-single-row fn-lbc-append-row-directory-count fn-lbc-count-of-append-row)) '((:executable-counterpart make-list-ac))))))

(defthm fn-lbr13-directory-append-repair-control (let* ((row (fn-lbr13-held)) (rows (list row))
        (log (fn-lb-log-model-append row *fn-lbr13-payload* 1 nil))
        (before (create-fn-lbc))
        (stray (fn-lbr13-extra-directory before))
        (after (fn-lbr13-finish-single-row row (fn-lbc-append-row row log before)))
        (mutant (fn-lbr13-finish-single-row row (fn-lbc-append-row row log stray))))
  (and (fn-lbc-p before) (fn-lbc-corr before nil log)
       (fn-lbc-p stray) (fn-lbr13-old-corr stray nil log)
       (not (fn-lbc-corr stray nil log))
       (fn-lbc-corr after rows log)
       (not (fn-lbc-corr mutant rows log)))) :hints (("Goal" :do-not-induct t :use ((:instance fn-lbr13-empty-corr-any-log (log (fn-lbr13-single-log))) (:instance fn-lbr13-stray-directory-properties (log (fn-lbr13-single-log))) (:instance fn-lbr13-clean-single-write-corr) (:instance fn-lbr13-stray-writer-refused) (:instance fn-lbr13-single-log-segsp)) :in-theory (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-single-log fn-lbr13-single-log-segsp fn-lbr13-clean-single-write-corr fn-lbr13-empty-corr-any-log fn-lbr13-stray-directory-properties fn-lbr13-stray-writer-refused create-fn-lbc create-fn-dmap (:executable-counterpart create-fn-dmap$a) (:executable-counterpart fn-lbc-p))) '((:executable-counterpart make-list-ac))))))

; BEGIN fresh-domain
(defthm fn-lbr13-fresh-log-layout
 (fn-lb-log-layoutp (fn-lbr13-fresh-log))
 :hints (("Goal" :do-not-induct t
 :expand ((fn-lbr13-fresh-log))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lb-log-append-preserves-type fn-lb-log-model-append-preserves-layout
 fn-lb-log-append-fresh-row-entry fn-lb-log-append-fresh-row-segment
 fn-lb-log-row-sourcep-of-fresh-append
 fn-lb-log-model-row-entry fn-lb-log-model-row-segment fn-lb-log-model-segment
 fn-lb-log-model-segsp fn-lb-log-layoutp
 fn-lb-log-next-entry-payload-by-definition fn-lb-log-next-entry-served-offset-by-definition
 fn-lb-log-next-entry-served-length-by-definition
 fn-lb-log-model-next-range fn-lbc-row-log-guardp
 (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-cat-rowp)
 (:executable-counterpart fn-cbor-octet-listp) (:executable-counterpart fn-record-payload)
 (:executable-counterpart fn-lb-log-model-pre) (:executable-counterpart fn-rcl-tombstonep)
 (:executable-counterpart fn-la-payload-wire))))))

(defthm fn-lbr13-fresh-log-payload
 (equal (nth 6 (fn-lb-log-model-row-entry (fn-lbr13-held) (fn-lbr13-fresh-log))) *fn-lbr13-payload*)
 :hints (("Goal" :do-not-induct t
 :expand ((fn-lbr13-fresh-log))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lb-log-append-preserves-type fn-lb-log-model-append-preserves-layout
 fn-lb-log-append-fresh-row-entry fn-lb-log-append-fresh-row-segment
 fn-lb-log-row-sourcep-of-fresh-append
 fn-lb-log-model-row-entry fn-lb-log-model-row-segment fn-lb-log-model-segment
 fn-lb-log-model-segsp fn-lb-log-layoutp
 fn-lb-log-next-entry-payload-by-definition fn-lb-log-next-entry-served-offset-by-definition
 fn-lb-log-next-entry-served-length-by-definition
 fn-lb-log-model-next-range fn-lbc-row-log-guardp
 (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-cat-rowp)
 (:executable-counterpart fn-cbor-octet-listp) (:executable-counterpart fn-record-payload)
 (:executable-counterpart fn-lb-log-model-pre) (:executable-counterpart fn-rcl-tombstonep)
 (:executable-counterpart fn-la-payload-wire))))))

(defthm fn-lbr13-fresh-log-segment
 (equal (fn-lb-log-model-row-segment (fn-lbr13-held) (fn-lbr13-fresh-log)) 2)
 :hints (("Goal" :do-not-induct t
 :expand ((fn-lbr13-fresh-log))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lb-log-append-preserves-type fn-lb-log-model-append-preserves-layout
 fn-lb-log-append-fresh-row-entry fn-lb-log-append-fresh-row-segment
 fn-lb-log-row-sourcep-of-fresh-append
 fn-lb-log-model-row-entry fn-lb-log-model-row-segment fn-lb-log-model-segment
 fn-lb-log-model-segsp fn-lb-log-layoutp
 fn-lb-log-next-entry-payload-by-definition fn-lb-log-next-entry-served-offset-by-definition
 fn-lb-log-next-entry-served-length-by-definition
 fn-lb-log-model-next-range fn-lbc-row-log-guardp
 (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-cat-rowp)
 (:executable-counterpart fn-cbor-octet-listp) (:executable-counterpart fn-record-payload)
 (:executable-counterpart fn-lb-log-model-pre) (:executable-counterpart fn-rcl-tombstonep)
 (:executable-counterpart fn-la-payload-wire))))))

(defthm fn-lbr13-fresh-log-row-profile
 (fn-lbc-row-log-guardp (fn-lbr13-held) (fn-lbr13-fresh-log))
 :hints (("Goal" :do-not-induct t
 :expand ((fn-lbr13-fresh-log))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lb-log-append-preserves-type fn-lb-log-model-append-preserves-layout
 fn-lb-log-append-fresh-row-entry fn-lb-log-append-fresh-row-segment
 fn-lb-log-row-sourcep-of-fresh-append
 fn-lb-log-model-row-entry fn-lb-log-model-row-segment fn-lb-log-model-segment
 fn-lb-log-model-segsp fn-lb-log-layoutp
 fn-lb-log-next-entry-payload-by-definition fn-lb-log-next-entry-served-offset-by-definition
 fn-lb-log-next-entry-served-length-by-definition
 fn-lb-log-model-next-range fn-lbc-row-log-guardp
 (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-cat-rowp)
 (:executable-counterpart fn-cbor-octet-listp) (:executable-counterpart fn-record-payload)
 (:executable-counterpart fn-lb-log-model-pre) (:executable-counterpart fn-rcl-tombstonep)
 (:executable-counterpart fn-la-payload-wire))))))

(defthm fn-lbr13-fresh-log-row-source
 (fn-lb-log-row-sourcep (fn-lbr13-held) (fn-lbr13-fresh-log))
 :hints (("Goal" :do-not-induct t
 :expand ((fn-lbr13-fresh-log))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lb-log-append-preserves-type fn-lb-log-model-append-preserves-layout
 fn-lb-log-append-fresh-row-entry fn-lb-log-append-fresh-row-segment
 fn-lb-log-row-sourcep-of-fresh-append
 fn-lb-log-model-row-entry fn-lb-log-model-row-segment fn-lb-log-model-segment
 fn-lb-log-model-segsp fn-lb-log-layoutp
 fn-lb-log-next-entry-payload-by-definition fn-lb-log-next-entry-served-offset-by-definition
 fn-lb-log-next-entry-served-length-by-definition
 fn-lb-log-model-next-range fn-lbc-row-log-guardp
 (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-cat-rowp)
 (:executable-counterpart fn-cbor-octet-listp) (:executable-counterpart fn-record-payload)
 (:executable-counterpart fn-lb-log-model-pre) (:executable-counterpart fn-rcl-tombstonep)
 (:executable-counterpart fn-la-payload-wire))))))

(defun-nx fn-lbr13-fresh-state () (fn-lbc-open-rebuild (list (fn-lbr13-held)) (fn-lbr13-fresh-log) (create-fn-lbc)))

(in-theory (disable fn-lbr13-fresh-state (:executable-counterpart fn-lbr13-fresh-state)))

(defthm fn-lbr13-fresh-state-corr
 (fn-lbc-corr (fn-lbr13-fresh-state) (list (fn-lbr13-held)) (fn-lbr13-fresh-log))
 :hints (("Goal" :do-not-induct t :expand ((fn-lbr13-fresh-state))
 :use ((:instance fn-lbc-corr-of-open-rebuild (rows (list (fn-lbr13-held))) (log (fn-lbr13-fresh-log)) (fn-lbc (create-fn-lbc)))
       (:instance fn-lbr13-fresh-log-row-profile) (:instance fn-lbr13-fresh-log-row-source))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-cat-rowsp fn-lbc-rows-log-guardp fn-lb-log-rows-sourcep
 fn-lbr13-fresh-log-layout fn-lbr13-fresh-segsp create-fn-lbc create-fn-dmap
 (:executable-counterpart create-fn-dmap$a) (:executable-counterpart fn-lbc-p)
 (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-cat-rowp))))))

; BEGIN payload-observations
(local (defun fn-lbr13-shadow-pure-exec (runes)
 (declare (xargs :guard t :verify-guards t))
 (if (consp runes)
 (let* ((r (car runes)) (sym (ec-call (car (ec-call (cdr r)))))
        (name (if (symbolp sym) (symbol-name sym) "")))
 (if (and (equal (ec-call (car r)) :executable-counterpart)
 (not (equal sym 'make-list-ac)) (not (equal sym 'create-fn-lbc))
 (not (equal (subseq name 0 (min 7 (length name))) "FN-LBC-"))
 (not (equal (subseq name 0 (min 9 (length name))) "FN-LBR13-"))
 (not (equal (subseq name 0 (min 14 (length name))) "UPDATE-FN-LBC-")))
 (cons r (fn-lbr13-shadow-pure-exec (cdr runes)))
 (fn-lbr13-shadow-pure-exec (cdr runes)))) nil)))

(defthm fn-lbr13-shadow-row-corr-observation
 (implies (and (equal (fn-lbc-loc0 0 fn-lbc) 2)
 (equal (fn-lbc-loc1 0 fn-lbc)
 (mv-nth 1 (fn-loc-make 2
 (nth 3 (fn-lb-log-model-row-entry (fn-lbr13-held) (fn-lbr13-fresh-log)))
 (nth 4 (fn-lb-log-model-row-entry (fn-lbr13-held) (fn-lbr13-fresh-log)))))))
 (equal (fn-lbc-row-corr 0 (fn-lbr13-held) 5 fn-lbc (fn-lbr13-shadow-log))
        (fn-lbc-row-corr 0 (fn-lbr13-held) 5 fn-lbc (fn-lbr13-fresh-log))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
 (append '(fn-lbc-row-corr fn-lbc-home-entry fn-lbr13-fresh-log fn-lbr13-single-log fn-lbr13-good-log
 (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-lbr13-shadow-log))
 (fn-lbr13-shadow-pure-exec (universal-theory :here))))
 '((tau-system) (:definition make-list-ac) (:executable-counterpart make-list-ac))))))

(defthm fn-lbr13-retained-row-corr-observation
 (implies (and (equal (fn-lbc-loc0 0 fn-lbc) 2)
 (equal (fn-lbc-loc1 0 fn-lbc)
 (mv-nth 1 (fn-loc-make 2
 (nth 3 (fn-lb-log-model-row-entry (fn-lbr13-held) (fn-lbr13-fresh-log)))
 (nth 4 (fn-lb-log-model-row-entry (fn-lbr13-held) (fn-lbr13-fresh-log)))))))
 (equal (fn-lbc-row-corr 0 (fn-lbr13-held) 5 fn-lbc (fn-lbr13-good-log))
        (fn-lbc-row-corr 0 (fn-lbr13-held) 5 fn-lbc (fn-lbr13-fresh-log))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
 (append '(fn-lbc-row-corr fn-lbc-home-entry fn-lbr13-fresh-log fn-lbr13-single-log fn-lbr13-good-log
 (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-lbr13-shadow-log))
 (fn-lbr13-shadow-pure-exec (universal-theory :here))))
 '((tau-system) (:definition make-list-ac) (:executable-counterpart make-list-ac))))))

; BEGIN clamp-render
(local
 (defthm fn-lbr13-mutant-repeat-zero
  (equal (make-list-ac 0 item acc) acc)
  :hints (("Goal" :in-theory (enable make-list-ac)))))

(local
 (defthm fn-lbr13-mutant-repeat-three
  (equal (make-list-ac 3 item acc) (cons item (cons item (cons item acc))))
  :hints
  (("Goal"
    :expand ((make-list-ac 3 item acc)
             (make-list-ac 2 item (cons item acc))
             (make-list-ac 1 item (cons item (cons item acc))))
    :in-theory (enable make-list-ac)))))

(local (defun fn-lbr13-mutant-column-runes (runes kind)
 (declare (xargs :guard t :verify-guards t))
 (if (consp runes)
  (let* ((r (car runes)) (sym (ec-call (car (ec-call (cdr r)))))
         (name (if (symbolp sym) (symbol-name sym) "")))
   (if (and (equal (ec-call (car r)) kind)
            (or (equal (subseq name 0 (min 7 (length name))) "FN-LBC-")
                (equal (subseq name 0 (min 9 (length name))) "FN-LBR13-")
                (equal (subseq name 0 (min 6 (length name))) "FN-LB-")
                (equal (subseq name 0 (min 8 (length name))) "FN-DMAP-")
                (equal (subseq name 0 (min 9 (length name))) "FN-ARENA-")
                (equal sym 'create-fn-arena)
                (equal (subseq name 0 (min 14 (length name))) "UPDATE-FN-LBC-") (equal sym 'create-fn-dmap) (equal sym 'create-fn-lbc)))
       (cons r (fn-lbr13-mutant-column-runes (cdr runes) kind))
     (fn-lbr13-mutant-column-runes (cdr runes) kind))) nil))
)

(local (defthm fn-lbr13-mutant-repeat-true-list
 (implies (and (natp n) (true-listp acc))
          (true-listp (make-list-ac n item acc)))
 :hints (("Goal" :induct (make-list-ac n item acc) :in-theory (enable make-list-ac)))))

(local (defthm fn-lbr13-mutant-repeat-length
 (implies (natp n)
          (equal (len (make-list-ac n item acc)) (+ n (len acc))))
 :hints (("Goal" :induct (make-list-ac n item acc) :in-theory (enable make-list-ac)))))

(local (defthm fn-lbr13-mutant-repeat-schema
 (implies (and (natp n) (adt-rec-p schema item) (adt-seq-p schema acc))
          (adt-seq-p schema (make-list-ac n item acc)))
 :hints (("Goal" :induct (make-list-ac n item acc)
                  :in-theory (enable make-list-ac adt-seq-p)))))

(local (defthm fn-lbr13-mutant-repeat-consp
 (implies (and (natp n) (or (posp n) (consp acc)))
          (consp (make-list-ac n item acc)))
 :hints (("Goal" :induct (make-list-ac n item acc) :in-theory (enable make-list-ac)))))

(local (defthm fn-lbr13-mutant-repeat-car
 (implies (and (natp n)
              (or (posp n) (and (consp acc) (equal (car acc) item))))
          (equal (car (make-list-ac n item acc)) item))
 :hints (("Goal" :induct (make-list-ac n item acc) :in-theory (enable make-list-ac)))))

(local (defthm fn-lbr13-mutant-repeat-first-after-append
 (implies (posp n)
          (equal (car (append (make-list-ac n item nil) tail)) item))
 :hints (("Goal" :do-not-induct t
                  :use ((:instance fn-lbr13-mutant-repeat-consp (acc nil))
                        (:instance fn-lbr13-mutant-repeat-car (acc nil)))
                  :expand ((binary-append (make-list-ac n item nil) tail))))))

(local (defun fn-lbr13-mutant-pure-exec (runes)
 (declare (xargs :guard t :verify-guards t))
 (if (consp runes)
 (let* ((r (car runes)) (sym (ec-call (car (ec-call (cdr r)))))
        (name (if (symbolp sym) (symbol-name sym) "")))
 (if (and (equal (ec-call (car r)) :executable-counterpart)
 (not (equal sym 'make-list-ac)) (not (equal sym 'create-fn-lbc))
 (not (equal (subseq name 0 (min 7 (length name))) "FN-LBC-"))
 (not (equal (subseq name 0 (min 9 (length name))) "FN-LBR13-"))
 (not (equal (subseq name 0 (min 14 (length name))) "UPDATE-FN-LBC-")))
 (cons r (fn-lbr13-mutant-pure-exec (cdr runes)))
 (fn-lbr13-mutant-pure-exec (cdr runes)))) nil)))

(local (defthm fn-lbr13-mutant-len-append
 (equal (len (append a b)) (+ (len a) (len b)))
 :hints (("Goal" :induct (len a) :in-theory (enable len binary-append)))))

(local (defthm fn-lbr13-mutant-append-associative
 (equal (append (append a b) c) (append a (append b c)))
 :hints (("Goal" :induct (len a) :in-theory (enable len binary-append)))))

(defthm fn-lbr13-clamped-row-render
 (equal (fn-lbc-render-nov 0 (fn-lbr13-clamped-row-write))
        (fn-hnov-make nil t (coerce (list (code-char 0)) 'string) "" "" "" ""))
 :hints (("Goal" :do-not-induct t
 :expand ((fn-lbr13-clamped-row-write) (fn-lbr13-wide-empty) (fn-lbr13-single-log)
 (:free (texts offset) (fn-lbr13-clamp-nov-spans texts offset))
 (:free (texts fn-lbc) (fn-lbc-append-nov-texts texts fn-lbc))
 (:free (texts fn-lbc) (fn-lbr13-clamp-append-nov texts fn-lbc))
 (:free (bytes fn-lbc) (fn-lbc-overview-pool-append bytes fn-lbc))
 (:free (off n fn-lbc) (fn-lbc-overview-pool-range off n fn-lbc)))
 :in-theory (set-difference-theories (union-theories
 (theory 'ground-zero)
 (append '(fn-lbr13-mutant-len-append fn-lbr13-mutant-append-associative fn-lbr13-mutant-repeat-zero fn-lbr13-mutant-repeat-three fn-lbr13-mutant-repeat-true-list fn-lbr13-mutant-repeat-length fn-lbr13-mutant-repeat-schema fn-lbr13-mutant-repeat-consp fn-lbr13-mutant-repeat-car fn-lbr13-mutant-repeat-first-after-append)
 (fn-lbr13-mutant-column-runes (universal-theory :here) :definition)
 (fn-lbr13-mutant-pure-exec (universal-theory :here)))) '((:definition make-list-ac) (:executable-counterpart make-list-ac) (tau-system))))))

; BEGIN fresh-locators
(local (defthm fn-lbr13-clear-create-unfolds
 (equal (fn-lbc-clear-columns (create-fn-lbc)) (create-fn-lbc))
 :hints (("Goal" :do-not-induct t
 :in-theory (e/d (fn-lbc-clear-columns create-fn-lbc create-fn-dmap
 fn-lbc-rowwords-clear-is-nil fn-lbc-msgid-octets-clear-is-nil
 fn-lbc-overview-octets-clear-is-nil fn-lbc-msgid-slots-clear-is-nil
 fn-lbc-directory-clear-is-nil fn-lbc-memberships-clear-is-nil fn-lbc-nov-clear-is-nil
 fn-lbc-escape-store-clear update-fn-lbc-slot-escape-keys update-fn-lbc-summary-groups fn-dmap-clear)
 ((:executable-counterpart fn-lbc-clear-columns) (:executable-counterpart create-fn-lbc)))))))

(local (defthm fn-lbr13-rebuild-one-row-unfolds
 (equal (fn-lbc-rebuild-rows (list row) log fn-lbc)
        (fn-lbc-number-put-row (fn-held-numbers row) (fn-lbc-count fn-lbc)
                              (fn-lbc-append-row row log fn-lbc)))
 :hints (("Goal" :do-not-induct t
 :expand ((fn-lbc-rebuild-rows (list row) log fn-lbc)
          (:free (state) (fn-lbc-rebuild-rows nil log state)))
 :in-theory (union-theories (theory 'minimal-theory) '(car-cons cdr-cons (:executable-counterpart consp)))))))

(local (defthm fn-lbr13-clean-single-write-is-open-rebuild
 (equal (fn-lbr13-finish-single-row row (fn-lbc-append-row row log (create-fn-lbc)))
        (fn-lbc-open-rebuild (list row) log (create-fn-lbc)))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbr13-clear-create-unfolds))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-finish-single-row fn-lbc-open-rebuild fn-lbr13-clear-create-unfolds
 fn-lbr13-rebuild-one-row-unfolds fn-lbc-count fn-lbc-row-store
 fn-lbc-rowwords-count-is-len create-fn-lbc create-fn-dmap
 (:executable-counterpart create-fn-dmap$a)))))))

(local (defthm fn-lbr13-loc0-of-finish-single-row
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)))
 (equal (fn-lbc-loc0 i (fn-lbr13-finish-single-row row fn-lbc)) (fn-lbc-loc0 i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-finish-single-row fn-lbc-loc0-of-number-put-row
 fn-lbc-loc0-of-rebuild-summaries fn-lbc-loc0-of-summary-groups-update
 fn-lbc-loc0-of-reserve-slots fn-lbc-loc0-of-index-slots-in-bounds
 fn-lbc-count-of-number-put-row fn-lbc-count-of-rebuild-summaries
 fn-lbc-count-of-summary-groups-update fn-lbc-count-of-reserve-slots))))))

(defthm fn-lbr13-fresh-state-loc0
 (equal (fn-lbc-loc0 0 (fn-lbr13-fresh-state))
 (mv-nth 0 (fn-loc-make 2
 (nth 3 (fn-lb-log-model-row-entry (fn-lbr13-held) (fn-lbr13-fresh-log)))
 (nth 4 (fn-lb-log-model-row-entry (fn-lbr13-held) (fn-lbr13-fresh-log))))))
 :hints (("Goal" :do-not-induct t :expand ((fn-lbr13-fresh-state))
 :use ((:instance fn-lbr13-clean-single-write-is-open-rebuild (row (fn-lbr13-held)) (log (fn-lbr13-fresh-log)))
       (:instance fn-lbc-loc0-of-append-row-new (row (fn-lbr13-held)) (log (fn-lbr13-fresh-log)) (fn-lbc (create-fn-lbc))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-loc0-of-finish-single-row fn-lbc-count-of-append-row fn-lbr13-fresh-log-segment
 fn-lbc-count fn-lbc-row-store fn-lbc-rowwords-count-is-len
 create-fn-lbc create-fn-dmap (:executable-counterpart create-fn-dmap$a))))))

(local (defthm fn-lbr13-loc1-of-finish-single-row
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)))
 (equal (fn-lbc-loc1 i (fn-lbr13-finish-single-row row fn-lbc)) (fn-lbc-loc1 i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-finish-single-row fn-lbc-loc1-of-number-put-row
 fn-lbc-loc1-of-rebuild-summaries fn-lbc-loc1-of-summary-groups-update
 fn-lbc-loc1-of-reserve-slots fn-lbc-loc1-of-index-slots-in-bounds
 fn-lbc-count-of-number-put-row fn-lbc-count-of-rebuild-summaries
 fn-lbc-count-of-summary-groups-update fn-lbc-count-of-reserve-slots))))))

(defthm fn-lbr13-fresh-state-loc1
 (equal (fn-lbc-loc1 0 (fn-lbr13-fresh-state))
 (mv-nth 1 (fn-loc-make 2
 (nth 3 (fn-lb-log-model-row-entry (fn-lbr13-held) (fn-lbr13-fresh-log)))
 (nth 4 (fn-lb-log-model-row-entry (fn-lbr13-held) (fn-lbr13-fresh-log))))))
 :hints (("Goal" :do-not-induct t :expand ((fn-lbr13-fresh-state))
 :use ((:instance fn-lbr13-clean-single-write-is-open-rebuild (row (fn-lbr13-held)) (log (fn-lbr13-fresh-log)))
       (:instance fn-lbc-loc1-of-append-row-new (row (fn-lbr13-held)) (log (fn-lbr13-fresh-log)) (fn-lbc (create-fn-lbc))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-loc1-of-finish-single-row fn-lbc-count-of-append-row fn-lbr13-fresh-log-segment
 fn-lbc-count fn-lbc-row-store fn-lbc-rowwords-count-is-len
 create-fn-lbc create-fn-dmap (:executable-counterpart create-fn-dmap$a))))))

; BEGIN payload-binding
(defthm fn-lbr13-shadow-corr-refused
 (not (fn-lbc-corr fn-lbc rows (fn-lbr13-shadow-log)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbc-corr fn-lbr13-bad-segsp-refused)))))

(defthm fn-lbr13-real-seal-readback
 (equal (fn-nntp-payload-bytes 0 (fn-arena-seal-list *fn-lbr13-payload* (create-fn-arena))) *fn-lbr13-payload*)
 :hints (("Goal" :do-not-induct t :use ((:instance fn-arena-seal-list-is-append (xs *fn-lbr13-payload*) (fn-arena (create-fn-arena)))) :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-nntp-payload-bytes fn-arena-payload-is-nth fn-arena-p (:executable-counterpart fn-arena$ap) fn-arena-count-is-len fn-arena-seal-list-len create-fn-arena)))))

(defthm fn-lbr13-good-payload-observation
 (equal (fn-lb-log-payload (fn-lbr13-held) (fn-lbr13-good-log)) *fn-lbr13-payload*)
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-good-log fn-lbr13-fresh-log fn-lbr13-single-log fn-lbr13-after-log (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-lb-log-payload) (:executable-counterpart fn-lb-log-model-append) (:executable-counterpart fn-lb-log-model-recycle))))))

(defthm fn-lbr13-good-arena-binding
 (fn-lb-arena-is-log (fn-arena-seal-list *fn-lbr13-payload* (create-fn-arena)) (list (fn-lbr13-held)) (fn-lbr13-good-log))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbr13-good-payload-observation)) :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lb-arena-is-log fn-lbr13-real-seal-readback fn-lbr13-good-payload-observation (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-record-payload))))))

(defthm fn-lbr13-after-payload-observation
 (equal (fn-lb-log-payload (fn-lbr13-held) (fn-lbr13-after-log)) *fn-lbr13-payload*)
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-good-log fn-lbr13-fresh-log fn-lbr13-single-log fn-lbr13-after-log (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-lb-log-payload) (:executable-counterpart fn-lb-log-model-append) (:executable-counterpart fn-lb-log-model-recycle))))))

(defthm fn-lbr13-after-arena-binding
 (fn-lb-arena-is-log (fn-arena-seal-list *fn-lbr13-payload* (create-fn-arena)) (list (fn-lbr13-held)) (fn-lbr13-after-log))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbr13-after-payload-observation)) :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lb-arena-is-log fn-lbr13-real-seal-readback fn-lbr13-after-payload-observation (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-record-payload))))))

; BEGIN payload-corr-transfer
(local (defthm fn-lbr13-summaries-corr-boolean
 (booleanp (fn-lbc-summaries-corr groups rows fn-lbc))
 :rule-classes :type-prescription
 :hints (("Goal" :induct (fn-lbc-summaries-corr groups rows fn-lbc)
 :in-theory (enable fn-lbc-summaries-corr)))))

(local (defthm fn-lbr13-log-segsp-boolean
 (booleanp (fn-lb-log-model-segsp log))
 :rule-classes :type-prescription
 :hints (("Goal" :induct (fn-lb-log-model-segsp log)
 :in-theory (enable fn-lb-log-model-segsp)))))

(defthm fn-lbr13-new-corr-implies-old
 (implies (fn-lbc-corr fn-lbc rows log) (fn-lbr13-old-corr fn-lbc rows log))
:hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbc-corr fn-lbr13-old-corr fn-lbr13-summaries-corr-boolean fn-lbr13-log-segsp-boolean)))))

(defthm fn-lbr13-old-corr-plus-amendments
 (equal (fn-lbc-corr fn-lbc rows log)
 (and (fn-lbr13-old-corr fn-lbc rows log)
 (equal (fn-lbc-directory-count (nth *fn-lbc-directory-store* fn-lbc)) (fn-lbc-count fn-lbc))
 (fn-lb-log-model-segsp log)
 (fn-lb-retained-payloads-agreep rows log)))
:rule-classes nil
:hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbc-corr fn-lbr13-old-corr fn-lbr13-summaries-corr-boolean fn-lbr13-log-segsp-boolean)))))

(defthm fn-lbr13-shadow-old-corr-observation
 (implies (and (equal (fn-lbc-loc0 0 fn-lbc) 2)
 (equal (fn-lbc-loc1 0 fn-lbc)
 (mv-nth 1 (fn-loc-make 2
 (nth 3 (fn-lb-log-model-row-entry (fn-lbr13-held) (fn-lbr13-fresh-log)))
 (nth 4 (fn-lb-log-model-row-entry (fn-lbr13-held) (fn-lbr13-fresh-log)))))))
 (equal (fn-lbr13-old-corr fn-lbc (list (fn-lbr13-held)) (fn-lbr13-shadow-log))
        (fn-lbr13-old-corr fn-lbc (list (fn-lbr13-held)) (fn-lbr13-fresh-log))))
:rule-classes nil
:hints (("Goal" :do-not-induct t :use ((:instance fn-lbr13-shadow-row-corr-observation)) :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-old-corr fn-lbc-rows-corr (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-record-stamp))))))

(defthm fn-lbr13-retained-old-corr-observation
 (implies (and (equal (fn-lbc-loc0 0 fn-lbc) 2)
 (equal (fn-lbc-loc1 0 fn-lbc)
 (mv-nth 1 (fn-loc-make 2
 (nth 3 (fn-lb-log-model-row-entry (fn-lbr13-held) (fn-lbr13-fresh-log)))
 (nth 4 (fn-lb-log-model-row-entry (fn-lbr13-held) (fn-lbr13-fresh-log)))))))
 (equal (fn-lbr13-old-corr fn-lbc (list (fn-lbr13-held)) (fn-lbr13-good-log))
        (fn-lbr13-old-corr fn-lbc (list (fn-lbr13-held)) (fn-lbr13-fresh-log))))
:rule-classes nil
:hints (("Goal" :do-not-induct t :use ((:instance fn-lbr13-retained-row-corr-observation)) :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-old-corr fn-lbc-rows-corr (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-record-stamp))))))

; BEGIN pool-full-control
(local (defthm fn-lbr13-pool-empty-repeat-zero
 (equal (make-list-ac 0 item acc) acc)
 :hints (("Goal" :in-theory (enable make-list-ac)))))

(defthm fn-lbr13-corr-implies-render
 (implies (fn-lbc-corr fn-lbc (list (fn-lbr13-held)) log)
 (equal (fn-lbc-render-nov 0 fn-lbc) (fn-hnov-of (fn-lb-log-payload (fn-lbr13-held) log))))
 :hints (("Goal" :do-not-induct t :in-theory (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbc-corr fn-lbc-rows-corr fn-lbc-row-corr (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-record-stamp))) '((:definition make-list-ac) (:executable-counterpart make-list-ac) (tau-system))))))

(defthm fn-lbr13-single-log-payload-observation
 (equal (fn-lb-log-payload (fn-lbr13-held) (fn-lbr13-single-log)) *fn-lbr13-payload*)
 :hints (("Goal" :do-not-induct t :in-theory (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lb-log-payload fn-lbr13-single-log-payload)) '((:definition make-list-ac) (:executable-counterpart make-list-ac) (tau-system))))))

(defthm fn-lbr13-clamped-indexed-render-is-wrong
 (not (equal (fn-lbc-render-nov 0 (fn-lbr13-clamped-indexed-write))
 (fn-hnov-of *fn-lbr13-payload*)))
 :hints (("Goal" :do-not-induct t :in-theory (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-clamped-indexed-write fn-lbr13-render-nov-of-finish-single-row fn-lbr13-clamped-row-render (:executable-counterpart fn-hnov-of) (:executable-counterpart fn-hnov-make))) '((:definition make-list-ac) (:executable-counterpart make-list-ac) (tau-system))))))

(defthm fn-lbr13-clamped-indexed-corr-is-false
 (not (fn-lbc-corr (fn-lbr13-clamped-indexed-write) (list (fn-lbr13-held)) (fn-lbr13-single-log)))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbr13-corr-implies-render (fn-lbc (fn-lbr13-clamped-indexed-write)) (log (fn-lbr13-single-log)))) :in-theory (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-clamped-indexed-render-is-wrong fn-lbr13-single-log-payload-observation)) '((:definition make-list-ac) (:executable-counterpart make-list-ac) (tau-system))))))

(defthm fn-lbr13-wide-empty-corr
 (fn-lbc-corr (fn-lbr13-wide-empty) nil (fn-lbr13-single-log))
 :hints (("Goal" :do-not-induct t :in-theory (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-pool-empty-repeat-zero fn-lbr13-wide-empty fn-lbc-corr fn-lbc-count fn-lbc-row-store fn-lbc-rowwords-count-is-len fn-lbc-directory-count-is-len fn-lbc-summary-groups fn-lbc-row-group-keys fn-lbc-rows-corr fn-lbc-tables-corr fn-lbc-number-cells-corr fn-lbc-summary-cells-corr fn-lbc-number-rows-covered fn-lbc-slots-corr fn-lbc-slot-count-by-store fn-lbc-slot-cells-corr fn-lbc-summaries-corr fn-lbc-canonical-slots-from fn-dm-nth-update-nth fn-lbr13-single-log-segsp create-fn-lbc create-fn-dmap (:executable-counterpart create-fn-dmap$a))) '((:definition make-list-ac) (:executable-counterpart make-list-ac) (tau-system))))))

(defthm fn-lbr13-pool-clamp-repair-control
 (let* ((row (fn-lbr13-held)) (rows (list row))
        (log (fn-lb-log-model-append row *fn-lbr13-payload* 1 nil))
        (before (update-nth *fn-lbc-overview-store*
                 (make-list-ac 18446744073709551616 '(0) nil) (create-fn-lbc)))
        (after (fn-lbr13-finish-single-row row (fn-lbc-append-row row log before)))
        (mutant (fn-lbr13-finish-single-row row (fn-lbr13-clamp-append-row row log before))))
  (and (fn-lbc-p before) (fn-cat$ap rows) (fn-lb-log-model-segsp log)
       (fn-lbc-corr before nil log)
       (equal (fn-lbc-render-nov 0 after) (fn-hnov-of *fn-lbr13-payload*))
       (fn-lbc-corr after rows log)
       (not (equal (fn-lbc-render-nov 0 mutant) (fn-hnov-of *fn-lbr13-payload*)))
       (not (fn-lbc-corr mutant rows log))))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbr13-wide-empty-p) (:instance fn-lbr13-wide-empty-corr) (:instance fn-lbr13-single-log-segsp) (:instance fn-lbr13-wide-indexed-write-render) (:instance fn-lbr13-wide-indexed-write-corr) (:instance fn-lbr13-clamped-indexed-render-is-wrong) (:instance fn-lbr13-clamped-indexed-corr-is-false)) :in-theory (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-wide-empty fn-lbr13-wide-row-write fn-lbr13-wide-indexed-write fn-lbr13-clamped-row-write fn-lbr13-clamped-indexed-write fn-lbr13-single-log (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-cat$ap))) '((:definition make-list-ac) (:executable-counterpart make-list-ac) (tau-system))))))

; BEGIN payload-full-control
(defthm fn-lbr13-fresh-state-p
 (fn-lbc-p (fn-lbr13-fresh-state))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbr13-fresh-log-row-profile)) :expand ((fn-lbr13-fresh-state)) :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbc-p-of-open-rebuild fn-cat-rowsp fn-lbc-rows-log-guardp fn-lbr13-fresh-log-row-profile create-fn-lbc create-fn-dmap (:executable-counterpart create-fn-dmap$a) (:executable-counterpart fn-lbc-p) (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-cat-rowp))))))

(defthm fn-lbr13-shadow-old-corr-accepted
 (fn-lbr13-old-corr (fn-lbr13-fresh-state) (list (fn-lbr13-held)) (fn-lbr13-shadow-log))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbr13-fresh-state-corr) (:instance fn-lbr13-fresh-state-loc0) (:instance fn-lbr13-fresh-state-loc1) (:instance fn-lbr13-new-corr-implies-old (fn-lbc (fn-lbr13-fresh-state)) (rows (list (fn-lbr13-held))) (log (fn-lbr13-fresh-log))) (:instance fn-lbr13-shadow-old-corr-observation (fn-lbc (fn-lbr13-fresh-state)))) :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-loc-make)))))

(defthm fn-lbr13-retained-corr
 (fn-lbc-corr (fn-lbr13-fresh-state) (list (fn-lbr13-held)) (fn-lbr13-good-log))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbr1-retained-log-agreement) (:instance fn-lbr13-fresh-state-corr) (:instance fn-lbr13-fresh-state-loc0) (:instance fn-lbr13-fresh-state-loc1) (:instance fn-lbr13-new-corr-implies-old (fn-lbc (fn-lbr13-fresh-state)) (rows (list (fn-lbr13-held))) (log (fn-lbr13-fresh-log))) (:instance fn-lbr13-retained-old-corr-observation (fn-lbc (fn-lbr13-fresh-state))) (:instance fn-lbr13-old-corr-plus-amendments (fn-lbc (fn-lbr13-fresh-state)) (rows (list (fn-lbr13-held))) (log (fn-lbr13-fresh-log))) (:instance fn-lbr13-old-corr-plus-amendments (fn-lbc (fn-lbr13-fresh-state)) (rows (list (fn-lbr13-held))) (log (fn-lbr13-good-log)))) :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-loc-make fn-lbr13-good-segsp)))))

(defthm fn-lbr13-recycled-corr
 (fn-lbc-corr (fn-lbr13-fresh-state) (list (fn-lbr13-held)) (fn-lbr13-after-log))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-after-is-fresh fn-lbr13-fresh-state-corr)))))

(defthm fn-lbr13-payload-observation-repair-control
 (let* ((row (fn-lbr13-held)) (rows (list row))
        (fresh (fn-lb-log-model-append row *fn-lbr13-payload* 2 nil))
        (good (append (fn-lb-log-model-append row *fn-lbr13-payload* 1 nil) fresh))
        (bad (fn-lbr13-shadow-log))
        (fn-lbc (fn-lbc-open-rebuild rows fresh (create-fn-lbc)))
        (fn-arena (fn-arena-seal-list *fn-lbr13-payload* (create-fn-arena)))
        (after (fn-lb-log-model-recycle 1 good)))
  (and (fn-lbc-p fn-lbc) (fn-cat$ap rows)
       (fn-lbr13-old-log-model-segsp bad) (fn-lbr13-old-corr fn-lbc rows bad)
       (not (fn-lb-log-model-segsp bad)) (not (fn-lbc-corr fn-lbc rows bad))
       (fn-lb-log-model-segsp good) (fn-lbc-corr fn-lbc rows good)
       (fn-lb-arena-is-log fn-arena rows good)
       (fn-lb-log-model-segsp after) (fn-lbc-corr fn-lbc rows after)
       (fn-lb-arena-is-log fn-arena rows after)))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbr13-after-is-fresh) (:instance fn-lbr13-fresh-state-p) (:instance fn-lbr13-shadow-old-corr-accepted) (:instance fn-lbr13-retained-corr) (:instance fn-lbr13-recycled-corr) (:instance fn-lbr13-good-arena-binding) (:instance fn-lbr13-after-arena-binding) (:instance fn-lbr13-bad-old-segsp-accepted) (:instance fn-lbr13-bad-segsp-refused) (:instance fn-lbr13-good-segsp) (:instance fn-lbr13-shadow-corr-refused (fn-lbc (fn-lbr13-fresh-state)) (rows (list (fn-lbr13-held)))) (:instance fn-lbr13-fresh-segsp)) :in-theory (union-theories (theory 'ground-zero) '(fn-lbr1-single-log-agreement fn-lb-retained-payloads-agreep fn-lbr13-fresh-state fn-lbr13-fresh-log fn-lbr13-good-log fn-lbr13-after-log fn-lbr13-single-log (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-cat$ap))))))
