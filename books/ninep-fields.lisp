; Resumable base9P2000 request fields. Strings are borrowed buffer spans,
; validated one UTF8 scalar per STEP. No request/body list is materialized.
(in-package "ACL2")
(include-book "ninep-header")
(include-book "utf8")
(local (include-book "arithmetic/top" :dir :system))

(defun fn-9p-request-schema (kind)
 (declare (xargs :guard t))
 (case kind
  (100 '(:u32 :string))
  (102 '(:u32 :string :string))
  (104 '(:u32 :u32 :string :string))
  (108 '(:u16))
  (110 '(:u32 :u32 :walk-count))
  (112 '(:u32 :u8))
  (116 '(:u32 :u64 :u32))
  (120 '(:u32))
  (124 '(:u32))
  (otherwise nil)))

(defun fn-9p-readonly-kindp (kind)
 (declare (xargs :guard t)) (member-equal kind '(114 118 122 126)))

(defun fn-9p-fields-cursor (kind tag pos end schema values stop start phase)
 (declare (xargs :guard t))
 (list :ninep-fields kind tag pos end schema values stop start phase))

(defun fn-9p-fields-start (header)
 (declare (xargs :guard t))
 (if (not (and (true-listp header) (equal (len header) 6)
               (eq (car header) :header)
               (natp (nth 1 header)) (natp (nth 2 header))
               (natp (nth 4 header)) (natp (nth 5 header))
               (<= (nth 4 header) (nth 5 header))))
     (fn-9p-fields-cursor 0 0 0 0 nil nil 0 0 :invalid-header)
  (let* ((kind (nth 1 header)) (schema (fn-9p-request-schema kind)))
   (fn-9p-fields-cursor kind (nth 2 header) (nth 4 header) (nth 5 header)
                       schema nil 0 0
                       (cond ((fn-9p-readonly-kindp kind) :readonly)
                             (schema :fields) (t :unsupported))))))

(defun fn-9p-fields-ready-p (c)
 (declare (xargs :guard t))
 (and (fn-wildmat-at-mostp c 10) (true-listp c) (equal (len c) 10)
      (eq (car c) :ninep-fields)
      (natp (nth 1 c)) (natp (nth 2 c))
      (natp (nth 3 c)) (natp (nth 4 c)) (<= (nth 3 c) (nth 4 c))
      (fn-wildmat-at-mostp (nth 5 c) 20) (true-listp (nth 5 c))
      (fn-wildmat-at-mostp (nth 6 c) 20) (true-listp (nth 6 c))
      (<= (+ (len (nth 5 c)) (len (nth 6 c))
             (if (eq (nth 9 c) :string) 1 0)) 20)
      ; Only the actual two fixed Twalk scalars precede MAXWELEM issuance.
      (if (and (member-eq (nth 9 c) '(:fields :string))
               (member-eq :walk-count (nth 5 c)))
          (and (equal (nth 1 c) 110) (eq (nth 9 c) :fields)
               (or (and (equal (nth 5 c) '(:u32 :u32 :walk-count))
                        (equal (len (nth 6 c)) 0))
                   (and (equal (nth 5 c) '(:u32 :walk-count))
                        (equal (len (nth 6 c)) 1))
                   (and (equal (nth 5 c) '(:walk-count))
                        (equal (len (nth 6 c)) 2))))
        t)
      (natp (nth 7 c)) (natp (nth 8 c))
      (<= (nth 8 c) (nth 7 c)) (<= (nth 7 c) (nth 4 c))
      (if (eq (nth 9 c) :string)
          (<= (nth 3 c) (nth 7 c)) t)))

; Fixed four-octet lookahead only. The shared literal UTF8 decoder consumes
; just its scalar; any extra lookahead stays borrowed for the next quantum.
(defun fn-9p-utf8-window-at (pos end fn-octets)
 (declare (xargs :stobjs fn-octets
                 :guard (and (natp pos) (natp end) (<= pos end)
                             (<= end (fn-octets-len fn-octets)))))
 (if (>= pos end) nil
  (cons (fn-octets-get pos fn-octets)
   (if (>= (+ pos 1) end) nil
    (cons (fn-octets-get (+ pos 1) fn-octets)
     (if (>= (+ pos 2) end) nil
      (cons (fn-octets-get (+ pos 2) fn-octets)
       (if (>= (+ pos 3) end) nil
        (list (fn-octets-get (+ pos 3) fn-octets))))))))))

(defun fn-9p-scalar-width (field)
 (declare (xargs :guard t))
 (case field (:u8 1) (:u16 2) (:walk-count 2) (:u32 4) (:u64 8) (otherwise 0)))

(defun fn-9p-fields-step (c fn-octets)
 (declare (xargs :stobjs fn-octets
                 :guard (and (fn-9p-fields-ready-p c)
                             (<= (nth 4 c) (fn-octets-len fn-octets)))
                 :verify-guards nil))
 (let* ((kind (nth 1 c)) (tag (nth 2 c)) (pos (nth 3 c)) (end (nth 4 c))
        (schema (nth 5 c)) (values (nth 6 c)) (stop (nth 7 c))
        (start (nth 8 c)) (phase (nth 9 c)))
  (cond
   ((not (member-eq phase '(:fields :string))) (mv phase c))
   ((eq phase :string)
    (if (equal pos stop)
        (mv :yield (fn-9p-fields-cursor kind tag pos end schema
                     (cons (list :string start (- stop start)) values) 0 0 :fields))
      (let* ((window (fn-9p-utf8-window-at pos stop fn-octets))
             (next (fn-wildmat-utf8-next window)))
       (if (or (not (fn-wildmat-result-okp next)) (equal (fn-wildmat-result-value next) 0))
           (mv :malformed-string (fn-9p-fields-cursor kind tag pos end schema values stop start :malformed-string))
         (mv :yield (fn-9p-fields-cursor kind tag
                      (+ pos (- (len window) (len (fn-wildmat-utf8-rest next))))
                      end schema values stop start :string))))))
   ((endp schema)
    (if (equal pos end)
        (mv :parsed (fn-9p-fields-cursor kind tag pos end nil (reverse values) 0 0 :parsed))
      (mv :trailing-octets (fn-9p-fields-cursor kind tag pos end nil values 0 0 :trailing-octets))))
   ((eq (car schema) :string)
    (if (> (+ pos 2) end)
        (mv :truncated-field (fn-9p-fields-cursor kind tag pos end schema values 0 0 :truncated-field))
      (let* ((size (fn-octets-get-word pos 2 fn-octets)) (begin (+ pos 2)) (next-end (+ begin size)))
       (if (> next-end end)
           (mv :truncated-field (fn-9p-fields-cursor kind tag pos end schema values 0 0 :truncated-field))
         (mv :yield (fn-9p-fields-cursor kind tag begin end (cdr schema) values next-end begin :string))))))
   (t
    (let ((width (fn-9p-scalar-width (car schema))))
     (cond ((equal width 0)
            (mv :invalid-schema (fn-9p-fields-cursor kind tag pos end schema values 0 0 :invalid-schema)))
           ((> (+ pos width) end)
            (mv :truncated-field (fn-9p-fields-cursor kind tag pos end schema values 0 0 :truncated-field)))
           (t
            (let ((value (fn-octets-get-word pos width fn-octets)))
             (if (and (eq (car schema) :walk-count) (> value 16))
                 (mv :too-many-walk-elements
                     (fn-9p-fields-cursor kind tag pos end schema values 0 0 :too-many-walk-elements))
               (mv :yield
                (fn-9p-fields-cursor kind tag (+ pos width) end
                 (if (eq (car schema) :walk-count)
                     (append (make-list value :initial-element :string) (cdr schema))
                   (cdr schema))
                 (cons value values) 0 0 :fields)))))))))))

(local
 (defthm fn-9p-make-list-is-true-list
  (implies (true-listp acc) (true-listp (make-list-ac n value acc)))
  :hints (("Goal" :induct (make-list-ac n value acc)
                   :in-theory (enable make-list-ac)))))

(verify-guards fn-9p-fields-step
 :hints (("Goal" :in-theory (enable fn-9p-fields-ready-p fn-9p-scalar-width))))

(local
 (defthm fn-9p-bounded-metadata-is-length
  (implies (and (natp bound) (true-listp xs))
   (equal (fn-wildmat-at-mostp xs bound) (<= (len xs) bound)))
  :hints (("Goal" :induct (fn-cbor-at-mostp xs bound)
                   :in-theory (enable fn-wildmat-at-mostp fn-cbor-at-mostp)))))

(local
 (defthm fn-9p-make-list-length
  (implies (natp n) (equal (len (make-list-ac n value acc)) (+ n (len acc))))
  :hints (("Goal" :induct (make-list-ac n value acc)
                   :in-theory (enable make-list-ac)))))

(local
 (defthm fn-9p-make-string-list-has-no-count-marker
  (implies (not (member-eq :walk-count acc))
           (not (member-eq :walk-count (make-list-ac n :string acc))))
  :hints (("Goal" :induct (make-list-ac n :string acc)
                   :in-theory (enable make-list-ac)))))

(local
 (defthm fn-9p-utf8-rest-is-within-window
  (<= (len (fn-wildmat-utf8-rest (fn-wildmat-utf8-next xs))) (len xs))
  :rule-classes :linear
  :hints (("Goal" :in-theory
           (e/d (fn-wildmat-utf8-next fn-wildmat-utf8-rest
                 fn-wildmat-utf8-ok fn-wildmat-error)
                (fn-wildmat-utf8-2p fn-wildmat-utf8-3-tailsp fn-wildmat-utf8-4-tailsp
                 fn-wildmat-utf8-2-value fn-wildmat-utf8-3-value fn-wildmat-utf8-4-value))))))

(local
 (defthm fn-9p-utf8-window-within-end
  (implies (and (natp pos) (natp end) (<= pos end))
   (and (true-listp (fn-9p-utf8-window-at pos end fn-octets))
        (<= (len (fn-9p-utf8-window-at pos end fn-octets)) 4)
        (<= (+ pos (len (fn-9p-utf8-window-at pos end fn-octets))) end)))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable fn-9p-utf8-window-at)))))

(local
 (defthm fn-9p-revappend-length
  (equal (len (revappend xs ys)) (+ (len xs) (len ys)))
  :hints (("Goal" :induct (revappend xs ys)
                   :in-theory (enable revappend)))))

(local
 (defthm fn-9p-append-length
  (equal (len (append xs ys)) (+ (len xs) (len ys)))
  :hints (("Goal" :induct (append xs ys)
                   :in-theory (enable append)))))
(local
 (defthm fn-9p-make-list-preserves-true-list
  (implies (true-listp acc) (true-listp (make-list-ac n value acc)))
  :hints (("Goal" :induct (make-list-ac n value acc)
                   :in-theory (enable make-list-ac)))))

(local
 (defthm fn-9p-utf8-window-end-bound
  (implies (and (natp pos) (natp end) (<= pos end))
   (<= (+ pos (len (fn-9p-utf8-window-at pos end fn-octets))) end))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-9p-utf8-window-at)))))

(defthm fn-9p-fields-step-preserves-carried-ready
 (implies (fn-9p-fields-ready-p c)
          (fn-9p-fields-ready-p (mv-nth 1 (fn-9p-fields-step c fn-octets))))
 :hints (("Goal" :in-theory
          (e/d (fn-9p-fields-ready-p fn-9p-fields-step fn-9p-fields-cursor
                fn-9p-scalar-width)
               (fn-wildmat-at-mostp fn-cbor-at-mostp fn-9p-utf8-window-at
                fn-wildmat-utf8-next fn-wildmat-utf8-rest
                make-list-ac fn-oct-word-at)))))
