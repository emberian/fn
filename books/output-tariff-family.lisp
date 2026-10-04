; fn: the family tariff generator (lane tariff3, 2026-10-04;
; planning/design/tariff-2026-10-04.md Q3 "Order of the 28 families", Q5).
;
; The admission gate (books/output-command-admission.lisp
; fn-ocap-admit-preview) consumes one descriptor per first command, produced
; by ACL2 before any factory.  A family is PRICED when one row of
; DEF-FAMILY-TARIFFS names it with the octets its reply touches in the
; current representation, a term over the factory's own context; every
; other family keeps (:unpriced F) and is refused by name in accounted mode.
; The ratchet (tools/cost_obligations.py "families") counts the rows.
;
; One declaration emits, from the rows:
;   *fn-tariff-priced-families*        the priced families, in row order;
;   fn-tariff-family-octets            the rows' terms, one arm a family;
;   fn-tariff-family-price             the price at the preview's context;
;   fn-tariff-family-preview           the producer the host calls;
;   fn-tariff-family-preview-charges-before-effect
;                                      the producer's keystone: the gate
;                                      holds exactly a priced family whose
;                                      price is within the capacity;
;   fn-tariff-F-charges-before-effect  per row, its instance.
; A row is data, never a hand-written producer arm.

(in-package "ACL2")
(include-book "output-command-admission")

(defconst *fn-tariff-u64* 18446744073709551616)

; The descriptor of a priced family: (:tariff F OCTETS) when OCTETS is a
; u64, else refused by name (:unrepresentable F), never saturated (D27).
(defun fn-tariff-descriptor (family octets)
  (declare (xargs :guard t))
  (if (and (keywordp family) (natp octets) (< octets *fn-tariff-u64*))
      (list :tariff family octets)
    (list :unrepresentable family)))

(defthm fn-tariff-descriptor-is-a-tariff
  (implies (and (keywordp family) (natp octets) (< octets *fn-tariff-u64*))
           (fn-ocap-tariffp (fn-tariff-descriptor family octets))))

; KEYSTONE (charge-before-effect at the gate, every family): over a preview
; of FAMILY the descriptor is held EXACTLY when its octets are within the
; capacity, and then the held prefix is the preview's own; otherwise it is
; refused as unaffordable, by name.
(defthm fn-tariff-descriptor-admits-exactly-within-capacity
  (implies (and (fn-ocap-previewp preview)
                (equal (fn-ocap-at 2 preview) family)
                (natp octets) (< octets *fn-tariff-u64*)
                (natp capacity) (< capacity *fn-tariff-u64*))
           (equal (fn-ocap-admit-preview preview (fn-tariff-descriptor family octets) capacity)
                  (if (<= octets capacity)
                      (list :hold (fn-ocap-at 1 preview) family)
                    (list :refused :output-tariff-unaffordable family)))))

; An unrepresentable price is refused, never held.
(defthm fn-tariff-descriptor-unrepresentable-is-refused
  (implies (not (and (natp octets) (< octets *fn-tariff-u64*)))
           (equal (fn-ocap-at 0 (fn-ocap-admit-preview preview (fn-tariff-descriptor family octets)
                                                       capacity))
                  :refused)))

(in-theory (disable fn-tariff-descriptor))

; The admission a priced family's price earns, spelled out for the keystone.
(defun fn-tariff-family-admission (preview pricedp price capacity)
  (declare (xargs :guard t))
  (let ((f (fn-ocap-at 2 preview)))
    (cond ((not (and pricedp (natp price) (< price *fn-tariff-u64*)))
           (list :refused :unpriced-output-family f))
          ((and (natp capacity) (< capacity *fn-tariff-u64*) (<= price capacity))
           (list :hold (fn-ocap-at 1 preview) f))
          (t (list :refused :output-tariff-unaffordable f)))))

(defun fn-tariff-family-arms (rows)
  (declare (xargs :mode :program))
  (if (atom rows) nil
    (cons (list (car (car rows)) (list 'nfix (cadr (car rows))))
          (fn-tariff-family-arms (cdr rows)))))

(defun fn-tariff-family-instances (rows)
  (declare (xargs :mode :program))
  (if (atom rows) nil
    (let ((f (car (car rows))))
      (cons
       `(defthm ,(intern-in-package-of-symbol
                  (concatenate 'string "FN-TARIFF-" (symbol-name f) "-CHARGES-BEFORE-EFFECT")
                  'fn-tariff-descriptor)
          (implies (and (fn-ocap-previewp preview)
                        (equal (fn-ocap-at 2 preview) ,f)
                        (< (fn-tariff-family-price preview as config fn-arena fn-cat) *fn-tariff-u64*)
                        (natp capacity) (< capacity *fn-tariff-u64*))
                   (equal (fn-ocap-admit-preview
                           preview (fn-tariff-family-preview preview as config fn-arena fn-cat)
                           capacity)
                          (if (<= (fn-tariff-family-price preview as config fn-arena fn-cat) capacity)
                              (list :hold (fn-ocap-at 1 preview) ,f)
                            (list :refused :output-tariff-unaffordable ,f))))
          :hints (("Goal" :use fn-tariff-family-preview-charges-before-effect
                   :in-theory (e/d (fn-tariff-family-admission)
                                   (fn-tariff-family-preview-charges-before-effect
                                    fn-tariff-family-price fn-tariff-family-preview
                                    fn-ocap-admit-preview fn-ocap-previewp fn-ocap-at)))))
       (fn-tariff-family-instances (cdr rows))))))

; (def-family-tariffs :context BINDINGS :rows ((FAMILY OCTETS) ...))
; BINDINGS: let* bindings of SESSION, ARGS and SERVER over PREVIEW, AS (the
; connection's authenticated session) and CONFIG (its pinned configuration);
; OCTETS: a term over SESSION ARGS SERVER FN-ARENA FN-CAT, read-only.
(defmacro def-family-tariffs (&key context rows)
  (let ((families (strip-cars rows)))
    `(progn
       (defconst *fn-tariff-priced-families* ',families)
       (defun fn-tariff-family-octets (family session args server fn-arena fn-cat)
         (declare (xargs :stobjs (fn-arena fn-cat) :guard t)
                  (ignorable session args server))
         (case family
           ,@(fn-tariff-family-arms rows)
           (otherwise 0)))
       (defun fn-tariff-family-price (preview as config fn-arena fn-cat)
         (declare (xargs :stobjs (fn-arena fn-cat) :guard t)
                  (ignorable as config))
         (let* ,context
           (declare (ignorable session args server))
           (fn-tariff-family-octets (fn-ocap-at 2 preview) session args server fn-arena fn-cat)))
       (defthm fn-tariff-family-price-natp
         (natp (fn-tariff-family-price preview as config fn-arena fn-cat))
         :rule-classes :type-prescription)
       (defun fn-tariff-family-preview (preview as config fn-arena fn-cat)
         (declare (xargs :stobjs (fn-arena fn-cat) :guard t))
         (if (member-eq (fn-ocap-at 2 preview) *fn-tariff-priced-families*)
             (fn-tariff-descriptor (fn-ocap-at 2 preview)
                                   (fn-tariff-family-price preview as config fn-arena fn-cat))
           (fn-ocap-unpriced-tariff preview)))
       ; KEYSTONE (the producer the host calls): at any capacity the gate
       ; holds exactly a priced family whose price is a u64 within it; a
       ; priced family over it is unaffordable, every other family unpriced,
       ; by name.
       (defthm fn-tariff-family-preview-charges-before-effect
         (implies (fn-ocap-previewp preview)
                  (equal (fn-ocap-admit-preview
                          preview (fn-tariff-family-preview preview as config fn-arena fn-cat)
                          capacity)
                         (fn-tariff-family-admission
                          preview
                          (member-eq (fn-ocap-at 2 preview) *fn-tariff-priced-families*)
                          (fn-tariff-family-price preview as config fn-arena fn-cat)
                          capacity)))
         :hints (("Goal" :in-theory (e/d (fn-tariff-descriptor)
                                         (fn-tariff-family-price)))))
       (in-theory (disable fn-tariff-family-price fn-tariff-family-preview))
       ,@(fn-tariff-family-instances rows))))
