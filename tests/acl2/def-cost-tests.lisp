; Teeth for books/def-cost.lisp: the derived visit cost of a real entry, its
; bound, the refusals, and the served whole-state-guard refusal on a fixture
; with the catalog guard's shape.
;
;   1. fn-id-hex-octets (books/identity-hex.lisp; host/native/bp-app.lisp
;      and bp-node.lisp dispatch it) declared served here: the derivation
;      inspected (route, the two cost terms, nothing unaccounted), the twins
;      pinned literally, the bound 2 + 2 n over n = (len octets) proved, the
;      row and the owed teeth row; the witnesses evaluated (; GEN: defteeth:
;      the positive witness under the kind check, the attaining witness).
;   2. An internal (undeclared) function: route :internal, body only.
;   3. A callee no contract covers: UNACCOUNTED, named; the bound partial
;      over it; a declaration that omits it refused.
;   4. Refusals by their words.
;   5. The served refusal: a stobj with a count and a guard that walks it by
;      the count, as fn-cat-handles-inp walks the catalog
;      (books/served-plan-cursor.lisp fn-splan-cursor-step's guard).
;   6. def-cost-check re-derives and agrees.

(in-package "ACL2")
(include-book "../../books/def-cost")
(include-book "../../books/identity-hex")
(include-book "../../books/payload-kinds")
(include-book "must-fail-checked")
(local (include-book "arithmetic/top" :dir :system))

(defmacro fn-cst-refused (fn kvs expected)
  `(make-event
    (mv-let (problem route cost un sizes bound)
      (fn-cost-problem ',fn ',kvs (w state))
      (declare (ignore route cost un sizes bound))
      (let ((text (if (and (consp problem) (stringp (car problem))) (car problem) "")))
        (if (search ,expected text)
            (value '(value-triple :refused))
          (er soft 'fn-cst-refused "~x0 refused by ~@1, expected ~x2"
              ',fn (or problem "nothing") ,expected))))))

; ---------------------------------------------------------------------------
; 1. A served entry over octets.

(definterface fn-id-hex-octets
  :class :common-lisp-compliant
  :kinds ((octets fn-cbor-octet-listp)))

(assert-event
 (mv-let (msg route rcost bcost un)
   (fn-cost-derive 'fn-id-hex-octets (w state))
   (and (null msg) (eq route :served) (null un)
        ; the kind check, evaluated once at the entry
        (equal rcost '(binary-+ '1 (len octets)))
        ; the body: a cons step per octet (every leaf 0: cons, car, floor,
        ; mod, the inlined fn-id-hex-digit), the recursion on the cdr
        (equal bcost '(if (consp octets) (fn-id-hex-octets-visits (cdr octets)) '0)))))

(def-cost fn-id-hex-octets
  :visits (+ 1 n)
  :sizes ((n (len octets))))

(assert-event
 (equal (getpropc 'fn-id-hex-octets-visits-bound 'theorem nil (w state))
        '(implies (fn-cbor-octet-listp octets)
                  (not (< (binary-+ '1 (len octets)) (fn-id-hex-octets-route-visits octets))))))
(assert-event
 (equal (cdr (assoc-eq 'fn-id-hex-octets (table-alist 'fn-cost (w state))))
        '(:route :served :twin fn-id-hex-octets-visits :route-twin fn-id-hex-octets-route-visits
          :route-cost (binary-+ '1 (len octets))
          :body-cost (if (consp octets) (fn-id-hex-octets-visits (cdr octets)) '0)
          :unaccounted nil :sizes ((n . (len octets))) :bound (binary-+ '1 n)
          :theorem fn-id-hex-octets-visits-bound :allocation :deferred)))
(assert-event
 (equal (cdr (assoc-eq 'fn-id-hex-octets-visits-bound (table-alist 'fn-teeth-owed (w state))))
        '(:by def-cost
          :claim (((g (fn-cbor-octet-listp octets)))
                  (<= (fn-id-hex-octets-route-visits octets) (binary-+ '1 (len octets))))
          :subject fn-id-hex-octets
          :visits ((route (fn-id-hex-octets-route-visits octets) (binary-+ '1 (len octets)))))))
; GEN: defteeth (lanedumps/generators-2.md v1): the positive witness under
; the kind check, and the bound ATTAINED there (the body visits nothing: its
; work is per cons, which allocation will count; the kind check is the walk)
(assert-event (and (fn-cbor-octet-listp '(0 15 255))
                   (equal (fn-id-hex-octets-route-visits '(0 15 255)) 4)
                   (equal (fn-id-hex-octets-visits '(0 15 255)) 0)))
(assert-event (equal (fn-id-hex-octets-route-visits nil) 1))

; ---------------------------------------------------------------------------
; 2. An internal function: no interface row, so no entry cost.

(defun fn-cst-pair-sum (xs)
  (declare (xargs :guard (true-listp xs)))
  (if (consp xs) (+ (len xs) (fn-cst-pair-sum (cdr xs))) 0))
(assert-event
 (mv-let (msg route rcost bcost un)
   (fn-cost-derive 'fn-cst-pair-sum (w state))
   (and (null msg) (eq route :internal) (null un)
        (equal rcost ''0)
        (equal bcost '(if (consp xs)
                          (binary-+ (binary-+ '1 (len xs)) (fn-cst-pair-sum-visits (cdr xs)))
                        '0)))))
(def-cost fn-cst-pair-sum
  :visits (+ n (* n n))
  :sizes ((n (len xs)))
  :hints (("Goal" :in-theory (enable fn-cst-pair-sum-visits fn-cst-pair-sum-route-visits)
           :induct (fn-cst-pair-sum-visits xs))))
(assert-event (equal (fn-cst-pair-sum-route-visits '(a b c)) 9))

; ---------------------------------------------------------------------------
; 3. A callee with no contract, no row and a body the inliner refuses (it
; recurs): unaccounted, named; the bound is partial over it.

(defun fn-cst-walk (xs)
  (declare (xargs :guard t))
  (if (consp xs) (fn-cst-walk (cdr xs)) nil))
(defun fn-cst-uses-walk (xs)
  (declare (xargs :guard t))
  (fn-cst-walk xs))
(assert-event
 (mv-let (msg route rcost bcost un)
   (fn-cost-derive 'fn-cst-uses-walk (w state))
   (and (null msg) (eq route :internal) (equal un '(fn-cst-walk)) (equal rcost ''0)
        (equal bcost '(fn-cost-unaccounted 'fn-cst-walk (list xs))))))
(fn-cst-refused fn-cst-uses-walk (:visits 0 :sizes ()) "unaccounted (no contract")
(def-cost fn-cst-uses-walk :visits 0 :sizes () :unaccounted (fn-cst-walk))
(assert-event
 (equal (getpropc 'fn-cst-uses-walk-visits-bound 'theorem nil (w state))
        '(not (< (fn-cost-unaccounted 'fn-cst-walk (cons xs 'nil)) (fn-cst-uses-walk-route-visits xs)))))
; once the callee has its own row, the caller's derivation uses it
(def-cost fn-cst-walk :visits n :sizes ((n (len xs))))
(defun fn-cst-uses-walk-2 (xs) (declare (xargs :guard t)) (fn-cst-walk xs))
(assert-event
 (mv-let (msg route rcost bcost un)
   (fn-cost-derive 'fn-cst-uses-walk-2 (w state))
   (declare (ignore route rcost))
   (and (null msg) (null un) (equal bcost '(fn-cst-walk-visits xs)))))

; ---------------------------------------------------------------------------
; 4. Refusals.

(fn-cst-refused fn-id-hex-octets (:visits 1 :sizes ()) "already has a cost row")
(fn-cst-refused fn-cst-nothing () "is not a function in this world")
(fn-cst-refused fn-cst-walk (:bogus 1) "unknown keyword")
(defun fn-cst-prog (xs) (declare (xargs :mode :program)) xs)
(fn-cst-refused fn-cst-prog () "is :program mode")
(fn-cst-refused fn-cst-uses-walk-2 (:sizes (n)) "is not ((S TERM) ...)")
(fn-cst-refused fn-cst-uses-walk-2 (:visits (+ 1 m) :sizes ((n (len xs)))) "not size names")
(fn-cst-refused fn-cst-uses-walk-2 (:visits 1 :sizes ((n (len ys)))) "not a formal")
(fn-cst-refused fn-cst-uses-walk-2 (:visits nil :sizes ()) "names no bound")

; ---------------------------------------------------------------------------
; 5. The served refusal: the catalog guard's shape.

(defstobj fn-cst-cat (fn-cst-rows :type (array integer (0)) :initially 0 :resizable t))
(defun fn-cst-count (fn-cst-cat)
  (declare (xargs :stobjs fn-cst-cat))
  (fn-cst-rows-length fn-cst-cat))
; the walk by the count, as fn-cat-handles-inp: a whole-state size in a guard
; (the rows themselves are not read: the walk's shape is what the fixture tests)
(defun fn-cst-rows-okp (n fn-cst-cat)
  (declare (xargs :stobjs fn-cst-cat :guard (natp n)))
  (if (zp n) t (and (<= n (fn-cst-count fn-cst-cat)) (fn-cst-rows-okp (- n 1) fn-cst-cat))))
(defun fn-cst-step (fn-cst-cat)
  (declare (xargs :stobjs fn-cst-cat :guard (fn-cst-rows-okp (fn-cst-count fn-cst-cat) fn-cst-cat)))
  fn-cst-cat)
(definterface fn-cst-step :class :common-lisp-compliant)
; the size function is named in the trusted list for this fixture's world
(assert-event (member-eq 'fn-cat-count *fn-cost-whole-state-sizes*))
; the fixture's count stands in: the guard's derived cost on the served route
; mentions it through the unaccounted walk
(assert-event
 (mv-let (msg route rcost bcost un)
   (fn-cost-derive 'fn-cst-step (w state))
   (declare (ignore bcost un))
   (and (null msg) (eq route :served)
        ; the count is one array length (a stobj primitive), the walk unaccounted
        (equal rcost '(binary-+ '1 (fn-cost-unaccounted 'fn-cst-rows-okp
                                                        (list (fn-cst-count fn-cst-cat) fn-cst-cat)))))))
; with fn-cst-count a whole-state size the declaration is refused: the real
; list names fn-cat-count, so the refusal is asserted on the real catalog
; entry in the image world (host/cost-host.lisp), and here on the term
(assert-event
 (equal (fn-cost-mentions '(fn-cost-unaccounted 'fn-cat-handles-inp
                                                (list (fn-cat-count fn-cat) fn-arena fn-cat))
                          *fn-cost-whole-state-sizes*)
        'fn-cat-count))

; ---------------------------------------------------------------------------
; 6. def-cost-check agrees with itself.

(def-cost-check fn-id-hex-octets)
(def-cost-check fn-cst-pair-sum)
; fn-cst-walk gained a row AFTER fn-cst-uses-walk's partial row: the world
; now derives (fn-cst-walk-visits xs) where the row holds the unaccounted
; term, so the stale row is refused until it is declared again
(must-fail-checked (def-cost-check fn-cst-uses-walk)
                   :unchecked "the callee's later row changes the derivation; the stale row refuses")
(must-fail-checked (def-cost-check fn-cst-uses-walk-2) :unchecked "no cost row")
