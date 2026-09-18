; fn: correspondence of the polynomial matcher with anchored wildcard meaning.
(in-package "ACL2")
(include-book "wildmat")

; Independent backtracking semantics, reading both lists right-to-left.
; Empty patterns match only empty targets.  A star either consumes nothing
; or consumes one codepoint and remains available; ? consumes exactly one;
; literals consume exactly the same codepoint.  This reference is for logic,
; not the runtime implementation (it may perform exponential work).
(defun fn-wm-reference (reverse-items reverse-target)
  (declare (xargs :measure (+ (acl2-count reverse-items)
                             (acl2-count reverse-target))))
  (if (consp reverse-items)
      (if (equal (car reverse-items) 42)
          (or (fn-wm-reference (cdr reverse-items) reverse-target)
              (and (consp reverse-target)
                   (fn-wm-reference reverse-items (cdr reverse-target))))
        (and (consp reverse-target)
             (or (equal (car reverse-items) 63)
                 (and (fn-wildmat-exactp (car reverse-items))
                      (equal (car reverse-items) (car reverse-target))))
             (fn-wm-reference (cdr reverse-items) (cdr reverse-target))))
    (not (consp reverse-target))))

; Meaning of every row position: match the whole consumed target prefix.
(defun fn-wm-reference-row (reverse-items target reverse-prefix)
  (declare (xargs :measure (acl2-count target)))
  (if (consp target)
      (cons (fn-wm-reference reverse-items reverse-prefix)
            (fn-wm-reference-row reverse-items (cdr target)
                                 (cons (car target) reverse-prefix)))
    (list (fn-wm-reference reverse-items reverse-prefix))))

(defthm fn-wm-reference-boolean
  (booleanp (fn-wm-reference items target))
  :rule-classes :type-prescription)

(defthm fn-wm-reference-row-consp
  (consp (fn-wm-reference-row items target prefix))
  :rule-classes :type-prescription)

(defthm fn-wm-reference-row-car
  (equal (car (fn-wm-reference-row items target prefix))
         (fn-wm-reference items prefix)))

(defthm fn-wm-reference-row-length
  (equal (len (fn-wm-reference-row items target prefix))
         (+ 1 (len target))))

(defthm fn-wm-reference-row-boolean
  (boolean-listp (fn-wm-reference-row items target prefix)))

(defthm fn-wm-character-aux-correspondence
  (implies (not (equal item 42))
           (equal (fn-wildmat-step-character-aux
                   target (fn-wm-reference-row items target prefix) item)
                  (cdr (fn-wm-reference-row (cons item items) target prefix))))
  :hints (("Goal" :induct (fn-wm-reference-row items target prefix)
           :in-theory (disable fn-wildmat-exactp))))

(defthm fn-wm-character-correspondence
  (implies (not (equal item 42))
           (equal (fn-wildmat-step-character
                   target (fn-wm-reference-row items target nil) item)
                  (fn-wm-reference-row (cons item items) target nil)))
  :hints (("Goal" :in-theory (disable fn-wildmat-step-character-aux))))

(defthm fn-wm-star-aux-correspondence
  (equal (fn-wildmat-step-star-aux
          target (cdr (fn-wm-reference-row items target prefix))
          (fn-wm-reference (cons 42 items) prefix))
         (cdr (fn-wm-reference-row (cons 42 items) target prefix)))
  :hints (("Goal" :induct (fn-wm-reference-row items target prefix)
           :in-theory (enable fn-wildmat-bool-or))))

(defthm fn-wm-star-correspondence
  (equal (fn-wildmat-step-star
          target (fn-wm-reference-row items target nil))
         (fn-wm-reference-row (cons 42 items) target nil))
  :hints (("Goal" :use ((:instance fn-wm-star-aux-correspondence (prefix nil)))
           :in-theory (disable fn-wildmat-step-star-aux
                               fn-wm-star-aux-correspondence
                               fn-wm-reference-row))))

(defun fn-wm-row-induct (items target prefix)
  (if (consp items)
      (fn-wm-row-induct (cdr items) target (cons (car items) prefix))
    (list target prefix)))

(defthm fn-wm-pattern-row-correspondence
  (equal (fn-wildmat-pattern-row
          items target (fn-wm-reference-row prefix target nil))
         (fn-wm-reference-row (revappend items prefix) target nil))
  :hints (("Goal" :induct (fn-wm-row-induct items target prefix)
           :in-theory (disable fn-wildmat-step-character
                               fn-wildmat-step-star
                               fn-wm-reference-row fn-wm-reference))))

(defthm fn-wm-empty-pattern-row-tail
  (implies (consp prefix)
           (equal (fn-wm-reference-row nil target prefix)
                  (cons nil (fn-wildmat-false-row target))))
  :hints (("Goal" :induct (fn-wm-reference-row nil target prefix))))

(defthm fn-wm-initial-row-correspondence
  (equal (fn-wildmat-initial-row target)
         (fn-wm-reference-row nil target nil)))

(defthm fn-wm-last-reference-row
  (equal (fn-wildmat-row-last (fn-wm-reference-row items target prefix))
         (fn-wm-reference items (revappend target prefix)))
  :hints (("Goal" :induct (fn-wm-reference-row items target prefix)
           :in-theory (disable fn-wm-reference))))

; Public reference meaning is anchored to the entire target, not a substring.
; Reversing both lists only changes which end is consumed by backtracking.
(defun fn-wm-anchored-matchp (items target)
  (fn-wm-reference (revappend items nil) (revappend target nil)))

(defthm fn-wildmat-pattern-matchp-is-anchored-reference
  (equal (fn-wildmat-pattern-matchp items target)
         (fn-wm-anchored-matchp items target))
  :hints (("Goal" :in-theory (disable fn-wildmat-pattern-row
                                      fn-wildmat-initial-row
                                      fn-wildmat-row-last
                                      fn-wm-reference-row
                                      fn-wm-reference))))

(defthm fn-wildmat-matcher-row-length
  (equal (len (fn-wildmat-pattern-row
               items target (fn-wildmat-initial-row target)))
         (+ 1 (len target)))
  :hints (("Goal" :in-theory (disable fn-wildmat-pattern-row
                                      fn-wildmat-initial-row
                                      fn-wm-reference-row))))

(defthm fn-wildmat-matcher-row-boolean
  (boolean-listp (fn-wildmat-pattern-row
                  items target (fn-wildmat-initial-row target)))
  :hints (("Goal" :in-theory (disable fn-wildmat-pattern-row
                                      fn-wildmat-initial-row
                                      fn-wm-reference-row))))

; Independent left-to-right selection: each matching constituent replaces the
; earlier choice.  Unlike the implementation this does not search from right.
(defun fn-wm-select-reference (patterns target previous)
  (if (consp patterns)
      (fn-wm-select-reference
       (cdr patterns) target
       (if (fn-wm-anchored-matchp
            (fn-wildmat-pattern-items (car patterns)) target)
           (car patterns)
         previous))
    previous))

(defthm fn-wm-selection-correspondence
  (implies (fn-wildmat-pattern-listp patterns)
           (equal (fn-wm-select-reference patterns target previous)
                  (if (fn-wildmat-rightmost-match patterns target)
                      (fn-wildmat-rightmost-match patterns target)
                    previous)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-wm-select-reference patterns target previous)
           :in-theory (disable fn-wm-anchored-matchp
                               fn-wildmat-pattern-matchp))))

(defthm fn-wildmat-rightmost-match-is-last-reference-match
  (implies (fn-wildmat-pattern-listp patterns)
           (equal (fn-wildmat-rightmost-match patterns target)
                  (fn-wm-select-reference patterns target nil)))
  :hints (("Goal" :use ((:instance fn-wm-selection-correspondence
                                   (previous nil)))
           :in-theory (disable fn-wildmat-rightmost-match
                               fn-wm-select-reference))))

(defthm fn-wildmat-match-codepoints-is-reference-decision
  (implies (fn-wildmat-pattern-listp patterns)
           (equal (fn-wildmat-match-codepoints patterns target)
                  (fn-wildmat-pattern-positivep
                   (fn-wm-select-reference patterns target nil))))
  :hints (("Goal" :in-theory (disable fn-wildmat-rightmost-match
                                      fn-wm-select-reference))))
