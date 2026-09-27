; Teeth for PRF-230 (books/article-header-limits): the header limits are the
; operator's and the parser admits exactly up to them.  Each keystone has a
; reachable witness asserting its whole antecedent and conclusion, and one
; must-fail per hypothesis: the hypothesis false and the conclusion false.
(in-package "ACL2")
(include-book "../../books/article-header-limits")
(include-book "std/testing/must-fail" :dir :system)

(defun fn-ahlt-fields (n)
  ; N fields "X: x" then the blank line and a one-line body.
  (if (zp n)
      '(13 10 98 13 10)
    (append '(88 58 32 120 13 10) (fn-ahlt-fields (1- n)))))

(defun fn-ahlt-folds (n)
  (if (zp n) nil (append '(9 120 13 10) (fn-ahlt-folds (1- n)))))

(defconst *ahlt-900* (fn-ahlt-fields 900))
(defconst *ahlt-1000* (fn-ahlt-fields 1000))
(defconst *ahlt-1001* (fn-ahlt-fields 1001))
(defconst *ahlt-64* (fn-ahlt-fields 64))
(defconst *ahlt-65* (fn-ahlt-fields 65))
; The profile of the native case: 1,000 fields, 2,000 lines, 1 MiB.
(defconst *ahlt-raised* (fn-article-limits 1000 2000 1048576))
; The widest limits a profile may write (STO-030's codec relation).
(defconst *ahlt-ceiling*
  (fn-article-limits 4261412864 4261412864 4261412864))

; The default parser is today's: 64 fields admitted, the 65th refused by name.
(assert-event (fn-article-result-okp (fn-article-parse *ahlt-64*)))
(assert-event (equal (fn-article-parse *ahlt-65*) '(:error :header-fields-limit)))
(assert-event (equal (fn-article-parse *ahlt-900*) '(:error :header-fields-limit)))
; The raised profile: 900 and 1,000 admitted, 1,001 refused by name.
(assert-event (fn-article-result-okp (fn-article-parse-under *ahlt-900* *ahlt-raised*)))
(assert-event (fn-article-result-okp (fn-article-parse-under *ahlt-1000* *ahlt-raised*)))
(assert-event (equal (fn-article-parse-under *ahlt-1001* *ahlt-raised*)
                     '(:error :header-fields-limit)))
(assert-event (equal (len (fn-article-fields
                           (fn-article-result-article
                            (fn-article-parse-under *ahlt-1000* *ahlt-raised*))))
                     1000))
; Lines and octets, each at its limit and one past it, by name.
(defconst *ahlt-folded-10* (append '(88 58 32 120 13 10) (fn-ahlt-folds 9) '(13 10)))
(assert-event (fn-article-result-okp
               (fn-article-parse-under *ahlt-folded-10* (fn-article-limits 5 10 1000))))
(assert-event (equal (fn-article-parse-under *ahlt-folded-10* (fn-article-limits 5 9 1000))
                     '(:error :header-lines-limit)))
; 6 + 9 x 4 = 42 header octets.
(assert-event (equal (fn-article-header-census *ahlt-folded-10*) '(1 10 42)))
(assert-event (fn-article-result-okp
               (fn-article-parse-under *ahlt-folded-10* (fn-article-limits 5 10 42))))
(assert-event (equal (fn-article-parse-under *ahlt-folded-10* (fn-article-limits 5 10 41))
                     '(:error :header-octets-limit)))
; Folded to depth 2,000 (the hostile campaign's case): refused by the
; default profile by name, admitted by a profile raised to 2,001 lines.
(defconst *ahlt-folded-2000* (append '(88 58 32 120 13 10) (fn-ahlt-folds 2000) '(13 10)))
(assert-event (equal (fn-article-parse *ahlt-folded-2000*) '(:error :header-lines-limit)))
(assert-event (fn-article-result-okp
               (fn-article-parse-under *ahlt-folded-2000* (fn-article-limits 1 2001 1048576))))

; ---------------------------------------------------------------------------
; Keystone fn-article-parse-under-admits-exactly-the-limits.
; Witness (within): WIDER the ceiling, LIMITS raised, 900 fields.
(assert-event
 (and (fn-article-result-okp (fn-article-parse-under *ahlt-900* *ahlt-ceiling*))
      (fn-article-census-within (fn-article-header-census *ahlt-900*) *ahlt-raised*)
      (equal (fn-article-parse-under *ahlt-900* *ahlt-raised*)
             (fn-article-parse-under *ahlt-900* *ahlt-ceiling*))))
; Witness (past): 1,001 fields under the raised limits: refused by name.
(assert-event
 (and (fn-article-result-okp (fn-article-parse-under *ahlt-1001* *ahlt-ceiling*))
      (not (fn-article-census-within (fn-article-header-census *ahlt-1001*) *ahlt-raised*))
      (equal (car (fn-article-parse-under *ahlt-1001* *ahlt-raised*)) :error)
      (fn-article-limit-reasonp (cadr (fn-article-parse-under *ahlt-1001* *ahlt-raised*)))))
; Tooth (the input parses under WIDER): WIDER admits 1 field, the input has 2
; within LIMITS; the two parses differ.
(must-fail
 (assert-event
  (let ((wider (fn-article-limits 1 10 100)) (octets (fn-ahlt-fields 2)))
    (implies (fn-article-census-within (fn-article-header-census octets) *ahlt-raised*)
             (equal (fn-article-parse-under octets *ahlt-raised*)
                    (fn-article-parse-under octets wider))))))
; Tooth, the other branch: an input no limits admit (a continuation line
; first) is refused by :invalid-header, not a limit name.
(defconst *ahlt-bad* '(9 120 13 10 13 10))
(assert-event (equal (fn-article-parse-under *ahlt-bad* *ahlt-ceiling*)
                     '(:error :invalid-header)))
(must-fail
 (assert-event
  (fn-article-limit-reasonp (cadr (fn-article-parse-under *ahlt-bad* (fn-article-limits 5 10 1000))))))

; Keystone fn-article-parse-under-within-its-limits.
(assert-event
 (and (fn-article-result-okp (fn-article-parse-under *ahlt-1000* *ahlt-raised*))
      (fn-article-census-within (fn-article-header-census *ahlt-1000*) *ahlt-raised*)))
; Tooth (the parse succeeds): 1,001 fields are not within the raised limits.
(must-fail
 (assert-event
  (fn-article-census-within (fn-article-header-census *ahlt-1001*) *ahlt-raised*)))

; Keystone fn-article-parse-under-raised-limits-agree.
(assert-event
 (and (fn-article-result-okp (fn-article-parse-under *ahlt-64* *fn-article-default-limits*))
      (fn-article-limits-within *fn-article-default-limits* *ahlt-raised*)
      (equal (fn-article-parse-under *ahlt-64* *ahlt-raised*)
             (fn-article-parse-under *ahlt-64* *fn-article-default-limits*))))
; Tooth (the parse succeeds under LIMITS): 65 fields, refused by the
; defaults, admitted by the raised limits.
(must-fail
 (assert-event
  (equal (fn-article-parse-under *ahlt-65* *ahlt-raised*)
         (fn-article-parse-under *ahlt-65* *fn-article-default-limits*))))
; Tooth (LIMITS within WIDER): "wider" narrower than the defaults.
(must-fail
 (assert-event
  (equal (fn-article-parse-under *ahlt-64* (fn-article-limits 10 256 16384))
         (fn-article-parse-under *ahlt-64* *fn-article-default-limits*))))
