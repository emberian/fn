(in-package "ACL2")
(include-book "../books/columns")
(include-book "std/testing/must-fail" :dir :system)

; A scalar named STAMP must not be mistaken for an array predicate ending
; in P. Unbounded numeric arrays have no bound rule; metadata has neither.
(assert-event
 (equal
  (fn2-columns-array-nth-runes
   '((stamp :type (unsigned-byte 60))
     (bytes :type (array (unsigned-byte 8) (0)))
     (naturals :type (array (integer 0 *) (0)))
     (metadata :type t)))
  '((:type-prescription bytesp-nth-natp)
    (:linear bytesp-nth-bound)
    (:type-prescription naturalsp-nth-natp))))

(must-fail
 (defcolumns fn2-unjustified ((value :u8))
   :extra-fields ((fn2-unjustified-metadata :type t)))
 :expected :hard :with-output-off nil :check-expansion t)
(must-fail
 (defcolumns fn2-unjustified-hash ((value :u8))
   :extra-fields ((fn2-unjustified-cache :type (hash-table equal))))
 :expected :hard :with-output-off nil :check-expansion t)
(must-fail
 (defcolumns fn2-empty-reason ((value :u8))
   :extra-fields ((fn2-empty-metadata :type t :why "")))
 :expected :hard :with-output-off nil :check-expansion t)

(defcolumns fn2-justified ((value :u8)) :rows-bound 8
 :extra-fields ((fn2-justified-metadata :type t
                :why "Unit-only metadata: never served.")))
(assert-event
 (let ((schema (fn2-decl-row (list :columns 'fn2-justified) (w state))))
   (and (equal (cadr (member-eq :extra-fields schema)) '((fn2-justified-metadata :type t)))
        (equal (cadr (member-eq :extra-field-reasons schema))
               '((fn2-justified-metadata . "Unit-only metadata: never served."))))))
(value-triple (cw "COLUMNS UNIT: unbounded t/hash/empty-reason refused; reason recorded, raw specs preserved PASS~%"))

(must-fail (defcolumns fn2-unjustified-u64 ((value :u64)))
 :expected :hard :with-output-off nil :check-expansion t)
(must-fail
 (defcolumns fn2-unjustified-raw-u64 ((value :u8))
   :extra-fields ((fn2-raw-wide :type (array (unsigned-byte 64) (0)) :initially 0 :resizable t)))
 :expected :hard :with-output-off nil :check-expansion t)
(assert-event (and (fn2-columns-extra-okp '((raw :type (unsigned-byte 63))))
                   (fn2-columns-extra-okp '((raw :type (integer 0 9223372036854775807))))))
(assert-event (and (not (fn2-columns-extra-okp '((raw :type (integer 0 9223372036854775808)))))
                   (not (fn2-columns-extra-okp '((raw :type (unsigned-byte 64)))))
                   (not (fn2-columns-extra-okp '((raw :type (integer 0 18446744073709551615)))))))
(defcolumns fn2-u64-test ((value :u64 :why "Unit-only full-width native u64 roundtrip.")) :rows-bound 4
 :extra-fields ((fn2-u64-test-raw :type (array (unsigned-byte 64) (0)) :initially 0 :resizable t
                :why "Unit-only raw u64 reason recording.")))
(assert-event
 (let ((schema (fn2-decl-row (list :columns 'fn2-u64-test) (w state))))
   (and (equal (cadr (member-eq :columns schema)) '((value :u64)))
        (equal (cadr (member-eq :column-reasons schema))
               '((value . "Unit-only full-width native u64 roundtrip.")))
        (equal (cadr (member-eq :extra-field-reasons schema))
               '((fn2-u64-test-raw . "Unit-only raw u64 reason recording."))))))
(assert-event
 (equal (cadr (member-eq :type (car (fn2-columns-fields 'fn2-u64-test '((value :u64))))))
        '(array (unsigned-byte 64) (0))))
(defun fn2-u64-unit ()
 (declare (xargs :guard t))
 (with-local-stobj fn2-u64-test
  (mv-let (answer fn2-u64-test)
   (let* ((fn2-u64-test (fn2-u64-test-init 2 fn2-u64-test))
          (fn2-u64-test (fn2-u64-test-set-value 0 9223372036854775815 fn2-u64-test))
          (fn2-u64-test (fn2-u64-test-set-value 1 18446744073709551615 fn2-u64-test)))
     (mv (and (= (fn2-u64-test-value 0 fn2-u64-test) 9223372036854775815)
              (= (fn2-u64-test-value 1 fn2-u64-test) 18446744073709551615)) fn2-u64-test))
   answer)))
(assert-event (fn2-u64-unit))

(defwide-columns fn2-wide-test :rows-bound 4)
(defun fn2-wide-unit ()
 (declare (xargs :guard t))
 (with-local-stobj fn2-wide-test
  (mv-let (answer fn2-wide-test)
   (let* ((fn2-wide-test (fn2-wide-test-init 2 fn2-wide-test))
          (fn2-wide-test (fn2-wide-test-set-hi 0 7 fn2-wide-test))
          (fn2-wide-test (fn2-wide-test-set-lo 0 1152921504606846975 fn2-wide-test))
          (fn2-wide-test (fn2-wide-test-set-hi 1 7 fn2-wide-test))
          (low-order (fn2-wide-test-compare 0 1 fn2-wide-test))
          (fn2-wide-test (fn2-wide-test-set-hi 1 8 fn2-wide-test))
          (before (fn2-wide-test-compare 0 1 fn2-wide-test)))
    (mv-let (code fn2-wide-test) (fn2-wide-test-increment 0 fn2-wide-test)
     (let* ((carried (and (eq low-order :gt) (eq before :lt) (eq code :ok)
                         (eq (fn2-wide-test-compare 0 1 fn2-wide-test) :eq)
                         (= (fn2-wide-test-hi 0 fn2-wide-test) 8)
                         (= (fn2-wide-test-lo 0 fn2-wide-test) 0)))
            (fn2-wide-test (fn2-wide-test-set-hi 1 1152921504606846975 fn2-wide-test))
            (fn2-wide-test (fn2-wide-test-set-lo 1 1152921504606846975 fn2-wide-test)))
      (mv-let (code fn2-wide-test) (fn2-wide-test-increment 1 fn2-wide-test)
       (mv (and carried (eq code :exhausted)
                (= (fn2-wide-test-hi 1 fn2-wide-test) 1152921504606846975)
                (= (fn2-wide-test-lo 1 fn2-wide-test) 1152921504606846975)
                (eq (fn2-wide-test-compare 0 1 fn2-wide-test) :lt)
                (eq (fn2-wide-test-compare 1 0 fn2-wide-test) :gt)) fn2-wide-test)))))
   answer)))
(assert-event (fn2-wide-unit))
(value-triple (cw "COLUMN WIDTH UNIT: native u64 roundtrip/reason; pair comparison/carry/exhaustion PASS~%"))
