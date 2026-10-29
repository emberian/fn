(in-package "ACL2")
(include-book "../books/columns")
(include-book "std/testing/must-fail" :dir :system)

(must-fail
 (defcolumns fn2-unjustified ((value :u8))
   :extra-fields ((fn2-unjustified-metadata :type t)))
 :expected :soft :with-output-off nil :check-expansion t)
(must-fail
 (defcolumns fn2-unjustified-hash ((value :u8))
   :extra-fields ((fn2-unjustified-cache :type (hash-table equal))))
 :expected :soft :with-output-off nil :check-expansion t)
(must-fail
 (defcolumns fn2-empty-reason ((value :u8))
   :extra-fields ((fn2-empty-metadata :type t :why "")))
 :expected :soft :with-output-off nil :check-expansion t)

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
 :expected :soft :with-output-off nil :check-expansion t)
(must-fail
 (defcolumns fn2-unjustified-bounded ((value :u8))
   :extra-fields ((fn2-unjustified-count :type (unsigned-byte 8) :initially 0)))
 :expected :soft :with-output-off nil :check-expansion t)
(assert-event (and (fn2-columns-extra-okp '((raw :type (unsigned-byte 63) :why "Unit-only bounded scalar.")))
                   (fn2-columns-extra-okp '((raw :type (integer 0 9223372036854775807) :why "Unit-only bounded scalar.")))))
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
          (fn2-wide-test (fn2-wide-test-set-lo 0 *fn2-u60-max* fn2-wide-test))
          (fn2-wide-test (fn2-wide-test-set-hi 1 7 fn2-wide-test))
          (low-order (fn2-wide-test-compare 0 1 fn2-wide-test))
          (fn2-wide-test (fn2-wide-test-set-hi 1 8 fn2-wide-test))
          (before (fn2-wide-test-compare 0 1 fn2-wide-test)))
    (mv-let (code fn2-wide-test) (fn2-wide-test-increment 0 fn2-wide-test)
     (let* ((carried (and (eq low-order :gt) (eq before :lt) (eq code :ok)
                         (eq (fn2-wide-test-compare 0 1 fn2-wide-test) :eq)
                         (= (fn2-wide-test-hi 0 fn2-wide-test) 8)
                         (= (fn2-wide-test-lo 0 fn2-wide-test) 0)))
            (fn2-wide-test (fn2-wide-test-set-hi 1 *fn2-u60-max* fn2-wide-test))
            (fn2-wide-test (fn2-wide-test-set-lo 1 *fn2-u60-max* fn2-wide-test)))
      (mv-let (code fn2-wide-test) (fn2-wide-test-increment 1 fn2-wide-test)
       (mv (and carried (eq code :exhausted)
                (= (fn2-wide-test-hi 1 fn2-wide-test) *fn2-u60-max*)
                (= (fn2-wide-test-lo 1 fn2-wide-test) *fn2-u60-max*)
                (eq (fn2-wide-test-compare 0 1 fn2-wide-test) :lt)
                (eq (fn2-wide-test-compare 1 0 fn2-wide-test) :gt)) fn2-wide-test)))))
   answer)))
(assert-event (fn2-wide-unit))
(value-triple (cw "COLUMN WIDTH UNIT: native u64 roundtrip/reason; pair comparison/carry/exhaustion PASS~%"))

; A small local instance exercises all kinds, enums and extra raw fields.
; No example storage or exported names are imposed on includers.
(local
 (defcolumns fn2-columns-example
   ((byte :u8) (short :u16) (word :u32) (gen :u60) (flag :bool)
    (phase (:enum fn2-columns-example-phase (:free :busy))) (next :link))
   :rows-bound 32
   :extra-fields
   ((fn2-columns-example-bytes :type (array (unsigned-byte 8) (0))
                               :initially 0 :resizable t :why "Unit fixture exercises resizable extra arrays.")
    (fn2-columns-example-count :type (integer 0 16) :initially 0 :why "Unit fixture exercises bounded scalar extras.")
    (fn2-columns-example-heads :initially 0 :type (array (unsigned-byte 32) (16)) :why "Unit fixture exercises fixed extra arrays.")
    (fn2-columns-example-metadata :initially nil :type t
     :why "Local DSL test: unrestricted metadata is never served.")
    (fn2-columns-example-objects :initially nil :type (array t (3))
     :why "Local DSL test: exercises object arrays, never served.")
    (fn2-columns-example-cache :type (hash-table equal) :initially nil
     :why "Local DSL test: exercises hash-table fields, never served.")
    (fn2-columns-example-bare :why "Local DSL test: exercises the default t field type, never served."))))

(local
 (defun fn2-columns-example-extra-reader (i fn2-columns-example)
   (declare (xargs :stobjs fn2-columns-example :guard (and (natp i) (< i 16))))
   (+ 1 (fn2-columns-example-headsi i fn2-columns-example))))

(local
 (defun fn2-columns-example-row-arithmetic (i fn2-columns-example)
   (declare (xargs :stobjs fn2-columns-example
                   :guard (and (fn2-columns-example-wfp fn2-columns-example)
                               (natp i) (< i (fn2-columns-example-rows fn2-columns-example)))))
   (+ (fn2-columns-example-rows fn2-columns-example)
      (fn2-columns-example-word i fn2-columns-example))))

(local
 (defun fn2-columns-example-test ()
   (declare (xargs :guard t))
   (with-local-stobj fn2-columns-example
     (mv-let (answer fn2-columns-example)
       (let* ((fn2-columns-example (fn2-columns-example-init 3 fn2-columns-example))
              (fn2-columns-example (fn2-columns-example-set-word 2 42 fn2-columns-example))
              (fn2-columns-example (fn2-columns-example-set-flag 1 1 fn2-columns-example))
              (fn2-columns-example (fn2-columns-example-set-phase 2
                (- *fn2-columns-example-phase-count* 1) fn2-columns-example)))
         (mv (and (equal (fn2-columns-example-word 2 fn2-columns-example) 42)
                  (equal (fn2-columns-example-flag 1 fn2-columns-example) 1)
                  (equal (fn2-columns-example-rows fn2-columns-example) 3)
                  (equal (fn2-columns-example-next 2 fn2-columns-example) *fn2-none*)
                  (equal (fn2-columns-example-record-word (fn2-columns-example-row-snapshot 2 fn2-columns-example))
                         (fn2-columns-example-word 2 fn2-columns-example))
                  (equal (fn2-columns-example-row-snapshot 2 fn2-columns-example) `(0 0 42 0 0 1 ,*fn2-none*)))
             fn2-columns-example))
       answer))))

(local (assert-event (fn2-columns-example-test)))
(local (assert-event (equal (fn2-columns-example-phase-code->keyword 1) :busy)))
(local (assert-event (equal (fn2-columns-example-phase-keyword->code :free) 0)))
(local (assert-event (assoc-eq 'fn2-columns-example (reverse (fn2-decl-rows :columns (w state))))))

(assert-event
 (equal (fn2-columns-copy-bindings 'scratch 'scratch-ref
          '((octets :type (array (unsigned-byte 8) (0)) :resizable t)
            (sample-counter :type (unsigned-byte 32))))
        '((scratch-ref (resize-octets (octets-length scratch) scratch-ref))
          (scratch-ref (octets-copy (octets-length scratch) 0 scratch scratch-ref))
          (scratch-ref (update-sample-counter (sample-counter scratch) scratch-ref)))))
(assert-event
 (equal (fn2-columns-diff-terms 'scratch 'scratch-ref
          '((octets :type (array (unsigned-byte 8) (0)))
            (sample-counter :type (unsigned-byte 32))) '(octets))
        '((if (equal (octets-length scratch) (octets-length scratch-ref)) nil
              (list 'octets-length))
          (and (not (equal (sample-counter scratch) (sample-counter scratch-ref))) (list 'sample-counter)))))
(local (assert-event (= *fn2-columns-example-phase-count* 2)))
(local
 (must-fail
  (defun fn2-columns-example-unnamed-phase (fn2-columns-example)
    (declare (xargs :stobjs fn2-columns-example
                    :guard (and (fn2-columns-example-wfp fn2-columns-example)
                                (< 0 (fn2-columns-example-rows fn2-columns-example)))))
    (fn2-columns-example-set-phase 0 *fn2-columns-example-phase-count* fn2-columns-example))
  :with-output-off nil :check-expansion t))

(defconst *fn2-columns-scalar-dimension* 3)
(defcolumns fn2-columns-scalar nil
 :extra-fields
 ((fn2-columns-scalar-head :type (unsigned-byte 32) :initially *fn2-none*
   :why "Single fixture head has no row index.")
  (fn2-columns-scalar-bytes :type (array (unsigned-byte 8) (*fn2-columns-scalar-dimension*)) :initially 0
   :why "Raw fixture bytes test a named dimension without a dummy row column.")))
(defun fn2-columns-scalar-control ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-columns-scalar
  (mv-let (ok fn2-columns-scalar)
    (mv (equal (list (fn2-columns-scalar-head fn2-columns-scalar)
                     (fn2-columns-scalar-bytes-length fn2-columns-scalar))
               (list *fn2-none* *fn2-columns-scalar-dimension*)) fn2-columns-scalar) ok)))
(assert-event (fn2-columns-scalar-control))
