; W9's explicit reservation coordinate: current 64-bit SBCL cons layout,
; byte-character radix and record metadata codec. This arithmetic budget
; does not itself prove that actual owner writers carry its support bound.
(in-package "ACL2")
(include-book "records-shape")
(local (include-book "arithmetic/top" :dir :system))

; Fixed carry overhead includes view/count and one global-table binding.
; One path edge has branch spine+entry = two 16-byte conses. The terminal
; adds three conses (spine, entry and contribution pair). Each count/charge
; is reserved at the uint64 bound: retention-obligation-view-bounds proves
; this conditional on ledger capacity. The actual configured-owner bridge
; remains open. Reserve 32 bytes for representation/alignment per integer.
(defconst *fn-ovb-cons-octets* 16)
(defconst *fn-ovb-integer-octets* 32)
(defconst *fn-ovb-branch-width* 257)

(defun fn-ovb-object-octets (characters subjects)
  (declare (xargs :guard t))
  (+ 80 (* 32 (nfix characters))
     (* (+ 48 (* 2 *fn-ovb-integer-octets*)) (nfix subjects))))

; Every accepted record contributes at most one subject. T is cumulative;
; compaction/reclaim does not return transaction credits. Old/new carry
; coexist during off-mutex rebuild; both also need collector copy room.
(defun fn-ovb-retained-reserve (records)
  (declare (xargs :guard t))
  (* 4 (fn-ovb-object-octets
         (* *fn-record-max-metadata* (nfix records)) (nfix records))))

; A delta coerces at most metadata characters and copies at most 258 conses
; per path level: 256 preceding branches, two new entry conses. There are
; metadata+1 levels (including terminal). Include new pair/integer/carry
; allocation and collector copy room. The actual bounded-step proof is open.
(defun fn-ovb-delta-reserve ()
  (declare (xargs :guard t))
  (* 2 (+ (* *fn-ovb-cons-octets*
             (+ *fn-record-max-metadata*
                (* (+ 1 *fn-record-max-metadata*) (+ 1 *fn-ovb-branch-width*))))
          128)))

(defun fn-heap-obligation-view-reserve (records)
  (declare (xargs :guard t))
  (+ (fn-ovb-retained-reserve records) (fn-ovb-delta-reserve)))

(defthm fn-heap-obligation-view-reserve-natp
  (natp (fn-heap-obligation-view-reserve records))
  :rule-classes :type-prescription)
(defthm fn-heap-obligation-view-reserve-monotone
  (implies (<= (nfix n) (nfix m))
           (<= (fn-heap-obligation-view-reserve n)
               (fn-heap-obligation-view-reserve m))))
(defthm fn-ovb-funded-support-reserve
  (implies (and (<= (nfix characters) (* *fn-record-max-metadata* (nfix records)))
                (<= (nfix subjects) (nfix records)))
           (<= (+ (* 4 (fn-ovb-object-octets characters subjects))
                  (fn-ovb-delta-reserve))
               (fn-heap-obligation-view-reserve records))))

(in-theory (disable fn-ovb-object-octets fn-ovb-retained-reserve
                    fn-ovb-delta-reserve fn-heap-obligation-view-reserve))
