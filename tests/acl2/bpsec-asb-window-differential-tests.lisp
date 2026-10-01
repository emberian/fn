(in-package "ACL2")
(include-book "../../books/bpsec-asb")
; Differential schedule tests only. Immutable backing/slice relation is
; constructed in ACL2; no installed provider or primitive is represented.
(defconst *fn-bpsdw-limits* (fn-bps-limits-make 4096 128 16 16 2048 2048))
(defconst *fn-bpsdw-bib-wire*
 (append '(130 0 27 255 255 255 255 255 255 255 255 1 0 130 2 130 10 0 130 129 130 1 88 48)
         (make-list 48 :initial-element 65) '(129 130 1 88 48)
         (make-list 48 :initial-element 66)))
(defconst *fn-bpsdw-bib*
 (fn-bps-asb-make 11 '(0 18446744073709551615) 1 0 '(:ipn 10 0) nil
  (list (list (list 1 (cons :bytes (make-list 48 :initial-element 65))))
        (list (list 1 (cons :bytes (make-list 48 :initial-element 66)))))))
(defconst *fn-bpsdw-bcb-wire*
 '(129 1 2 1 130 1 0 129 130 1 76 0 1 2 3 4 5 6 7 8 9 10 11 129 128))
(defconst *fn-bpsdw-bcb*
 (fn-bps-asb-make 12 '(1) 2 1 '(:dtn-none)
   (list (list 1 (cons :bytes '(0 1 2 3 4 5 6 7 8 9 10 11)))) '(nil)))
(defconst *fn-bpsdw-tag-wire*
 (append '(129 1 2 1 130 1 0 129 130 1 76 0 1 2 3 4 5 6 7 8 9 10 11 129 129 130 1 80)
         (make-list 16 :initial-element 90)))
(defconst *fn-bpsdw-tag*
 (fn-bps-asb-make 12 '(1) 2 1 '(:dtn-none)
   (list (list 1 (cons :bytes '(0 1 2 3 4 5 6 7 8 9 10 11))))
   (list (list (list 1 (cons :bytes (make-list 16 :initial-element 90)))))))

(defun fn-bpsdw-run (cursor remaining first-left pause quantum fuel original kind)
 (declare (xargs :guard (and (true-listp remaining) (true-listp original)) :measure (nfix fuel)
  :hints (("Goal" :in-theory (disable fn-bps-asb-step fn-bps-field fn-bps-get)))
  :guard-hints (("Goal" :in-theory (disable fn-bps-asb-step fn-bps-field fn-bps-get)))))
 (if (zp (nfix fuel)) (list :test-fuel cursor remaining)
  (let* ((width (if pause (min 64 (min (nfix first-left) (len remaining))) (min 64 (len remaining))))
         (window (take width remaining))
         (step (fn-bps-asb-step cursor (fn-bps-window-make :differential (fn-bps-get :offset cursor) window) quantum))
         (status (fn-bps-field 0 step)) (next (fn-bps-field 2 step))
         (consumed (nfix (fn-bps-field 3 step))) (rest (nthcdr consumed remaining)))
   (if (not (and (<= consumed width) (<= consumed (nfix quantum))
                 (equal (fn-bps-field 4 step) (nthcdr consumed window))
                 (equal (fn-bps-get :offset next) (+ (nfix (fn-bps-get :offset cursor)) consumed))))
       (list :broken-boundary step)
    (if (member-equal status '(:more :need-input))
       (if (and (eq status :need-input) (null rest)) (list :missing-physical-input next)
        (fn-bpsdw-run next rest (nfix (- (nfix first-left) consumed))
          (and pause (not (eq status :need-input))) quantum (1- (nfix fuel)) original kind))
     (list
      (cond ((eq status :parsed)
             (list :parsed (fn-bps-asb-span-alpha (fn-bps-asb-span-result next)
                              (list (cons :differential original)))))
            ((eq status :unsupported) (list :unsupported (list (fn-bps-field 1 step) (list :raw-asb kind original))))
            ((eq status :refused) (list :refused (fn-bps-field 1 step) (fn-bps-get :offset next)))
            (t (list :unexpected-status status)))
      (fn-bps-get :offset next) rest))))))

(defun fn-bpsdw-at-cut (kind wire expected cut quantum)
 (declare (xargs :guard (true-listp wire)))
 (let* ((start (fn-bps-asb-start kind :differential 0 (len wire) *fn-bpsdw-limits*))
        (run (fn-bpsdw-run start wire cut t quantum 4096 wire kind)))
   (and (equal (fn-bps-field 0 run) expected)
        (natp (fn-bps-field 1 run)) (<= (fn-bps-field 1 run) (len wire))
        (equal (fn-bps-field 2 run) (nthcdr (fn-bps-field 1 run) wire))
        (implies (eq (fn-bps-field 0 expected) :parsed)
                 (and (equal (fn-bps-field 1 run) (len wire)) (null (fn-bps-field 2 run)))))))

(defun fn-bpsdw-all-cuts (kind wire expected cut)
 (declare (xargs :guard (true-listp wire) :measure (nfix cut)
  :hints (("Goal" :in-theory (disable fn-bpsdw-at-cut)))
  :guard-hints (("Goal" :in-theory (disable fn-bpsdw-at-cut)))))
 (and (fn-bpsdw-at-cut kind wire expected (nfix cut) 1)
      (fn-bpsdw-at-cut kind wire expected (nfix cut) 7)
      (fn-bpsdw-at-cut kind wire expected (nfix cut) 64)
      (if (zp (nfix cut)) t (fn-bpsdw-all-cuts kind wire expected (1- (nfix cut))))))

(assert-event
 (and (eq (symbol-class 'fn-bpsdw-run (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bpsdw-at-cut (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bpsdw-all-cuts (w state)) :common-lisp-compliant)))
; Independent literal semantic anchors, then compare every cut/quantum with
; those anchors and the frozen whole-input reference. No encoder oracle.
(assert-event (and (equal (fn-bps-asb-decode 11 *fn-bpsdw-bib-wire* *fn-bpsdw-limits*) (list :parsed *fn-bpsdw-bib*))
                   (fn-bpsdw-all-cuts 11 *fn-bpsdw-bib-wire* (list :parsed *fn-bpsdw-bib*) (len *fn-bpsdw-bib-wire*))))
(assert-event (and (equal (fn-bps-asb-decode 12 *fn-bpsdw-bcb-wire* *fn-bpsdw-limits*) (list :parsed *fn-bpsdw-bcb*))
                   (fn-bpsdw-all-cuts 12 *fn-bpsdw-bcb-wire* (list :parsed *fn-bpsdw-bcb*) (len *fn-bpsdw-bcb-wire*))))
(assert-event (and (equal (fn-bps-asb-decode 12 *fn-bpsdw-tag-wire* *fn-bpsdw-limits*) (list :parsed *fn-bpsdw-tag*))
                   (fn-bpsdw-all-cuts 12 *fn-bpsdw-tag-wire* (list :parsed *fn-bpsdw-tag*) (len *fn-bpsdw-tag-wire*))))
(assert-event (and (equal (fn-bps-asb-decode 11 '(130 1 1) *fn-bpsdw-limits*) '(:refused :duplicate-target 3))
                   (fn-bpsdw-all-cuts 11 '(130 1 1) '(:refused :duplicate-target 3) (len '(130 1 1)))))
(assert-event (and (equal (fn-bps-asb-decode 11 '(129 64) *fn-bpsdw-limits*) '(:refused :target-type 2))
                   (fn-bpsdw-all-cuts 11 '(129 64) '(:refused :target-type 2) (len '(129 64)))))
(assert-event (and (equal (fn-bps-asb-decode 11 '(129 1 99) *fn-bpsdw-limits*) (list :unsupported (list :context-type (list :raw-asb 11 '(129 1 99)))))
                   (fn-bpsdw-all-cuts 11 '(129 1 99) (list :unsupported (list :context-type (list :raw-asb 11 '(129 1 99)))) (len '(129 1 99)))))
(assert-event (and (equal (fn-bps-asb-decode 11 (append *fn-bpsdw-bib-wire* '(0)) *fn-bpsdw-limits*) '(:refused :trailing-data 125))
                   (fn-bpsdw-all-cuts 11 (append *fn-bpsdw-bib-wire* '(0)) '(:refused :trailing-data 125) (len (append *fn-bpsdw-bib-wire* '(0))))))
(assert-event (and (equal (fn-bps-asb-decode 11 (take 124 *fn-bpsdw-bib-wire*) *fn-bpsdw-limits*) '(:refused :truncated 77))
                   (fn-bpsdw-all-cuts 11 (take 124 *fn-bpsdw-bib-wire*) '(:refused :truncated 77) (len (take 124 *fn-bpsdw-bib-wire*)))))
; Explicit zero quantum cannot consume bytes or alter the cursor; later
; bounded actual windows still reconstruct the same complete ASB.
(assert-event
 (let* ((start (fn-bps-asb-start 12 :differential 0 (len *fn-bpsdw-tag-wire*) *fn-bpsdw-limits*))
        (zero (fn-bps-asb-step start (fn-bps-window-make :differential 0 (take 16 *fn-bpsdw-tag-wire*)) 0)))
  (and (eq (fn-bps-field 0 zero) :more) (equal (fn-bps-field 2 zero) start)
       (equal (fn-bps-field 3 zero) 0) (equal (fn-bps-field 4 zero) (take 16 *fn-bpsdw-tag-wire*))
       (fn-bpsdw-all-cuts 12 *fn-bpsdw-tag-wire* (list :parsed *fn-bpsdw-tag*) (len *fn-bpsdw-tag-wire*)))))

; Unsigned context99 is encoded with major0 argument24,99. The one-byte
; octet99 above is major3 and correctly remains a distinct context-type.
(assert-event
 (let ((wire '(129 1 24 99))
       (expected '(:unsupported (:security-context (:raw-asb 11 (129 1 24 99))))))
  (and (equal (fn-bps-asb-decode 11 wire *fn-bpsdw-limits*) expected)
       (fn-bpsdw-all-cuts 11 wire expected (len wire)))))
; Provider-relation omission witness. The same ID/offset and a single changed
; body octet are accepted structurally. Alpha against the claimed old backing
; conceals the changed octet; alpha against actual input exposes it. This is
; not a verifier failure: the mandatory genuine slice relation is absent.
(assert-event
 (let* ((changed (append (take 124 *fn-bpsdw-bib-wire*) '(67)))
        (start (fn-bps-asb-start 11 :differential 0 125 *fn-bpsdw-limits*))
        (step (fn-bps-asb-step start (fn-bps-window-make :differential 0 changed) 4096))
        (span (fn-bps-asb-span-result (fn-bps-field 2 step))))
  (and (equal (len changed) (len *fn-bpsdw-bib-wire*))
       (not (equal changed *fn-bpsdw-bib-wire*)) (eq (fn-bps-field 0 step) :parsed)
       (equal (fn-bps-asb-span-alpha span (list (cons :differential *fn-bpsdw-bib-wire*))) *fn-bpsdw-bib*)
       (not (equal (fn-bps-asb-span-alpha span (list (cons :differential changed))) *fn-bpsdw-bib*)))))
