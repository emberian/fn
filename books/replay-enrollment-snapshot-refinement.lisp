; Actual same-produced nested decode to the selected public enrollment value.
; Every helper here is ghost-only; the executable producer remains staged.
(in-package "ACL2")
(include-book "replay-enrollment-parser-refinement")
(include-book "statement-items-cursor-public")
(include-book "statement-items-cursor-terminal")
(include-book "hybrid-store")

(local (defthm fn-rse-stxe-encoder-is-public-statement-encoder
 (equal (fn-stxe-encode-items items) (fn-stmt-encode-items items))
 :hints (("Goal" :in-theory (enable fn-stxe-encode-items)))))

(defthm fn-rse-source-produced-fields-are-the-selected-subject
 (implies (and (fn-rse-result-spans result)
               (fn-sic-span-item-listp (fn-rsc-at 1 result) source)
               (fn-cbor-octet-listp source))
  (let ((value (fn-rse-enrollment-model (fn-rse-result-spans result))))
   (fn-hsig-subject-p (car value) (cadr value) nil)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-rse-selected-span-layout-and-widths-by-definition)
        (:instance fn-rse-selected-spans-retain-the-original-source)
        (:instance fn-rse-parser-byte-span-denotes-exact-octets
          (span (fn-rsc-at 0 (fn-rse-result-spans result))))
        (:instance fn-rse-parser-byte-span-denotes-exact-octets
          (span (fn-rsc-at 1 (fn-rse-result-spans result))))
        (:instance fn-rse-parser-byte-span-denotes-exact-octets
          (span (fn-rsc-at 2 (fn-rse-result-spans result)))))
  :in-theory
  (union-theories (theory 'minimal-theory)
   '((:definition fn-rse-enrollment-model)
     (:definition fn-rsc-at)
     (:definition fn-hsig-subject-p)
     (:definition fn-hsig-keyset-p)
     (:definition fn-hsig-exact-octets-p)
     (:definition fn-cbor-ag-car)
     (:definition fn-cbor-ag-cdr)
     (:definition len)
     (:definition true-listp)
     (:rewrite car-cons) (:rewrite cdr-cons) (:rewrite cons-equal)
     (:executable-counterpart binary-+) (:executable-counterpart <)
     (:executable-counterpart len) (:executable-counterpart true-listp)
     (:executable-counterpart fn-cbor-octet-listp))))))

; The actual admitted parser/public boundary supplies canonicality. No
; caller-provided equality decision, byte census or attachment is assumed.
(local (defthm fn-rse-paid-success-projects-the-same-public-items
 (let* ((begin (fn-sic-begin-legacy 5 octets))
        (parser (fn-sic-run (fn-sic-completion-cost begin) begin)))
  (implies (fn-stmt-okp (fn-sic-result parser))
   (and (fn-stmt-okp (fn-stmt-decode-items 5 octets))
    (equal (fn-stmt-value (fn-stmt-decode-items 5 octets))
           (fn-sic-items-abstract (fn-stmt-value (fn-sic-result parser)))))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-sic-paid-legacy-is-public-result (fuel 5)))
  :in-theory (e/d (fn-sic-result-abstract fn-stmt-okp fn-stmt-value fn-stmt-ok)
   (fn-sic-begin-legacy fn-sic-run fn-sic-result fn-sic-completion-cost
    fn-sic-complete fn-sic-completion-is-paid-run
    fn-sic-items-abstract fn-stmt-decode-items
    fn-sic-paid-legacy-is-public-result))))))
(local (defthm fn-rse-ok-list-projection
 (implies (equal result (fn-stmt-ok items))
  (and (consp result) (consp (cdr result))
       (equal (car result) :ok) (equal (cadr result) items)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-stmt-ok)))))
; Projection support avoids reopening the decoder or recursively rewriting
; its compound result while folding the literal selected public branch.
(local (defthm fn-rse-ok-five-items-projections
 (implies (equal result
                 (fn-stmt-ok (list a b c d e)))
  (and (consp result) (consp (cdr result))
       (equal (car result) :ok)
       (equal (len (cadr result)) 5)
       (equal (nth 0 (cadr result)) a)
       (equal (nth 1 (cadr result)) b)
       (equal (nth 2 (cadr result)) c)
       (equal (nth 3 (cadr result)) d)
       (equal (nth 4 (cadr result)) e)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-stmt-ok nth len)))))
(local (defthm fn-rse-public-selected-five-items-fold-to-subject
 (let* ((keys (list (cons :ed25519 ed) (cons :ml-dsa-65 ml)))
        (items (list (cons :bytes principal) (cons :uint 1)
                     (cons :bytes ed) (cons :uint 2) (cons :bytes ml))))
  (implies
   (and (fn-stxk-p snapshot)
        (equal (fn-stxk-profile snapshot) *fn-hsig-profile-tag*)
        (fn-hsig-subject-p principal keys nil)
        (equal (fn-stmt-decode-items 5 (fn-stxk-snapshot snapshot))
               (fn-stmt-ok items))
        (equal (fn-stxk-snapshot snapshot) (fn-stxe-encode-items items)))
   (equal (fn-hsig-keyring-snapshot-value snapshot) (list principal keys))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-rse-ok-five-items-projections
   (result (fn-stmt-decode-items 5 (fn-stxk-snapshot snapshot)))
   (a (cons :bytes principal)) (b (cons :uint 1))
   (c (cons :bytes ed)) (d (cons :uint 2)) (e (cons :bytes ml)))
   (:instance fn-rse-ok-list-projection
   (result (fn-stmt-decode-items 5 (fn-stxk-snapshot snapshot)))
   (items (list (cons :bytes principal) (cons :uint 1)
                (cons :bytes ed) (cons :uint 2) (cons :bytes ml)))))
  :in-theory
  (union-theories (theory 'minimal-theory)
   '((:definition fn-hsig-keyring-snapshot-value)
     (:definition fn-stmt-okp) (:definition fn-stmt-value)
     (:definition fn-stmt-bytes-item-p) (:definition fn-stmt-uint-item-p)
     (:definition fn-record-uint32p)
     (:definition fn-hsig-subject-p) (:definition fn-hsig-keyset-p)
     (:definition fn-hsig-exact-octets-p)
     (:definition fn-cbor-ag-car) (:definition fn-cbor-ag-cdr)
     (:definition len)
     (:rewrite car-cons) (:rewrite cdr-cons) (:rewrite cons-equal)
     (:executable-counterpart len)
     (:executable-counterpart fn-cbor-octet-listp)
     (:executable-counterpart fn-record-uint32p)))))))
(defthm fn-rse-paid-selected-enrollment-is-actual-public-value
 (let* ((snapshot-bytes (fn-stxk-snapshot snapshot))
        (begin (fn-sic-begin-legacy 5 snapshot-bytes))
        (parser (fn-sic-run (fn-sic-completion-cost begin) begin))
        (result (fn-sic-result parser))
        (spans (fn-rse-result-spans result)))
  (implies (and (fn-stxk-p snapshot) spans
                (equal (fn-stxk-profile snapshot) *fn-hsig-profile-tag*))
   (equal (fn-hsig-keyring-snapshot-value snapshot)
          (fn-rse-enrollment-model spans))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-rse-public-selected-five-items-fold-to-subject
          (principal (car (fn-rse-enrollment-model (fn-rse-result-spans (fn-sic-result (fn-sic-run (fn-sic-completion-cost (fn-sic-begin-legacy 5 (fn-stxk-snapshot snapshot))) (fn-sic-begin-legacy 5 (fn-stxk-snapshot snapshot))))))))
          (ed (cdr (car (cadr (fn-rse-enrollment-model (fn-rse-result-spans (fn-sic-result (fn-sic-run (fn-sic-completion-cost (fn-sic-begin-legacy 5 (fn-stxk-snapshot snapshot))) (fn-sic-begin-legacy 5 (fn-stxk-snapshot snapshot))))))))))
          (ml (cdr (cadr (cadr (fn-rse-enrollment-model (fn-rse-result-spans (fn-sic-result (fn-sic-run (fn-sic-completion-cost (fn-sic-begin-legacy 5 (fn-stxk-snapshot snapshot))) (fn-sic-begin-legacy 5 (fn-stxk-snapshot snapshot)))))))))))
        (:instance fn-rse-selected-parser-result-is-accepted-by-definition
          (result (fn-sic-result (fn-sic-run
           (fn-sic-completion-cost (fn-sic-begin-legacy 5 (fn-stxk-snapshot snapshot)))
           (fn-sic-begin-legacy 5 (fn-stxk-snapshot snapshot))))))
        (:instance fn-rse-paid-success-projects-the-same-public-items
          (octets (fn-stxk-snapshot snapshot)))
        (:instance fn-rse-selected-parser-items-have-exact-five-field-denotation
          (result (fn-sic-result (fn-sic-run
           (fn-sic-completion-cost (fn-sic-begin-legacy 5 (fn-stxk-snapshot snapshot)))
           (fn-sic-begin-legacy 5 (fn-stxk-snapshot snapshot))))))
        (:instance fn-rse-source-produced-fields-are-the-selected-subject
          (source (fn-stxk-snapshot snapshot))
          (result (fn-sic-result (fn-sic-run
           (fn-sic-completion-cost (fn-sic-begin-legacy 5 (fn-stxk-snapshot snapshot)))
           (fn-sic-begin-legacy 5 (fn-stxk-snapshot snapshot))))))
        (:instance fn-sic-paid-legacy-is-public-result
          (fuel 5) (octets (fn-stxk-snapshot snapshot)))
        (:instance fn-sic-paid-legacy-success-is-canonical
          (fuel 5) (octets (fn-stxk-snapshot snapshot)))
        (:instance fn-sic-paid-begin-completion-retains-source-spans
          (fuel 5) (octets (fn-stxk-snapshot snapshot))
          (outer-budget *fn-cbor-max-input*) (item-budget *fn-cbor-max-bytes*))
        (:instance fn-sic-paid-success-has-octet-source
          (fuel 5) (octets (fn-stxk-snapshot snapshot))
          (outer-budget *fn-cbor-max-input*) (item-budget *fn-cbor-max-bytes*)))
  :in-theory
  (union-theories (theory 'minimal-theory)
   '((:definition fn-sic-begin-legacy)
     (:definition fn-sic-result-abstract)
     (:definition fn-stmt-okp) (:definition fn-stmt-value)
     (:definition fn-stmt-ok)
     (:definition fn-stmt-bytes-item-p) (:definition fn-stmt-uint-item-p)
     (:definition fn-record-uint32p)
     (:definition fn-hsig-subject-p) (:definition fn-hsig-keyset-p)
     (:definition fn-hsig-exact-octets-p)
     (:definition fn-rse-enrollment-model)
     (:definition fn-cbor-ag-car) (:definition fn-cbor-ag-cdr)
     (:definition len) (:definition true-listp) (:definition natp)
     (:definition nth) (:definition fn-rsc-at)
     (:rewrite car-cons) (:rewrite cdr-cons) (:rewrite cons-equal)
     (:rewrite fn-rse-stxe-encoder-is-public-statement-encoder)
     (:executable-counterpart binary-+) (:executable-counterpart <)
     (:executable-counterpart len) (:executable-counterpart true-listp)
     (:executable-counterpart fn-cbor-octet-listp)
     (:executable-counterpart fn-sic-items-abstract)
     (:executable-counterpart fn-sic-item-abstract)
     (:executable-counterpart fn-rse-result-spans))))))

; The actual caller schedules the original parser one step at a time. It
; need not execute the ghost completion-cost function to consume this bridge.
(defthm fn-rse-scheduled-terminal-enrollment-is-actual-public-value
 (let* ((begin (fn-sic-begin-legacy 5 (fn-stxk-snapshot snapshot)))
        (parser (fn-sic-run q begin))
        (spans (fn-rse-result-spans (fn-sic-result parser))))
  (implies (and (natp q) (fn-stxk-p snapshot)
                (equal (fn-sic-at 0 parser) :done) spans
                (equal (fn-stxk-profile snapshot) *fn-hsig-profile-tag*))
   (equal (fn-hsig-keyring-snapshot-value snapshot)
          (fn-rse-enrollment-model spans))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-sic-terminal-begin-is-paid-completion
                    (fuel 5) (octets (fn-stxk-snapshot snapshot))
                    (outer-budget *fn-cbor-max-input*)
                    (item-budget *fn-cbor-max-bytes*))
        fn-rse-paid-selected-enrollment-is-actual-public-value)
  :in-theory (e/d (fn-sic-begin-legacy)
                  (fn-sic-run fn-sic-begin fn-sic-completion-cost fn-sic-at
                   fn-sic-result fn-rse-result-spans fn-rse-enrollment-model
                   fn-hsig-keyring-snapshot-value
                   fn-sic-terminal-begin-is-paid-completion)))))
