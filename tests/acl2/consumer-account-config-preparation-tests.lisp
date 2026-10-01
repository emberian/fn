(in-package "ACL2")
(include-book "../../books/consumer-account-config-preparation")

; Test-only scheduling and canonical abstraction; never a served mapper.
(defun fn-bcpt-complete (s fuel)
 (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
 (if (zp fuel) '(:refused :test-fuel)
  (let* ((cursor (fn-cp-nth 11 s))
         (one (fn-bcp-tick s (fn-scs-summary (if (consp cursor) (car cursor) nil)))))
   (if (eq (fn-cp-nth 0 one) :yield)
       (fn-bcpt-complete (fn-cp-nth 1 one) (1- fuel)) one))))
(defconst *bcpt-old* (make-list 32 :initial-element 4))
(defconst *bcpt-new* (make-list 32 :initial-element 9))
(defconst *bcpt-redeemed* (fn-cfg-row-make "receipt" "c" "verifier" 1))
(defconst *bcpt-accounts*
 (list (fn-bcp-binding-row '(97) *bcpt-old*) *bcpt-redeemed*
       (fn-bcp-binding-row '(98) *bcpt-old*)
       (fn-bcp-binding-row '(99) *bcpt-old*)
       (fn-bcp-binding-row '(100) *bcpt-old*)))
(defconst *bcpt-base*
 (fn-cfg-make 7 (fn-cfg-value-make nil 8 nil nil nil nil nil nil nil *bcpt-accounts*)))
(defun fn-bcpt-event (name origin mode principal sequence)
 (declare (xargs :guard t))
 (list :consumer-authority sequence (1+ (nfix sequence)) 0
       (fn-cab-operation '(65) 3 name origin mode principal)))
(defun fn-bcpt-stage (s name kind origin mode principal sequence)
 (declare (xargs :guard t))
 (let ((expected (fn-bcp-expect s name kind)))
  (if (eq (fn-cp-nth 0 expected) :ok)
      (fn-bcp-stage (fn-cp-nth 1 expected) (fn-bcpt-event name origin mode principal sequence))
    expected)))
(defconst *bcpt-start* (fn-bcp-begin '(65) *bcpt-base* 3))
(defconst *bcpt-a* (fn-cp-nth 1 (fn-bcpt-stage *bcpt-start* '(97) :row 0 1 *fn-cab-zero-principal* 1)))
(defconst *bcpt-b* (fn-cp-nth 1 (fn-bcpt-stage *bcpt-a* '(98) :row 0 2 *bcpt-new* 3)))
(defconst *bcpt-c* (fn-cp-nth 1 (fn-bcpt-stage *bcpt-b* '(99) :row 1 0 *fn-cab-zero-principal* 5)))
(defconst *bcpt-d* (fn-cp-nth 1 (fn-bcpt-stage *bcpt-c* '(100) :tombstone 2 1 *fn-cab-zero-principal* 7)))
(defconst *bcpt-ready*
 (fn-cp-nth 1 (fn-bcpt-complete (fn-cp-nth 1 (fn-bcp-seal *bcpt-d*)) 40)))
;@mutation-witness actual-static-redeemed-tombstone-config-preparation
(assert-event
 (let ((one (fn-bcp-prepared *bcpt-ready* 8)))
  (and (eq (fn-cp-nth 0 one) :ok)
       (equal (fn-cfg-generation (fn-cp-nth 1 one)) 8)
       (equal (fn-cfg-accounts (fn-cfg-value (fn-cp-nth 1 one)))
              (list *bcpt-redeemed* (fn-bcp-binding-row '(99) *bcpt-old*)
                    (fn-bcp-binding-row '(98) *bcpt-new*)))
       (equal (fn-cp-nth 2 *bcpt-ready*) *bcpt-base*))))
;@mutation-witness actual-config-accounts-samepass-carry
(assert-event
 (let ((one (fn-bcp-prepared *bcpt-ready* 8)))
  (equal (fn-caac-list-carry (fn-cp-nth 2 one))
         (fn-scs-summary (fn-cfg-accounts (fn-cfg-value (fn-cp-nth 1 one)))))))
;@mutation-witness actual-binding-stage-missing-duplicate-reordered-refusal
(assert-event
 (let ((await (fn-cp-nth 1 (fn-bcp-expect *bcpt-start* '(97) :row))))
  (and (equal (fn-bcp-seal await) '(:refused :binding-stage-missing))
       (equal (fn-bcp-expect await '(98) :row) '(:refused :binding-row-order))
       (equal (fn-bcp-stage await (fn-bcpt-event '(98) 0 1 *fn-cab-zero-principal* 1))
              '(:refused :binding-stage))
       (equal (fn-bcp-stage *bcpt-a* (fn-bcpt-event '(97) 0 1 *fn-cab-zero-principal* 1))
              '(:refused :binding-stage))
       (equal (fn-bcp-prepared *bcpt-d* 8) '(:refused :configuration-not-prepared)))))
;@mutation-witness actual-tombstone-provenance-must-delete-binding
(assert-event
 (let ((await (fn-cp-nth 1 (fn-bcp-expect *bcpt-start* '(97) :tombstone))))
  (and (equal (fn-bcp-stage await (fn-bcpt-event '(97) 0 2 *bcpt-new* 1))
              '(:refused :binding-stage))
       (equal (fn-bcp-stage await (fn-bcpt-event '(97) 1 0 *fn-cab-zero-principal* 1))
              '(:refused :binding-stage)))))

; A stored CFG name outside the actual authority login domain is retained,
; rather than truncated, refused, or coerced into a large temporary octet list.
;@mutation-witness long-stored-config-name-preserved-during-bounded-intent-lookup
(assert-event
 (let* ((name (coerce (make-list 4096 :initial-element #\a) 'string))
        (row (fn-cfg-row-make name "principal" "" 2))
        (s (fn-bcp-state '(65) *bcpt-base* 3 :scan nil nil
                         (fn-cp-nth 7 *bcpt-d*) (fn-cp-nth 8 *bcpt-d*)
                         nil nil (list row) nil nil nil nil))
        (one (fn-bcp-tick s (fn-scs-summary row))))
  (and (equal (fn-cp-nth 0 one) :yield)
       (null (fn-cp-nth 11 (fn-cp-nth 1 one)))
       (equal (fn-cp-nth 12 (fn-cp-nth 1 one)) (list row)))))
