(in-package "ACL2")
(include-book "../../books/consumer-remote-buffer")
(include-book "consumer-remote-ingress-tests")

(defun fn-crbt-fields-run (fuel answer fn-octets)
 (declare (xargs :stobjs fn-octets :guard (natp fuel) :measure (nfix fuel)))
 (if (or (zp fuel) (not (eq (fn-cp-nth 0 answer) :yield))) answer
  (fn-crbt-fields-run (1- fuel) (fn-crb-fields-tick (fn-cp-nth 1 answer) fn-octets) fn-octets)))

(defun fn-crbt-groups-run (fuel answer source fn-octets)
 (declare (xargs :stobjs fn-octets :guard (natp fuel) :measure (nfix fuel)))
 (if (or (zp fuel) (not (eq (fn-cp-nth 0 answer) :yield))) answer
  (fn-crbt-groups-run (1- fuel) (fn-crb-groups-tick (fn-cp-nth 1 answer) source fn-octets)
                     source fn-octets)))

(defconst *crbt-digest* (make-list 32 :initial-element 7))
(defconst *crbt-request* (fn-crit-request :register '(97) '(99) '((97) (98)) nil 0))
; Explicit digest: integrity's abstract model has no crypto content claim.
(defconst *crbt-payload* (fn-frame-fields-octets (fn-cr-spec 3)
 (list :register '(97) *crat-secret* '(99) '(2 65 97 65 98) '(0) 0)))
(defconst *crbt-frame* (append (fn-frame-protected *fn-cr-magic* 1 1 *crbt-payload*) *crbt-digest*))

;@positive fn-crb-open-with-is-fncr-frame-reference
(assert-event
 (let* ((fn-octets (fn-octets-clear fn-octets))
        (fn-octets (fn-octets-append-list *crbt-frame* fn-octets))
        (opened (fn-crb-open-with *crbt-digest* 3 fn-octets))
        (fields (fn-crbt-fields-run 8 opened fn-octets))
        (request (fn-cp-nth 1 fields))
        (start (fn-crb-groups-begin request '(:retained-fixture-frame) 3 fn-octets))
        (one (fn-crbt-groups-run 1 start '(:retained-fixture-frame) fn-octets))
        (end (fn-crbt-groups-run 8 one '(:retained-fixture-frame) fn-octets)))
  (mv (and (fn-octets-p fn-octets)
           (equal opened (fn-crb-frame-reference *crbt-digest* 3 *crbt-frame*))
           (eq (car fields) :located) (eq (car one) :yield)
           (equal (fn-cp-nth 5 (fn-cp-nth 1 one)) 1)
           (eq (car end) :groups-ready) (equal (fn-cp-nth 2 end) '((98) (97)))
           (equal (fn-crb-groups-tick (fn-cp-nth 1 start) '(:other-source) fn-octets)
                  '(:refused :frame-source-changed))) fn-octets))
 :stobjs-out '(nil fn-octets))

;@hypothesis-removal fn-crb-open-with-is-fncr-frame-reference buffer-invariant
; Corrupted-value witness; no live concrete octet buffer contains 300.
(defconst *crbt-bad* (append '(70 78 67 82 1 1 0 0 0 1 300) *crbt-digest*))
(defthm fn-crbt-open-invariant-removal-witness
 (and (not (fn-octets-p *crbt-bad*))
      (not (equal (fn-crb-open-with *crbt-digest* 3 *crbt-bad*)
                  (fn-crb-frame-reference *crbt-digest* 3 *crbt-bad*))))
 :rule-classes nil)

; A supported count beyond the historical article-grammar limit is retained,
; not rejected or eagerly expanded. Truncation remains a later query refusal.
(assert-event
 (let* ((fn-octets (fn-octets-clear fn-octets))
        (fn-octets (fn-octets-append-list '(26 0 1 0 0 65 97) fn-octets))
        (request (list :remote-consumer :register '(97) *crat-secret* '(99)
                       '(:remote-group-window 0 7) nil 0))
        (start (fn-crb-groups-begin request '(:retained-fixture-frame) 65536 fn-octets))
        (one (fn-crbt-groups-run 1 start '(:retained-fixture-frame) fn-octets)))
  (mv (and (eq (car start) :yield) (equal (fn-cp-nth 5 (fn-cp-nth 1 start)) 65536)
           (eq (car one) :yield) (equal (fn-cp-nth 5 (fn-cp-nth 1 one)) 65535)
           (equal (fn-crbt-groups-run 2 one '(:retained-fixture-frame) fn-octets)
                  '(:refused :query))) fn-octets))
 :stobjs-out '(nil fn-octets))
