(in-package "ACL2")
(include-book "../../books/consumer-entry-preparation-model")
(local (include-book "consumer-progress-metadata-tests"))

(defconst *cept-cp*
 (fn-cp-apply-trace (car *cpmm-seed*)
  '((:register (4) (8) (9) 0 0 1)
    (:register (3) (7) (9) 0 0 2)
    (:register (2) (6) (9) 0 0 3)
    (:register (1) (5) (9) 0 0 4))))
(defconst *cept-entries* (fn-cp-nth 5 *cept-cp*))
; The CP comes from four actual registration transitions. Annotation construction
; is a proof oracle in this test only; it is never a runtime bootstrap fallback.
(defconst *cept-meta* (fn-cpmm-annotation *cept-cp*))
(defconst *cept-start* (fn-cp-nth 1 (fn-cep-begin *cept-cp* '(:unregister (2) 3) *cept-meta*)))
(defun fn-cept-next (cursor)
 (declare (xargs :guard t))
 (fn-cp-nth 1 (fn-cep-tick cursor)))
(defun fn-cept-run (cursor fuel)
 (declare (xargs :guard (natp fuel) :verify-guards nil :measure (nfix fuel)))
 (if (zp fuel) cursor
   (if (eq (fn-cp-nth 6 cursor) :ready) cursor
     (fn-cept-run (fn-cept-next cursor) (1- fuel)))))

;@positive fn-cepm-begin-establishes-exact-selected-entry-and-removal
(assert-event
 (and (fn-cpm-metadatap *cept-meta*)
      (equal (fn-cepm-denotation *cept-start*)
             (list (fn-cp-remove '(2) *cept-entries*) (fn-cp-find '(2) *cept-entries*)))))
;@hypothesis-removal fn-cepm-begin-establishes-exact-selected-entry-and-removal metadata-five
(assert-event
 (and (not (fn-cpm-metadatap (fn-cpm-account4 *cept-meta*)))
      (not (equal (fn-cepm-denotation (fn-cp-nth 1 (fn-cep-begin *cept-cp*
                       '(:unregister (2) 3) (fn-cpm-account4 *cept-meta*))))
                  (list (fn-cp-remove '(2) *cept-entries*) (fn-cp-find '(2) *cept-entries*))))))
;@positive fn-cepm-actual-tick-preserves-selected-entry-and-removal
(assert-event
 (equal (fn-cepm-denotation (fn-cept-next *cept-start*)) (fn-cepm-denotation *cept-start*)))
;@positive fn-cepm-actual-tick-maintains-entry-annotations
(assert-event
 (and (fn-cepm-metadata-relp *cept-start*)
      (fn-cepm-metadata-relp (fn-cept-next *cept-start*))))
;@hypothesis-removal fn-cepm-actual-tick-maintains-entry-annotations metadata-relation
(assert-event
 (let ((bad (update-nth 3 (update-nth 1 '(999 nil nil) (fn-cp-nth 3 *cept-start*)) *cept-start*)))
  (and (not (fn-cepm-metadata-relp bad))
       (not (fn-cepm-metadata-relp (fn-cept-next bad))))))

;@mutation-witness fn-cep-one-inspection-per-tick
(assert-event
 (let ((one (fn-cep-tick *cept-start*)))
  (and (equal (car one) :yield)
       (equal (fn-cp-nth 2 (fn-cp-nth 1 one)) (cdr *cept-entries*))
       (equal (fn-cp-nth 4 (fn-cp-nth 1 one)) (list (car *cept-entries*)))
       (not (fn-cp-nth 9 (fn-cp-nth 1 one))))))
 ;@corrupted-state-witness fn-cep-selects-first-duplicate-only
(assert-event
 (let* ((entries (list (car *cept-entries*) (cadr *cept-entries*)
                       (fn-cp-entry '(2) '(99) '(9) 0 0 5 0) (cadddr *cept-entries*)))
        (cp (update-nth 5 entries *cept-cp*))
        (start (fn-cp-nth 1 (fn-cep-begin cp '(:unregister (2) 3) (fn-cpmm-annotation cp))))
        (hit (fn-cept-run start 2)) (done (fn-cept-run hit 2))
        (result (fn-cep-ready-result done)))
  (and (eq (fn-cp-nth 6 hit) :reverse)
       (equal (fn-cp-nth 9 hit) (cadr entries))
       (equal (car result) :ready)
       (equal (fn-cp-nth 1 result) (list (car entries) (caddr entries) (cadddr entries)))
       (equal (fn-cp-nth 2 result) (fn-caam-list-annotation (fn-cp-nth 1 result)))
       (equal (fn-cp-nth 3 result) (cadr entries))
       (equal (fn-cp-nth 4 result) (fn-scs-summary (cadr entries)))
       (fn-cepm-metadata-relp done))))
;@mutation-witness fn-cep-absent-key-preserves-table-and-carries
(assert-event
 (let* ((start (fn-cp-nth 1 (fn-cep-begin *cept-cp* '(:unregister (99) 2) *cept-meta*)))
        (done (fn-cept-run start 10)) (result (fn-cep-ready-result done)))
  (and (equal (car result) :ready)
       (equal (fn-cp-nth 1 result) *cept-entries*)
       (equal (fn-cp-nth 2 result) (fn-caam-list-annotation *cept-entries*))
       (not (fn-cp-nth 3 result)) (not (fn-cp-nth 4 result))
       (fn-cepm-metadata-relp done))))
;@mutation-witness fn-cep-actual-ack-key-is-cursor-consumer
(assert-event
 (equal (fn-cep-operation-key
          (list :ack (fn-cp-cursor '(10) '(11) '(2) '(6) '(9) 0 0 2 4))) '(2)))
;@mutation-witness fn-cep-incomplete-phase-never-publishes
(assert-event
 (and (equal (fn-cep-ready-result *cept-start*) '(:refused :consumer-preparation-incomplete))
      (equal (fn-cep-tick (update-nth 6 :bad *cept-start*)) '(:refused :consumer-preparation-phase))))
