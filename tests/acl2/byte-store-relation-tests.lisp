; Executable K0 witnesses use the concrete metadata seam, not an invented
; logical interpretation.  Witnesses are functions because ACL2 ignores
; defattach while evaluating defconsts.
(in-package "ACL2")
(include-book "../../books/byte-store-relation")
(include-book "../../books/byte-store-frame")
(include-book "std/testing/must-fail" :dir :system)

(defun fn-bs-test-config () (fn-bs-initial-config-octets))
(defun fn-bs-test-frontier () (fn-bs-initial-frontier-octets))
(defun fn-bs-test-next () (fn-bs-frontier-encode-impl 1))
(defun fn-bs-test-initial (unit config frontier)
  (fn-bs-initial-image unit config frontier))
(defun fn-bs-test-frontier-run (unit config frontier stage next)
  (fn-bs-run (fn-bs-test-initial unit config frontier) (fn-sf-initial-state)
             (fn-bs-frontier-program stage next) nil nil nil))

(assert-event (posp 4))
(assert-event (fn-bs-initial-inputp (fn-bs-test-config) (fn-bs-test-frontier)))
(assert-event (fn-cbor-octet-listp (fn-bs-test-config)))
(assert-event (fn-cbor-octet-listp (fn-bs-test-frontier)))
(assert-event (fn-bs-config-okp (fn-bs-test-config)))
(assert-event (equal (fn-bs-frontier-decode (fn-bs-test-frontier)) 0))
(assert-event (fn-bs-frontier-inputp (fn-sf-initial-state) ".allocation-test"
                                    (fn-bs-test-next)))

; The successful initializer reaches its exact concrete representation,
; including unfenced staging cleanup; it establishes the relation.
(assert-event
 (let ((bs (car (car (last
             (fn-bs-run *fn-bs-empty-store* (fn-sf-initial-state)
                        (fn-bs-init-program (fn-bs-test-config)
                                             (fn-bs-test-frontier))
                        nil nil nil))))))
   (and (equal bs (fn-bs-initial-image 4 (fn-bs-test-config) (fn-bs-test-frontier)))
        (fn-bs-store-relation bs (fn-sf-initial-state))
        (fn-bs-authority-knownp bs)
        (not (fn-bs-dir-quietp bs :staging))
        (fn-bs-dir-quietp bs :root))))

; A real full allocation, with two distinct frontier byte strings and a
; nonempty staging namespace operation at the rename cut.
(assert-event
 (let ((run (fn-bs-test-frontier-run 4 (fn-bs-test-config) (fn-bs-test-frontier)
                                    ".allocation-test" (fn-bs-test-next))))
   (and (fn-bs-run-relatedp run)
        (equal (len run) (len (fn-bs-frontier-program ".allocation-test"
                                                    (fn-bs-test-next))))
        (equal (fn-sf-phase (cdr (car (last run)))) :reserved)
        (equal (fn-bs-durable-frontier (car (car (last run)))) 1))))

; Initialization keystone: without its initial-input boundary, the actual
; initializer finishes but cannot establish a valid configuration relation.
(must-fail
 (assert-event
  (fn-bs-store-relation
   (car (car (last (fn-bs-run *fn-bs-empty-store* (fn-sf-initial-state)
                              (fn-bs-init-program nil (fn-bs-test-frontier))
                              nil nil nil))))
   (fn-sf-initial-state))))

; Additional constructor/guard cases. With the concrete codec, malformed
; octets also fail metadata validation, so these are NOT claimed to isolate
; each conjunct of fn-bs-initial-inputp independently.
(must-fail
 (assert-event
  (fn-bs-store-relation (fn-bs-test-initial 0 (fn-bs-test-config) (fn-bs-test-frontier))
                       (fn-sf-initial-state))))
(must-fail
 (assert-event
  (fn-bs-store-relation (fn-bs-test-initial 4 '(256) (fn-bs-test-frontier))
                       (fn-sf-initial-state))))
(must-fail
 (assert-event
  (fn-bs-store-relation (fn-bs-test-initial 4 (fn-bs-test-config) '(256))
                       (fn-sf-initial-state))))
(must-fail
 (assert-event
  (fn-bs-store-relation (fn-bs-test-initial 4 nil (fn-bs-test-frontier))
                       (fn-sf-initial-state))))
(must-fail
 (assert-event
  (fn-bs-store-relation (fn-bs-test-initial 4 (fn-bs-test-config) (fn-bs-test-next))
                       (fn-sf-initial-state))))

; Every-pair preservation has three hypotheses: a positive write unit, the
; initial-input boundary, and the successor-input boundary. The unit=0,
; config=nil, and old-frontier-as-next cases below each drop exactly one.
; The remaining cases separately exercise malformed input guards.
(must-fail
 (assert-event
  (fn-bs-run-relatedp (fn-bs-test-frontier-run 0 (fn-bs-test-config)
                       (fn-bs-test-frontier) ".allocation-test" (fn-bs-test-next)))))
(must-fail
 (assert-event
  (fn-bs-run-relatedp (fn-bs-test-frontier-run 4 '(256)
                       (fn-bs-test-frontier) ".allocation-test" (fn-bs-test-next)))))
(must-fail
 (assert-event
  (fn-bs-run-relatedp (fn-bs-test-frontier-run 4 (fn-bs-test-config)
                       '(256) ".allocation-test" (fn-bs-test-next)))))
(must-fail
 (assert-event
  (fn-bs-run-relatedp (fn-bs-test-frontier-run 4 nil
                       (fn-bs-test-frontier) ".allocation-test" (fn-bs-test-next)))))
(must-fail
 (assert-event
  (fn-bs-run-relatedp (fn-bs-test-frontier-run 4 (fn-bs-test-config)
                       (fn-bs-test-next) ".allocation-test" (fn-bs-test-next)))))
(must-fail
 (assert-event
  (fn-bs-run-relatedp (fn-bs-test-frontier-run 4 (fn-bs-test-config)
                       (fn-bs-test-frontier) ".allocation-test" (fn-bs-test-frontier)))))

; The old K0 formula fails at an actual named host cut, after valid staging,
; although the program still completes. This separates the failed content
; contract from malformed state or a refused create.
(assert-event
 (equal (nth 9 (fn-bs-frontier-program ".allocation-test" (fn-bs-test-frontier)))
        '(:cut "frontier-replaced")))
(assert-event
 (let ((run (fn-bs-test-frontier-run 4 (fn-bs-test-config) (fn-bs-test-frontier)
                                    ".allocation-test" (fn-bs-test-frontier))))
   (and (fn-bs-run-relatedp (take 8 run))
        (not (fn-bs-store-relation (car (nth 9 run)) (cdr (nth 9 run))))
        (equal (fn-sf-phase (cdr (car (last run)))) :reserved))))

; The existential image recognizer is non-executable. This local constructor
; lemma connects the executable admissible-choice checks below to it.
(local
 (defthm fn-bs-test-legal-choice-constructs-admissible-image
   (implies (fn-bs-crash-choicesp choices (fn-bs-pending bs) (fn-bs-unit bs))
            (fn-bs-crash-imagep bs (fn-bs-crash bs choices)))
   :hints (("Goal" :use ((:instance fn-bs-crash-imagep-suff
                                    (s bs) (image (fn-bs-crash bs choices))))))))

; K1 gets its previously missing executable positive witness, with actual
; OLD and NEW byte crash images of the live rename window. Staging create
; and removal are independent crash choices and remain in the model.
(assert-event
 (let* ((run (fn-bs-test-frontier-run 4 (fn-bs-test-config) (fn-bs-test-frontier)
                                     ".allocation-test" (fn-bs-test-next)))
        (bs (car (nth 9 run)))
        (old (fn-bs-crash bs nil))
        (new (fn-bs-crash bs '(:drop :drop :drop :drop :drop :apply :drop))))
   (and (fn-bs-store-relation bs (cdr (nth 9 run)))
        (fn-bs-crash-choicesp nil (fn-bs-pending bs) (fn-bs-unit bs))
        (fn-bs-crash-choicesp '(:drop :drop :drop :drop :drop :apply :drop)
                              (fn-bs-pending bs) (fn-bs-unit bs))
        (fn-bs-scan-okp (fn-bs-scan-store old))
        (fn-bs-scan-okp (fn-bs-scan-store new))
        (equal (fn-bs-scan-frontier (fn-bs-scan-store old)) 0)
        (equal (fn-bs-scan-frontier (fn-bs-scan-store new)) 1)
        (not (equal old new)))))
