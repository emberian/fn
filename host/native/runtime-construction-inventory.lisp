;;; Isolated image builder only. No runtime census or admission entry.
(in-package "ACL2")

(defstruct (fnn-runtime-construction-inventory
             (:constructor %fnn-runtime-construction-inventory
                 (pool image recipe))
             (:copier nil))
  (pool nil :read-only t) (image nil :read-only t)
  (recipe nil :read-only t)
  objects sizes primary constructor-primary native-octets resident sealed)

(defun fnn-runtime-construction-inventory-observe (inventory)
  "Shallow observations only; ACL2 computes every resource total."
  (let ((objects (fnn-runtime-construction-inventory-objects inventory))
        (sizes (fnn-runtime-construction-inventory-sizes inventory)))
    (dotimes (i (length objects))
      (setf (svref sizes i)
            (sb-ext:primitive-object-size (svref objects i))))
    (fnn-core 'fn-runtime-construction-inventory
              (coerce sizes 'list)
              (fnn-runtime-construction-inventory-constructor-primary inventory)
              (fnn-runtime-construction-inventory-native-octets inventory)
              most-positive-fixnum)))

(defun fnn-runtime-construction-inventory-prepare
    (pool image recipe owned constructor-primary native-octets)
  "OWNED is the finite actual constructor recipe, never a transitive heap walk.
This private builder helper does not establish completeness of that recipe.
The caller must include its source-descriptor cells and all owned backings.
Shared code/symbols are in the declared image boundary, not entries of OWNED."
  (unless (and pool image (compiled-function-p recipe) (simple-vector-p owned))
    (error "runtime-construction-inventory-source"))
  (let* ((inventory (%fnn-runtime-construction-inventory pool image recipe))
         ;; EQ deduplication is build-time object identity, not a logical
         ;; resource decision. No referenced subobjects are silently followed.
         (roots (remove-duplicates (coerce owned 'list) :test #'eq))
         (objects (make-array (+ 3 (length roots)) :initial-element nil))
         (sizes (make-array (length objects) :initial-element 0)))
    (unless (every (lambda (x) (or (consp x) (arrayp x)
                                  (typep x 'structure-object))) roots)
      (error "runtime-construction-inventory-object"))
    ;; Include the observer's own retained storage before any observation.
    ;; Self references are harmless: primitive-object-size is shallow.
    (setf (svref objects 0) inventory
          (svref objects 1) objects
          (svref objects 2) sizes)
    (loop for object in roots for i from 3 do (setf (svref objects i) object))
    (setf (fnn-runtime-construction-inventory-objects inventory) objects
          (fnn-runtime-construction-inventory-sizes inventory) sizes
          (fnn-runtime-construction-inventory-constructor-primary inventory)
          constructor-primary
          (fnn-runtime-construction-inventory-native-octets inventory)
          native-octets)
    (let ((answer (fnn-runtime-construction-inventory-observe inventory)))
      (unless (eq (first answer) :inventory-observed)
        (error "runtime-construction-inventory-domain"))
      (setf (fnn-runtime-construction-inventory-primary inventory) (second answer)
            (fnn-runtime-construction-inventory-resident inventory) (fifth answer)))
    inventory))

(defun fnn-runtime-construction-inventory-replace (inventory old replacement)
  "Replace a descriptor prototype with the actual final constructor object.
Only equal shallow layouts may replace it; sealing rechecks the entire cohort."
  (when (fnn-runtime-construction-inventory-sealed inventory)
    (error "runtime-construction-inventory-sealed"))
  (let* ((objects (fnn-runtime-construction-inventory-objects inventory))
         (i (position old objects :test #'eq)))
    (unless (and i (>= i 3)
                 (not (find replacement objects :test #'eq))
                 (equal (type-of old) (type-of replacement))
                 (= (sb-ext:primitive-object-size replacement)
                    (svref (fnn-runtime-construction-inventory-sizes inventory) i)))
      (error "runtime-construction-inventory-replacement"))
    (setf (svref objects i) replacement))
  inventory)

(defun fnn-runtime-construction-inventory-seal (inventory)
  "Call after final source descriptor replacement, before saving the image.
The recipe owner must separately validate SAME roots and source identities."
  (when (fnn-runtime-construction-inventory-sealed inventory)
    (error "runtime-construction-inventory-sealed"))
  (let ((objects (fnn-runtime-construction-inventory-objects inventory))
        (sizes (fnn-runtime-construction-inventory-sizes inventory)))
    (dotimes (i (length objects))
      (unless (= (svref sizes i) (sb-ext:primitive-object-size (svref objects i)))
        (error "runtime-construction-inventory-layout-changed"))))
  (let ((answer (fnn-runtime-construction-inventory-observe inventory)))
    (unless (and (eq (first answer) :inventory-observed)
                 (eql (second answer)
                      (fnn-runtime-construction-inventory-primary inventory))
                 (eql (fifth answer)
                      (fnn-runtime-construction-inventory-resident inventory)))
      (error "runtime-construction-inventory-total-changed")))
  (setf (fnn-runtime-construction-inventory-sealed inventory) t)
  inventory)
