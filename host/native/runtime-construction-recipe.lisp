;;; Isolated image construction only. This literal roster is not a heap walk.
;;; It observes existing constructor objects; future ATS/DATA6 allocations are
;;; a separate compiled reserve. No quantity or resource grant is supplied here.
(in-package "ACL2")

(defun fnn-runtime-construction-owned-roots (source-owned)
  "Return actual objects owned by the selected saved bootstrap constructors.
SOURCE-OWNED explicitly names original compiled descriptor cells/backings.
Shared functions, symbols, literal names and runtime thread storage belong to
 the selected image/runtime boundary; this helper does not traverse them."
  (unless (simple-vector-p source-owned)
    (error "runtime-construction-descriptor-roster-unavailable"))
  (let* ((pool (fnn-live-page-read-pool))
         (bootstrap *fnn-runtime-bootstrap*)
         (participants cl-user::*fnn-runtime-participants*)
         (policy cl-user::*fnn-runtime-image-policy*)
         (profile *fnn-runtime-profile-envelope-binding*)
         (registry (user-stobj-alist *the-live-state*))
         (slots (fnn-runtime-bootstrap-live-slots)))
    (unless (and bootstrap participants policy profile
                 (fn-rbc-virgin-poolp pool)
                 (eq pool (fnn-runtime-bootstrap-pool bootstrap))
                 (eq participants (fnn-runtime-bootstrap-participants bootstrap))
                 (eq policy (fnn-runtime-bootstrap-image-policy bootstrap))
                 (eq profile (fnn-runtime-bootstrap-profile-envelope bootstrap))
                 (eq slots (fnn-runtime-bootstrap-slots bootstrap))
                 (eq pool (cdr (assoc 'fn-page-read-pool registry)))
                 (eq slots (cdr (assoc 'fn-allocation-turn-slots registry))))
      (error "runtime-construction-root-association-unavailable"))
    (multiple-value-bind (word same)
        (fnn-runtime-profile-envelope-live-binding pool policy)
      (unless (and (eq word :profile-envelope-available) (eq same profile))
        (error "runtime-construction-profile-association-unavailable")))
    ;; These are generated field indices from the actual exported DEFSTOBJ.
    ;; Never replace missing metadata with guessed offsets.
    (let ((owned (list pool bootstrap
                       (fnn-runtime-bootstrap-observation bootstrap)
                       participants
                       (cl-user::fnn-runtime-participants-lock participants)
                       (cl-user::fnn-runtime-participants-changed participants)
                       policy profile
                       (fnn-runtime-profile-envelope-binding-controller profile) slots
                       (svref slots *fn-ats-kindsi*)
                       (svref slots *fn-ats-noncesi*)
                       (svref slots *fn-ats-phasesi*)
                       (fnn-runtime-profile-envelope-binding-buffer profile)
                       (fnn-runtime-profile-envelope-binding-workspace profile))))
      ;; The registry constructor owns its list spine and association pairs.
      ;; Only these declared two levels are followed, never stobj fields.
      (loop for tail on registry do (push tail owned) (push (car tail) owned))
      ;; The core envelope and image-selected signal list are retained lists
      ;; whose literal constructors own each spine cell, with scalar elements.
      (loop for tail on (fnn-runtime-profile-envelope-binding-envelope profile)
            do (push tail owned))
      (loop for tail on cl-user::*fnn-runtime-bootstrap-ordinary-signals*
            do (push tail owned))
      (loop for object across source-owned do (push object owned))
      (coerce owned 'vector))))


(defvar *fnn-runtime-construction-inventory* nil)
(defun fnn-runtime-construction-image-capture (source-owned)
  "Capture actual existing roots after ImagePrepare. This stage cannot seal.
The compiled source recipe supplies SOURCE-OWNED explicitly; missing future
constructor/native projections remain unavailable in the returned inventory."
  (when *fnn-runtime-construction-inventory*
    (error "runtime-construction-image-capture-repeated"))
  (let* ((pool (fnn-live-page-read-pool))
         (policy cl-user::*fnn-runtime-image-policy*)
         (owned (fnn-runtime-construction-owned-roots source-owned)))
    (setf *fnn-runtime-construction-inventory*
          (fnn-runtime-construction-inventory-capture
            pool policy #'fnn-runtime-construction-owned-roots owned))))
