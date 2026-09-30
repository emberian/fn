;;; Selected SBCL collector observation primitive.  Not installed on a served
;;; path yet: the SAMEpool nonce-only core wrapper and process allocation
;;; barrier own authorization, validation, reset and resumption.
;;;
;;; This carrier is constructed during installation, never after exhausting
;;; admission capacity.  Association/epoch/nonce come from the actual core
;;; request; they are retained even if collection or observation escapes.
;;; Page high-water and page size are RAW runtime observations.  ACL2, not
;;; this file, converts them to an occupied-prefix bound and applies the
;;; installed allocator geometry, non-dynamic reserves and Qresume.
(in-package "ACL2")

(defstruct (fnn-runtime-collection
            (:constructor make-fnn-runtime-collection ())
            (:copier nil))
  association epoch nonce
  (status :unobserved)
  (dynamic-pages 0 :type (integer 0 *))
  (page-octets 0 :type (integer 0 *))
  (dynamic-reservation 0 :type (integer 0 *)))

(defun fnn-runtime-collect-into (observation)
  "Perform the selected full collector and overwrite a preallocated carrier.
Caller keeps allocation admission closed through the core's completion.
A nonlocal exit leaves :UNCERTAIN and the original request identity intact."
  (declare (type fnn-runtime-collection observation))
  ;; Publish uncertainty FIRST. Old numeric fields are not new evidence.
  (setf (fnn-runtime-collection-status observation) :uncertain)
  ;; SB-EXT:GC returns NIL both after completion and when collection is
  ;; inhibited. The selected SUB-GC primitive returns T only after it has
  ;; actually collected the requested generation. POST-GC is the other
  ;; operation performed by SB-EXT:GC; preserve it on successful completion.
  (cond
    ((eq t (sb-kernel::sub-gc sb-vm:+pseudo-static-generation+))
     (sb-kernel::post-gc)
     (setf (fnn-runtime-collection-dynamic-pages observation)
           (sb-alien:extern-alien "next_free_page" sb-alien:int)
           (fnn-runtime-collection-page-octets observation)
           sb-vm:gencgc-page-bytes
           (fnn-runtime-collection-dynamic-reservation observation)
           (sb-ext:dynamic-space-size))
     ;; Status is published only after every primitive observation returned.
     (setf (fnn-runtime-collection-status observation) :completed))
    (t (setf (fnn-runtime-collection-status observation) :deferred))))
