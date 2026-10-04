;;; Internal preallocated filesystem observation primitive. No served caller
;;; selects it yet. A genuine installer owns constructor costs, native storage,
;;; source/runtime association and subsequent request/turn admission.
(in-package "ACL2")

(defstruct (fnn-fs-observation
            (:constructor %make-fnn-fs-observation) (:copier nil))
  path-storage word-storage path-sap word-sap
  (status :unobserved) (code 0 :type fixnum))

(sb-alien:define-alien-routine
    ("fn_fs_space_observe" fnn-%fs-space-observe) sb-alien:int
  (path sb-sys:system-area-pointer) (words sb-sys:system-area-pointer))

(defun fnn-fs-observation-make (path-octets)
  "Installation only: copy an already encoded, singly NUL-terminated path.
No finalizer is installed. The owner retains this carrier and releases its
native storage only after every issued I/O has definitely joined."
  (check-type path-octets (simple-array (unsigned-byte 8) (*)))
  (assert (and (plusp (length path-octets))
               (zerop (aref path-octets (1- (length path-octets))))
               (not (position 0 path-octets :end (1- (length path-octets))))))
  (let ((path nil) (words nil) (retained nil))
    (unwind-protect
        (progn
          (setf path (sb-alien:make-alien (sb-alien:unsigned 8) (length path-octets))
                words (sb-alien:make-alien (sb-alien:unsigned 32) 4))
          (dotimes (i (length path-octets))
            (setf (sb-alien:deref path i) (aref path-octets i)))
          (dotimes (i 4) (setf (sb-alien:deref words i) 0))
          (multiple-value-prog1
              (%make-fnn-fs-observation
               :path-storage path :word-storage words
               :path-sap (sb-alien:alien-sap path) :word-sap (sb-alien:alien-sap words))
            (setf retained t)))
      (unless retained
        (when words (sb-alien:free-alien words))
        (when path (sb-alien:free-alien path))))))

(defun fnn-fs-observe-into (observation)
  "Only raw observation: no path conversion, native allocation or byte product.
Caller has exclusive issued ownership of this preallocated carrier. This
function does not release a turn, establish I/O custody or authorize resume."
  (declare (type fnn-fs-observation observation))
  (setf (fnn-fs-observation-status observation) :uncertain)
  (setf (fnn-fs-observation-code observation)
        (fnn-%fs-space-observe (fnn-fs-observation-path-sap observation)
                              (fnn-fs-observation-word-sap observation)))
  (setf (fnn-fs-observation-status observation) :returned))

(defun fnn-fs-observation-readout (observation)
  "Separately admitted completion reads status, return code and four raw u32s.
ACL2 must judge availability and compose the u64 fields and byte product.
The words are not evidence when the status/code do not report success."
  (declare (type fnn-fs-observation observation))
  (let ((sap (fnn-fs-observation-word-sap observation)))
    (values (fnn-fs-observation-status observation)
            (fnn-fs-observation-code observation)
            (sb-sys:sap-ref-32 sap 0) (sb-sys:sap-ref-32 sap 4)
            (sb-sys:sap-ref-32 sap 8) (sb-sys:sap-ref-32 sap 12))))

(defun fnn-fs-observation-release (observation)
  "Installation teardown only, after definite I/O join. Never a finalizer."
  (declare (type fnn-fs-observation observation))
  (let ((words (fnn-fs-observation-word-storage observation))
        (path (fnn-fs-observation-path-storage observation)))
    (setf (fnn-fs-observation-status observation) :released
          (fnn-fs-observation-word-storage observation) nil
          (fnn-fs-observation-path-storage observation) nil
          (fnn-fs-observation-word-sap observation) nil
          (fnn-fs-observation-path-sap observation) nil)
    (unwind-protect (when words (sb-alien:free-alien words))
      (when path (sb-alien:free-alien path)))))
