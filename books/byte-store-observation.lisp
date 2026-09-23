(in-package "ACL2")
(include-book "byte-store")

; A physical directory walk cannot report the kernel's orphaned inodes or
; preserve its inode numbers across machines.  This projection retains every
; visible name, file octet and directory alias in the Store's three served
; directories.  It is deliberately narrower than fn-bs-crash-imagep.
(defun fn-bso-entry (s dir name)
  (declare (xargs :guard t :verify-guards nil))
  (let ((value (fn-bs-lookup s dir name)))
    (cond ((fn-bs-inop value)
           (list :file (fn-bs-content s value)))
          ((fn-bs-dir-idp value) (list :directory value))
          (t nil))))

(defun fn-bso-names-agree (names left right dir)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom names)
      t
    (and (member-equal (car names) (fn-bs-names right dir))
         (equal (fn-bso-entry left dir (car names))
                (fn-bso-entry right dir (car names)))
         (fn-bso-names-agree (cdr names) left right dir))))

(defun fn-bso-directory-agree (left right dir)
  (declare (xargs :guard t :verify-guards nil))
  (let ((lnames (fn-bs-names left dir))
        (rnames (fn-bs-names right dir)))
    (and (equal (len lnames) (len rnames))
         (fn-bso-names-agree lnames left right dir))))

(defun fn-bso-locations (s dir)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom (fn-bs-names s dir)) nil
    (pairlis$ (make-list (len (fn-bs-names s dir)) :initial-element dir)
              (fn-bs-names s dir))))

(defun fn-bso-location-inode (s location)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-lookup s (car location) (cdr location)))

(defun fn-bso-aliases-agree-with (location rest left right)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom rest) t
    (and (equal (equal (fn-bso-location-inode left location)
                       (fn-bso-location-inode left (car rest)))
                (equal (fn-bso-location-inode right location)
                       (fn-bso-location-inode right (car rest))))
         (fn-bso-aliases-agree-with location (cdr rest) left right))))

(defun fn-bso-aliases-agree (locations left right)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom locations) t
    (and (fn-bso-aliases-agree-with (car locations) (cdr locations) left right)
         (fn-bso-aliases-agree (cdr locations) left right))))

(defun fn-bso-served-image-agree (left right)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-bso-directory-agree left right :root)
       (fn-bso-directory-agree left right :transactions)
       (fn-bso-directory-agree left right :staging)
       (fn-bso-aliases-agree
        (append (fn-bso-locations left :root)
                (fn-bso-locations left :transactions)
                (fn-bso-locations left :staging)) left right)))
