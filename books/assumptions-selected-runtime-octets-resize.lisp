; A-SELECTED-RUNTIME-OCTETS-RESIZE, PRF-1165: successful primary array request only.
(in-package "ACL2")
(defconst *fn-sror-coordinate*
 '(:sbcl "2.6.8" :x86-64-linux :saved-core-callback-policy
   :toolchain "fcedce7e3aa26e7ef93c7b3801bc39b2c56b7968cc1dfdf8e710a8931b349d52"
   :policy ((inhibit-warnings 3) (speed 3) (space 1) (safety 0) (debug 1) (compilation-speed 0))
   :foundation "3fbd390317fe7c3527add9c3d831ec967e8dccd3247142f2fa37fa29423697c4"
   :component "4f24f0402faf15375e4f80f8a79e10b5aae3c2ffb1349541da4ed96c8157a2fd"
   :genuine-simple-ub8 :installed-hons-association-nil :primary-success-object-only))
(defun fn-sror-primary-request (request)
 (declare (xargs :guard t))
 (cond ((equal request 64) 80) ((equal request 3494) 3520)
       ((equal request 65536) 65552) (t 0)))
(defun fn-sror-resize-domain-p (request old-capacity coordinate)
 (declare (xargs :guard t))
 (and (equal coordinate *fn-sror-coordinate*)
      (member-equal request '(64 3494 65536))
      (natp old-capacity) (< old-capacity request)))
; The coordinate qualifiers require installed backing/metadata facts; shape is
; no authority. This assumption excludes caller, error, memoization, collector,
; first-use and retained old/new array lifetime costs.
(encapsulate
 (((fn-assume-sror-success-object-octets * * *) => *))
 (local (defun fn-assume-sror-success-object-octets (request old coordinate)
          (declare (ignore request old coordinate)) 0))
 (defthm fn-assume-sror-success-object-natural
  (natp (fn-assume-sror-success-object-octets request old coordinate))
  :rule-classes :type-prescription)
 (defthm fn-assume-sror-success-primary-object-bound
  (implies (fn-sror-resize-domain-p request old coordinate)
   (<= (fn-assume-sror-success-object-octets request old coordinate)
       (fn-sror-primary-request request)))
  :rule-classes nil))
(defun fn-sror-success-object-request (request old-capacity coordinate)
 (declare (xargs :guard t))
 (if (fn-sror-resize-domain-p request old-capacity coordinate)
     (mv :primary-object (fn-sror-primary-request request) 1)
   (mv :unavailable nil nil)))
(verify-guards fn-sror-primary-request)
(verify-guards fn-sror-resize-domain-p)
(verify-guards fn-sror-success-object-request)
