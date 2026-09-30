; Proof-only denotation of the actual sorted input-preparation continuation.
; No model list traversal is called by admission, the scheduler or the fence.
(in-package "ACL2")
(include-book "consumer-account-candidate")

(defun fn-cadm-insert-first (credential rows)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp rows)
     (let ((name (fn-auth-cred-name credential))
           (old (fn-auth-cred-name (car rows))))
      (cond ((equal name old) rows)
            ((fn-caa-name-lessp name old) (cons credential rows))
            (t (cons (car rows) (fn-cadm-insert-first credential (cdr rows))))))
  (list credential)))

(defun fn-cadm-denotation (s)
 (declare (xargs :guard t :verify-guards nil))
 (case (fn-cp-nth 1 s)
  (:idle (fn-cp-nth 2 s))
  (:seek (revappend (fn-cp-nth 8 s)
                    (fn-cadm-insert-first (fn-cp-nth 4 s) (fn-cp-nth 6 s))))
  (:rebuild (revappend (fn-cp-nth 8 s) (fn-cp-nth 6 s)))
  (otherwise nil)))

; Car/suffix are well-typed under the actual input producer; this structural
; fact makes total malformed rows distinct from a valid empty continuation.
(defun fn-cadm-sourcep (s)
 (declare (xargs :guard t :verify-guards nil))
 (and (member-eq (fn-cp-nth 1 s) '(:idle :seek :rebuild))
      (true-listp (fn-cp-nth 8 s))
      (true-listp (fn-cp-nth 6 s))
      (or (not (eq (fn-cp-nth 1 s) :seek))
          (and (equal (fn-cp-nth 2 s)
                       (revappend (fn-cp-nth 8 s) (fn-cp-nth 6 s)))
               (or (not (consp (fn-cp-nth 6 s)))
                   (car (fn-cp-nth 6 s)))))))

(defthm fn-cadm-actual-tick-preserves-complete-denotation
 (implies (fn-cadm-sourcep s)
          (let ((one (fn-cad-tick s)))
           (and (member-eq (fn-cp-nth 0 one) '(:yield :ready))
                (equal (fn-cadm-denotation (fn-cp-nth 1 one))
                       (fn-cadm-denotation s)))))
 :hints (("Goal" :in-theory
          (e/d (fn-cadm-sourcep fn-cadm-denotation fn-cadm-insert-first
                fn-cad-tick fn-cad-state fn-cp-nth revappend)
               (fn-caa-name-lessp fn-auth-cred-name fn-caac-list-cons revappend-removal)))))

(defthm fn-cadm-actual-ready-is-the-complete-candidate
 (implies (and (fn-cadm-sourcep s)
               (eq (fn-cp-nth 0 (fn-cad-tick s)) :ready))
          (equal (fn-cp-nth 2 (fn-cp-nth 1 (fn-cad-tick s)))
                 (fn-cadm-denotation s)))
 :hints (("Goal" :in-theory
          (e/d (fn-cadm-sourcep fn-cadm-denotation fn-cadm-insert-first
                fn-cad-tick fn-cad-state fn-cp-nth revappend)
               (fn-caa-name-lessp fn-auth-cred-name fn-caac-list-cons revappend-removal)))))

(in-theory (disable fn-cadm-insert-first fn-cadm-denotation fn-cadm-sourcep))
