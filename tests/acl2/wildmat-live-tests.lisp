(in-package "ACL2")
(include-book "../../books/defkeystone")

; Test-only traces; actual served code invokes one retained step.
(defun wmlt-find (s tag fuel)
 (declare (xargs :measure (nfix fuel) :verify-guards nil))
 (if (or (zp fuel) (eq (fn-wmc-at 0 (fn-wmc-at 0 s)) tag)) s
   (wmlt-find (fn-wmc-step s 1 (fn-wmc-demand s)) tag (1- fuel))))
(defun wmlt-frames (s fuel)
 (declare (xargs :measure (nfix fuel) :verify-guards nil))
 (if (zp fuel) (len (fn-wmc-at 1 s))
   (max (len (fn-wmc-at 1 s))
        (wmlt-frames (fn-wmc-step s 1 (fn-wmc-demand s)) (1- fuel)))))
(defconst *wmlt-patterns* '((:positive (42 97 98 42)) (:positive (42 99 99 99)) (:negative (42 100 100 100))))
(defconst *wmlt-start* (fn-wmc-start *wmlt-patterns* "abb"))
(defconst *wmlt-row* (wmlt-find *wmlt-start* :star-aux 1000))

; TEETH-22 END
