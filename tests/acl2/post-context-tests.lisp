; Executed witnesses for the approved Section C statements.
(in-package "ACL2")
(include-book "../../books/post-context")
(include-book "../../books/defkeystone")
(set-verify-guards-eagerness 1)

; The maximal phase-1 ground context: every scalar width and field bound
; is attained, and the encoding attains the 8384-octet context bound.
(defconst *fn-pctxt-maximal*
  (let ((k (fn-adm-acc-out-max)))
    (list 18446744073709551615
          (make-list k :initial-element 255)
          (make-list k :initial-element 128)
          4294967295
          (make-list *fn-pctx-sufhead-max* :initial-element 1)
          (make-list k :initial-element 0))))
(defconst *fn-pctxt-input*
  (append (fn-pctx-encode *fn-pctxt-maximal*) '(1 2 3)))

; A real codec fault: reserve four txid octets where version 1 needs eight.
; The production definitions stay unchanged; this is only the checked mutant.
(defun fn-pctxt-encode-txid32 (ctx)
  (declare (xargs :guard t))
  (cons 1 (fn-pctx-cat (fn-pctx-uint-be (fn-pctx-get 0 ctx) 4)
                      (nthcdr 9 (true-list-fix (fn-pctx-encode ctx))))))

(defteeth fn-pctx-round-trip
  :claim (((valid (fn-pctx-p ctx)))
          (equal (fn-pctx-decode (append (fn-pctx-encode ctx) rest))
                 (list t ctx (len (fn-pctx-encode ctx)))))
  :subject fn-pctx-decode
  :witness ((ctx *fn-pctxt-maximal*) (rest '(1 2 3)))
  :breaks ((valid ((ctx '(18446744073709551616 nil nil 0 nil nil)))))
  :mutations ((txid-written-in-four-octets
               (:conclusion
                (equal (fn-pctx-decode (append (fn-pctxt-encode-txid32 ctx) rest))
                       (list t ctx (len (fn-pctxt-encode-txid32 ctx)))))
               ()
               :fault "writing the txid in four octets truncates values >= 2^32 and shifts every following field; the eight-octet decoder cannot recover the maximal context")))

(defteeth fn-pctx-encode-bounded
  :claim (((valid (fn-pctx-p ctx)))
          (<= (len (fn-pctx-encode ctx)) *fn-pctx-max*))
  :subject fn-pctx-encode
  :witness ((ctx *fn-pctxt-maximal*))
  :breaks ((valid ((ctx (list 0 (make-list *fn-pctx-max* :initial-element 0)
                            nil 0 nil nil)))))
  :mutations ((four-octet-txid-budget
               (:conclusion
                (<= (len (fn-pctx-encode ctx)) (- *fn-pctx-max* 4)))
               ()
               :fault "budgeting 1 + 6*4 fixed octets undercounts the eight-octet txid by four; the maximal valid context exceeds that budget")))

(defteeth fn-pctx-decode-shape
  :claim (let ((d (fn-pctx-decode x)))
           (((decoded (car d)))
            (and (fn-pctx-p (cadr d)) (natp (caddr d))
                 (<= (caddr d) (len x)) (<= (caddr d) *fn-pctx-max*))))
  :subject fn-pctx-decode
  :witness ((x *fn-pctxt-input*))
  :breaks ((decoded ((x '(2)))))
  :mutations ((article-suffix-counted-as-context
               (:conclusion
                (and (fn-pctx-p (cadr d)) (natp (len x))
                     (<= (len x) (len x)) (<= (len x) *fn-pctx-max*)))
               ()
               :fault "reporting the full handed buffer length as the consumed context also counts the article suffix; a maximal context followed by three octets then exceeds the context bound")))

(defteeth-check (fn-pctx-round-trip fn-pctx-encode-bounded fn-pctx-decode-shape))
