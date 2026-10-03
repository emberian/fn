; The native web page continuation. The segment vocabulary and escaping are
; web-render's. This program boundary is not yet a certified refinement of
; fn-wr-seq; the raw consumer compares its exact bytes to that reference.
(in-package "ACL2")
(include-book "web-render")

; (remaining-segments active-kind list-source span-start span-end bol pending)
; List sources and segment tails share the retained plan. Pending is at most
; one escaped source octet (or one percent-encoded source octet).
(defun fn-wpc-cursor (segs)
  (declare (xargs :mode :program))
  (list segs nil nil 0 0 t nil))

(defun fn-wpc-next (cursor fn-web-in)
  (declare (xargs :mode :program :stobjs fn-web-in))
  (let* ((segs (fn-wrq-nth 0 cursor)) (kind (fn-wrq-nth 1 cursor))
         (xs (fn-wrq-nth 2 cursor)) (s (nfix (fn-wrq-nth 3 cursor)))
         (e (nfix (fn-wrq-nth 4 cursor))) (bol (fn-wrq-nth 5 cursor))
         (pending (fn-wrq-nth 6 cursor)))
    (cond
     ((consp pending)
      (mv t (car pending) (list segs kind xs s e bol (cdr pending)) nil))
     ((member kind '(:m :t :u))
      (if (consp xs)
          (mv nil nil
              (list segs kind (cdr xs) s e bol
                    (case kind
                      (:m (list (car xs)))
                      (:u (fn-wr-escape (fn-wr-pct-encode (list (car xs)))))
                      (otherwise (fn-wr-escape-octet (car xs))))) nil)
        (mv nil nil (fn-wpc-cursor segs) nil)))
     ((member kind '(:s :d))
      (if (< s e)
          (let ((o (fn-octets-get s fn-web-in)))
            (if (and (equal kind :d) bol (equal o 46) (< (1+ s) e)
                     (equal (fn-octets-get (1+ s) fn-web-in) 46))
                (mv nil nil (list segs kind nil (1+ s) e nil nil) nil)
              (mv nil nil (list segs kind nil (1+ s) e (equal o 10)
                               (fn-wr-escape-octet o)) nil)))
        (mv nil nil (fn-wpc-cursor segs) nil)))
     ((consp segs)
      (let* ((seg (car segs)) (kind (car seg))
             (s (nfix (cadr seg))) (e (nfix (cddr seg))))
        (mv nil nil
            (case kind
              ((:m :t :u) (list (cdr segs) kind (cdr seg) 0 0 t nil))
              (:w (if (<= (- e s) *fn-w47-max*)
                      (list (cdr segs) :t (fn-w47-decode (fn-oct-slice-list s e fn-web-in)) 0 0 t nil)
                    (list (cdr segs) :s nil s e t nil)))
              (otherwise (list (cdr segs) kind nil s e t nil))) nil)))
     (t (mv nil nil cursor t)))))

(defun fn-wpc-drive (fuel cursor count emitp rev fn-web-in)
  (declare (xargs :mode :program :stobjs fn-web-in))
  (if (zp fuel)
      (mv (reverse rev) cursor (nfix count) nil)
    (mv-let (present octet next done) (fn-wpc-next cursor fn-web-in)
      (if done
          (mv (reverse rev) next (nfix count) t)
        (fn-wpc-drive (1- fuel) next (if present (1+ (nfix count)) (nfix count))
                      emitp (if (and present emitp) (cons octet rev) rev) fn-web-in)))))

(defun fn-wpc-step (cursor count emitp fn-web-in)
  (declare (xargs :mode :program :stobjs fn-web-in))
  ; Fixed scheduling quantum, not a response length ceiling. The bounded
  ; RFC2047 decoder may additionally inspect at most *fn-w47-max* bytes.
  (fn-wpc-drive 4096 cursor count emitp nil fn-web-in))
