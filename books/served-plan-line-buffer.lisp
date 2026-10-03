; PRF-1281: direct line windows for an immutable NEWNEWS render continuation.
; No arena/catalog read occurs in this phase; the response retains its captured
; roots. Other cursor phases still use the existing serialized cursor entry.
(in-package "ACL2")
(include-book "string-line-fill")
(include-book "newnews-stream-cursor")
(include-book "served-plan-window")

(defun fn-splan-line-ready-p (p)
  (declare (xargs :guard t))
  (let* ((rest (fn-splan-rest p))
         (effect (fn-ag-car rest))
         (cur (fn-cur-at 1 effect))
         (progress (fn-cur-progress cur)))
    (and (atom (fn-splan-cur p))
         (fn-nnw-meta-effectp effect)
         (not (fn-cur-dependency cur))
         (not (consp (fn-cur-pending cur)))
         (fn-nnw-stream-renderp progress)
         (if (member-eq (fn-cur-at 2 (fn-cur-at 1 progress))
                       '(:stuff :text :cr :lf)) t nil))))

(defun fn-splan-line-window (p bytes fn-octets)
  (declare (xargs :guard (natp bytes) :stobjs fn-octets))
  (let ((fn-octets (fn-octets-clear fn-octets)))
    (if (or (zp bytes) (not (fn-splan-line-ready-p p)))
        (mv :ineligible p fn-octets)
      (let* ((rest (fn-splan-rest p))
             (cur (fn-cur-at 1 (fn-ag-car rest)))
             (progress (fn-cur-progress cur)))
        (mv-let (line fn-octets)
          (fn-sl-fill (fn-cur-at 1 progress) bytes fn-octets)
          (let* ((next-progress
                  (if line
                      (fn-nnw-stream-render line (fn-cur-at 2 progress))
                    (or (fn-cur-at 2 progress) '(:terminator))))
                 (next (fn-cur-make (fn-cur-context cur) next-progress nil nil)))
            (mv :ok (cons nil (cons (fn-nnw-meta-effect next) (fn-ag-cdr rest)))
                fn-octets)))))))

; The host-called boundary preserves its first cursor residual, untouched
; later effects and capture, while bounding the filled output.
(local
 (defthm fn-slbuf-append-assoc (equal (append (append x y) z) (append x (append y z)))))

(local
 (defthm fn-slbuf-owes-terminator
 (equal (fn-nnw-stream-owes '(:terminator) fn-arena fn-cat) '(46 13 10))
 :hints (("Goal" :expand ((fn-nnw-stream-owes '(:terminator) fn-arena fn-cat))
          :in-theory (enable fn-nnw-stream-renderp)))))

(local
 (defthm fn-slbuf-render-remaining
 (implies (fn-nnw-stream-renderp p)
  (equal (fn-nnw-stream-owes p fn-arena fn-cat)
         (append (fn-sl-remaining (fn-cur-at 1 p))
                 (if (fn-cur-at 2 p) (fn-nnw-stream-owes (fn-cur-at 2 p) fn-arena fn-cat)
                   '(46 13 10)))))
 :hints (("Goal" :expand ((fn-nnw-stream-owes p fn-arena fn-cat))
          :in-theory (e/d (fn-nnw-stream-renderp) (fn-nnw-stream-owes fn-sl-remaining))))))

(local
 (defthm fn-slbuf-fill-residual-onto
 (equal (append (mv-nth 1 (fn-sl-fill cur bytes nil))
                (append (fn-sl-remaining (mv-nth 0 (fn-sl-fill cur bytes nil))) suffix))
        (append (fn-sl-remaining cur) suffix))
 :hints (("Goal"
 :use ((:instance fn-sl-fill-exact-residual (fn-octets nil))
       (:instance fn-slbuf-append-assoc (x (mv-nth 1 (fn-sl-fill cur bytes nil)))
        (y (fn-sl-remaining (mv-nth 0 (fn-sl-fill cur bytes nil)))) (z suffix)))
 :in-theory (disable fn-sl-fill fn-sl-remaining fn-sl-fill-exact-residual fn-slbuf-append-assoc)))))

(local
 (defthm fn-splan-line-window-exact-residual
 (implies (and (fn-splan-line-ready-p p) (posp bytes))
  (equal
   (append (mv-nth 2 (fn-splan-line-window p bytes fn-octets))
           (fn-nnw-stream-remaining
            (fn-cur-at 1 (car (fn-splan-rest (mv-nth 1 (fn-splan-line-window p bytes fn-octets)))))
            fn-arena fn-cat))
   (fn-nnw-stream-remaining (fn-cur-at 1 (car (fn-splan-rest p))) fn-arena fn-cat)))
 :hints (("Goal"
  :use ((:instance fn-sl-fill-exact-residual
         (cur (fn-cur-at 1 (fn-cur-progress (fn-cur-at 1 (car (fn-splan-rest p))))))
         (fn-octets nil)))
  :in-theory (e/d (fn-splan-line-window fn-splan-line-ready-p fn-nnw-meta-effect fn-nnw-meta-effectp
                   fn-nnw-stream-remaining fn-cur-make fn-cur-progress fn-cur-pending fn-cur-dependency
                   fn-cur-at fn-nnw-stream-render fn-nnw-stream-renderp)
                  (fn-sl-fill fn-sl-remaining fn-nnw-stream-owes fn-sl-fill-exact-residual))))))

(defthm fn-splan-line-window-preserves-residual
  (equal
   (append (mv-nth 2 (fn-splan-line-window p bytes fn-octets))
           (fn-nnw-stream-remaining
            (fn-cur-at 1 (car (fn-splan-rest (mv-nth 1 (fn-splan-line-window p bytes fn-octets)))))
            fn-arena fn-cat))
   (fn-nnw-stream-remaining (fn-cur-at 1 (car (fn-splan-rest p))) fn-arena fn-cat))
 :hints (("Goal" :use fn-splan-line-window-exact-residual
   :cases ((fn-splan-line-ready-p p) (zp bytes))
   :in-theory (e/d (fn-splan-line-window posp)
                   (fn-splan-line-ready-p fn-sl-fill fn-nnw-stream-remaining
                    fn-nnw-stream-owes fn-splan-line-window-exact-residual)))))

(defthm fn-splan-line-window-keeps-tail
 (equal (cdr (fn-splan-rest (mv-nth 1 (fn-splan-line-window p bytes fn-octets))))
        (cdr (fn-splan-rest p)))
 :hints (("Goal" :in-theory (e/d (fn-splan-line-window fn-nnw-meta-effect)
                                (fn-sl-fill fn-splan-line-ready-p)))))

(defthm fn-splan-line-window-keeps-context
 (equal (fn-cur-context (fn-cur-at 1 (car (fn-splan-rest (mv-nth 1 (fn-splan-line-window p bytes fn-octets))))))
        (fn-cur-context (fn-cur-at 1 (car (fn-splan-rest p)))))
 :hints (("Goal" :in-theory (e/d (fn-splan-line-window fn-nnw-meta-effect fn-cur-context fn-cur-make fn-cur-at)
                                (fn-sl-fill fn-splan-line-ready-p)))))

(defthm fn-splan-line-window-byte-bound
 (<= (len (mv-nth 2 (fn-splan-line-window p bytes fn-octets))) (nfix bytes))
 :rule-classes :linear
 :hints (("Goal" :in-theory (e/d (fn-splan-line-window) (fn-sl-fill fn-splan-line-ready-p)))))
