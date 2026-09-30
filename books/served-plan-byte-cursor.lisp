; Atomic full-plan adapter for OVER. Dormant PRF-1066 integration component.
; The caller retains every returned PLAN before another ONE may cold-throw.
; PLAN always contains the complete untouched effect tail and the saved quantum;
; neither the host nor FINISH reconstructs a cursor from independent aliases.
; Head positioning and the old-reply refinement are separate obligations.
(in-package "ACL2")
(include-book "served-plan-shape")
(include-book "served-plan-position")
(include-book "over-byte-cursor")

(defun fn-spbc-effect (tag value)
  (declare (xargs :guard t))
  (list :over-cursor (list tag value)))

(defun fn-spbc-cur (p)
  (declare (xargs :guard t))
  (if (fn-spp-holderp p) (fn-spp-cur p) (fn-splan-cur p)))

(defun fn-spbc-rest (p)
  (declare (xargs :guard t))
  (if (fn-spp-holderp p) (fn-spp-rest p) (fn-splan-rest p)))

(defun fn-spbc-with-rest (p rest)
  (declare (xargs :guard t))
  (if (fn-spp-holderp p)
      (fn-spp-save-active p (cons (fn-spbc-cur p) rest))
    (cons (fn-spbc-cur p) rest)))

(defun fn-spbc-head (p)
  (declare (xargs :guard t))
  (fn-lpc-at 0 (fn-spbc-rest p)))

(defun fn-spbc-payload (p)
  (declare (xargs :guard t))
  (fn-lpc-at 1 (fn-spbc-head p)))

(defun fn-spbc-tail (p)
  (declare (xargs :guard t))
  (fn-ag-cdr (fn-spbc-rest p)))

(defun fn-spbc-put (p effect)
  (declare (xargs :guard t))
  (fn-spbc-with-rest p (cons effect (fn-spbc-tail p))))

; The HEAD requirement prevents an uncharged scan/rebuild of surrounding
; effects. No validator of the arena, catalog, F or complete cursor executes.
(defun fn-spbc-begin (p pin fuel)
  (declare (xargs :guard t))
  (let* ((payload (fn-spbc-payload p))
         (bytep (eq (fn-lpc-at 0 payload) :byte))
         (s (if bytep (fn-lpc-at 1 payload) (fn-obc-begin payload pin))))
    (cond ((or (consp (fn-spbc-cur p))
               (not (fn-splan-cursor-effectp (fn-spbc-head p)))
               (and (not bytep) (not (fn-ovw-cursorp payload))))
           (mv :malformed p))
          ((and (fn-spp-holderp p) (not (equal (fn-spp-origin p) pin)))
           (mv :stale-pin p))
          ((not (equal (fn-lpc-at 1 s) pin)) (mv :stale-pin p))
          (t (mv :ok (fn-spbc-put p
                       (fn-spbc-effect :byte-quantum
                         (fn-obc-quantum-begin s fuel))))))))

(defun fn-spbc-quantum (p)
  (declare (xargs :guard t))
  (fn-lpc-at 1 (fn-spbc-payload p)))

(defun fn-spbc-status (p)
  (declare (xargs :guard t))
  (if (and (fn-splan-cursor-effectp (fn-spbc-head p))
           (eq (fn-lpc-at 0 (fn-spbc-payload p)) :byte-quantum))
      (if (and (fn-lpc-at 0 (fn-spbc-quantum p))
               (posp (fn-lpc-at 1 (fn-spbc-quantum p))))
          :continue :ready)
    :malformed))

; Guard vocabulary only. The native boundary must carry it, not execute it.
(defun fn-spbc-ready-p (p fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t :verify-guards nil))
  (let ((q (fn-spbc-quantum p)))
    (and (not (eq (fn-spbc-status p) :malformed))
         (true-listp q) (natp (nth 1 q)) (true-listp (nth 2 q))
         (natp (nth 3 q))
         (or (null (nth 0 q))
             (and (fn-obc-statep (nth 0 q) fn-arena)
                  (fn-obc-source-ready-p (nth 0 q) fn-arena fn-cat))))))

(defun fn-spbc-one (p fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (fn-spbc-ready-p p fn-arena fn-cat)
                  :verify-guards nil))
  (if (eq (fn-spbc-status p) :continue)
      (fn-spbc-put p (fn-spbc-effect :byte-quantum
                       (fn-obc-quantum-one (fn-spbc-quantum p) fn-arena fn-cat)))
    p))

; Called on the last RETURNED PLAN after budget exhaustion or a cold throw.
; Saved output is published once; the exact continuation remains in the same
; full plan. The response origin is retained inside S until final drain.
(defun fn-spbc-finish (p)
  (declare (xargs :guard (and (true-listp (fn-spbc-quantum p))
                             (true-listp (fn-lpc-at 2 (fn-spbc-quantum p))))
                  :verify-guards nil))
  (mv-let (out next) (fn-obc-quantum-finish (fn-spbc-quantum p))
    (fn-spbc-with-rest p
          (cons (fn-nntp-reply-effect out)
                (if next
                    (cons (fn-spbc-effect :byte next) (fn-spbc-tail p))
                  (fn-spbc-tail p))))))

(defthm fn-spbc-cur-of-with-rest-by-definition
  (equal (fn-spbc-cur (fn-spbc-with-rest p rest)) (fn-spbc-cur p))
  :hints (("Goal" :in-theory (enable fn-spbc-cur fn-spbc-with-rest fn-spp-holderp
    fn-spp-save-active fn-spp-make fn-spp-cur fn-spp-at fn-ag-car fn-ag-cdr))))

(defthm fn-spbc-rest-of-with-rest-by-definition
  (equal (fn-spbc-rest (fn-spbc-with-rest p rest)) rest)
  :hints (("Goal" :in-theory (enable fn-spbc-rest fn-spbc-with-rest fn-spp-holderp
    fn-spp-save-active fn-spp-make fn-spp-rest fn-spp-at fn-ag-car fn-ag-cdr))))

(defthm fn-spbc-put-retains-surroundings
  (and (equal (fn-spbc-cur (fn-spbc-put p e)) (fn-spbc-cur p))
       (equal (fn-spbc-tail (fn-spbc-put p e)) (fn-spbc-tail p)))
  :hints (("Goal" :in-theory (enable fn-spbc-put fn-spbc-tail fn-spbc-rest fn-ag-cdr))))

(defthm fn-spbc-one-retains-surroundings
  (and (equal (fn-spbc-cur (fn-spbc-one p fn-arena fn-cat)) (fn-spbc-cur p))
       (equal (fn-spbc-tail (fn-spbc-one p fn-arena fn-cat)) (fn-spbc-tail p)))
  :hints (("Goal" :in-theory (disable fn-obc-quantum-one fn-spbc-status))))

(local (defthm fn-spbc-at-is-nth
  (equal (fn-lpc-at i x) (nth (nfix i) x))
  :hints (("Goal" :in-theory (enable fn-lpc-at fn-ag-car fn-ag-cdr nth)))))

(verify-guards fn-spbc-ready-p)
(verify-guards fn-spbc-one
  :hints (("Goal" :in-theory (enable fn-spbc-ready-p))))
(verify-guards fn-spbc-finish)

(defthm fn-spbc-quantum-of-put-by-definition
  (equal (fn-spbc-quantum (fn-spbc-put p (fn-spbc-effect :byte-quantum q))) q)
  :hints (("Goal" :in-theory (enable fn-spbc-quantum fn-spbc-payload fn-spbc-head
                                    fn-spbc-put fn-spbc-effect fn-spbc-tail
                                    fn-spbc-cur fn-spbc-rest fn-lpc-at fn-ag-car fn-ag-cdr))))

(defthm fn-spbc-one-is-saved-atomic-quantum-by-definition
  (implies (equal (fn-spbc-status p) :continue)
           (equal (fn-spbc-quantum (fn-spbc-one p fn-arena fn-cat))
                  (fn-obc-quantum-one (fn-spbc-quantum p) fn-arena fn-cat)))
  :hints (("Goal" :in-theory (disable fn-obc-quantum-one fn-spbc-quantum fn-spbc-put
                                      fn-spbc-effect fn-spbc-status))))

(defthm fn-spbc-finish-retains-exact-output-and-continuation-by-definition
  (let* ((q (fn-spbc-quantum p))
         (next (mv-nth 1 (fn-obc-quantum-finish q)))
         (rest (fn-spbc-rest (fn-spbc-finish p))))
    (and (equal (car rest)
                (fn-nntp-reply-effect (mv-nth 0 (fn-obc-quantum-finish q))))
         (equal (cdr rest)
                (if next (cons (fn-spbc-effect :byte next) (fn-spbc-tail p))
                  (fn-spbc-tail p)))
         (equal (fn-spbc-cur (fn-spbc-finish p)) (fn-spbc-cur p))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-obc-quantum-finish fn-spbc-quantum
                                      fn-spbc-tail fn-spbc-effect fn-nntp-reply-effect))))

; The response holder remains the sole owner across a returned byte quantum.
(defthm fn-spbc-with-rest-retains-holder-ownership
  (implies (fn-spp-holderp p)
    (and (fn-spp-holderp (fn-spbc-with-rest p rest))
         (equal (fn-spp-prefix (fn-spbc-with-rest p rest)) (fn-spp-prefix p))
         (equal (fn-spp-origin (fn-spbc-with-rest p rest)) (fn-spp-origin p))
         (equal (fn-spp-resource (fn-spbc-with-rest p rest)) (fn-spp-resource p))))
  :hints (("Goal" :in-theory (enable fn-spbc-with-rest fn-spp-holderp
                                      fn-spp-save-active fn-spp-make))))

(defthm fn-spbc-begin-retains-holder-ownership
  (implies (fn-spp-holderp p)
    (let ((next (mv-nth 1 (fn-spbc-begin p pin fuel))))
      (and (fn-spp-holderp next)
           (equal (fn-spp-prefix next) (fn-spp-prefix p))
           (equal (fn-spp-origin next) (fn-spp-origin p))
           (equal (fn-spp-resource next) (fn-spp-resource p)))))
  :hints (("Goal" :in-theory (e/d (fn-spbc-begin fn-spbc-put)
    (fn-spbc-with-rest fn-obc-begin fn-obc-quantum-begin fn-spbc-payload
     fn-spbc-head fn-spbc-cur fn-lpc-at fn-spp-origin fn-spp-prefix
     fn-spp-resource fn-spp-holderp)))))

(defthm fn-spbc-one-retains-holder-ownership
  (implies (fn-spp-holderp p)
    (let ((next (fn-spbc-one p fn-arena fn-cat)))
      (and (fn-spp-holderp next)
           (equal (fn-spp-prefix next) (fn-spp-prefix p))
           (equal (fn-spp-origin next) (fn-spp-origin p))
           (equal (fn-spp-resource next) (fn-spp-resource p)))))
  :hints (("Goal" :in-theory (e/d (fn-spbc-one fn-spbc-put)
    (fn-spbc-with-rest fn-obc-quantum-one fn-spbc-status fn-spp-holderp
     fn-spp-prefix fn-spp-origin fn-spp-resource)))))

(defthm fn-spbc-finish-retains-holder-ownership
  (implies (fn-spp-holderp p)
    (let ((next (fn-spbc-finish p)))
      (and (fn-spp-holderp next)
           (equal (fn-spp-prefix next) (fn-spp-prefix p))
           (equal (fn-spp-origin next) (fn-spp-origin p))
           (equal (fn-spp-resource next) (fn-spp-resource p)))))
  :hints (("Goal" :in-theory (e/d (fn-spbc-finish)
    (fn-spbc-with-rest fn-obc-quantum-finish fn-spbc-quantum fn-spp-holderp
     fn-spp-prefix fn-spp-origin fn-spp-resource)))))
