; LC withdrawal model. Mark one row, retain its payload/locators, and
; maintain only the affected live-summary cells. Number ownership is stable.
(in-package "ACL2")
(include-book "log-checkpoint-record")

(defun fn-lc-live-numberp (group number segs fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc) :verify-guards nil))
 (let ((i (ec-call (fn-lbc-number-get group number fn-lbc))))
  (and (natp i) (< i (fn-lbc-count fn-lbc))
       (ec-call (fn-cat-live-rowp group number (ec-call (fn-lbc-at i fn-lbc segs)))))))
(defun fn-lc-next-live-number (group number top segs fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc) :verify-guards nil
   :measure (nfix (- (+ 1 (nfix top)) (nfix number)))))
 (if (<= (nfix number) (nfix top))
  (if (fn-lc-live-numberp group (nfix number) segs fn-lbc) (nfix number)
   (fn-lc-next-live-number group (+ 1 (nfix number)) top segs fn-lbc)) 0))
(defun fn-lc-previous-live-number (group number segs fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc) :verify-guards nil
   :measure (nfix number)))
 (if (zp (nfix number)) 0
  (if (fn-lc-live-numberp group (nfix number) segs fn-lbc) (nfix number)
   (fn-lc-previous-live-number group (1- (nfix number)) segs fn-lbc))))

; Capture only numbers actually owned by TARGET and live before marking it.
; Repeated group names contribute once, matching the catalog's first binding.
(defun fn-lc-withdraw-live-bindings (numbers seen target segs fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc) :verify-guards nil))
 (if (consp numbers)
  (let* ((g (fn-lc-head (car numbers))) (n (fn-lc-rest (car numbers)))
         (rest (fn-lc-withdraw-live-bindings (cdr numbers) (cons g seen) target segs fn-lbc)))
   (if (and (not (member-equal g (true-list-fix seen)))
            (equal (ec-call (fn-lbc-number-get g n fn-lbc)) target)
            (fn-lc-live-numberp g n segs fn-lbc))
       (cons (cons g n) rest) rest)) nil))

(defun fn-lc-withdraw-summary-cells (bindings segs fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc) :verify-guards nil))
 (if (consp bindings)
  (let* ((g (fn-lc-head (car bindings))) (n (fn-lc-rest (car bindings)))
         (old (ec-call (fn-lbc-live-summary g fn-lbc)))
         (count (nfix (- (nfix (fn-lc-at 0 old)) 1)))
         (low (if (equal count 0) 0
                (if (equal n (fn-lc-at 1 old))
                    (fn-lc-next-live-number g (+ 1 (nfix n))
                                               (fn-lc-at 2 old) segs fn-lbc)
                  (fn-lc-at 1 old))))
         (high (if (equal count 0) 0
                 (if (equal n (fn-lc-at 2 old))
                     (fn-lc-previous-live-number g (nfix (- (nfix n) 1)) segs fn-lbc)
                   (fn-lc-at 2 old))))
         (fn-lbc (ec-call (fn-lbc-summary-put g
                           (list count low high (fn-lc-at 3 old)) 1 fn-lbc))))
   (fn-lc-withdraw-summary-cells (cdr bindings) segs fn-lbc)) fn-lbc))

(defun fn-lc-withdraw (target by fn-lbc segs)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc) :verify-guards nil))
 (if (or (not (natp target)) (not (< target (fn-lbc-count fn-lbc)))
         (not (natp by)))
     (mv :invalid-withdraw fn-lbc segs)
  (if (ec-call (fn-lbc-withdrawn target fn-lbc)) (mv :ok fn-lbc segs)
   (let* ((numbers (ec-call (fn-lbc-numbers target fn-lbc)))
          (bindings (fn-lc-withdraw-live-bindings numbers nil target segs fn-lbc))
          (cell (ec-call (fn-lbc-escape-store-get target fn-lbc)))
          ; Escapes carry arbitrary natural versions/identities without a
          ; data ceiling. Existing fields, including slot owners, are retained.
          (cell (ec-call (put-assoc-equal :withdrawal-at (fn-lbc-count fn-lbc) cell)))
          (cell (ec-call (put-assoc-equal :withdrawal-by by cell)))
          (fn-lbc (ec-call (fn-lbc-escape-store-put target cell fn-lbc)))
          (fn-lbc
           (stobj-let ((fn-lbc-rowwords (fn-lbc-row-store fn-lbc)))
            (fn-lbc-rowwords)
            (let* ((flags (ec-call (fn-lbc-rowwords-get-flags target fn-lbc-rowwords)))
                   (fn-lbc-rowwords (ec-call (fn-lbc-rowwords-set-withdrawal-at
                                               target 0 fn-lbc-rowwords)))
                   (fn-lbc-rowwords (ec-call (fn-lbc-rowwords-set-withdrawal-by
                                               target 0 fn-lbc-rowwords)))
                   (fn-lbc-rowwords (ec-call (fn-lbc-rowwords-set-flags
                                       target (logior 12 (nfix flags)) fn-lbc-rowwords))))
              fn-lbc-rowwords) fn-lbc))
          (fn-lbc (fn-lc-withdraw-summary-cells bindings segs fn-lbc)))
     (mv :ok fn-lbc segs)))))

(verify-guards fn-lc-live-numberp)
(verify-guards fn-lc-next-live-number)
(verify-guards fn-lc-previous-live-number)
(verify-guards fn-lc-withdraw-live-bindings)
(verify-guards fn-lc-withdraw-summary-cells)
(verify-guards fn-lc-withdraw)
