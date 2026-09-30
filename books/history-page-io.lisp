; Positional writes into the unchanged FNSI image region. LIMIT is the
; admitted runtime/profile maximum file extent, never an invented reserve.
(in-package "ACL2")
(include-book "history-image-snapshot")

(defun fn-hpi-region (np limit)
  (declare (xargs :guard t))
  (if (not (and (unsigned-byte-p 64 np) (natp limit)))
      (list :refused :domain)
    (let ((end (fn-his-region-octets np)))
      (if (< limit end) (list :refused :extent)
        (list :region end)))))

(defun fn-hpi-page (addr np limit)
  (declare (xargs :guard t))
  (let ((region (fn-hpi-region np limit)))
    (cond ((not (equal (car region) :region)) region)
          ((not (and (natp addr) (< addr np))) (list :refused :page))
          (t (list :pwrite (+ (fn-his-base-octets) (* 16384 addr)) 16384)))))

(defthm fn-hpi-page-contained-in-current-image
  (implies (equal (car (fn-hpi-page addr np limit)) :pwrite)
           (let ((p (fn-hpi-page addr np limit)))
             (and (natp (nth 1 p))
                  (<= (fn-his-base-octets) (nth 1 p))
                  (equal (nth 2 p) 16384)
                  (<= (+ (nth 1 p) (nth 2 p)) (fn-his-region-octets np))
                  (<= (fn-his-region-octets np) limit))))
  :hints (("Goal" :in-theory
           (union-theories
            '(fn-hpi-page fn-hpi-region fn-his-region-octets fn-his-skip-octets
              fn-his-base-octets unsigned-byte-p integer-range-p natp nth
              car-cons cdr-cons (:e equal) (:e car) (:e cdr) (:e consp)
              (:e binary-+) (:e binary-*) (:e expt) (:e <) (:e zp)
              default-+-1 default-+-2 fold-consts-in-+ commutativity-of-+)
            (theory 'minimal-theory)))))

(defthm fn-hpi-distinct-pages-do-not-overlap
  (implies (and (equal (car (fn-hpi-page a np limit)) :pwrite)
                (equal (car (fn-hpi-page b np limit)) :pwrite)
                (< a b))
           (<= (+ (nth 1 (fn-hpi-page a np limit)) (nth 2 (fn-hpi-page a np limit)))
               (nth 1 (fn-hpi-page b np limit))))
  :hints (("Goal" :in-theory
           (union-theories
            '(fn-hpi-page fn-hpi-region fn-his-region-octets fn-his-skip-octets
              fn-his-base-octets unsigned-byte-p integer-range-p natp nth
              car-cons cdr-cons (:e equal) (:e car) (:e cdr) (:e consp)
              (:e binary-+) (:e binary-*) (:e expt) (:e <) (:e zp)
              default-+-1 default-+-2 fold-consts-in-+ commutativity-of-+)
            (theory 'minimal-theory)))))

(defthm fn-hpi-page-step-matches-current-stream
  (implies (and (equal (car (fn-hpi-page a np limit)) :pwrite)
                (equal (car (fn-hpi-page (+ 1 a) np limit)) :pwrite))
           (equal (+ (nth 1 (fn-hpi-page a np limit)) (nth 2 (fn-hpi-page a np limit)))
                  (nth 1 (fn-hpi-page (+ 1 a) np limit))))
  :hints (("Goal" :in-theory
           (union-theories
            '(fn-hpi-page fn-hpi-region fn-his-region-octets fn-his-skip-octets
              fn-his-base-octets unsigned-byte-p integer-range-p natp nth
              car-cons cdr-cons (:e equal) (:e car) (:e cdr) (:e consp)
              (:e binary-+) (:e binary-*) (:e expt) (:e <) (:e zp)
              default-+-1 default-+-2 fold-consts-in-+ commutativity-of-+)
            (theory 'minimal-theory)))))

(in-theory (disable fn-hpi-region fn-hpi-page))
