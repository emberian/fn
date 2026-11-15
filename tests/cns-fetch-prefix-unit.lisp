(in-package "ACL2")
(include-book "../books/cns-fetch-prefix-codec")

(defun fn2-cfp-read (i end fn2-pool)
 (declare (xargs :stobjs fn2-pool :verify-guards nil :measure (nfix (- (nfix end) (nfix i)))))
 (if (or (not (natp i)) (not (natp end)) (>= i end)) nil
  (mv-let (code byte) (fn2-pool-read 0 1 i 1 0 1 fn2-pool)
   (if (eq code :ok) (cons byte (fn2-cfp-read (+ i 1) end fn2-pool)) nil))))

(defun fn2-cfp-model (n)
 (declare (xargs :verify-guards nil))
 (let* ((article (repeat n 120))
        (result (fn2-layout-octets (cadr (assoc-eq 'fetch *fn2-fnct-results*)) (list article)))
        (port (fn2-layout-octets *fn2-fnct-port-reply-layout*
                               (list *fn2-cns-fetch-accepted-class* nil result)))
        (header (fn2-layout-octets *fn2-fnct-header-layout*
                  (list *fn2-fnct-magic* *fn2-fnct-version* *fn2-fnct-port-reply-kind* (len port)))))
  (take *fn2-cns-fetch-frame-prefix-octets* (append header port))))

(defun fn2-cfp-unit (n)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-fields
  (mv-let (ok fn2-fields)
   (with-local-stobj fn2-pool
    (mv-let (ok fn2-fields fn2-pool)
     (b* ((fn2-fields (fn2-fields-init 128 fn2-fields))
          (fn2-pool (fn2-pool-init '((1 . 4096)) 1 100 fn2-pool))
          ((mv reserve slot gen fn2-pool) (fn2-pool-reserve 0 1 0 1 fn2-pool))
          ((mv code end fn2-fields fn2-pool)
           (fn2-cns-fetch-stream-prefix 0 n slot gen 1 0 1 fn2-fields fn2-pool)))
      (mv (and (eq reserve :ok) (eq code :ok)
               (equal end *fn2-cns-fetch-frame-prefix-octets*)
               (equal (fn2-cfp-read 0 end fn2-pool) (fn2-cfp-model n))) fn2-fields fn2-pool))
     (mv ok fn2-fields)))
   ok)))
(assert-event (fn2-cfp-unit 0))
(assert-event (fn2-cfp-unit 6144))
(assert-event (fn2-cfp-unit 16384))
