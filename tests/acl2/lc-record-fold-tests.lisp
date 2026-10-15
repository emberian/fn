; Actual public accepted-record fold: two accepts update rows, numbers and summaries.

(in-package "ACL2")

(include-book "lc-withdraw-model-tests")

(defun lcf2-packet (prev row payload ordinal start)
 (declare (xargs :guard t))
 (let* ((frame (fn-lc-record-frame prev row payload))
        (entry (list (nfix ordinal) (nfix start) (nfix (- (len frame) 32))
          (+ (nfix start) (fn-lc-record-frame-served-offset frame))
          (fn-lc-record-frame-served-length frame)
          (ec-call (fn-record-payload row)) payload
          (ec-call (fn-lb-log-model-homes row)) (ec-call (fn-record-sequence row)))))
  (list row frame entry)))

(defun lcf2-public-control (fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc) :verify-guards nil))
 (let* ((r0 (lcw-held 0)) (r1 (lcw-held 1))
        (p0 (lcf2-packet *fn-lg-genesis* r0 *lct-payload* 0 0))
        (p1 (lcf2-packet (fn-lg-trailer (fn-lc-at 1 p0)) r1 *lct-payload*
                         1 (len (fn-lc-at 1 p0))))
        (records (list p0 p1))
        (header (list :lc-header (list 0 0 0 8 *fn-lg-genesis*) 1 nil nil nil))
        (segs '((0 nil nil)))
        (ready (ec-call (fn-lc-prepared-recordsp records *fn-lg-genesis* 1 *fn-lg-batch-payload-max*))))
  (mv-let (answer fn-lbc after)
   (ec-call (fn-lc-commit records segs header 2 fn-lbc))
   (mv (list ready answer (fn-lbc-count fn-lbc)
       (len (ec-call (fn-lc-tail-history after header)))
       (ec-call (fn-lc-locators-resolve fn-lbc after))
       (if (posp (fn-lbc-count fn-lbc)) (ec-call (fn-lbc-numbers 0 fn-lbc)) nil)
       (if (< 1 (fn-lbc-count fn-lbc)) (ec-call (fn-lbc-numbers 1 fn-lbc)) nil)
       (ec-call (fn-lbc-number-get "g" 1 fn-lbc))
       (ec-call (fn-lbc-number-get "g" 2 fn-lbc))
       (ec-call (fn-lbc-live-summary "g" fn-lbc))) fn-lbc))))

(defun lcf2-public-run ()
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-lbc
  (mv-let (out fn-lbc) (lcf2-public-control fn-lbc) out)))

(verify-guards lcf2-public-control)

(verify-guards lcf2-public-run)

(assert-event (equal (lcf2-public-run) '(t :ok 2 2 t (("g" . 1)) (("g" . 2)) 0 1 (2 1 2 3))))
