; Served CNS read/wait request-limit boundaries (books/cns.lisp).
(in-package "ACL2")
(include-book "../books/cns")
(include-book "layout-unit")

(defconst *fn2-cdu-cursor*
  (fn2-fncu-encode '(:cursor 0 (0) (0) (1) (2) (1) 1 1 1 5)))

(defun fn2-cdu-check (word max-items)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-fields
    (mv-let (ok fn2-fields)
      (with-local-stobj fn2-pool
        (mv-let (ok fn2-fields fn2-pool)
          (b* ((alist (list (cons 'cursor *fn2-cdu-cursor*)
                            (cons 'max-items max-items) (cons 'max-octets 65536)))
               (alist (if (eq word :wait) (append alist '((seconds . 30))) alist))
               (payload (fn2-fnct-request-encode (if (eq word :wait) :wait-cursor :read) alist))
               ((mv fn2-fields fn2-pool) (fn2-layout-test-init fn2-fields fn2-pool))
               (fn2-fields (fn2-fields-init 128 fn2-fields))
               (fn2-pool (fn2-layout-test-write payload 0 0 fn2-pool))
               ((mv reason verb & & & lim & wait-ms & & & & fn2-fields)
                (if (eq word :wait)
                    (fn2-cns-dec-wait 0 0 (len payload) 2 0 1 1 0 1 fn2-fields fn2-pool)
                  (fn2-cns-dec-read 0 0 (len payload) 2 0 1 1 0 1 fn2-fields fn2-pool))))
            (mv (list reason lim wait-ms verb) fn2-fields fn2-pool))
          (mv ok fn2-fields)))
      ok)))

(value-triple
 (cw "CDU-OBSERVED ~x0~%"
     (list (fn2-cdu-check :read 1) (fn2-cdu-check :wait 1)
           (fn2-cdu-check :read 0) (fn2-cdu-check :wait 0)
           (fn2-cdu-check :read 65535) (fn2-cdu-check :read 65536))))

(assert-event
 (and (equal (fn2-cdu-check :read 1)
             (list 0 1 0 *fn2-cns-verb-read*))
      (equal (fn2-cdu-check :wait 1)
             (list 0 1 30000 *fn2-cns-verb-wait*))
      (equal (fn2-cdu-check :read 65535)
             (list 0 65535 0 *fn2-cns-verb-read*))
      (equal (fn2-cdu-check :wait 65535)
             (list 0 65535 30000 *fn2-cns-verb-wait*))
      (equal (fn2-cdu-check :read 0)
             (list *fn2-cns-reason-meter* 0 0 0))
      (equal (fn2-cdu-check :wait 0)
             (list *fn2-cns-reason-meter* 0 0 0))
      (equal (fn2-cdu-check :read 65536)
             (list *fn2-cns-reason-meter* 0 0 0))
      (equal (fn2-cdu-check :wait 65536)
             (list *fn2-cns-reason-meter* 0 0 0))
      (equal (fn2-cdu-check :read 4294967295)
             (list *fn2-cns-reason-meter* 0 0 0))))
