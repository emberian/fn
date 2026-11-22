; Served CNS read/wait request-limit boundaries (books/cns.lisp).
(in-package "ACL2")
(include-book "../books/cns")
(include-book "layout-unit")

(defconst *fn2-cdu-cursor*
  (fn2-fncu-encode '(:cursor 0 (1 14) (2 15) (1) (2) (1) 1 1 1 5)))

(defun fn2-cdu-check-with-cursor (word max-items cursor)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-fields
    (mv-let (ok fn2-fields)
      (with-local-stobj fn2-pool
        (mv-let (ok fn2-fields fn2-pool)
          (b* ((alist (list (cons 'cursor cursor)
                            (cons 'max-items max-items) (cons 'max-octets 65536)))
               (alist (if (eq word :wait) (append alist '((seconds . 30))) alist))
               (payload (fn2-fnct-request-encode (if (eq word :wait) :wait-cursor :read) alist))
               ((mv fn2-fields fn2-pool) (fn2-layout-test-init fn2-fields fn2-pool))
               (fn2-fields (fn2-fields-init 128 fn2-fields))
               (fn2-pool (fn2-layout-test-write payload 0 0 fn2-pool))
               ((mv reason verb & & & lim & wait-ms & & & & fn2-fields)
                (if (eq word :wait)
                    (fn2-cns-dec-wait 0 0 (len payload) 2 270 527 0 1 1 0 1 fn2-fields fn2-pool)
                  (fn2-cns-dec-read 0 0 (len payload) 2 270 527 0 1 1 0 1 fn2-fields fn2-pool))))
            (mv (list reason lim wait-ms verb) fn2-fields fn2-pool))
          (mv ok fn2-fields)))
      ok)))

(defun fn2-cdu-check (word max-items)
  (declare (xargs :verify-guards nil))
  (fn2-cdu-check-with-cursor word max-items *fn2-cdu-cursor*))

(assert-event
 (let ((old-placeholder (fn2-fncu-encode '(:cursor 0 (0) (0) (1) (2) (1) 1 1 1 5))))
   (and (equal (fn2-cdu-check-with-cursor :read 1 old-placeholder)
               (list *fn2-cns-reason-scope* 0 0 0))
        (equal (fn2-cdu-check-with-cursor :wait 1 old-placeholder)
               (list *fn2-cns-reason-scope* 0 0 0)))))

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

; Exercise the encoder and concrete decoder over a real range. The list
; codec independently checks which identity bytes the encoder emitted.
(defun fn2-cdu-scope (principal history incarnation)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-fields
    (mv-let (observation fn2-fields)
      (with-local-stobj fn2-pool
        (mv-let (observation fn2-fields fn2-pool)
          (b* (((mv fn2-fields fn2-pool) (fn2-layout-test-init fn2-fields fn2-pool))
               (fn2-fields (fn2-fields-init 128 fn2-fields))
               ((mv code offset length fn2-fields fn2-pool)
                (fn2-cns-put-cursor 0 1 4294967297 270 527 1 1 5 0 1 1 0 1 fn2-fields fn2-pool))
               ((unless (eq code :ok)) (mv (list code) fn2-fields fn2-pool))
               (octets (fn2-layout-test-read length 0 offset fn2-pool))
               ((mv reason cid epoch position fn2-fields)
                (fn2-cns-decode-cursor 0 offset length principal history incarnation
                                       0 1 1 0 1 fn2-fields fn2-pool)))
            (mv (list code (fn2-fncu-decode octets) reason cid epoch position) fn2-fields fn2-pool))
          (mv observation fn2-fields)))
      observation)))

(defconst *fn2-cdu-scope-encoded*
  '(:ok (:cursor 0 (1 14) (2 15) (1) (1 0 0 0 1) (1) 1 1 1 5)))

(assert-event
 (equal (fn2-cdu-scope 4294967297 270 527)
        (list :ok *fn2-cdu-scope-encoded* 0 1 1 5)))

; Remove the decoder theorem's success hypothesis by changing one expected
; component at a time. The actual range still carries the original bytes.
(assert-event
 (let ((refusal (list :ok *fn2-cdu-scope-encoded* *fn2-cns-reason-scope* 0 0 0)))
   (and (equal (fn2-cdu-scope 1 270 527) refusal)
        (equal (fn2-cdu-scope 4294967297 271 527) refusal)
        (equal (fn2-cdu-scope 4294967297 270 528) refusal)
        (equal (fn2-cdu-scope 4294967297 0 0) refusal))))
