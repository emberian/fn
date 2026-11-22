; Compare the pool encoder to the published list codec at the exact wire extent.
(in-package "ACL2")
(include-book "../books/peer-pull-request-encode")

(defun fn2-ppre-char-codes (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (endp chars) nil
    (cons (char-code (car chars)) (fn2-ppre-char-codes (cdr chars)))))

(defun fn2-ppre-put (bytes i slot gen fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (if (atom bytes) (mv :ok fn2-pool)
    (b* (((mv code fn2-pool) (fn2-pool-write slot gen i (car bytes) 1 1 1 fn2-pool))
         ((unless (eq code :ok)) (mv code fn2-pool)))
      (fn2-ppre-put (cdr bytes) (+ 1 (nfix i)) slot gen fn2-pool))))

(defun fn2-ppre-match (bytes i slot gen fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (if (atom bytes) (equal i (fn2-pool-fill-value slot fn2-pool))
    (mv-let (code byte) (fn2-pool-read slot gen i 1 1 1 fn2-pool)
      (and (eq code :ok) (equal byte (car bytes))
           (fn2-ppre-match (cdr bytes) (+ 1 (nfix i)) slot gen fn2-pool)))))

(defun fn2-ppre-check (case fn2-fields fn2-digests fn2-b3 fn2-pool)
  (declare (xargs :stobjs (fn2-fields fn2-digests fn2-b3 fn2-pool) :verify-guards nil))
  (b* ((fn2-fields (fn2-fields-init 16 fn2-fields))
       (fn2-digests (fn2-digests-init *fn2-digest-stride* fn2-digests))
       (fn2-b3 (fn2-b3-table-init 1 fn2-b3))
       (fn2-pool (fn2-pool-init '((2 . 1024)) 1 100 fn2-pool))
       ((mv source-code src sg fn2-pool) (fn2-pool-reserve 0 1 1 1 fn2-pool))
       ((mv tx-code tx tg fn2-pool) (fn2-pool-reserve 0 1 1 1 fn2-pool))
       (name (if (eq case :register-wide) (make-list 64 :initial-element 112) '(112 101 101 114)))
       (cursor '(102 110 99 117 2 0 18 41))
       ((mv put-code fn2-pool)
        (fn2-ppre-put (append name '(255 254 253) cursor '(252)) 0 src sg fn2-pool))
       ((unless (and (eq source-code :ok) (eq tx-code :ok) (eq put-code :ok)))
        (mv nil fn2-fields fn2-digests fn2-b3 fn2-pool))
       (registerp (member-eq case '(:register :register-wide)))
       (consumer (if (eq case :register-wide) (- (expt 2 60) 1) 256))
       ((mv code fn2-fields fn2-digests fn2-b3 fn2-pool)
        (if registerp
            (fn2-peer-pull-encode-register 0 0 consumer src sg (len name) tx tg 1 1 1
                                           fn2-fields fn2-digests fn2-b3 fn2-pool)
          (fn2-peer-pull-encode-read 0 0 src (if (eq case :stale-source) (+ sg 1) sg)
                                     7 8 17 65536 tx tg 1 1 1
                                     fn2-fields fn2-digests fn2-b3 fn2-pool)))
       (frame (fn2-fnct-seal 4
                (if registerp
                    (fn2-fnct-request-encode :register-query
                      (list (cons 'consumer (if (eq case :register-wide) '(15 255 255 255 255 255 255 255) '(1 0)))
                            (cons 'streams (cons (len name) name)) '(start . 1)))
                  (fn2-fnct-request-encode :read
                    (list (cons 'cursor cursor) '(max-items . 17) '(max-octets . 65536))))))
       (digits (explode-nonnegative-integer (len frame) 10 nil))
       (wire (append '(88 70 78 67 32) (fn2-ppre-char-codes digits) '(13 10) frame)))
    (mv (if (eq case :stale-source)
            (and (not (eq code :ok)) (equal 0 (fn2-pool-fill-value tx fn2-pool)))
          (and (eq code :ok) (fn2-ppre-match wire 0 tx tg fn2-pool)))
        fn2-fields fn2-digests fn2-b3 fn2-pool)))

(defun fn2-ppre-test (case)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-fields
    (mv-let (answer fn2-fields)
      (with-local-stobj fn2-digests
        (mv-let (answer fn2-fields fn2-digests)
          (with-local-stobj fn2-b3
            (mv-let (answer fn2-fields fn2-digests fn2-b3)
              (with-local-stobj fn2-pool
                (mv-let (answer fn2-fields fn2-digests fn2-b3 fn2-pool)
                  (fn2-ppre-check case fn2-fields fn2-digests fn2-b3 fn2-pool)
                  (mv answer fn2-fields fn2-digests fn2-b3)))
              (mv answer fn2-fields fn2-digests)))
          (mv answer fn2-fields)))
      answer)))

(assert-event (fn2-ppre-test :register))
(assert-event (fn2-ppre-test :register-wide))
(assert-event (fn2-ppre-test :read))
(assert-event (fn2-ppre-test :stale-source))
