; Concrete counted RX tests, with a frame made by the logical codec.
(in-package "ACL2")
(include-book "../books/xfnc-rx")

(defmacro fn2-xru-plan (args)
  `(mv-let (status next left) (fn2-xfnc-rx-plan ,@args) (list status next left)))

(assert-event
 (and (equal (fn2-xru-plan (nil 8 64 20 128 64 256 nil)) '(:need-more 8 64))
      (equal (fn2-xru-plan (nil 100 64 128 128 64 256 nil)) '(:compact 100 64))
      (equal (fn2-xru-plan (nil 8 64 20 128 64 256 t)) '(:close 0 0))
      (equal (fn2-xru-plan (nil 8 257 20 128 64 256 nil)) '(:close 0 0))
      (equal (fn2-xru-plan (nil 8 65 20 128 64 256 nil)) '(:discard-need-more 20 53))
      (equal (fn2-xru-plan (t 0 53 60 128 64 256 nil)) '(:discarded 53 0))
      (equal (fn2-xru-plan (t 0 5000 6000 6000 64 6000 nil)) '(:discard-more 4096 904))))

(defun fn2-xru-put (bytes i slot gen fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (if (atom bytes) (mv :ok fn2-pool)
    (b* (((mv code fn2-pool) (fn2-pool-write slot gen i (car bytes) 1 1 1 fn2-pool))
         ((unless (eq code :ok)) (mv code fn2-pool)))
      (fn2-xru-put (cdr bytes) (+ 1 (nfix i)) slot gen fn2-pool))))

(defun fn2-xru-check-stages (case position length slot gen fn2-fields fn2-digests fn2-b3 fn2-pool)
  (declare (xargs :stobjs (fn2-fields fn2-digests fn2-b3 fn2-pool) :verify-guards nil))
  (b* (((mv header next left verb fn2-fields fn2-digests fn2-b3)
        (fn2-xfnc-rx-stage 0 0 slot gen 1 1 1 *fn2-xfnc-rx-header-phase*
                           nil position length 128 256 nil fn2-fields fn2-digests fn2-b3 fn2-pool))
       (end (+ position length))
       ((unless (and (eq header :hash) (equal next end) (zp left) (eq verb :none)))
        (mv nil fn2-fields fn2-digests fn2-b3))
       ((mv hashed next left verb fn2-fields fn2-digests fn2-b3)
        (fn2-xfnc-rx-stage 0 0 slot gen 1 1 1 *fn2-xfnc-rx-hash-phase*
                           nil position length 128 256 nil fn2-fields fn2-digests fn2-b3 fn2-pool))
       ((unless (and (eq hashed :trailer) (equal next end) (zp left) (eq verb :none)))
        (mv nil fn2-fields fn2-digests fn2-b3))
       ((mv checked next left verb fn2-fields fn2-digests fn2-b3)
        (fn2-xfnc-rx-stage 0 0 slot gen 1 1 1 *fn2-xfnc-rx-trailer-phase*
                           nil position length 128 256 nil fn2-fields fn2-digests fn2-b3 fn2-pool)))
    (mv (and (equal next end) (zp left)
             (if (eq case :staged-bad-trailer)
                 (and (eq checked :frame) (eq verb :none))
               (and (eq checked :ready) (eq verb :register))))
        fn2-fields fn2-digests fn2-b3)))

(defun fn2-xru-check (case fn2-fields fn2-digests fn2-b3 fn2-pool)
  (declare (xargs :stobjs (fn2-fields fn2-digests fn2-b3 fn2-pool) :verify-guards nil))
  (b* ((payload (fn2-fnct-request-encode :register-query
                                              '((consumer . (97)) (streams) (start . :history))))
       (frame (fn2-fnct-seal 4 (if (eq case :wrong-verb) '(16) payload)))
       (position 8)
       (length (len frame))
       (rx (append '(88 70 78 67 32 57 13 10)
                   (if (member-eq case '(:bad-trailer :staged-bad-trailer))
                       (append (take (- length 1) frame) (list (logxor 1 (nth (- length 1) frame))))
                     frame)
                   '(81 85 73 84 13 10)))
       (fn2-fields (fn2-fields-init 16 fn2-fields))
       (fn2-digests (fn2-digests-init *fn2-digest-stride* fn2-digests))
       (fn2-b3 (fn2-b3-table-init 1 fn2-b3))
       (fn2-pool (fn2-pool-init '((1 . 1024)) 1 100 fn2-pool))
       ((mv reserve slot gen fn2-pool) (fn2-pool-reserve 0 1 1 1 fn2-pool))
       ((mv wrote fn2-pool) (fn2-xru-put rx 0 slot gen fn2-pool))
       ((unless (and (eq reserve :ok) (eq wrote :ok)))
        (mv nil fn2-fields fn2-digests fn2-b3 fn2-pool))
       ((when (member-eq case '(:staged-ready :staged-bad-trailer)))
        (mv-let (answer fn2-fields fn2-digests fn2-b3)
          (fn2-xru-check-stages case position length slot gen fn2-fields fn2-digests fn2-b3 fn2-pool)
          (mv answer fn2-fields fn2-digests fn2-b3 fn2-pool)))
       ((mv status next remaining verb fn2-fields fn2-digests fn2-b3)
        (fn2-xfnc-rx-step 0 0 slot gen 1 1 (if (eq case :wrong-owner) 2 1) nil position
                         (if (eq case :trailing) (+ 1 length) length)
                         128 256 nil fn2-fields fn2-digests fn2-b3 fn2-pool)))
    (mv (and (eq reserve :ok) (eq wrote :ok)
             (case case
               (:ready (and (eq status :ready) (equal next (+ position length))
                            (equal remaining 0) (eq verb :register)))
               (:wrong-owner (and (eq status :access) (equal next 0) (eq verb :none)))
               (otherwise (and (eq status :frame) (equal next 0) (eq verb :none)))))
        fn2-fields fn2-digests fn2-b3 fn2-pool)))

(defun fn2-xru-test (case)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-fields
    (mv-let (answer fn2-fields)
      (with-local-stobj fn2-digests
        (mv-let (answer fn2-fields fn2-digests)
          (with-local-stobj fn2-b3
            (mv-let (answer fn2-fields fn2-digests fn2-b3)
              (with-local-stobj fn2-pool
                (mv-let (answer fn2-fields fn2-digests fn2-b3 fn2-pool)
                  (fn2-xru-check case fn2-fields fn2-digests fn2-b3 fn2-pool)
                  (mv answer fn2-fields fn2-digests fn2-b3)))
              (mv answer fn2-fields fn2-digests)))
          (mv answer fn2-fields)))
      answer)))

(assert-event
 (and (fn2-xru-test :ready) (fn2-xru-test :bad-trailer) (fn2-xru-test :trailing)
      (fn2-xru-test :wrong-owner) (fn2-xru-test :wrong-verb)
      (fn2-xru-test :staged-ready) (fn2-xru-test :staged-bad-trailer)))
