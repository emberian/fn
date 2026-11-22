; Outbound requests for the protected NNTP XFNC carrier.
(in-package "ACL2")
(include-book "xfnc-request-layout")
(include-book "pool-ranges")
(fn2-book-layer :e)

(local (in-theory (disable fn2-fieldsp fn2-fields-wfp fn2-fields-rows
                           fn2-poolp fn2-pool-wfp fn2-pool-rows
                           fn2-digestsp fn2-digests-wfp fn2-digests-rows
                           fn2-b3p fn2-b3-wfp fn2-b3-rows)))

(defconst *fn2-pull-register-binding* (fn2-consumer-remote-binding 'register))
(defconst *fn2-pull-read-binding* (fn2-consumer-remote-binding 'read))
(defconst *fn2-pull-history*
  (position-eq :history
               (caddr (cadr (assoc-eq 'start (caddr (fn2-fnct-word-row :register-query *fn2-fnct-codes*)))))))

(defun fn2-peer-pull-request-roomp (base fn2-fields)
  (declare (xargs :stobjs fn2-fields :guard (fn2-fields-wfp fn2-fields)))
  (and (natp base)
       (<= (+ base (max *fn2-fnct-header-num-fields*
                        *fn2-xfnc-stream-name-num-fields*
                        *fn2-fnct-k4-register-query-num-fields*
                        *fn2-fnct-k4-read-num-fields*))
           (fn2-fields-rows fn2-fields))))

(defun fn2-peer-pull-stage-register (base consumer secret sgen stream-len tx tgen kind owner generation fn2-fields fn2-pool)
  (declare (xargs :stobjs (fn2-fields fn2-pool)
                  :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool)
                              (fn2-peer-pull-request-roomp base fn2-fields))))
  (b* (((unless (and (posp consumer) (unsigned-byte-p 60 consumer)
                    (not (equal secret tx)) (posp stream-len) (<= stream-len 64)
                    (fn2-fnct-handlep secret sgen 0 stream-len)
                    (fn2-fnct-handlep tx tgen 0 (+ 1 stream-len))))
        (mv :bounds fn2-fields fn2-pool))
       (width (fn2-fnct-be-width consumer))
       ((unless (and (posp width) (<= width 8))) (mv :bounds fn2-fields fn2-pool))
       ((mv code fn2-pool) (fn2-fnct-put-be 0 consumer width tx tgen kind owner generation fn2-pool))
       ((unless (eq code :ok)) (mv code fn2-fields fn2-pool))
       (fn2-fields (fn2-fnct-set-ref (+ base *fn2-xfnc-stream-name-field-name*)
                                    secret sgen 0 stream-len fn2-fields))
       ((mv code end fn2-pool)
        (fn2-xfnc-stream-name-encode base tx tgen width kind owner generation fn2-fields fn2-pool))
       ((unless (and (eq code :ok) (equal end (+ width 1 stream-len))))
        (mv :frame fn2-fields fn2-pool))
       (fn2-fields (fn2-fields-set-value (+ base *fn2-fnct-k4-register-query-field-code*)
                                         (cadr *fn2-pull-register-binding*) fn2-fields))
       (fn2-fields (fn2-fnct-set-ref (+ base *fn2-fnct-k4-register-query-field-consumer*)
                                    tx tgen 0 width fn2-fields))
       (fn2-fields (fn2-fnct-set-ref (+ base *fn2-fnct-k4-register-query-field-streams*)
                                    tx tgen width (+ 1 stream-len) fn2-fields))
       (fn2-fields (fn2-fields-set-value (+ base *fn2-fnct-k4-register-query-field-start*)
                                         *fn2-pull-history* fn2-fields)))
    (mv :ok fn2-fields fn2-pool)))
(fn2-pool-block-shape fn2-peer-pull-stage-register-shape
  (fn2-peer-pull-stage-register base consumer secret sgen stream-len tx tgen kind owner generation fn2-fields fn2-pool)
  (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
       (fn2-peer-pull-request-roomp base fn2-fields))
  ((fn2-fields 1) (fn2-pool 2))
  (("Goal" :in-theory (enable fn2-peer-pull-stage-register))))
(in-theory (disable fn2-peer-pull-stage-register))

(defun fn2-peer-pull-stage-read (base private pgen cursor-off cursor-len max-items max-octets tx fn2-fields)
  (declare (xargs :stobjs fn2-fields
                  :guard (and (fn2-fields-wfp fn2-fields) (fn2-peer-pull-request-roomp base fn2-fields))))
  (b* (((unless (and (not (equal private tx)) (posp cursor-len) (<= cursor-len 366)
                    (fn2-fnct-handlep private pgen cursor-off cursor-len)
                    (posp max-items) (unsigned-byte-p 32 max-items)
                    (posp max-octets) (unsigned-byte-p 32 max-octets)))
        (mv :bounds fn2-fields))
       (fn2-fields (fn2-fields-set-value (+ base *fn2-fnct-k4-read-field-code*)
                                         (cadr *fn2-pull-read-binding*) fn2-fields))
       (fn2-fields (fn2-fnct-set-ref (+ base *fn2-fnct-k4-read-field-cursor*)
                                    private pgen cursor-off cursor-len fn2-fields))
       (fn2-fields (fn2-fields-set-value (+ base *fn2-fnct-k4-read-field-max-items*) max-items fn2-fields))
       (fn2-fields (fn2-fields-set-value (+ base *fn2-fnct-k4-read-field-max-octets*) max-octets fn2-fields)))
    (mv :ok fn2-fields)))
(fn2-pool-block-shape fn2-peer-pull-stage-read-shape
  (fn2-peer-pull-stage-read base private pgen cursor-off cursor-len max-items max-octets tx fn2-fields)
  (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
       (fn2-peer-pull-request-roomp base fn2-fields))
  ((fn2-fields 1))
  (("Goal" :in-theory (enable fn2-peer-pull-stage-read))))
(in-theory (disable fn2-peer-pull-stage-read))

(defun fn2-peer-pull-put-count (count tx tgen kind owner generation fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp count))))
  (b* (((mv code fn2-pool) (fn2-pool-append-text 0 "XFNC " tx tgen kind owner generation fn2-pool))
       ((unless (eq code :ok)) (mv code fn2-pool))
       (digits (coerce (explode-nonnegative-integer count 10 nil) 'string))
       ((mv code fn2-pool) (fn2-pool-append-text 0 digits tx tgen kind owner generation fn2-pool))
       ((unless (eq code :ok)) (mv code fn2-pool)))
    (fn2-fnct-put-be 0 #x0d0a 2 tx tgen kind owner generation fn2-pool)))
(fn2-pool-preserves fn2-peer-pull-put-count (count tx tgen kind owner generation fn2-pool) :position 1)
(in-theory (disable fn2-peer-pull-put-count))

; The temporary REGISTER consumer and encoded name precede the command.
; Their references stay disjoint from the generated K4 encoder's output.
(defun fn2-peer-pull-seal-request (registerp base row tx tgen kind owner generation fn2-fields fn2-digests fn2-b3 fn2-pool)
  (declare (xargs :stobjs (fn2-fields fn2-digests fn2-b3 fn2-pool)
                  :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool)
                              (fn2-peer-pull-request-roomp base fn2-fields))))
  (b* ((start (fn2-pool-fill-value tx fn2-pool))
       (size (if registerp (fn2-fnct-k4-register-query-size base fn2-fields)
               (fn2-fnct-k4-read-size base fn2-fields)))
       ((unless (and (posp size)
                     (<= size (if registerp *fn2-xfnc-register-body-max* *fn2-xfnc-read-body-max*))))
        (mv :size fn2-fields fn2-digests fn2-b3 fn2-pool))
       (count (+ size *fn2-fnct-overhead*))
       ((mv code fn2-pool) (fn2-peer-pull-put-count count tx tgen kind owner generation fn2-pool))
       ((unless (eq code :ok)) (mv code fn2-fields fn2-digests fn2-b3 fn2-pool))
       (frame (fn2-pool-fill-value tx fn2-pool))
       ((mv code fn2-pool) (fn2-fnct-put-be 0 0 *fn2-fnct-header-octets* tx tgen kind owner generation fn2-pool))
       ((unless (eq code :ok)) (mv code fn2-fields fn2-digests fn2-b3 fn2-pool))
       (body (+ frame *fn2-fnct-header-octets*))
       ((mv code end fn2-pool)
        (if registerp
            (fn2-fnct-k4-register-query-encode base tx tgen body kind owner generation fn2-fields fn2-pool)
          (fn2-fnct-k4-read-encode base tx tgen body kind owner generation fn2-fields fn2-pool)))
       ((unless (and (eq code :ok) (equal end (+ body size))))
        (mv :frame fn2-fields fn2-digests fn2-b3 fn2-pool))
       ((mv code actual fn2-fields fn2-digests fn2-b3 fn2-pool)
        (fn2-fnct-seal-pool base row frame
                            (if registerp (car *fn2-pull-register-binding*) (car *fn2-pull-read-binding*))
                            tx tgen kind owner generation fn2-fields fn2-digests fn2-b3 fn2-pool))
       ((unless (and (eq code :ok) (equal count actual)))
        (mv :frame fn2-fields fn2-digests fn2-b3 fn2-pool))
       ((when (zp start)) (mv :ok fn2-fields fn2-digests fn2-b3 fn2-pool))
       ((mv code & fn2-pool)
        (fn2-pool-drop-prefix tx tgen start 0 *fn2-pool-block-bytes* kind owner generation fn2-pool)))
    (mv code fn2-fields fn2-digests fn2-b3 fn2-pool)))
(fn2-pool-block-shape fn2-peer-pull-seal-request-shape
  (fn2-peer-pull-seal-request registerp base row tx tgen kind owner generation fn2-fields fn2-digests fn2-b3 fn2-pool)
  (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
       (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests) (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3)
       (fn2-peer-pull-request-roomp base fn2-fields))
  ((fn2-fields 1) (fn2-digests 2) (fn2-b3 3) (fn2-pool 4))
  (("Goal" :in-theory (e/d (fn2-peer-pull-seal-request) (fn2-peer-pull-request-roomp)))))
(in-theory (disable fn2-peer-pull-seal-request))

; Caller owns the authenticated actor and checkpoints its source handles.
; A staged error resets TX without taking a transport borrow.
(defun fn2-peer-pull-encode-request (registerp base row consumer source sgen off len max-items max-octets
                                     tx tgen kind owner generation fn2-fields fn2-digests fn2-b3 fn2-pool)
  (declare (xargs :stobjs (fn2-fields fn2-digests fn2-b3 fn2-pool)
                  :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
  (b* (((unless (and (fn2-peer-pull-request-roomp base fn2-fields)
                    (eq :ok (fn2-pool-workspace-code tx tgen kind owner generation fn2-pool))
                    (zp (fn2-pool-fill-value tx fn2-pool))))
        (mv :state fn2-fields fn2-digests fn2-b3 fn2-pool))
       ((mv stage fn2-fields fn2-pool)
        (if registerp
            (fn2-peer-pull-stage-register base consumer source sgen len tx tgen kind owner generation fn2-fields fn2-pool)
          (mv-let (code fn2-fields)
            (fn2-peer-pull-stage-read base source sgen off len max-items max-octets tx fn2-fields)
            (mv code fn2-fields fn2-pool))))
       ((mv code fn2-fields fn2-digests fn2-b3 fn2-pool)
        (if (eq stage :ok)
            (fn2-peer-pull-seal-request registerp base row tx tgen kind owner generation fn2-fields fn2-digests fn2-b3 fn2-pool)
          (mv stage fn2-fields fn2-digests fn2-b3 fn2-pool)))
       ((when (eq code :ok)) (mv code fn2-fields fn2-digests fn2-b3 fn2-pool))
       ((mv reset fn2-pool) (fn2-pool-reset tx tgen kind owner generation fn2-pool)))
    (mv (if (eq reset :ok) code :state) fn2-fields fn2-digests fn2-b3 fn2-pool)))
(fn2-pool-block-shape fn2-peer-pull-encode-request-shape
  (fn2-peer-pull-encode-request registerp base row consumer source sgen off len max-items max-octets
                               tx tgen kind owner generation fn2-fields fn2-digests fn2-b3 fn2-pool)
  (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
       (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests) (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3))
  ((fn2-fields 1) (fn2-digests 2) (fn2-b3 3) (fn2-pool 4))
  (("Goal" :in-theory (e/d (fn2-peer-pull-encode-request) (fn2-peer-pull-request-roomp)))))
(in-theory (disable fn2-peer-pull-encode-request))

(defun fn2-peer-pull-encode-register (base row consumer secret sgen stream-len tx tgen kind owner generation
                                      fn2-fields fn2-digests fn2-b3 fn2-pool)
  (declare (xargs :stobjs (fn2-fields fn2-digests fn2-b3 fn2-pool)
                  :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
  (fn2-peer-pull-encode-request t base row consumer secret sgen 0 stream-len 0 0
                               tx tgen kind owner generation fn2-fields fn2-digests fn2-b3 fn2-pool))

(defun fn2-peer-pull-encode-read (base row private pgen cursor-off cursor-len max-items max-octets
                                 tx tgen kind owner generation fn2-fields fn2-digests fn2-b3 fn2-pool)
  (declare (xargs :stobjs (fn2-fields fn2-digests fn2-b3 fn2-pool)
                  :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
  (fn2-peer-pull-encode-request nil base row 0 private pgen cursor-off cursor-len max-items max-octets
                               tx tgen kind owner generation fn2-fields fn2-digests fn2-b3 fn2-pool))

