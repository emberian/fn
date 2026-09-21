; Outbound BP lifecycle: durable queue, contact, attempt and restart.
;
; This is the bounded first processing-machine slice from specs/bp-design.md
; sections 1.5 and 1.6.  The host calls fn-bpn-step.  It may observe time,
; sockets and persistence outcomes, but it does not decide queue admission,
; retry, expiry or what bytes are sent.
;
; The creation-timestamp sequence is an input that has already crossed the
; separate durable FNBS sequence frontier.  This book neither allocates nor
; replays that frontier.  A restart whose sequence dependency is not ready is
; fenced before lifecycle replay.

(in-package "ACL2")
(include-book "bp-node")
(include-book "defrecord")
(include-book "frame-fields")

(defconst *fn-bpn-machine-max-jobs* 64)
(defconst *fn-bpn-machine-max-octets* 16777216)
(defconst *fn-bpn-machine-max-job-octets* *fn-frame-max-blob*)
(defconst *fn-bpn-machine-max-records* 4096)

(defun fn-bpn-machine-u64p (x)
  (declare (xargs :guard t))
  (and (natp x) (< x 18446744073709551616)))

(defun fn-bpn-machine-textp (x)
  (declare (xargs :guard t))
  (fn-frame-textp x))

(defun fn-bpn-routep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 7) (equal (car x) :route)
       (fn-bpn-machine-textp (nth 1 x))
       (natp (nth 2 x)) (< 0 (nth 2 x)) (<= (nth 2 x) 65535)
       (fn-bpn-machine-textp (nth 3 x))
       (fn-bpn-machine-u64p (nth 4 x))
       (fn-bpn-machine-u64p (nth 5 x))
       (fn-bpn-machine-u64p (nth 6 x))))

(defun fn-bpn-member (x xs)
  (declare (xargs :guard t))
  (if (atom xs)
      nil
    (or (equal x (car xs))
        (fn-bpn-member x (cdr xs)))))

(defun fn-bpn-append (xs ys)
  (declare (xargs :guard t))
  (if (atom xs)
      ys
    (cons (car xs) (fn-bpn-append (cdr xs) ys))))

(defun fn-bpn-nth (n xs)
  (declare (xargs :guard t))
  (if (or (not (natp n)) (zp n) (atom xs))
      (fn-cbor-ag-car xs)
    (fn-bpn-nth (1- n) (cdr xs))))

(defun fn-bpn-job-statusp (x)
  (declare (xargs :guard t))
  (fn-bpn-member x '(:queued :attempting :forwarded :expired)))

(fn-defrecord fn-bpn-job
  :tag :fn-bpn-job
  :constructor (fn-bpn-make-job work-id attempt-id generation sequence age-anchor peer
                                route bundle wire status last-token)
  :fields ((fn-bpn-job-work-id fn-bpn-machine-textp)
           (fn-bpn-job-attempt-id fn-bpn-machine-textp)
           (fn-bpn-job-generation fn-bpn-machine-u64p)
           (fn-bpn-job-sequence fn-bpp-timep)
           (fn-bpn-job-age-anchor fn-clock-age-anchorp)
           (fn-bpn-job-peer fn-bpp-eidp)
           (fn-bpn-job-route fn-bpn-routep)
           (fn-bpn-job-bundle fn-bpb-bundlep)
           (fn-bpn-job-wire fn-cbor-octet-listp)
           (fn-bpn-job-status fn-bpn-job-statusp)
           (fn-bpn-job-last-token fn-bpn-machine-u64p))
  :car-fn fn-cbor-ag-car
  :cdr-fn fn-cbor-ag-cdr)

(defun fn-bpn-job-key (job)
  (declare (xargs :guard t))
  (list (fn-bpn-job-work-id job)
        (fn-bpn-job-attempt-id job)
        (fn-bpn-job-generation job)))

(defun fn-bpn-keyp (key)
  (declare (xargs :guard t))
  (and (true-listp key) (equal (len key) 3)
       (fn-bpn-machine-textp (nth 0 key))
       (fn-bpn-machine-textp (nth 1 key))
       (fn-bpn-machine-u64p (nth 2 key))))

(defun fn-bpn-job-with-status (job status token)
  (declare (xargs :guard t))
  (fn-bpn-make-job
   (fn-bpn-job-work-id job) (fn-bpn-job-attempt-id job)
   (fn-bpn-job-generation job) (fn-bpn-job-sequence job)
   (fn-bpn-job-age-anchor job) (fn-bpn-job-peer job) (fn-bpn-job-route job)
   (fn-bpn-job-bundle job) (fn-bpn-job-wire job)
   status token))

(defun fn-bpn-find-job (key jobs)
  (declare (xargs :guard t))
  (if (atom jobs)
      nil
    (if (equal key (fn-bpn-job-key (car jobs)))
        (car jobs)
      (fn-bpn-find-job key (cdr jobs)))))

(defun fn-bpn-job-key-memberp (key jobs)
  (declare (xargs :guard t))
  (and (fn-bpn-find-job key jobs) t))

(defun fn-bpn-job-listp (jobs)
  (declare (xargs :guard t))
  (if (atom jobs)
      (null jobs)
    (and (fn-bpn-jobp (car jobs))
         (not (fn-bpn-job-key-memberp (fn-bpn-job-key (car jobs)) (cdr jobs)))
         (fn-bpn-job-listp (cdr jobs)))))

(defun fn-bpn-replace-job (key replacement jobs)
  (declare (xargs :guard t))
  (if (atom jobs)
      nil
    (if (equal key (fn-bpn-job-key (car jobs)))
        (cons replacement (cdr jobs))
      (cons (car jobs) (fn-bpn-replace-job key replacement (cdr jobs))))))

(defun fn-bpn-jobs-octets (jobs)
  (declare (xargs :guard t))
  (if (atom jobs)
      0
    (+ (len (fn-bpn-job-wire (car jobs)))
       (fn-bpn-jobs-octets (cdr jobs)))))

(defun fn-bpn-contact-listp (contacts)
  (declare (xargs :guard t))
  (if (atom contacts)
      (null contacts)
    (and (fn-bpp-eidp (car contacts))
         (not (fn-bpn-member (car contacts) (cdr contacts)))
         (fn-bpn-contact-listp (cdr contacts)))))

(defun fn-bpn-contact-openp (peer contacts)
  (declare (xargs :guard t))
  (and (fn-bpn-member peer contacts) t))

(defun fn-bpn-open-contact (peer contacts)
  (declare (xargs :guard t))
  (if (fn-bpn-contact-openp peer contacts) contacts (cons peer contacts)))

(defun fn-bpn-close-contact (peer contacts)
  (declare (xargs :guard t))
  (if (atom contacts)
      nil
    (if (equal peer (car contacts))
        (fn-bpn-close-contact peer (cdr contacts))
      (cons (car contacts) (fn-bpn-close-contact peer (cdr contacts))))))

(defun fn-bpn-effectp (effect)
  (declare (xargs :guard t))
  (and (true-listp effect)
       (fn-bpn-member (car effect)
                  '(:persist :bundle-queue-accepted :bundle-queue-refused
                    :bundle-queue-uncertain :cl-send :transport
                    :forward-refused :restart-ready :restart-fault))))

(defun fn-bpn-effect-listp (effects)
  (declare (xargs :guard t))
  (if (atom effects)
      (null effects)
    (and (fn-bpn-effectp (car effects))
         (fn-bpn-effect-listp (cdr effects)))))

(defun fn-bpn-record-kindp (x)
  (declare (xargs :guard t))
  (fn-bpn-member x '(:queued :attempting :requeued :finished :expired)))

(defun fn-bpn-lifecycle-recordp (record)
  (declare (xargs :guard t :verify-guards nil))
  (let ((kind (fn-cbor-ag-car record)))
    (cond
     ((equal kind :queued)
      (and (true-listp record) (equal (len record) 3)
           (fn-bpn-machine-u64p (nth 1 record))
           (fn-bpn-jobp (nth 2 record))
           (equal (fn-bpn-job-status (nth 2 record)) :queued)
           (equal (fn-bpn-job-last-token (nth 2 record)) (nth 1 record))
           (<= (len (fn-bpn-job-wire (nth 2 record)))
               *fn-bpn-machine-max-job-octets*)
           (equal (fn-bpn-job-wire (nth 2 record))
                  (fn-bpb-encode (fn-bpn-job-bundle (nth 2 record))))
           (equal (fn-bpn-job-peer (nth 2 record))
                  (fn-bpp-destination
                   (fn-bpb-bundle-primary (fn-bpn-job-bundle (nth 2 record)))))))
     ((equal kind :attempting)
      (and (true-listp record) (equal (len record) 5)
           (fn-bpn-machine-u64p (nth 1 record))
           (fn-bpn-machine-textp (nth 2 record))
           (fn-bpn-machine-textp (nth 3 record))
           (fn-bpn-machine-u64p (nth 4 record))))
     ((fn-bpn-member kind '(:requeued :finished :expired))
      (and (true-listp record) (equal (len record) 7)
           (fn-bpn-machine-u64p (nth 1 record))
           (fn-bpn-machine-textp (nth 2 record))
           (fn-bpn-machine-textp (nth 3 record))
           (fn-bpn-machine-u64p (nth 4 record))
           (if (equal kind :requeued)
               (fn-bpn-member (nth 5 record) '(:refused :failed :uncertain))
             (equal (nth 5 record) :none))
           (equal (nth 6 record) kind)))
     (t nil))))

(defun fn-bpn-record-token (record)
  (declare (xargs :guard t))
  (fn-bpn-nth 1 record))

(defun fn-bpn-record-key (record)
  (declare (xargs :guard t))
  (if (equal (fn-cbor-ag-car record) :queued)
      (fn-bpn-job-key (fn-bpn-nth 2 record))
    (list (fn-bpn-nth 2 record) (fn-bpn-nth 3 record)
          (fn-bpn-nth 4 record))))

(fn-defrecord fn-bpn-pending
  :tag :fn-bpn-pending
  :constructor (fn-bpn-make-pending token record success-effects
                                    refusal-effect uncertainty-effect)
  :fields ((fn-bpn-pending-token fn-bpn-machine-u64p)
           (fn-bpn-pending-record fn-bpn-lifecycle-recordp)
           (fn-bpn-pending-success-effects fn-bpn-effect-listp)
           (fn-bpn-pending-refusal-effect fn-bpn-effectp)
           (fn-bpn-pending-uncertainty-effect fn-bpn-effectp))
  :recognizer-verify-guards nil
  :car-fn fn-cbor-ag-car
  :cdr-fn fn-cbor-ag-cdr)

(defun fn-bpn-maybe-pendingp (x)
  (declare (xargs :guard t :verify-guards nil))
  (or (null x) (fn-bpn-pendingp x)))

(defun fn-bpn-machine-boolp (x)
  (declare (xargs :guard t))
  (or (equal x t) (equal x nil)))

(defun fn-bpn-machine-limitp (x)
  (declare (xargs :guard t))
  (and (posp x) (<= x 16777216)))

(fn-defrecord fn-bpn-machine-state
  :tag :fn-bpn-machine-state
  :constructor (fn-bpn-make-machine-state config jobs contacts pending fenced
                                          next-token max-jobs max-octets)
  :fields ((fn-bpn-machine-state-config fn-bpn-configp)
           (fn-bpn-machine-state-jobs fn-bpn-job-listp)
           (fn-bpn-machine-state-contacts fn-bpn-contact-listp)
           (fn-bpn-machine-state-pending fn-bpn-maybe-pendingp)
           (fn-bpn-machine-state-fenced fn-bpn-machine-boolp)
           (fn-bpn-machine-state-next-token fn-bpn-machine-u64p)
           (fn-bpn-machine-state-max-jobs fn-bpn-machine-limitp)
           (fn-bpn-machine-state-max-octets fn-bpn-machine-limitp))
  :recognizer fn-bpn-machine-recordp
  :recognizer-verify-guards nil
  :car-fn fn-cbor-ag-car
  :cdr-fn fn-cbor-ag-cdr)

(defun fn-bpn-machine-statep (st)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-bpn-machine-recordp st)
       (<= (len (fn-bpn-machine-state-jobs st))
           (fn-bpn-machine-state-max-jobs st))
       (<= (fn-bpn-jobs-octets (fn-bpn-machine-state-jobs st))
           (fn-bpn-machine-state-max-octets st))
       (or (null (fn-bpn-machine-state-pending st))
           (equal (fn-bpn-pending-token (fn-bpn-machine-state-pending st))
                  (fn-bpn-machine-state-next-token st)))))

(defun fn-bpn-existing-sequence (st key)
  (declare (xargs :guard t :verify-guards nil))
  (let ((job (fn-bpn-find-job key (fn-bpn-machine-state-jobs st))))
    (if (and (fn-bpn-machine-statep st) (fn-bpn-keyp key) job)
        (list :existing (fn-bpn-job-sequence job))
      (list :absent))))

(defun fn-bpn-existing-sequencep (answer)
  (declare (xargs :guard t))
  (and (true-listp answer) (equal (len answer) 2)
       (equal (car answer) :existing)
       (fn-bpp-timep (nth 1 answer))))

(fn-defrecord fn-bpn-answer
  :tag :fn-bpn-answer
  :constructor (fn-bpn-answer st effects)
  :fields ((fn-bpn-answer-state fn-bpn-machine-statep)
           (fn-bpn-answer-effects fn-bpn-effect-listp))
  :recognizer-verify-guards nil
  :car-fn fn-cbor-ag-car
  :cdr-fn fn-cbor-ag-cdr)

; The transition layer is total and deliberately accepts malformed host events
; so it can refuse them in the logic.  Its raw execution is reached through
; the validating host facade below; keep admission separate from raw guards.
(set-verify-guards-eagerness 0)

(defun fn-bpn-initial-machine-state (config max-jobs max-octets)
  (declare (xargs :guard t))
  (if (and (fn-bpn-configp config)
           (fn-bpn-machine-limitp max-jobs)
           (fn-bpn-machine-limitp max-octets))
      (fn-bpn-make-machine-state config nil nil nil nil 0 max-jobs max-octets)
    nil))

(defun fn-bpn-state-with (st jobs contacts pending fenced next-token)
  (declare (xargs :guard t))
  (fn-bpn-make-machine-state
   (fn-bpn-machine-state-config st) jobs contacts pending fenced next-token
   (fn-bpn-machine-state-max-jobs st) (fn-bpn-machine-state-max-octets st)))

(defun fn-bpn-record-applicablep (st record)
  (declare (xargs :guard t))
  (let* ((kind (fn-cbor-ag-car record))
         (key (fn-bpn-record-key record))
         (job (fn-bpn-find-job key (fn-bpn-machine-state-jobs st))))
    (and (fn-bpn-lifecycle-recordp record)
         (equal (fn-bpn-record-token record)
                (fn-bpn-machine-state-next-token st))
         (cond
          ((equal kind :queued)
           (and (not job)
                (< (len (fn-bpn-machine-state-jobs st))
                   (fn-bpn-machine-state-max-jobs st))
                (<= (+ (fn-bpn-jobs-octets (fn-bpn-machine-state-jobs st))
                       (len (fn-bpn-job-wire (nth 2 record))))
                    (fn-bpn-machine-state-max-octets st))))
          ((equal kind :attempting)
           (and job (equal (fn-bpn-job-status job) :queued)))
          ((equal kind :requeued)
           (and job (equal (fn-bpn-job-status job) :attempting)))
          ((equal kind :finished)
           (and job (equal (fn-bpn-job-status job) :attempting)))
          ((equal kind :expired)
           (and job (fn-bpn-member (fn-bpn-job-status job) '(:queued :attempting))))
          (t nil)))))

(defun fn-bpn-apply-record (st record)
  (declare (xargs :guard t))
  (if (not (fn-bpn-record-applicablep st record))
      st
    (let* ((kind (fn-cbor-ag-car record))
           (token (fn-bpn-record-token record))
           (key (fn-bpn-record-key record))
           (jobs (fn-bpn-machine-state-jobs st))
           (job (fn-bpn-find-job key jobs))
           (next-jobs
            (cond ((equal kind :queued) (fn-bpn-append jobs (list (nth 2 record))))
                  ((equal kind :attempting)
                   (fn-bpn-replace-job key (fn-bpn-job-with-status job :attempting token) jobs))
                  ((equal kind :requeued)
                   (fn-bpn-replace-job key (fn-bpn-job-with-status job :queued token) jobs))
                  ((equal kind :finished)
                   (fn-bpn-replace-job key (fn-bpn-job-with-status job :forwarded token) jobs))
                  (t (fn-bpn-replace-job key (fn-bpn-job-with-status job :expired token) jobs)))))
      (fn-bpn-state-with st next-jobs (fn-bpn-machine-state-contacts st)
                         nil nil (1+ token)))))

(defun fn-bpn-propose (st record success refusal uncertain)
  (declare (xargs :guard t))
  (let ((token (fn-bpn-machine-state-next-token st)))
    (if (>= token *fn-bpn-machine-max-records*)
        (fn-bpn-answer st (list refusal))
      (let* ((pending (fn-bpn-make-pending token record success refusal uncertain))
             (next (fn-bpn-state-with st (fn-bpn-machine-state-jobs st)
                                      (fn-bpn-machine-state-contacts st)
                                      pending nil token)))
        (fn-bpn-answer next (list (list :persist token record)))))))

(defun fn-bpn-job-exactp (job sequence route peer bundle wire)
  (declare (xargs :guard t))
  (and (equal (fn-bpn-job-sequence job) sequence)
       (equal (fn-bpn-job-route job) route)
       (equal (fn-bpn-job-peer job) peer)
       (equal (fn-bpn-job-bundle job) bundle)
       (equal (fn-bpn-job-wire job) wire)))

(defun fn-bpn-enqueue-step (st work attempt generation sequence route peer adu obs)
  (declare (xargs :guard t))
  (let* ((key (list work attempt generation))
         (jobs (fn-bpn-machine-state-jobs st))
         (old (fn-bpn-find-job key jobs)))
    (cond
     ((or (fn-bpn-machine-state-fenced st) (fn-bpn-machine-state-pending st))
      (fn-bpn-answer st (list (list :bundle-queue-refused work attempt generation :busy))))
     ((not (and (fn-bpn-keyp key) (fn-bpp-timep sequence) (fn-bpn-routep route)
                (fn-bpp-eidp peer)
                (fn-bpb-datap adu) (fn-clock-observationp obs)))
      (fn-bpn-answer st (list (list :bundle-queue-refused work attempt generation :arguments))))
     (t
      (let* ((bundle (fn-bpn-send-bundle (fn-bpn-machine-state-config st)
                                         peer adu sequence obs))
             (wire (fn-bpn-send (fn-bpn-machine-state-config st)
                                peer adu sequence obs)))
        (cond
         ((and old (fn-bpn-job-exactp old sequence route peer bundle wire))
          (fn-bpn-answer st
                         (list (list :bundle-queue-accepted work attempt generation
                                     sequence :duplicate))))
         (old
          (fn-bpn-answer st
                         (list (list :bundle-queue-refused work attempt generation
                                     :enqueue-conflict))))
         ((or (>= (len jobs) (fn-bpn-machine-state-max-jobs st))
              (> (len wire) *fn-bpn-machine-max-job-octets*)
              (> (+ (fn-bpn-jobs-octets jobs) (len wire))
                 (fn-bpn-machine-state-max-octets st)))
          (fn-bpn-answer st
                         (list (list :bundle-queue-refused work attempt generation
                                     :capacity))))
         (t
          (let* ((token (fn-bpn-machine-state-next-token st))
                 (job (fn-bpn-make-job work attempt generation sequence
                                       (fn-bpn-anchor-of bundle obs) peer route
                                       bundle wire :queued token))
                 (record (list :queued token job)))
            (fn-bpn-propose
             st record
             (list (list :bundle-queue-accepted work attempt generation sequence :durable))
             (list :bundle-queue-refused work attempt generation :persistence-refused)
             (list :bundle-queue-uncertain work attempt generation :persistence))))))))))

(defun fn-bpn-find-queued-for-peer (peer jobs)
  (declare (xargs :guard t))
  (if (atom jobs)
      nil
    (if (and (equal (fn-bpn-job-status (car jobs)) :queued)
             (equal (fn-bpn-job-peer (car jobs)) peer))
        (car jobs)
      (fn-bpn-find-queued-for-peer peer (cdr jobs)))))

(defun fn-bpn-ready-peers (jobs)
  (declare (xargs :guard t))
  (if (atom jobs)
      nil
    (let ((rest (fn-bpn-ready-peers (cdr jobs))))
      (if (and (equal (fn-bpn-job-status (car jobs)) :queued)
               (not (fn-bpn-member (fn-bpn-job-peer (car jobs)) rest)))
          (cons (fn-bpn-job-peer (car jobs)) rest)
        rest))))

(defun fn-bpn-start-one (st peer)
  (declare (xargs :guard t))
  (let ((job (fn-bpn-find-queued-for-peer peer (fn-bpn-machine-state-jobs st))))
    (if (or (not job) (fn-bpn-machine-state-fenced st)
            (fn-bpn-machine-state-pending st)
            (not (fn-bpn-contact-openp peer (fn-bpn-machine-state-contacts st))))
        (fn-bpn-answer st nil)
      (let* ((token (fn-bpn-machine-state-next-token st))
             (key (fn-bpn-job-key job))
             (record (list :attempting token (nth 0 key) (nth 1 key) (nth 2 key))))
        (fn-bpn-propose
         st record
         (list (list :cl-send (fn-bpn-job-route job) peer key
                     (fn-bpn-job-wire job)))
         (list :bundle-queue-refused (nth 0 key) (nth 1 key) (nth 2 key)
               :attempt-persistence-refused)
         (list :bundle-queue-uncertain (nth 0 key) (nth 1 key) (nth 2 key)
               :attempt-persistence))))))

(defun fn-bpn-contact-step (st peer openp)
  (declare (xargs :guard t))
  (if (not (fn-bpp-eidp peer))
      (fn-bpn-answer st nil)
    (if openp
        (let ((opened (fn-bpn-state-with st (fn-bpn-machine-state-jobs st)
                                         (fn-bpn-open-contact peer
                                                              (fn-bpn-machine-state-contacts st))
                                         (fn-bpn-machine-state-pending st)
                                         (fn-bpn-machine-state-fenced st)
                                         (fn-bpn-machine-state-next-token st))))
          (fn-bpn-start-one opened peer))
      (fn-bpn-answer
       (fn-bpn-state-with st (fn-bpn-machine-state-jobs st)
                          (fn-bpn-close-contact peer (fn-bpn-machine-state-contacts st))
                          (fn-bpn-machine-state-pending st)
                          (fn-bpn-machine-state-fenced st)
                          (fn-bpn-machine-state-next-token st))
       nil))))

(defun fn-bpn-persist-result-step (st token outcome)
  (declare (xargs :guard t))
  (let ((pending (fn-bpn-machine-state-pending st)))
    (if (or (not pending) (not (equal token (fn-bpn-pending-token pending))))
        (fn-bpn-answer st nil)
      (cond
       ((equal outcome :durable)
        (let ((next (fn-bpn-apply-record st (fn-bpn-pending-record pending))))
          (if (equal next st)
              (fn-bpn-answer
               (fn-bpn-state-with st (fn-bpn-machine-state-jobs st)
                                  (fn-bpn-machine-state-contacts st) nil t
                                  (fn-bpn-machine-state-next-token st))
               (list (fn-bpn-pending-uncertainty-effect pending)))
            (fn-bpn-answer next (fn-bpn-pending-success-effects pending)))))
       ((equal outcome :refused)
        (fn-bpn-answer
         (fn-bpn-state-with st (fn-bpn-machine-state-jobs st)
                            (fn-bpn-machine-state-contacts st) nil nil
                            (fn-bpn-machine-state-next-token st))
         (list (fn-bpn-pending-refusal-effect pending))))
       (t
        (fn-bpn-answer
         (fn-bpn-state-with st (fn-bpn-machine-state-jobs st)
                            (fn-bpn-machine-state-contacts st) nil t
                            (fn-bpn-machine-state-next-token st))
         (list (fn-bpn-pending-uncertainty-effect pending))))))))

(defun fn-bpn-forward-result-step (st key outcome)
  (declare (xargs :guard t))
  (let ((job (fn-bpn-find-job key (fn-bpn-machine-state-jobs st))))
    (if (or (fn-bpn-machine-state-fenced st) (fn-bpn-machine-state-pending st)
            (not job) (not (equal (fn-bpn-job-status job) :attempting)))
        (fn-bpn-answer st nil)
      (let* ((token (fn-bpn-machine-state-next-token st))
             (work (nth 0 key)) (attempt (nth 1 key)) (generation (nth 2 key)))
        (if (equal outcome :accepted)
            (fn-bpn-propose
             st (list :finished token work attempt generation :none :finished)
             (list (list :transport work attempt generation :forwarded))
             (list :bundle-queue-refused work attempt generation :result-persistence-refused)
             (list :bundle-queue-uncertain work attempt generation :result-persistence))
          (let ((reason (if (equal outcome :refused) :refused
                          (if (equal outcome :uncertain) :uncertain :failed))))
            (fn-bpn-propose
             st (list :requeued token work attempt generation reason :requeued)
             (list (list :transport work attempt generation :attempted)
                   (list :forward-refused work attempt generation reason))
             (list :bundle-queue-refused work attempt generation :result-persistence-refused)
             (list :bundle-queue-uncertain work attempt generation :result-persistence))))))))

(defun fn-bpn-job-expiry (job obs)
  (declare (xargs :guard t))
  (if (and (fn-bpn-jobp job) (fn-clock-observationp obs))
      (let ((primary (fn-bpb-bundle-primary (fn-bpn-job-bundle job))))
        (fn-clock-expiry-decision
         (fn-bpp-creation-time primary)
         (fn-bpp-lifetime primary)
         (fn-bpn-job-age-anchor job)
         obs))
    :uncertain))

(defun fn-bpn-find-expired (jobs obs)
  (declare (xargs :guard t))
  (if (atom jobs)
      nil
    (if (and (fn-bpn-member (fn-bpn-job-status (car jobs)) '(:queued :attempting))
             (equal (fn-bpn-job-expiry (car jobs) obs) :expired))
        (car jobs)
      (fn-bpn-find-expired (cdr jobs) obs))))

(defun fn-bpn-clock-step (st obs)
  (declare (xargs :guard t))
  (let ((job (and (fn-clock-observationp obs)
                  (fn-bpn-find-expired (fn-bpn-machine-state-jobs st) obs))))
    (if (or (fn-bpn-machine-state-fenced st) (fn-bpn-machine-state-pending st)
            (not job))
        (fn-bpn-answer st nil)
      (let* ((token (fn-bpn-machine-state-next-token st))
             (key (fn-bpn-job-key job)))
        (fn-bpn-propose
         st (list :expired token (nth 0 key) (nth 1 key) (nth 2 key) :none :expired)
         (list (list :transport (nth 0 key) (nth 1 key) (nth 2 key) :expired))
         (list :bundle-queue-refused (nth 0 key) (nth 1 key) (nth 2 key)
               :expiry-persistence-refused)
         (list :bundle-queue-uncertain (nth 0 key) (nth 1 key) (nth 2 key)
               :expiry-persistence))))))

(defun fn-bpn-resume-jobs (jobs)
  (declare (xargs :guard t))
  (if (atom jobs)
      nil
    (cons (if (equal (fn-bpn-job-status (car jobs)) :attempting)
              (fn-bpn-job-with-status (car jobs) :queued
                                      (fn-bpn-job-last-token (car jobs)))
            (car jobs))
          (fn-bpn-resume-jobs (cdr jobs)))))

(defun fn-bpn-replay-records (st records)
  (declare (xargs :guard t :measure (acl2-count records)))
  (if (atom records)
      (if (null records) (list :ready st) (list :fault st :improper-record-list))
    (if (not (fn-bpn-record-applicablep st (car records)))
        (list :fault st :lifecycle-record)
      (fn-bpn-replay-records (fn-bpn-apply-record st (car records)) (cdr records)))))

(defun fn-bpn-restart-step (st records sequence-ready)
  (declare (xargs :guard t))
  (let ((base (fn-bpn-initial-machine-state
               (fn-bpn-machine-state-config st)
               (fn-bpn-machine-state-max-jobs st)
               (fn-bpn-machine-state-max-octets st))))
    (if (not (equal sequence-ready :ready))
        (fn-bpn-answer
         (fn-bpn-state-with base nil nil nil t 0)
         (list (list :restart-fault :sequence-frontier)))
      (let ((replay (fn-bpn-replay-records base records)))
        (if (equal (car replay) :ready)
            (let* ((replayed (nth 1 replay))
                   (resumed (fn-bpn-state-with
                             replayed
                             (fn-bpn-resume-jobs (fn-bpn-machine-state-jobs replayed))
                             nil nil nil (fn-bpn-machine-state-next-token replayed))))
              (fn-bpn-answer resumed
                             (list (list :restart-ready
                                         (len (fn-bpn-machine-state-jobs resumed))))))
          (let ((prefix (nth 1 replay)))
            (fn-bpn-answer
             (fn-bpn-state-with prefix (fn-bpn-machine-state-jobs prefix)
                                nil nil t (fn-bpn-machine-state-next-token prefix))
             (list (list :restart-fault (nth 2 replay))))))))))

(defun fn-bpn-eventp (event)
  (declare (xargs :guard t))
  (and (true-listp event)
       (fn-bpn-member (car event)
                  '(:enqueue :contact :resume :persist-result :forward-result
                    :clock :restart))))

(defun fn-bpn-event-listp (events)
  (declare (xargs :guard t))
  (if (atom events)
      (null events)
    (and (fn-bpn-eventp (car events))
         (fn-bpn-event-listp (cdr events)))))

(defun fn-bpn-step (st event)
  (declare (xargs :guard t))
  (if (not (fn-bpn-machine-statep st))
      (fn-bpn-answer st nil)
    (case (car event)
      (:enqueue
       (fn-bpn-enqueue-step st (nth 1 event) (nth 2 event) (nth 3 event)
                            (nth 4 event) (nth 5 event) (nth 6 event)
                            (nth 7 event) (nth 8 event)))
      (:contact (fn-bpn-contact-step st (nth 1 event) (nth 2 event)))
      (:resume (fn-bpn-start-one st (nth 1 event)))
      (:persist-result (fn-bpn-persist-result-step st (nth 1 event) (nth 2 event)))
      (:forward-result (fn-bpn-forward-result-step st (nth 1 event) (nth 2 event)))
      (:clock (fn-bpn-clock-step st (nth 1 event)))
      (:restart (fn-bpn-restart-step st (nth 1 event) (nth 2 event)))
      (otherwise (fn-bpn-answer st nil)))))

(defun fn-bpn-trace (st events)
  (declare (xargs :guard t))
  (if (atom events)
      st
    (fn-bpn-trace (fn-bpn-answer-state (fn-bpn-step st (car events)))
                  (cdr events))))

(defun fn-bpn-effect-kind-memberp (kind effects)
  (declare (xargs :guard t))
  (if (atom effects)
      nil
    (or (equal kind (car (car effects)))
        (fn-bpn-effect-kind-memberp kind (cdr effects)))))

; KEYSTONE M1.  This layer has no effect spelling that can discharge an fn
; archive or forward undertaking.  TCPCL completion is only a transport fact.
(defthm fn-bpn-effectp-excludes-release
  (implies (fn-bpn-effectp effect)
           (not (equal (fn-cbor-ag-car effect) :release))))

(defthm fn-bpn-effect-listp-excludes-release
  (implies (fn-bpn-effect-listp effects)
           (not (fn-bpn-effect-kind-memberp :release effects))))

(defthm fn-bpn-step-emits-no-release
  (implies (fn-bpn-effect-listp
            (fn-bpn-answer-effects (fn-bpn-step st event)))
           (not (fn-bpn-effect-kind-memberp
                 :release (fn-bpn-answer-effects (fn-bpn-step st event)))))
  :hints (("Goal" :use ((:instance fn-bpn-effect-listp-excludes-release
                                    (effects (fn-bpn-answer-effects
                                              (fn-bpn-step st event))))))))

; KEYSTONE M2.  An interrupted attempt becomes queued at restart, keeping the
; exact peer and exact bundle bytes that were durably enqueued.
(defthm fn-bpn-resume-job-keeps-wire-and-peer
  (and (equal (fn-bpn-job-wire (fn-bpn-job-with-status job :queued token))
              (fn-bpn-job-wire job))
       (equal (fn-bpn-job-peer (fn-bpn-job-with-status job :queued token))
              (fn-bpn-job-peer job))
       (equal (fn-bpn-job-age-anchor (fn-bpn-job-with-status job :queued token))
              (fn-bpn-job-age-anchor job))))

; KEYSTONE M3.  A clock decision other than :expired is not selected by the
; expiry scan.  In particular an uncertain wall observation cannot expire it.
(defthm fn-bpn-find-expired-requires-expired-decision
  (implies (consp (fn-bpn-find-expired jobs obs))
           (equal (fn-bpn-job-expiry (fn-bpn-find-expired jobs obs) obs)
                  :expired))
  :hints (("Goal"
           :induct (fn-bpn-find-expired jobs obs)
           :in-theory '(fn-bpn-find-expired))))

(deftheory fn-bpn-machine-vocabulary
  '(fn-bpn-step-emits-no-release
    fn-bpn-resume-job-keeps-wire-and-peer
    fn-bpn-find-expired-requires-expired-decision))
