; INTERNAL pre-adoption producer. Immutable custody is captured from the
; actual transferred receiver before the recursive query-child walk.
; This is not a tuple setter or a terminal/alias settlement observation.
(in-package "ACL2")
(include-book "receiver-custody-row")
(include-book "receiver-index-custody")

(defun fn-ric-pending-custody-capture
 (ticket recipient fn-rx-provider fn-receiver-turn fn-index-backing fn-page-read-pool)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-index-backing
                         fn-page-read-pool)))
 (mv-let (word receipt) (fn-irr-pending-read recipient fn-index-backing)
  (if (not (fn-irq-committed-phasep word))
      (mv :unavailable-custody nil nil)
   (mv-let (custody-word row)
    (fn-owner-rx-turn-custody-row ticket fn-rx-provider fn-receiver-turn
                                 fn-page-read-pool)
    (let* ((request (fn-irr-receipt-request receipt))
           (source (fn-irr-request-input-source request)))
     (if (and (eq custody-word :retained-custody)
              (fn-omk-widthp request 10)
              (equal (fn-omk-at 2 row) recipient)
              (equal (fn-omk-at 1 row) source))
         (mv :captured-custody receipt row)
       (mv :unavailable-custody nil nil)))))))

(defthm fn-ric-pending-custody-capture-preserves-recipient-source
 (let ((answer (fn-ric-pending-custody-capture ticket recipient fn-rx-provider
                    fn-receiver-turn fn-index-backing fn-page-read-pool)))
  (implies (eq (mv-nth 0 answer) :captured-custody)
   (and (equal (fn-omk-at 2 (mv-nth 2 answer)) recipient)
        (equal (fn-omk-at 1 (mv-nth 2 answer))
               (fn-irr-request-input-source
                 (fn-irr-receipt-request (mv-nth 1 answer)))))))
 :hints (("Goal" :in-theory
          (e/d (fn-ric-pending-custody-capture)
               (fn-irr-pending-read fn-owner-rx-turn-custody-row
                fn-irr-receipt-request fn-irr-request-input-source
                fn-irq-committed-phasep fn-omk-widthp fn-omk-at))))
 :rule-classes nil)

; Reader-specific actual context constructor. PAYLOAD is the existing retained
; resource reference supplied by the internal reader admission transaction;
; it gains no authority from this constructor. Old fields0..8 are unchanged.
(defun fn-ric-pending-reader-context
 (ticket recipient payload fn-rx-provider fn-receiver-turn fn-index-backing
  fn-page-read-pool)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-index-backing
                         fn-page-read-pool)))
 (mv-let (word receipt row)
  (fn-ric-pending-custody-capture ticket recipient fn-rx-provider
                                fn-receiver-turn fn-index-backing fn-page-read-pool)
  (if (not (eq word :captured-custody)) (mv :unavailable-custody nil)
   (let ((request (fn-irr-receipt-request receipt)))
    (mv :captured-custody
     (list :reader-context (fn-omk-at 1 request) (fn-omk-at 2 request)
           (fn-omk-at 3 request) (fn-omk-at 4 request) payload
           (fn-irr-request-effects request) (fn-irr-request-origin request)
           receipt row))))))

(defthm fn-ric-pending-reader-context-preserves-reader-prefix-by-definition
 (let* ((captured (fn-ric-pending-custody-capture ticket recipient fn-rx-provider
                    fn-receiver-turn fn-index-backing fn-page-read-pool))
        (answer (fn-ric-pending-reader-context ticket recipient payload fn-rx-provider
                    fn-receiver-turn fn-index-backing fn-page-read-pool)))
  (implies (eq (mv-nth 0 answer) :captured-custody)
   (and (equal (take 9 (mv-nth 1 answer))
               (fn-irr-query-context (mv-nth 1 captured) payload))
        (equal (fn-omk-at 9 (mv-nth 1 answer)) (mv-nth 2 captured)))))
 :hints (("Goal" :in-theory
          (e/d (fn-ric-pending-reader-context fn-irr-query-context take fn-omk-at)
               (fn-ric-pending-custody-capture fn-irr-receipt-request
                fn-irr-request-effects fn-irr-request-origin))))
 :rule-classes nil)
