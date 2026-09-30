; One fnce namespace: local1, account2, binding3, reserved remote4.
; Dispatch is by the bounded version field, never the shared magic alone.
(in-package "ACL2")
(include-book "consumer-store-events")
(include-book "consumer-account-binding-codec")

(defun fn-cae-eventp (event)
 (declare (xargs :guard t))
 (or (fn-cac-eventp event) (fn-cab-eventp event)))

(defun fn-cae-encode (event)
 (declare (xargs :guard t))
 (if (fn-cab-eventp event) (fn-cab-encode event) (fn-cac-encode event)))

(defun fn-cne-decode-exact (bytes)
 (declare (xargs :guard t))
 (case (fn-cp-nth 4 bytes)
  (1 (fn-cpe-decode-exact bytes))
  (2 (fn-cac-decode-exact bytes))
  (3 (fn-cab-decode-exact bytes))
  ; The separately owned bounded remote parser must replace this arm in its
  ; coherent Store packet. Never interpret its bytes as account authority.
  (4 '(:error :remote-consumer-decoder-unavailable))
  (otherwise '(:error :consumer-envelope-version))))

(defthm fn-cae-event-shape
 (implies (fn-cae-eventp event)
          (and (true-listp event) (equal (len event) 5)
               (consp event) (equal (car event) :consumer-authority)
               (natp (fn-cp-nth 1 event)) (natp (fn-cp-nth 2 event))
               (natp (fn-cp-nth 3 event))))
 :hints (("Goal" :in-theory
          (e/d (fn-cae-eventp fn-cac-eventp fn-cab-eventp fn-cac-u64p fn-cp-nth)
               (fn-cac-operationp fn-cab-operationp)))))

(in-theory (disable fn-cae-eventp fn-cae-encode fn-cne-decode-exact))
