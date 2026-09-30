; One fnce namespace: local1, account2, binding3, remote4.
; Dispatch is by the bounded version field, never the shared magic alone.
(in-package "ACL2")
(include-book "consumer-store-events")
(include-book "consumer-account-binding-codec")
(include-book "consumer-remote-event-codec")

 ; Complete logical/recovery :consumer category. The served remote producer
; carries validated groups/charge and emits one bounded buffer chunk per tick;
; it must never call this whole-query predicate or reference encoder.
(defun fn-cne-eventp (event)
 (declare (xargs :guard t))
 (or (fn-cpe-eventp event) (fn-crev-eventp event)))

(defun fn-cne-encode (event)
 (declare (xargs :guard t))
 (if (fn-cpe-eventp event) (fn-cpe-encode event) (fn-crev-encode-reference event)))

(defthm fn-cne-event-shape
 (implies (fn-cne-eventp event)
          (and (true-listp event) (equal (len event) 5)
               (consp event) (equal (car event) :consumer)
               (natp (fn-cp-nth 1 event)) (natp (fn-cp-nth 2 event))
               (natp (fn-cp-nth 3 event))))
 :hints (("Goal" :in-theory
          (e/d (fn-cne-eventp fn-cpe-eventp fn-crev-eventp fn-crev-headp fn-cp-uintp fn-cp-nth)
               (fn-cpe-operationp fn-crev-groupsp fn-crs-namep)))))

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
  ; Logical recovery reference; served located parsing is separately funded.
  (4 (fn-crev-decode-exact bytes))
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

(in-theory (disable fn-cne-eventp fn-cne-encode fn-cae-eventp fn-cae-encode fn-cne-decode-exact))
