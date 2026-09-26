; Native host/composed-kernel observation correspondence for crash model K0.
;
; host/native/io.lisp calls fn-store-sn-io through fnn-observe.  That wrapper
; calls fn-sn-io, not fn-sf-dispatch.  The byte program uses the latter with
; the shorter event tags below.  This book names and proves the equality at
; the actual composed subject, so byte-program preservation facts can be
; carried to the function the native host calls without treating a sibling
; kernel API as the theorem subject.
(in-package "ACL2")
(include-book "byte-store-relation")
(include-book "store-node")

(defun fn-bs-native-io-event (operation result)
  (declare (xargs :guard t))
  (case operation
    (:start-frontier '(:start-frontier))
    (:frontier-file (list :frontier-file result))
    (:frontier-replace (list :frontier-replace result))
    (:frontier-directory (list :frontier-dir result))
    (:record-file (list :record-file result))
    (:record-link (list :record-link result))
    (:record-directory (list :record-dir result))
    (:recovery-barrier (list :recovery-barrier result))
    (otherwise nil)))

(defun fn-bs-native-io-operationp (operation)
  (declare (xargs :guard t))
  (member-equal operation
                '(:start-frontier :frontier-file :frontier-replace
                  :frontier-directory :record-file :record-link
                  :record-directory :recovery-barrier)))

(defun fn-bs-native-io-resultp (operation result)
  (declare (xargs :guard t))
  (case operation
    (:start-frontier t)
    (:frontier-file (member-equal result '(:ok :known-fail)))
    ((:frontier-replace :frontier-directory :record-link :record-directory)
     (member-equal result '(:ok :error)))
    (:record-file (member-equal result '(:ok :known-fail)))
    (:recovery-barrier (member-equal result '(:ok :uncertain)))
    (otherwise nil)))

; Store v6 carries topic and event-index projections beside the file state.
; Keep the constructor closed in the observation proof and state only the two
; selectors it needs.  The record-directory success arm updates the event
; index, but still keeps the same node.
(local
 (defthm fn-bs-native-node-of-update
   (equal (fn-sn-node (fn-sn-update s files node)) node)
   :hints (("Goal" :in-theory (enable fn-sn-update fn-sn-make-v6 fn-sn-make-v7
                                      fn-sn-node)))))
(local
 (defthm fn-bs-native-node-of-event-index-update
   (equal (fn-sn-node (fn-sn-with-event-index s event-index))
          (fn-sn-node s))
   :hints (("Goal" :in-theory (enable fn-sn-with-event-index
                                      fn-sn-make-v6 fn-sn-make-v7 fn-sn-node)))))

; Exact host-called subject bridge.  The node is unchanged because fn-sn-io
; is the composed file-observation entry; its file projection is precisely the
; byte program's kernel observation.
(defthm fn-bs-native-io-is-byte-observation
  (implies (and (fn-sn-statep s)
                (fn-bs-native-io-operationp operation))
           (let ((next (fn-sn-io s operation result))
                 (event (fn-bs-native-io-event operation result)))
             (and
              (equal (fn-sn-files next)
                     (fn-sf-dispatch (fn-sn-files s) event
                                     (fn-sn-groups s) (fn-sn-capacity s)))
              (equal (fn-sn-node next) (fn-sn-node s)))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-bs-native-io-operationp fn-bs-native-io-event
                 fn-sn-io fn-sn-file-step fn-sf-dispatch)
                (fn-sn-update fn-sn-with-event-index fn-sn-make-v6 fn-sn-make-v7
                 fn-cei-put)))))

; The native tags cover exactly the byte interpreter's observation language
; for the publication/recovery path.  This is executable and used by the test
; book for a reachable, non-degenerate directory-commit witness.
(defthm fn-bs-native-io-event-is-an-event
  (implies (and (fn-bs-native-io-operationp operation)
                (fn-bs-native-io-resultp operation result))
           (fn-sf-eventp (fn-bs-native-io-event operation result)))
  :hints (("Goal" :in-theory (enable fn-bs-native-io-operationp
                                     fn-bs-native-io-resultp
                                     fn-bs-native-io-event fn-sf-eventp))))
