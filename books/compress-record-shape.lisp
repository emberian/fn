; The host reads the transport returned by record-next through its columns.
(in-package "ACL2")
(include-book "compress-record")
(fn2-book-layer :d)

(make-event
 (let* ((world (w state))
        (readers
         (append
          '(fn2-compress-transport-rows fn2-compress-operation-rows
            fn2-compress-operation-bind fn2-compress-operation-request
            fn2-compress-operation-requestable-p fn2-compress-operation-finish
            fn2-compress-transport-select-encode fn2-compress-transport-select-decode
            fn2-compress-transport-select-drain fn2-compress-transport-select-fill)
          (fn2-columns-projection-readers 'fn2-compress-transport
           (fn2-decl-get :columns (fn2-decl-row '(:columns fn2-compress-transport) world)))
          (fn2-columns-projection-readers 'fn2-compress-operation
           (fn2-decl-get :columns (fn2-decl-row '(:columns fn2-compress-operation) world)))))
        (hyps '((fn2-compress-operationp fn2-compress-operation)
                (fn2-compress-operation-wfp fn2-compress-operation)
                (fn2-compress-transportp fn2-compress-transport)
                (fn2-compress-transport-wfp fn2-compress-transport)
                (= (fn2-compress-transport-rows fn2-compress-transport) 1)))
        (hints `(("Goal" :in-theory (disable ,@readers)))))
  (value `(fn2-compress-transport-preserves fn2-compress-record-next
    (cap nonce slot generation receive extent fn2-compress-operation fn2-compress-transport)
    :position 3 :hyps ,hyps :hints ,hints :forward t :disable nil))))
