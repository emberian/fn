; Exact consumer-event index readout, without replay or mutation.
(in-package "ACL2")
(include-book "cbor")
(include-book "consumer-position-fields")
(include-book "msgid-index-concrete")

(defconst *fn-cei-value-key* :fn-cei-value)

(defun fn-cei-branch-get (key branches)
  (declare (xargs :guard t))
  (if (consp branches)
      (if (equal key (fn-cbor-ag-car (fn-cbor-ag-car branches)))
          (fn-cbor-ag-cdr (fn-cbor-ag-car branches))
        (fn-cei-branch-get key (fn-cbor-ag-cdr branches)))
    nil))

(defun fn-cei-get-digits (digits trie)
  (declare (xargs :guard t))
  (if (consp digits)
      (fn-cei-get-digits
       (cdr digits) (fn-cei-branch-get (car digits) trie))
    (fn-cei-branch-get *fn-cei-value-key* trie)))

(defun fn-cei-sequence-trie (index)
  (declare (xargs :guard t))
  (if (consp index) (car index) nil))

(defun fn-cei-trie-records (msgid trie)
  (declare (xargs :guard t))
  (let ((value (fn-mxc-lookup msgid trie)))
    (if (true-listp value) value nil)))

(defun fn-cei-get (sequence index)
  (declare (xargs :guard t))
  (if (fn-cp-uintp sequence)
      (fn-cei-get-digits (fn-cbor-u32-bytes sequence)
                         (fn-cei-sequence-trie index))
    nil))
