; fn: host wrappers over books/config and books/node-config for the Python
; bridge (packets R1 and R4).
;
; `run_store.py init' writes the initial configuration record built here from
; the operator's group names; `recover' replays the record history through
; `fn-store-sn-recover' (host/store-node-host.lisp), and `group create' /
; `group retire' obtain their records from `fn-store-cfg-reconfigure' there.
; No value here is computed by Python: the record octets, the generation and
; the served table all come out of the books.  RFC 3977 section 3.1's
; initial-line ceiling is `fn-cnode-line-ceiling' (books/node-config), cited
; from `books/nntp-syntax'; this file no longer repeats the number.

(in-package "ACL2")
(include-book "../books/node-config")

(defun fn-cfg-host-creations (names)
  (declare (xargs :guard t))
  (if (consp names)
      (cons (fn-cfg-create-group (car names) *fn-cfg-default-policy-id*)
            (fn-cfg-host-creations (cdr names)))
    nil))

(defun fn-cfg-host-non-group-deltas (deltas)
  ; The capacity and limit deltas of the default record; the group creations
  ; are the operator's.
  (declare (xargs :guard t))
  (if (consp deltas)
      (if (equal (fn-cfg-delta-kind (car deltas)) :create-group)
          (fn-cfg-host-non-group-deltas (cdr deltas))
        (cons (car deltas) (fn-cfg-host-non-group-deltas (cdr deltas))))
    nil))

(defun fn-cfg-host-initial-octets (name-octets-list)
  ; The initial configuration record of a fresh store: generation 1, one
  ; creation per operator-supplied name, then the default record's capacity
  ; and limits.  Admitted by exactly the predicate replay will apply to it,
  ; or :bad.
  (declare (xargs :mode :program))
  (let ((names (fn-store-octet-lists->strings name-octets-list)))
    (if (or (equal names :bad) (null names))
        :bad
      (let ((record (fn-cfg-record-make
                     0 0 1
                     (append (fn-cfg-host-creations names)
                             (fn-cfg-host-non-group-deltas *fn-cfg-default-change*))
                     *fn-cfg-default-stamp*)))
        (if (fn-cnode-record-acceptablep (fn-cnode-initial (fn-cfg-initial))
                                         record (fn-cnode-line-ceiling))
            (fn-cfg-encode record)
          :bad)))))
