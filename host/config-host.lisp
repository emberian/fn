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
; `fn-native-admin-some-group-name-reservedp': RFC 5536 s3.1.4 reserved names.
(include-book "../books/native-admin")
;
; Loaded here, not left to a bridge's `ld' order: this file uses names
; host/store-host.lisp defines, so a session that loads this file alone
; must get them too.  A second `ld' of a file already in the session
; re-admits identical definitions, which ACL2 accepts as redundant.
(ld "store-host.lisp" :ld-error-action :error)

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

(defun fn-cfg-host-initial-octets-stamped (name-octets-list stamp)
  ; The initial configuration record of a fresh store: generation 1, one
  ; creation per operator-supplied name, then the default record's capacity
  ; and limits, stamped STAMP.  Admitted by exactly the predicate replay
  ; will apply to it, or :bad.
  (declare (xargs :mode :program))
  (let ((names (fn-store-octet-lists->strings name-octets-list)))
    (if (or (equal names :bad) (null names)
            ; RFC 5536 s3.1.4: "example.*" and "poster" are never created,
            ; whichever command line reaches this initial record.
            (fn-native-admin-some-group-name-reservedp names))
        :bad
      (let ((record (fn-cfg-record-make
                     0 0 1
                     (append (fn-cfg-host-creations names)
                             (fn-cfg-host-non-group-deltas *fn-cfg-default-change*))
                     stamp)))
        (if (fn-cnode-record-acceptablep (fn-cnode-initial (fn-cfg-initial))
                                         record (fn-cnode-line-ceiling))
            (fn-cfg-encode record)
          :bad)))))

(defun fn-cfg-host-initial-octets (name-octets-list)
  ; The zero stamp (no wall claim): tools/frame_bridge.py's initializer.
  (declare (xargs :mode :program))
  (fn-cfg-host-initial-octets-stamped name-octets-list *fn-cfg-default-stamp*))

(defun fn-cfg-host-initial-octets-at (name-octets-list monotonic wall has-wall)
  ; PKT-665 (PRF-243): the native `init' stamps its record with the host's
  ; clock (MONOTONIC and WALL, milliseconds, PRF-378; HAS-WALL whether the
  ; wall reading is usable, PRF-379), so each initial group's
  ; creation time is the record's commit time, durable with the record
  ; (NEWGROUPS, LIST ACTIVE.TIMES).  The codec decides whether the reading
  ; fits its schema (`fn-native-admin-clock-observation'); one that does not
  ; stamps the record with the zero observation, as before.
  (declare (xargs :mode :program
                  :guard (fn-octet-list-listp name-octets-list)))
  (let ((clock (fn-native-admin-clock-observation monotonic wall has-wall)))
    (fn-cfg-host-initial-octets-stamped
     name-octets-list
     (if (equal (fn-native-admin-clock-status clock) :accepted)
         (fn-native-admin-clock-stamp clock)
       *fn-cfg-default-stamp*))))
