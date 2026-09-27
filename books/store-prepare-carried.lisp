;; fn: the standalone store's POST prepare, over the retained row, without
;; the history replay.
;
; host/store-node-host.lisp fn-store-sn-prepare interns the offered wire
; record as a row and stages it.  books/store-intern.lisp's entry,
; fn-store-prepare-interned, stages through fn-sn-prepare: the specification,
; whose file gate fn-sf-prepare-record replays the whole durable history plus
; the candidate on every POST (books/store-prepare-correspondence.lisp's
; header).  Before the records flip the host called the carried
; fn-pcar-spc-prepare (books/owner-prepare-carried.lisp) instead, and that
; prepare now stages fn-held-p rows.  fn-store-prepare-interned-carried is
; the entry with that one call replaced.
;
; Its bridge to the entry holds under fn-snt-relation
; (books/store-node-traces-prepare.lisp): fn-pcar-spc-prepare is
; fn-spc-prepare for every value (fn-pcar-spc-prepare-is-spc-prepare), and
; fn-spc-prepare is fn-sn-prepare on a related state
; (fn-spc-prepare-equals-specification-under-relation).  The relation is
; what an observed open establishes and every live mutator keeps
; (fn-spc-observed-open-run-maintains-relation); the executable body checks
; none of it.  The cost left is fn-pcar-next-lower's walk to the history's
; last cons (no record is decoded).

(in-package "ACL2")
(include-book "store-intern")
(include-book "owner-prepare-carried")

(local (defthm fn-spca-record-p-payload-octets
  (implies (fn-record-p w) (fn-cbor-octet-listp (fn-record-payload w)))
  :hints (("Goal" :in-theory (enable fn-record-p fn-record-payloadp)))))

(defun fn-store-prepare-interned-carried (s w fn-arena)
  (declare (xargs :stobjs fn-arena :guard (fn-sn-statep s) :verify-guards nil))
  (if (and (fn-record-p w) (fn-prin-keyringp (fn-sn-keyring s))
           (natp (fn-sn-keyring-generation s)))
      (let* ((row (fn-intern-row-at w (fn-sn-keyring s) (fn-sn-keyring-generation s)
                                    (fn-arena-count fn-arena)))
             (next (fn-pcar-spc-prepare s row)))
        (if (equal next s)
            (mv s fn-arena)
          (let ((fn-arena (fn-arena-seal-list (fn-record-payload w) fn-arena)))
            (mv next fn-arena))))
    (mv s fn-arena)))

(verify-guards fn-store-prepare-interned-carried
  :hints (("Goal" :in-theory (e/d (fn-sn-statep)
                                  (fn-sf-statep fn-node-statep
                                   fn-pcar-spc-prepare-is-spc-prepare
                                   fn-intern-row-at fn-record-p)))))

; KEYSTONE (the host's prepare line): on a related store the carried entry the
; host calls IS books/store-intern's entry, both results (the store and the
; arena); fn-store-prepare-interned-is-intern-then-prepare,
; -refusal-keeps-the-arena and -acceptance-seals-one-payload then say what it
; does.
(defthm fn-store-prepare-interned-carried-is-prepare-interned
  (implies (fn-snt-relation s)
           (equal (fn-store-prepare-interned-carried s w fn-arena)
                  (fn-store-prepare-interned s w fn-arena)))
  :hints (("Goal"
           :use ((:instance fn-spc-prepare-equals-specification-under-relation
                  (record (fn-intern-row-at w (fn-sn-keyring s)
                                            (fn-sn-keyring-generation s)
                                            (fn-arena-count fn-arena)))))
           :in-theory (e/d (fn-store-prepare-interned-carried
                            fn-store-prepare-interned
                            fn-pcar-spc-prepare-is-spc-prepare)
                           (fn-snt-relation fn-spc-prepare fn-sn-prepare
                            fn-pcar-spc-prepare fn-intern-row-at
                            fn-record-p fn-arena-seal-list)))))

(in-theory (disable fn-store-prepare-interned-carried))
