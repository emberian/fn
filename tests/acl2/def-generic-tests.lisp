; What `def-generic' generates (books/def-representation-generic.lisp), proved
; once here.
;
; 1. The payload arena's generic is EQUAL to the hand-written one it
;    replaced: the abstract stobj's recorded interface (foundation,
;    recognizer, creator, and for every export its name, :logic and :exec
;    function, in order) is the list below, captured from dev 9a9fa4bab
;    (books/payload-arena.lisp before the hand forms were deleted).  The
;    attachment `(attach-stobj fn-arena fn-arena-extent)' matches the export
;    lists positionally, so the order is part of the statement.  The :protect
;    set is the ten updaters (seal-list seal-buffer clear seal-range
;    seal-extent reseat-extent release seal-lz-extent reseat-lz-extent
;    forget).

(in-package "ACL2")
(include-book "../../books/payload-arena")
(include-book "must-fail-checked")
(include-book "std/testing/assert-bang" :dir :system)

(defconst *dgt-hand-fn-arena-interface*
  '(FN-ARENA$L
    (FN-ARENA-P FN-ARENA$AP FN-ARENA$LP)
    (CREATE-FN-ARENA CREATE-FN-ARENA$A CREATE-FN-ARENA$L)
    (FN-ARENA-COUNT FN-ARENA$A-COUNT FN-ARENA$L-COUNT)
    (FN-ARENA-PAYLOAD-LEN FN-ARENA$A-PAYLOAD-LEN FN-ARENA$L-PAYLOAD-LEN)
    (FN-ARENA-GET FN-ARENA$A-GET FN-ARENA$L-GET)
    (FN-ARENA-GET-SPAN FN-ARENA$A-GET-SPAN FN-ARENA$L-GET-SPAN)
    (FN-ARENA-PAYLOAD FN-ARENA$A-PAYLOAD FN-ARENA$L-PAYLOAD)
    (FN-ARENA-SEAL-LIST FN-ARENA$A-SEAL-LIST FN-ARENA$L-SEAL-LIST)
    (FN-ARENA-SEAL-BUFFER FN-ARENA$A-SEAL-BUFFER FN-ARENA$L-SEAL-BUFFER)
    (FN-ARENA-CLEAR FN-ARENA$A-CLEAR FN-ARENA$L-CLEAR)
    (FN-ARENA-SEAL-RANGE FN-ARENA$A-SEAL-RANGE FN-ARENA$L-SEAL-RANGE)
    (FN-ARENA-SEAL-EXTENT FN-ARENA$A-SEAL-EXTENT FN-ARENA$L-SEAL-EXTENT)
    (FN-ARENA-RESEAT-EXTENT FN-ARENA$A-RESEAT-EXTENT FN-ARENA$L-RESEAT-EXTENT)
    (FN-ARENA-RELEASE FN-ARENA$A-RELEASE FN-ARENA$L-RELEASE)
    (FN-ARENA-SEAL-LZ-EXTENT FN-ARENA$A-SEAL-LZ-EXTENT FN-ARENA$L-SEAL-LZ-EXTENT)
    (FN-ARENA-RESEAT-LZ-EXTENT FN-ARENA$A-RESEAT-LZ-EXTENT FN-ARENA$L-RESEAT-LZ-EXTENT)
    (FN-ARENA-FORGET FN-ARENA$A-FORGET FN-ARENA$L-FORGET)))

(assert-event
 (equal (getprop 'fn-arena 'absstobj-info nil 'current-acl2-world (w state))
        *dgt-hand-fn-arena-interface*))
