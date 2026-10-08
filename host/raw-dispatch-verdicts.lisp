; host/raw-dispatch-verdicts.lisp -- D40's raw-dispatch verdicts, judged in
; this world (books/raw-dispatch-verdict.lisp).  ld'ed by every native build
; script that loads declarations, after the last of them and before the raw
; block, so tools/extract/world.py puts it last in the extraction world too:
; the image's fnn-install-raw-dispatch and the extracted core's (which has
; only the export of this table) admit raw dispatch from the same verdicts.
; A declaration added after this event has no verdict and is refused.
(in-package "ACL2")
; D61: the image attaches these (attach-stobj) before the generic they implement;
; a certified host file carries the same order in its own world (tools/host_check.py --attach-order).
(include-book "../books/payload-arena-attach")
(include-book "../books/history-paged-attach")
(include-book "../books/raw-dispatch-verdict")

(make-event
 `(table fn-raw-dispatch-verdicts nil
         ',(fn-rdv-verdicts (table-alist 'fn-interfaces (w state)) (w state))
         :clear))

(value-triple
 (cw "FN_RAW_DISPATCH_VERDICTS ~x0 judged; refused ~x1~%"
     (len (table-alist 'fn-raw-dispatch-verdicts (w state)))
     (fn-rdv-refused-names (table-alist 'fn-raw-dispatch-verdicts (w state)))))
