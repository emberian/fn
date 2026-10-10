; fn: the read's entry scratch is charged by the log's observed extent
; (Builder M, memory landing 4b; agreed with Builder A, whose probe passes
; the extent on lane/vertical).
;
; The open's reader allocates an entry's declared length before the step
; validates it (books/store-log-entry-bound.lisp fn-lgw-entry-len-bounded),
; capped by the octets the segment holds past the reader's position
; (books/store-log-stream.lisp fn-lgw-entry-len) and by the kind's open bound,
; for a batch the frame's payload limit.  An honest file's entry is
; covered by the reopen's terms over LOG; a damaged or padded one is not, so
; the observation raises LOG to the extent it saw (books/heap-command.lisp
; fn-mo-observed-totals) and every entry a segment within that extent yields
; is at most the observation's LOG.  The keystone is conditional on the
; read's segment extent being within the observed one: it protects the live
; read once the probe passes the extent (Builder A's line in
; host/native/heap.lisp fnn-heap-charged-totals; NIL today, the offline
; adapter) AND the read's open refuses a segment longer than the extent the
; probe observed (host/native/io.lisp, A's), since the store may grow between
; the observation and the open.  This book is separate so that
; heap-command's closure does not take in the log stream.
(in-package "ACL2")
(include-book "heap-command")
(include-book "store-log-entry-bound")

; KEYSTONE: every entry the open reads from a segment no longer than the
; observed extent is within the observation's LOG.
(defthm fn-mo-observed-log-holds-every-entry-read
  (implies (and (fn-mo-observed-totals hdr suffix extent)
                (<= (nfix segment-extent) extent))
           (<= (nfix (fn-lgw-entry-len-bounded h st segment-extent max))
               (fn-mm-tot-log (fn-mo-observed-totals hdr suffix extent))))
  :hints (("Goal" :in-theory (enable fn-lgw-entry-len-bounded fn-lgw-entry-len))))
