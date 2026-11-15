(fn2-pool-preserves fn2-run-zero (n slot gen pos okind oslot ogen fn2-pool) :position 1)
(fn2-fields-preserves fn2-run-write-restarts (k j w cursor scratch slot gen okind oslot ogen fn2-run-restarts fn2-fields fn2-pool)
 :position 1 :disable nil :hyps ((fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-run-restartsp fn2-run-restarts) (fn2-run-restarts-wfp fn2-run-restarts) (natp scratch) (< scratch (fn2-fields-rows fn2-fields))))
(fn2-pool-preserves fn2-run-write-restarts (k j w cursor scratch slot gen okind oslot ogen fn2-run-restarts fn2-fields fn2-pool)
 :position 2 :prefix "-POOL-PRESERVES")
(fn2-run-writers-preserves fn2-run-close-full (w fn2-run-writers) :position 1 :raw-rows t
 :hyps ((fn2-run-writersp fn2-run-writers) (fn2-run-writers-wfp fn2-run-writers) (natp w) (< w (fn2-run-writers-rows fn2-run-writers))))
(fn2-run-writers-preserves fn2-run-close (w fn2-run-writers) :position 1 :raw-rows t
 :hyps ((fn2-run-writersp fn2-run-writers) (fn2-run-writers-wfp fn2-run-writers) (natp w) (< w (fn2-run-writers-rows fn2-run-writers))))
(fn2-run-writers-preserves fn2-run-open (w slot gen schema version level run ordinal page-kind unit epoch counter history incarnation okind oslot ogen fields limit fn2-run-writers fn2-pool) :position 1 :raw-rows t :disable nil
 :hyps ((fn2-run-writersp fn2-run-writers) (fn2-run-writers-wfp fn2-run-writers) (natp w) (< w (fn2-run-writers-rows fn2-run-writers))))
(fn2-pool-preserves fn2-run-open (w slot gen schema version level run ordinal page-kind unit epoch counter history incarnation okind oslot ogen fields limit fn2-run-writers fn2-pool) :position 2 :prefix "-POOL-PRESERVES")
(fn2-run-writers-preserves fn2-run-note-restart (w fn2-run-writers fn2-run-restarts) :position 1 :raw-rows t :disable nil
 :hyps ((fn2-run-writersp fn2-run-writers) (fn2-run-writers-wfp fn2-run-writers) (natp w) (< w (fn2-run-writers-rows fn2-run-writers))))
(fn2-run-restarts-preserves fn2-run-note-restart (w fn2-run-writers fn2-run-restarts) :position 2 :prefix "-RESTARTS-PRESERVES" :raw-rows t
 :hyps ((fn2-run-restartsp fn2-run-restarts) (fn2-run-restarts-wfp fn2-run-restarts) (fn2-run-writersp fn2-run-writers) (fn2-run-writers-wfp fn2-run-writers) (natp w) (< w (fn2-run-writers-rows fn2-run-writers))
        (<= (* (+ 1 w) *fn2-run-restart-capacity*) (fn2-run-restarts-rows fn2-run-restarts))))
(fn2-run-writers-preserves fn2-run-close-step (w budget fn2-run-writers fn2-run-restarts fn2-fields fn2-pool) :position 1 :raw-rows t :disable nil
 :hyps ((fn2-run-writersp fn2-run-writers) (fn2-run-restartsp fn2-run-restarts) (fn2-run-writerp w fn2-run-writers fn2-run-restarts fn2-fields)))
(fn2-fields-preserves fn2-run-close-step (w budget fn2-run-writers fn2-run-restarts fn2-fields fn2-pool) :position 2 :prefix "-FIELDS-PRESERVES" :disable nil
 :hyps ((fn2-fieldsp fn2-fields) (fn2-run-writersp fn2-run-writers) (fn2-run-restartsp fn2-run-restarts) (fn2-run-writerp w fn2-run-writers fn2-run-restarts fn2-fields)))
(fn2-pool-preserves fn2-run-close-step (w budget fn2-run-writers fn2-run-restarts fn2-fields fn2-pool) :position 3 :prefix "-POOL-PRESERVES")
(fn2-fields-preserves fn2-run-head-b (w b fn2-run-writers fn2-fields fn2-pool) :position 1 :disable nil
 :hyps ((fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-run-writersp fn2-run-writers) (fn2-run-writers-wfp fn2-run-writers)
        (natp w) (< w (fn2-run-writers-rows fn2-run-writers))))
(fn2-pool-preserves fn2-run-head-b (w b fn2-run-writers fn2-fields fn2-pool) :position 2 :prefix "-POOL-PRESERVES")
(fn2-run-writers-preserves fn2-run-head (w fn2-run-writers fn2-run-restarts fn2-fields fn2-pool) :position 1 :raw-rows t :disable nil
 :hyps ((fn2-run-writersp fn2-run-writers) (fn2-run-writerp w fn2-run-writers fn2-run-restarts fn2-fields)))
(fn2-fields-preserves fn2-run-head (w fn2-run-writers fn2-run-restarts fn2-fields fn2-pool) :position 2 :prefix "-FIELDS-PRESERVES" :disable nil
 :hyps ((fn2-fieldsp fn2-fields) (fn2-run-writersp fn2-run-writers) (fn2-run-writerp w fn2-run-writers fn2-run-restarts fn2-fields)))
(fn2-pool-preserves fn2-run-head (w fn2-run-writers fn2-run-restarts fn2-fields fn2-pool) :position 3 :prefix "-POOL-PRESERVES")
(fn2-fc-context-preserves fn2-run-seal-context (w row hrow fn2-run-writers fn2-fc-context) :raw-rows t
 :hyps ((fn2-fc-contextp fn2-fc-context) (fn2-fc-context-wfp fn2-fc-context) (fn2-run-writersp fn2-run-writers)
        (fn2-run-writers-wfp fn2-run-writers) (natp w) (< w (fn2-run-writers-rows fn2-run-writers))
        (natp row) (< row (fn2-fc-context-rows fn2-fc-context))
        (< (fn2-digest-slot row *fn2-fc-previous-seal*) 4294967296) (unsigned-byte-p 32 hrow)))
(fn2-fields-preserves fn2-run-copy-row (from to fn2-fields)
 :hyps ((fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (natp from) (natp to)
        (< from (fn2-fields-rows fn2-fields)) (< to (fn2-fields-rows fn2-fields))))
(fn2-fields-preserves fn2-run-read-header (slot gen base okind oslot ogen fn2-fields fn2-pool) :position 1
 :hyps ((fn2-fieldsp fn2-fields) (fn2-run-readerp base fn2-fields)))
(fn2-fields-preserves fn2-run-restart-offset (j slot gen base okind oslot ogen fn2-fields fn2-pool) :position 2
 :hyps ((fn2-fieldsp fn2-fields) (fn2-run-readerp base fn2-fields)))
(fn2-run-writers-preserves fn2-run-add-commit (w code end fn2-run-writers) :position 1 :raw-rows t
 :hyps ((fn2-run-writersp fn2-run-writers) (fn2-run-writers-wfp fn2-run-writers) (natp w) (< w (fn2-run-writers-rows fn2-run-writers))))
