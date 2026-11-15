(fn2-checkpoints-preserves fn2-checkpoint-check-step
 (c row slot gen off len base okind oslot ogen budget fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
    fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
 :carriers ((fn2-checkpoints 1 :prefix "-CANDIDATES" :type-hints ((append
 (fn2-columns-guard-hint
  '(fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fc fn2-fc-context
    fn2-b3 fn2-fields fn2-pool fn2-digests)
  '(fn2-format-run fn2-checkpoint-decode fn2-checkpoint-capture-roots fn2-checkpoint-hash-matchesp)
  '(fn2-checkpoint-check-step) world)
 '(:use ((:instance fn2-checkpoint-decode-ok-room-by-definition
 (fn2-fields (mv-nth 3 (fn2-format-run :page nil row slot gen off len base okind oslot ogen budget
                       fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
 (fn2-pool (mv-nth 4 (fn2-format-run :page nil row slot gen off len base okind oslot ogen budget
                       fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))))
(:instance fn2-checkpoint-decode-fields-domain-value-type (i (+ base 1))
 (fn2-fields (mv-nth 3 (fn2-format-run :page nil row slot gen off len base okind oslot ogen budget
                       fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
 (fn2-pool (mv-nth 4 (fn2-format-run :page nil row slot gen off len base okind oslot ogen budget
                       fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))))
(:instance fn2-checkpoint-decode-fields-domain-value-type (i (+ base 2))
 (fn2-fields (mv-nth 3 (fn2-format-run :page nil row slot gen off len base okind oslot ogen budget
                       fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
 (fn2-pool (mv-nth 4 (fn2-format-run :page nil row slot gen off len base okind oslot ogen budget
                       fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))))))))
            (fn2-checkpoint-refs 2 :prefix "-REFS") (fn2-checkpoint-bytes 3 :prefix "-BYTES")
            (fn2-fc 4 :prefix "-CHECKER") (fn2-b3 5 :prefix "-HASHER")
            (fn2-fields 6 :prefix "-FIELDS") (fn2-pool 7 :prefix "-POOL") (fn2-digests 8 :prefix "-DIGESTS"))
 :hints ((fn2-columns-guard-hint
    '(fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fc fn2-fc-context
      fn2-b3 fn2-fields fn2-pool fn2-digests)
    '(fn2-format-run fn2-checkpoint-decode fn2-checkpoint-capture-roots fn2-checkpoint-hash-matchesp)
    '(fn2-checkpoint-check-step) world)))
