  ; The commit result is already consumed. Admission can yield here without
  ; taking that receipt twice or retaining a C observer through B settlement.
  (:refresh :on-refusal ((:stop :machine-phase))
   (:do (meta-code-refresh meta-receipt-refresh) (fn2-cns-request-acquire id row-generation)
    :accept (:ok) :case (((:admission) (:charge :steps *fn2-work-transition* :runnable t))))
   (:set (observer-serial meta-receipt-refresh))
   (:do (lcode lpos lver lpf)
    (fn2-cns-lookup-cursor (fn2-cns-cid-default row-consumer) (fn2-cns-ep-default row-epoch)
                         row-principal-slot row-cpos row-version row-pub-frontier row-xrow))
   (:set (cpos lpos) (version lver) (pub-frontier lpf))
   (:if (and (equal row-refresh *fn2-cns-refresh-duplicate*) (not (< 0 lver)))
        ((:set (reason *fn2-cns-reason-equal*)) (:goto refuse))
        ((:set (outcome *fn2-cns-outcome-accepted*)) (:goto answer))))
