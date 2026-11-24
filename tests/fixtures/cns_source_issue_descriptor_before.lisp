(:do (rc op og) (fn2-cns-stream-source-issue id row-generation row-ctl row-ctl-gen row-request row-principal-slot) :accept () :case (((:ok) (:charge :bytes *fn2-cns-source-unit-work-bytes* :descriptors 1 :steps *fn2-work-transition*)) ((:wait) (:charge :bytes *fn2-cns-source-unit-work-bytes* :descriptors 1 :steps *fn2-work-poll* :runnable t)) (:otherwise
       (:do () (fn2-cns-stream-source-abort id row-generation row-ctl row-ctl-gen row-request))
       (:charge :bytes *fn2-cns-source-unit-work-bytes* :descriptors 1 :steps *fn2-work-transition* :runnable t))))
