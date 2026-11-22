; Typed NNTP status lines mutate bytes and fill within an existing pool.
(in-package "ACL2")
(include-book "conn-answer")
(local (in-theory (disable fn2-poolp fn2-pool-wfp fn2-pool-rows
                           fn2-pool-write fn2-nntp-render fn2-nntp-reply-command
                           fn2-nntp-reply-admitted fn2-nntp-reply-template)))

(defmacro fn2-status-pool-rows (name)
 `(make-event
   (let* ((call (cons ',name (formals ',name (w state))))
          (thm (intern-in-package-of-symbol
                (concatenate 'string (symbol-name ',name) "-POOL-ROWS") ',name)))
     (value `(defthm ,thm
       (implies (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
                (equal (fn2-pool-rows (mv-nth 1 ,call)) (fn2-pool-rows fn2-pool)))
       :hints (("Goal" :in-theory (enable ,',name))))))))

(local (fn2-status-pool-rows fn2-gram-put))
(local (fn2-status-pool-rows fn2-gram-put-digits))
(local (fn2-status-pool-rows fn2-gram-put-number))
(local (fn2-status-pool-rows fn2-gram-put-digits14))
(local (fn2-status-pool-rows fn2-gram-put-span))
(local (fn2-status-pool-rows fn2-gram-put-template))
(local (fn2-status-pool-rows fn2-gram-put-crlf))
(local (fn2-status-pool-rows fn2-nntp-render))
(fn2-status-pool-rows fn2-answer-say)
