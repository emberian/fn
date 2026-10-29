(in-package "ACL2")
(include-book "../books/machines")
; Sprint 8e3488fcb: 10 declared fields, 18 array columns, 19 total storage fields.
(defun fn2-columns-cost10-initial-generation (slot base n gen)
  (declare (ignore slot base n) (xargs :guard (unsigned-byte-p 60 gen))) gen)
(defmachine fn2-columns-cost10
 :states (:accepting :greeting :command :article-input :reply :group-select :lookup :render :post-check :log-write :fence :publish :closing :draining :done)
 :fields ((rx-slot :u32) (rx-gen :u60) (tx-slot :u32) (tx-gen :u60) (up-slot :u32) (up-gen :u60) (cap-index :u32) (cap-nonce :u32) (scan :u32) (storage-bytes :u60))
 :accounts (:operations :bytes :row)
 :budget (:bytes 4096 :steps 32 :descriptors 4)
 :capacity 1
 :initial ((storage-bytes 131072) (generation fn2-columns-cost10-initial-generation) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 :continuations ((:accepting fn2-columns-cost10-accepting) (:greeting fn2-columns-cost10-greeting) (:command fn2-columns-cost10-command) (:article-input fn2-columns-cost10-article-input) (:reply fn2-columns-cost10-reply) (:group-select fn2-columns-cost10-group-select) (:lookup fn2-columns-cost10-lookup) (:render fn2-columns-cost10-render) (:post-check fn2-columns-cost10-post-check) (:log-write fn2-columns-cost10-log-write) (:fence fn2-columns-cost10-fence) (:publish fn2-columns-cost10-publish) (:closing fn2-columns-cost10-closing) (:draining fn2-columns-cost10-draining) (:done fn2-columns-cost10-done))
 :observes ((:read-result fn2-columns-cost10-observe-read) (:write-result fn2-columns-cost10-observe-write)))

; No I/O is exercised: every callback is a guard-verified scalar identity stub.
(defun fn2-columns-cost-stubs (entries args observep)
  (declare (xargs :verify-guards nil))
  (if (atom entries) nil
    (cons `(defun ,(cadar entries) ,args
             (declare (ignore ,@(butlast args 1)) (xargs :guard t))
             ,(if observep '(mv nil fn2-core) '(mv 0 0 0 nil fn2-core)))
          (fn2-columns-cost-stubs (cdr entries) args observep))))
(make-event
 (let* ((world (w state)) (calling (fn2-machine-property 'fn2-columns-cost10 :calling-convention world)))
   (value `(progn
      ,@(fn2-columns-cost-stubs (fn2-machine-property 'fn2-columns-cost10 :continuations world)
                               (cadr (member-eq :run calling)) nil)
      ,@(fn2-columns-cost-stubs (fn2-machine-property 'fn2-columns-cost10 :observes world)
                               (cadr (member-eq :observe calling)) t)))))
(assert-event (equal (len (fn2-machine-property 'fn2-columns-cost10 :columns (w state))) 18))
