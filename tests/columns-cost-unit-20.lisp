(in-package "ACL2")
(include-book "../books/machines")
; Sprint 8e3488fcb: 20 declared fields, 28 array columns, 29 total storage fields.
(defun fn2-columns-cost20-initial-generation (slot base n gen)
  (declare (ignore slot base n) (xargs :guard (unsigned-byte-p 60 gen))) gen)
(defmachine fn2-columns-cost20
 :states (:accepting :greeting :command :article-input :reply :group-select :lookup :render :post-check :log-write :fence :publish :closing :draining :done)
 :fields ((rx-slot :u32) (rx-gen :u60) (tx-slot :u32) (tx-gen :u60) (up-slot :u32) (up-gen :u60) (cap-index :u32) (cap-nonce :u32) (scan :u32) (start :u32) (selected :u60) (after-reply :u8) (tx-off :u32) (tx-len :u32) (pending :u32) (op-slot :u32) (op-gen :u60) (request :u8) (arg-off :u32) (storage-bytes :u60)) 
 :budget (:bytes 4096 :steps 32 :descriptors 4)
 :capacity 1
 :initial ((storage-bytes 131072) (generation fn2-columns-cost20-initial-generation) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 :continuations ((:accepting fn2-columns-cost20-accepting :cost (:steps 0) :writes () :next (:accepting) :uses ()) (:greeting fn2-columns-cost20-greeting :cost (:steps 0) :writes () :next (:greeting) :uses ()) (:command fn2-columns-cost20-command :cost (:steps 0) :writes () :next (:command) :uses ()) (:article-input fn2-columns-cost20-article-input :cost (:steps 0) :writes () :next (:article-input) :uses ()) (:reply fn2-columns-cost20-reply :cost (:steps 0) :writes () :next (:reply) :uses ()) (:group-select fn2-columns-cost20-group-select :cost (:steps 0) :writes () :next (:group-select) :uses ()) (:lookup fn2-columns-cost20-lookup :cost (:steps 0) :writes () :next (:lookup) :uses ()) (:render fn2-columns-cost20-render :cost (:steps 0) :writes () :next (:render) :uses ()) (:post-check fn2-columns-cost20-post-check :cost (:steps 0) :writes () :next (:post-check) :uses ()) (:log-write fn2-columns-cost20-log-write :cost (:steps 0) :writes () :next (:log-write) :uses ()) (:fence fn2-columns-cost20-fence :cost (:steps 0) :writes () :next (:fence) :uses ()) (:publish fn2-columns-cost20-publish :cost (:steps 0) :writes () :next (:publish) :uses ()) (:closing fn2-columns-cost20-closing :cost (:steps 0) :writes () :next (:closing) :uses ()) (:draining fn2-columns-cost20-draining :cost (:steps 0) :writes () :next (:draining) :uses ()) (:done fn2-columns-cost20-done :cost (:steps 0) :writes () :next (:done) :uses ()))
 :observes ((:read-result fn2-columns-cost20-observe-read :cost (:steps 0) :writes () :next () :uses ()) (:write-result fn2-columns-cost20-observe-write :cost (:steps 0) :writes () :next () :uses ())))

; No I/O is exercised: every callback is a guard-verified scalar identity stub.
(defun fn2-columns-cost-stubs (entries args observep)
  (declare (xargs :verify-guards nil))
  (if (atom entries) nil
    (cons `(defun ,(cadar entries) ,args
             (declare (ignore ,@(butlast args 1)) (xargs :guard t))
             ,(if observep '(mv nil fn2-core) '(mv 0 0 0 nil fn2-core)))
          (fn2-columns-cost-stubs (cdr entries) args observep))))
(make-event
 (let* ((world (w state)) (calling (fn2-machine-property 'fn2-columns-cost20 :calling-convention world)))
   (value `(progn
      ,@(fn2-columns-cost-stubs (fn2-machine-property 'fn2-columns-cost20 :continuations world)
                               (cadr (member-eq :run calling)) nil)
      ,@(fn2-columns-cost-stubs (fn2-machine-property 'fn2-columns-cost20 :observes world)
                               (cadr (member-eq :observe calling)) t)))))
(assert-event (equal (len (fn2-machine-property 'fn2-columns-cost20 :columns (w state))) 28))
