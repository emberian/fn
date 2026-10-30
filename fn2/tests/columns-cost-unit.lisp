(in-package "ACL2")
(include-book "../books/machines")
; Sprint 8e3488fcb: 32 declared fields, 40 array columns, 41 total storage fields.
(defun fn2-columns-cost32-initial-generation (slot base n gen)
  (declare (ignore slot base n) (xargs :guard (unsigned-byte-p 60 gen))) gen)
(defmachine fn2-columns-cost32
 :states (:accepting :greeting :command :article-input :reply :group-select :lookup :render :post-check :log-write :fence :publish :closing :draining :done)
 :fields ((rx-slot :u32) (rx-gen :u60) (tx-slot :u32) (tx-gen :u60)
          (up-slot :u32) (up-gen :u60) (cap-index :u32) (cap-nonce :u32)
          (scan :u32) (start :u32) (selected :u60) (after-reply :u8)
          (tx-off :u32) (tx-len :u32) (pending :u32) (op-slot :u32)
          (op-gen :u60) (request :u8) (arg-off :u32) (arg-len :u32)
          (query :u60) (seek :u32) (summary-count :u60) (summary-low :u60)
          (summary-high :u60) (mid-off :u32) (mid-len :u32) (post-len :u32)
          (storage-bytes :u60) (article-limit :u32) (outcome :u8) (ordinal :u60)) 
 :budget (:bytes 4096 :steps 32 :descriptors 4)
 :capacity 1
 :initial ((storage-bytes 131072) (generation fn2-columns-cost32-initial-generation) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 :continuations ((:accepting fn2-columns-cost32-accepting :cost (:steps 0) :writes () :next (:accepting) :uses ()) (:greeting fn2-columns-cost32-greeting :cost (:steps 0) :writes () :next (:greeting) :uses ()) (:command fn2-columns-cost32-command :cost (:steps 0) :writes () :next (:command) :uses ()) (:article-input fn2-columns-cost32-article-input :cost (:steps 0) :writes () :next (:article-input) :uses ()) (:reply fn2-columns-cost32-reply :cost (:steps 0) :writes () :next (:reply) :uses ()) (:group-select fn2-columns-cost32-group-select :cost (:steps 0) :writes () :next (:group-select) :uses ()) (:lookup fn2-columns-cost32-lookup :cost (:steps 0) :writes () :next (:lookup) :uses ()) (:render fn2-columns-cost32-render :cost (:steps 0) :writes () :next (:render) :uses ()) (:post-check fn2-columns-cost32-post-check :cost (:steps 0) :writes () :next (:post-check) :uses ()) (:log-write fn2-columns-cost32-log-write :cost (:steps 0) :writes () :next (:log-write) :uses ()) (:fence fn2-columns-cost32-fence :cost (:steps 0) :writes () :next (:fence) :uses ()) (:publish fn2-columns-cost32-publish :cost (:steps 0) :writes () :next (:publish) :uses ()) (:closing fn2-columns-cost32-closing :cost (:steps 0) :writes () :next (:closing) :uses ()) (:draining fn2-columns-cost32-draining :cost (:steps 0) :writes () :next (:draining) :uses ()) (:done fn2-columns-cost32-done :cost (:steps 0) :writes () :next (:done) :uses ()))
 :observes ((:read-result fn2-columns-cost32-observe-read :cost (:steps 0) :writes () :next () :uses ()) (:write-result fn2-columns-cost32-observe-write :cost (:steps 0) :writes () :next () :uses ())))

; No I/O is exercised: every callback is a guard-verified scalar identity stub.
(defun fn2-columns-cost-stubs (entries args observep)
  (declare (xargs :verify-guards nil))
  (if (atom entries) nil
    (cons `(defun ,(cadar entries) ,args
             (declare (ignore ,@(butlast args 1)) (xargs :guard t))
             ,(if observep '(mv nil fn2-core) '(mv 0 0 0 nil fn2-core)))
          (fn2-columns-cost-stubs (cdr entries) args observep))))
(make-event
 (let* ((world (w state)) (calling (fn2-machine-property 'fn2-columns-cost32 :calling-convention world)))
   (value `(progn
      ,@(fn2-columns-cost-stubs (fn2-machine-property 'fn2-columns-cost32 :continuations world)
                               (cadr (member-eq :run calling)) nil)
      ,@(fn2-columns-cost-stubs (fn2-machine-property 'fn2-columns-cost32 :observes world)
                               (cadr (member-eq :observe calling)) t)))))
(assert-event (equal (len (fn2-machine-property 'fn2-columns-cost32 :columns (w state))) 40))
(defun fn2-columns-cost-unit ()
 (declare (xargs :guard t))
 (with-local-stobj fn2-columns-cost32
  (mv-let (ok fn2-columns-cost32)
   (let ((fn2-columns-cost32 (fn2-columns-cost32-prepare 1 0 17 fn2-columns-cost32)))
    (mv (and (fn2-columns-cost32-wfp fn2-columns-cost32)
             (equal (fn2-columns-cost32-rows fn2-columns-cost32) 1)
             (equal (fn2-columns-cost32-generation 0 fn2-columns-cost32) 17)
             (equal (fn2-columns-cost32-storage-bytes 0 fn2-columns-cost32) 131072)
             (equal (fn2-columns-cost32-ready-prev 0 fn2-columns-cost32) *fn2-none*)
             (equal (fn2-columns-cost32-ready-next 0 fn2-columns-cost32) *fn2-none*)) fn2-columns-cost32)) ok)))
(assert-event (fn2-columns-cost-unit))
(value-triple (cw "COLUMNS COST UNIT: sprint 32 declared/40 array/41 total fields, initialization PASS~%"))
