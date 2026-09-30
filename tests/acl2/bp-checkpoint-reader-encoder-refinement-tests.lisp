; Exact typed encoder boundary and actual bounded runner, complete literals.
(in-package "ACL2")
(include-book "../../books/bp-checkpoint-reader-encoder-refinement")
(defconst *bpcret-value* (fn-bpnr-checkpoint 1 nil nil (cons 0 1) 8 0))
(defconst *bpcret-depth* (fn-bpnr-depth-budget 8))
(defconst *bpcret-bytes* (fn-bpnr-enc *bpcret-value* *bpcret-depth*))
(defconst *bpcret-answer*
 (fn-bpcr-run (fn-bpcr-begin *bpcret-depth*) (append *bpcret-bytes* '(42 43)) 10000))
; Reachable producer positive affirms all host refinement hypotheses and
; the entire returned job, including offset, and untouched caller suffix.
(assert-event
 (and (fn-bpnr-checkpointp *bpcret-value*) (fn-bpcv-valuep *bpcret-value*)
      (consp *bpcret-bytes*)
      (equal (fn-bpn-nth 1 (fn-bpn-nth 0 *bpcret-answer*)) :done)
      (equal (fn-bpn-nth 0 *bpcret-answer*)
       (fn-bpcr-make :done nil (list *bpcret-value*) :done nil 0 0 nil nil
                     (len *bpcret-bytes*)))
      (equal (fn-bpn-nth 1 *bpcret-answer*) '(42 43))))
; Logical endpoint witness is independently obtained from the actual
; bounded run and its generic continuation theorem, not this keystone.
(defthm bpcret-complete-producer-endpoint-literal
 (and (fn-bpcv-valuep *bpcret-value*) (consp *bpcret-bytes*)
  (equal (fn-bpcr-complete (fn-bpcr-begin *bpcret-depth*)
                          (append *bpcret-bytes* '(42 43)))
   (list :done
    (fn-bpcr-make :done nil (list *bpcret-value*) :done nil 0 0 nil nil
                  (len *bpcret-bytes*)) '(42 43))))
 :hints (("Goal"
  :use ((:instance fn-bpcr-run-preserves-completion
          (job (fn-bpcr-begin *bpcret-depth*))
          (input (append *bpcret-bytes* '(42 43))) (quantum 10000)))
  :in-theory (enable fn-bpcr-complete)))
 :rule-classes nil)
; Omit typed value only: the real encoder emits a foreign ACL2 symbol,
; while bounded decoding refuses it rather than reproducing that value.
(defconst *bpcret-foreign* 'acl2::foreign-checkpoint-symbol)
(defconst *bpcret-foreign-bytes* (fn-bpnr-enc *bpcret-foreign* 20))
(defconst *bpcret-foreign-answer*
 (fn-bpcr-run (fn-bpcr-begin 20) *bpcret-foreign-bytes* 1000))
(assert-event
 (and (not (fn-bpcv-valuep *bpcret-foreign*)) (consp *bpcret-foreign-bytes*)
      (equal (fn-bpn-nth 1 (fn-bpn-nth 0 *bpcret-foreign-answer*)) :refused)
      (not (equal (fn-bpn-nth 0 *bpcret-foreign-answer*)
       (fn-bpcr-make :done nil (list *bpcret-foreign*) :done nil 0 0 nil nil
                     (len *bpcret-foreign-bytes*))))))
(defthm bpcret-endpoint-typed-hypothesis-removal-literal
 (and (not (fn-bpcv-valuep *bpcret-foreign*)) (consp *bpcret-foreign-bytes*)
  (not (equal (fn-bpcr-complete (fn-bpcr-begin 20) *bpcret-foreign-bytes*)
    (list :done (fn-bpcr-make :done nil (list *bpcret-foreign*) :done nil
                             0 0 nil nil (len *bpcret-foreign-bytes*)) nil))))
 :hints (("Goal"
  :use ((:instance fn-bpcr-run-preserves-completion
    (job (fn-bpcr-begin 20)) (input *bpcret-foreign-bytes*) (quantum 1000)))
  :in-theory (enable fn-bpcr-complete)))
 :rule-classes nil)
; Omit nonempty encoding only: valid typed NIL with exhausted depth has
; no encoding, so no source read can yield the claimed completed value.
(defthm bpcret-endpoint-nonempty-hypothesis-removal-literal
 (and (fn-bpcv-valuep nil) (not (consp (fn-bpnr-enc nil 0)))
  (not (equal (fn-bpcr-complete (fn-bpcr-begin 0) nil)
       (list :done (fn-bpcr-make :done nil '(nil) :done nil 0 0 nil nil 0) nil))))
 :hints (("Goal" :in-theory (enable fn-bpcr-complete fn-bpcr-begin
  fn-bpcr-action fn-bpcr-decode-tick fn-bpcr-make fn-bpcr-refuse)))
 :rule-classes nil)
; Omit completed quantum only, retaining both encoder hypotheses.
(assert-event
 (let ((a (fn-bpcr-run (fn-bpcr-begin *bpcret-depth*) *bpcret-bytes* 1)))
  (and (fn-bpcv-valuep *bpcret-value*) (consp *bpcret-bytes*)
   (not (equal (fn-bpn-nth 1 (fn-bpn-nth 0 a)) :done))
   (not (equal (fn-bpn-nth 0 a)
    (fn-bpcr-make :done nil (list *bpcret-value*) :done nil 0 0 nil nil
                  (len *bpcret-bytes*)))))))

; Host continuation keystone positive: a real four-turn yielded producer
; job has the complete exact endpoint, despite not yet being done.
(defconst *bpcret-yielded*
 (fn-bpcr-run (fn-bpcr-begin *bpcret-depth*) (append *bpcret-bytes* '(42 43)) 4))
(defthm bpcret-yielded-encoder-endpoint-literal
 (and (fn-bpcv-valuep *bpcret-value*) (consp *bpcret-bytes*)
      (equal (fn-bpn-nth 1 (fn-bpn-nth 0 *bpcret-yielded*)) :decoding)
  (equal (fn-bpcr-complete (fn-bpn-nth 0 *bpcret-yielded*)
                          (fn-bpn-nth 1 *bpcret-yielded*))
   (list :done
    (fn-bpcr-make :done nil (list *bpcret-value*) :done nil 0 0 nil nil
                  (len *bpcret-bytes*)) '(42 43))))
 :hints (("Goal"
  :use ((:instance fn-bpcr-run-preserves-completion
          (job (fn-bpcr-begin *bpcret-depth*))
          (input (append *bpcret-bytes* '(42 43))) (quantum 4))
        bpcret-complete-producer-endpoint-literal)
  :in-theory (disable fn-bpcr-complete fn-bpcr-run)))
 :rule-classes nil)
(defthm bpcret-yielded-typed-hypothesis-removal-literal
 (let ((a (fn-bpcr-run (fn-bpcr-begin 20) *bpcret-foreign-bytes* 1)))
  (and (not (fn-bpcv-valuep *bpcret-foreign*)) (consp *bpcret-foreign-bytes*)
   (not (equal (fn-bpcr-complete (fn-bpn-nth 0 a) (fn-bpn-nth 1 a))
    (list :done (fn-bpcr-make :done nil (list *bpcret-foreign*) :done nil
                             0 0 nil nil (len *bpcret-foreign-bytes*)) nil)))))
 :hints (("Goal"
  :use ((:instance fn-bpcr-run-preserves-completion
    (job (fn-bpcr-begin 20)) (input *bpcret-foreign-bytes*) (quantum 1))
        bpcret-endpoint-typed-hypothesis-removal-literal)
  :in-theory (disable fn-bpcr-complete fn-bpcr-run)))
 :rule-classes nil)
(defthm bpcret-yielded-nonempty-hypothesis-removal-literal
 (let ((a (fn-bpcr-run (fn-bpcr-begin 0) nil 1)))
  (and (fn-bpcv-valuep nil) (not (consp (fn-bpnr-enc nil 0)))
   (not (equal (fn-bpcr-complete (fn-bpn-nth 0 a) (fn-bpn-nth 1 a))
       (list :done (fn-bpcr-make :done nil '(nil) :done nil 0 0 nil nil 0) nil)))))
 :hints (("Goal"
  :use ((:instance fn-bpcr-run-preserves-completion
    (job (fn-bpcr-begin 0)) (input nil) (quantum 1))
        bpcret-endpoint-nonempty-hypothesis-removal-literal)
  :in-theory (disable fn-bpcr-complete fn-bpcr-run)))
 :rule-classes nil)
