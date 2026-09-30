; Exact encoder-to-bounded-reader composition, built from actual continuation.
; Supported typed producer values compose to the resumable logical endpoint.
; File integrity, charged workspace and native recovery installation remain separate.
(in-package "ACL2")
(include-book "bp-node-checkpoint-reader")

(local (defthm fn-bpcr-live-completion-unfolds
 (let* ((action (fn-bpcr-action job))
        (tick (fn-bpcr-decode-tick job (if (equal action :read) (car input) 0)))
        (next (fn-bpn-nth 0 tick))
        (rest (if (equal (fn-bpn-nth 1 tick) 1) (fn-cbor-ag-cdr input) input)))
  (implies (and (equal (fn-bpn-nth 1 job) :decoding)
                (or (not (equal action :read)) (consp input)))
   (equal (fn-bpcr-complete job input)
    (if (equal (fn-bpn-nth 1 next) :decoding)
        (fn-bpcr-complete next rest)
        (list (fn-bpn-nth 1 next) next rest)))))
 :hints (("Goal" :expand ((fn-bpcr-complete job input))
                  :in-theory (disable fn-bpcr-complete fn-bpcr-action
                                      fn-bpcr-decode-tick)))
 :rule-classes nil))

; These single-transition equalities are definition-level proof supports,
; not standalone representation or host-called completion claims.
(local (defthm fn-bpcr-encoded-nil-continuation-by-definition
 (implies (posp depth)
  (equal
   (fn-bpcr-complete
    (fn-bpcr-make :decoding (cons depth goals) values :tag nil 0 0 nil nil offset)
    (append (fn-bpnr-enc nil depth) input))
   (fn-bpcr-complete
    (fn-bpcr-make :decoding goals (cons nil values) :tag nil 0 0 nil nil
                  (1+ (nfix offset))) input)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-bpcr-live-completion-unfolds
   (job (fn-bpcr-make :decoding (cons depth goals) values :tag nil 0 0 nil nil offset))
   (input (append (fn-bpnr-enc nil depth) input))))
  :in-theory (e/d (fn-bpnr-enc fn-bpcr-decode-tick fn-bpcr-action
                   fn-bpcr-make fn-bpcr-leaf fn-bpcr-refuse)
                  (fn-bpcr-complete fn-bpcr-keyword-byte
                   fn-bpcr-keyword-terminal))))
 :rule-classes nil))

(local (defthm fn-bpcr-pair-tag-continuation-by-definition
 (implies (posp depth)
  (equal
   (fn-bpcr-complete
    (fn-bpcr-make :decoding (cons depth goals) values :tag nil 0 0 nil nil offset)
    (cons 10 input))
   (fn-bpcr-complete
    (fn-bpcr-make :decoding
     (cons (1- depth) (cons (1- depth) (cons :pair goals)))
     values :tag nil 0 0 nil nil (1+ (nfix offset))) input)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-bpcr-live-completion-unfolds
   (job (fn-bpcr-make :decoding (cons depth goals) values :tag nil 0 0 nil nil offset))
   (input (cons 10 input))))
  :in-theory (e/d (fn-bpcr-decode-tick fn-bpcr-action fn-bpcr-make
                   fn-bpcr-leaf fn-bpcr-refuse)
                  (fn-bpcr-complete fn-bpcr-keyword-byte
                   fn-bpcr-keyword-terminal))))
 :rule-classes nil))

(local (defthm fn-bpcr-pair-combine-continuation-by-definition
 (equal
   (fn-bpcr-complete
    (fn-bpcr-make :decoding (cons :pair goals)
      (cons right (cons left values)) :tag nil 0 0 nil nil offset) input)
   (fn-bpcr-complete
    (fn-bpcr-make :decoding goals (cons (cons left right) values)
      :tag nil 0 0 nil nil (nfix offset)) input))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-bpcr-live-completion-unfolds
   (job (fn-bpcr-make :decoding (cons :pair goals)
      (cons right (cons left values)) :tag nil 0 0 nil nil offset))))
  :in-theory (e/d (fn-bpcr-decode-tick fn-bpcr-action fn-bpcr-make
                   fn-bpcr-leaf fn-bpcr-refuse)
                  (fn-bpcr-complete fn-bpcr-keyword-byte
                   fn-bpcr-keyword-terminal))))
 :rule-classes nil))

; Actual eight-turn word accumulator against the existing BP u64 decoder.
(local (defthm fn-bpcr-eight-word-turns-by-definition
 (let ((bytes (list b0 b1 b2 b3 b4 b5 b6 b7)))
  (implies (fn-cbor-octet-listp bytes)
   (equal
    (fn-bpcr-run
     (fn-bpcr-make :decoding goals values :word 5 8 0 nil nil offset)
     (append bytes input) 8)
    (list
     (fn-bpcr-make :decoding (fn-cbor-ag-cdr goals)
       (cons (fn-bpc-u64-from bytes) values) :tag nil 0 0 nil nil
       (+ 8 (nfix offset))) input 8 8))))
 :hints (("Goal" :do-not-induct t
  :expand ((:free (job input) (fn-bpcr-run job input 8)) (:free (job input) (fn-bpcr-run job input 7)) (:free (job input) (fn-bpcr-run job input 6)) (:free (job input) (fn-bpcr-run job input 5)) (:free (job input) (fn-bpcr-run job input 4)) (:free (job input) (fn-bpcr-run job input 3)) (:free (job input) (fn-bpcr-run job input 2)) (:free (job input) (fn-bpcr-run job input 1)) (:free (job input) (fn-bpcr-run job input 0)))
  :in-theory (e/d (fn-bpcr-run fn-bpcr-decode-tick fn-bpcr-action
                   fn-bpcr-make fn-bpcr-leaf fn-bpcr-refuse
                   fn-bpc-u64-from fn-cbor-u32-from fn-cbor-octet-listp
                   fn-cbor-octetp)
                  (fn-bpcr-complete fn-bpcr-keyword-byte
                   fn-bpcr-keyword-terminal))))
 :rule-classes nil))

(local (defthm fn-bpcr-word-natural-continuation
 (let ((bytes (list b0 b1 b2 b3 b4 b5 b6 b7)))
  (implies (fn-cbor-octet-listp bytes)
   (equal
    (fn-bpcr-complete
     (fn-bpcr-make :decoding goals values :word 5 8 0 nil nil offset)
     (append bytes input))
    (fn-bpcr-complete
     (fn-bpcr-make :decoding (fn-cbor-ag-cdr goals)
       (cons (fn-bpc-u64-from bytes) values) :tag nil 0 0 nil nil
       (+ 8 (nfix offset))) input))))
 :hints (("Goal"
  :use ((:instance fn-bpcr-eight-word-turns-by-definition)
        (:instance fn-bpcr-run-preserves-completion
         (job (fn-bpcr-make :decoding goals values :word 5 8 0 nil nil offset))
         (input (append (list b0 b1 b2 b3 b4 b5 b6 b7) input))
         (quantum 8)))
  :in-theory (e/d (fn-bpn-nth)
   (fn-bpcr-run fn-bpcr-complete fn-bpcr-make fn-bpcr-decode-tick
    fn-bpcr-action fn-bpc-u64-from))))
 :rule-classes nil))

(local (defun fn-bpcr-reverse-induction (work out offset)
 (declare (xargs :measure (len work)))
 (if (consp work)
     (fn-bpcr-reverse-induction (cdr work) (cons (car work) out) (nfix offset))
   (list out offset))))

(local (defthm fn-bpcr-reverse-completion-unfolds
 (equal
  (fn-bpcr-complete
   (fn-bpcr-make :decoding goals values :reverse kind 0 0 work out offset) input)
  (if (consp work)
   (fn-bpcr-complete
    (fn-bpcr-make :decoding goals values :reverse kind 0 0
      (cdr work) (cons (car work) out) (nfix offset)) input)
   (fn-bpcr-complete
    (fn-bpcr-make :decoding (fn-cbor-ag-cdr goals) (cons out values)
      :tag nil 0 0 nil nil (nfix offset)) input)))
 :hints (("Goal"
  :use ((:instance fn-bpcr-live-completion-unfolds
   (job (fn-bpcr-make :decoding goals values :reverse kind 0 0 work out offset))))
  :in-theory (e/d (fn-bpcr-decode-tick fn-bpcr-action fn-bpcr-make
                   fn-bpcr-leaf fn-bpcr-refuse)
                  (fn-bpcr-complete fn-bpcr-keyword-byte fn-bpcr-keyword-terminal))))))

; Reversal is a trajectory of actual pure constructor turns.
(local (defthm fn-bpcr-reverse-continuation
 (equal
  (fn-bpcr-complete
   (fn-bpcr-make :decoding goals values :reverse kind 0 0 work out offset) input)
  (fn-bpcr-complete
   (fn-bpcr-make :decoding (fn-cbor-ag-cdr goals)
    (cons (fn-ag-rev-onto work out) values) :tag nil 0 0 nil nil
    (nfix offset)) input))
 :hints (("Goal" :induct (fn-bpcr-reverse-induction work out offset)
  :in-theory (e/d (fn-ag-rev-onto)
   (fn-bpcr-complete fn-bpcr-decode-tick fn-bpcr-action fn-bpcr-make
    fn-bpcr-leaf fn-bpcr-refuse fn-bpcr-keyword-byte fn-bpcr-keyword-terminal
    fn-bpcr-reverse-completion-unfolds)))
  ("Subgoal *1/2" :use ((:instance fn-bpcr-reverse-completion-unfolds)))
  ("Subgoal *1/1" :use ((:instance fn-bpcr-reverse-completion-unfolds))))
 :rule-classes nil))

(local (defun fn-bpcr-octets-induction (bytes work offset)
 (declare (xargs :measure (len bytes)))
 (if (consp (cdr bytes))
  (fn-bpcr-octets-induction (cdr bytes) (cons (car bytes) work)
                           (1+ (nfix offset)))
  (list work offset))))

(local (defthm fn-bpcr-consp-length-positive
 (implies (consp xs) (< 0 (len xs)))
 :hints (("Goal" :in-theory (enable len)))
 :rule-classes :linear))

(local (defthm fn-bpcr-octet-read-unfolds
 (implies (consp bytes)
  (equal
   (fn-bpcr-complete
    (fn-bpcr-make :decoding goals values :octets 9 (len bytes) 0 work nil offset)
    (append bytes input))
   (fn-bpcr-complete
    (fn-bpcr-make :decoding goals values
     (if (consp (cdr bytes)) :octets :reverse) 9
     (if (consp (cdr bytes)) (len (cdr bytes)) 0) 0
     (cons (car bytes) work) nil (1+ (nfix offset)))
    (append (cdr bytes) input))))
 :hints (("Goal"
  :use ((:instance fn-bpcr-live-completion-unfolds
   (job (fn-bpcr-make :decoding goals values :octets 9 (len bytes) 0 work nil offset))
   (input (append bytes input))))
  :in-theory (e/d (fn-bpcr-decode-tick fn-bpcr-action fn-bpcr-make
                   fn-bpcr-leaf fn-bpcr-refuse)
                  (fn-bpcr-complete fn-bpcr-keyword-byte fn-bpcr-keyword-terminal))))
 :rule-classes nil))

; All incoming payload cells are consumed by actual one-octet turns.
(local (defthm fn-bpcr-counted-octet-continuation
 (implies (consp bytes)
  (equal
   (fn-bpcr-complete
    (fn-bpcr-make :decoding goals values :octets 9 (len bytes) 0 work nil offset)
    (append bytes input))
   (fn-bpcr-complete
    (fn-bpcr-make :decoding goals values :reverse 9 0 0
     (revappend bytes work) nil (+ (len bytes) (nfix offset))) input)))
 :hints (("Goal" :induct (fn-bpcr-octets-induction bytes work offset)
  :in-theory (e/d (revappend)
   (fn-bpcr-complete fn-bpcr-decode-tick fn-bpcr-action fn-bpcr-make
    fn-bpcr-leaf fn-bpcr-refuse fn-bpcr-keyword-byte fn-bpcr-keyword-terminal revappend-removal
    fn-bpcr-reverse-completion-unfolds)))
  ("Subgoal *1/2" :use ((:instance fn-bpcr-octet-read-unfolds)))
  ("Subgoal *1/1" :use ((:instance fn-bpcr-octet-read-unfolds))))
 :rule-classes nil))

; All counted leaf kinds share the actual eight-byte accumulation. The final
; decision remains FN-BPCR-DECODE-TICK itself, not a parallel seal interpreter.
(local (defthm fn-bpcr-eight-word-turns-all-kinds-by-definition
 (let ((bytes (list b0 b1 b2 b3 b4 b5 b6 b7)))
  (implies (fn-cbor-octet-listp bytes)
   (equal
    (fn-bpcr-run
     (fn-bpcr-make :decoding goals values :word kind 8 0 nil nil offset)
     (append bytes input) 8)
    (list
     (fn-bpn-nth 0
      (fn-bpcr-decode-tick
       (fn-bpcr-make :decoding goals values :word kind 1
        (fn-bpc-u64-from (list 0 b0 b1 b2 b3 b4 b5 b6)) nil nil
        (+ 7 (nfix offset))) b7)) input 8 8))))
 :hints (("Goal" :do-not-induct t
  :expand ((:free (job input) (fn-bpcr-run job input 8))
           (:free (job input) (fn-bpcr-run job input 7))
           (:free (job input) (fn-bpcr-run job input 6))
           (:free (job input) (fn-bpcr-run job input 5))
           (:free (job input) (fn-bpcr-run job input 4))
           (:free (job input) (fn-bpcr-run job input 3))
           (:free (job input) (fn-bpcr-run job input 2))
           (:free (job input) (fn-bpcr-run job input 1))
           (:free (job input) (fn-bpcr-run job input 0)))
  :in-theory (e/d (fn-bpcr-run fn-bpcr-decode-tick fn-bpcr-action
                   fn-bpcr-make fn-bpcr-leaf fn-bpcr-refuse
                   fn-bpc-u64-from fn-cbor-u32-from fn-cbor-octet-listp
                   fn-cbor-octetp)
                  (fn-bpcr-complete fn-bpcr-keyword-byte
                   fn-bpcr-keyword-terminal fn-bpcr-reverse-completion-unfolds))))
 :rule-classes nil))

(local (defthm fn-bpcr-u64-byte-list-rebuild-by-definition
 (equal (fn-bpc-u64-bytes n)
  (list (nth 0 (fn-bpc-u64-bytes n)) (nth 1 (fn-bpc-u64-bytes n))
        (nth 2 (fn-bpc-u64-bytes n)) (nth 3 (fn-bpc-u64-bytes n))
        (nth 4 (fn-bpc-u64-bytes n)) (nth 5 (fn-bpc-u64-bytes n))
        (nth 6 (fn-bpc-u64-bytes n)) (nth 7 (fn-bpc-u64-bytes n))))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-bpc-u64-bytes fn-bpc-u32-octets binary-append nth zp car-cons cdr-cons))))
 :rule-classes nil))

(local (defthm fn-bpcr-eight-encoded-natural-turns
 (implies (and (natp n) (<= n *fn-bpc-max-uint*))
  (equal
   (fn-bpcr-run
    (fn-bpcr-make :decoding goals values :word 5 8 0 nil nil offset)
    (append (fn-bpc-u64-bytes n) input) 8)
   (list
    (fn-bpcr-make :decoding (fn-cbor-ag-cdr goals)
     (cons n values) :tag nil 0 0 nil nil (+ 8 (nfix offset))) input 8 8)))
 :hints (("Goal"
  :use ((:instance fn-bpcr-eight-word-turns-by-definition
    (b0 (nth 0 (fn-bpc-u64-bytes n))) (b1 (nth 1 (fn-bpc-u64-bytes n)))
    (b2 (nth 2 (fn-bpc-u64-bytes n))) (b3 (nth 3 (fn-bpc-u64-bytes n)))
    (b4 (nth 4 (fn-bpc-u64-bytes n))) (b5 (nth 5 (fn-bpc-u64-bytes n)))
    (b6 (nth 6 (fn-bpc-u64-bytes n))) (b7 (nth 7 (fn-bpc-u64-bytes n))))
   (:instance fn-bpcr-u64-byte-list-rebuild-by-definition)
   (:instance fn-bpc-u64-bytes-have-eight-octets)
   (:instance fn-bpc-u64-from-of-u64-bytes))
  :in-theory (disable fn-bpcr-run fn-bpcr-complete fn-bpcr-make
   fn-bpc-u64-bytes fn-bpc-u64-from fn-bpc-u32-octets floor mod
   fn-bpcr-reverse-completion-unfolds)))
 :rule-classes nil))

(local (defthm fn-bpcr-word-tag-continuation-by-definition
 (implies (and (posp depth) (member-equal tag '(2 5 9)))
  (equal
   (fn-bpcr-complete
    (fn-bpcr-make :decoding (cons depth goals) values :tag nil 0 0 nil nil offset)
    (cons tag input))
   (fn-bpcr-complete
    (fn-bpcr-make :decoding (cons depth goals) values :word tag 8 0 nil nil
      (1+ (nfix offset))) input)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-bpcr-live-completion-unfolds
   (job (fn-bpcr-make :decoding (cons depth goals) values :tag nil 0 0 nil nil offset))
   (input (cons tag input))))
  :in-theory (e/d (fn-bpcr-decode-tick fn-bpcr-action fn-bpcr-make
                   fn-bpcr-leaf fn-bpcr-refuse)
                  (fn-bpcr-complete fn-bpcr-keyword-byte fn-bpcr-keyword-terminal
                   fn-bpcr-reverse-completion-unfolds))))
 :rule-classes nil))

(local (defthm fn-bpcr-encoded-natural-continuation
 (implies (and (posp depth) (natp n) (<= n *fn-bpc-max-uint*))
  (equal
   (fn-bpcr-complete
    (fn-bpcr-make :decoding (cons depth goals) values :tag nil 0 0 nil nil offset)
    (append (fn-bpnr-enc n depth) input))
   (fn-bpcr-complete
    (fn-bpcr-make :decoding goals (cons n values) :tag nil 0 0 nil nil
      (+ 9 (nfix offset))) input)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-bpcr-word-tag-continuation-by-definition
         (tag 5) (input (append (fn-bpc-u64-bytes n) input)))
        (:instance fn-bpcr-eight-encoded-natural-turns
         (goals (cons depth goals)) (offset (1+ (nfix offset))))
        (:instance fn-bpcr-run-preserves-completion
         (job (fn-bpcr-make :decoding (cons depth goals) values :word 5 8 0
                           nil nil (1+ (nfix offset))))
         (input (append (fn-bpc-u64-bytes n) input)) (quantum 8)))
  :in-theory (e/d (fn-bpnr-enc fn-bpn-nth)
   (fn-bpcr-run fn-bpcr-complete fn-bpcr-make fn-bpcr-decode-tick
    fn-bpcr-action fn-bpc-u64-bytes fn-bpc-u64-from
    fn-bpcr-reverse-completion-unfolds))))
 :rule-classes nil))

(local (defthm fn-bpcr-eight-octet-length-turns-by-definition
 (let ((bytes (list b0 b1 b2 b3 b4 b5 b6 b7)))
  (implies (and (fn-cbor-octet-listp bytes) (posp (fn-bpc-u64-from bytes)))
   (equal
    (fn-bpcr-run
     (fn-bpcr-make :decoding goals values :word 9 8 0 nil nil offset)
     (append bytes input) 8)
    (list
     (fn-bpcr-make :decoding goals values :octets 9
       (fn-bpc-u64-from bytes) 0 nil nil
       (+ 8 (nfix offset))) input 8 8))))
 :hints (("Goal" :do-not-induct t
  :expand ((:free (job input) (fn-bpcr-run job input 8)) (:free (job input) (fn-bpcr-run job input 7)) (:free (job input) (fn-bpcr-run job input 6)) (:free (job input) (fn-bpcr-run job input 5)) (:free (job input) (fn-bpcr-run job input 4)) (:free (job input) (fn-bpcr-run job input 3)) (:free (job input) (fn-bpcr-run job input 2)) (:free (job input) (fn-bpcr-run job input 1)) (:free (job input) (fn-bpcr-run job input 0)))
  :in-theory (e/d (fn-bpcr-run fn-bpcr-decode-tick fn-bpcr-action
                   fn-bpcr-make fn-bpcr-leaf fn-bpcr-refuse
                   fn-bpc-u64-from fn-cbor-u32-from fn-cbor-octet-listp
                   fn-cbor-octetp)
                  (fn-bpcr-complete fn-bpcr-keyword-byte
                   fn-bpcr-keyword-terminal fn-bpcr-reverse-completion-unfolds))))
 :rule-classes nil))


(local (defthm fn-bpcr-eight-encoded-octet-length-turns
 (implies (and (posp n) (<= n *fn-bpc-max-uint*))
  (equal
   (fn-bpcr-run
    (fn-bpcr-make :decoding goals values :word 9 8 0 nil nil offset)
    (append (fn-bpc-u64-bytes n) input) 8)
   (list
    (fn-bpcr-make :decoding goals values :octets 9 n 0 nil nil (+ 8 (nfix offset))) input 8 8)))
 :hints (("Goal"
  :use ((:instance fn-bpcr-eight-octet-length-turns-by-definition
    (b0 (nth 0 (fn-bpc-u64-bytes n))) (b1 (nth 1 (fn-bpc-u64-bytes n)))
    (b2 (nth 2 (fn-bpc-u64-bytes n))) (b3 (nth 3 (fn-bpc-u64-bytes n)))
    (b4 (nth 4 (fn-bpc-u64-bytes n))) (b5 (nth 5 (fn-bpc-u64-bytes n)))
    (b6 (nth 6 (fn-bpc-u64-bytes n))) (b7 (nth 7 (fn-bpc-u64-bytes n))))
   (:instance fn-bpcr-u64-byte-list-rebuild-by-definition)
   (:instance fn-bpc-u64-bytes-have-eight-octets)
   (:instance fn-bpc-u64-from-of-u64-bytes))
  :in-theory (disable fn-bpcr-run fn-bpcr-complete fn-bpcr-make
   fn-bpc-u64-bytes fn-bpc-u64-from fn-bpc-u32-octets floor mod
   fn-bpcr-reverse-completion-unfolds)))
 :rule-classes nil))


(local (defthm fn-bpcr-rev-onto-of-rev-onto
 (equal (fn-ag-rev-onto (fn-ag-rev-onto a z) b)
        (fn-ag-rev-onto z (append a b)))
 :hints (("Goal" :in-theory (e/d (fn-ag-rev-onto)
   (fn-bpcr-complete fn-bpcr-reverse-completion-unfolds))))))

(local (defthm fn-bpcr-revappend-is-rev-onto-by-definition
 (equal (revappend a b) (fn-ag-rev-onto a b))
 :hints (("Goal" :induct (fn-ag-rev-onto a b)
  :in-theory (e/d (revappend fn-ag-rev-onto)
   (revappend-removal fn-bpcr-complete fn-bpcr-reverse-completion-unfolds))))))

(local (defthm fn-bpcr-rev-onto-empty-by-definition
 (equal (fn-ag-rev-onto nil out) out)
 :hints (("Goal" :in-theory (enable fn-ag-rev-onto)))))

(local (defthm fn-bpcr-encoded-octet-list-continuation
 (implies (and (posp depth) (consp bytes) (fn-cbor-octet-listp bytes)
               (<= (len bytes) *fn-bpc-max-uint*))
  (equal
   (fn-bpcr-complete
    (fn-bpcr-make :decoding (cons depth goals) values :tag nil 0 0 nil nil offset)
    (append (fn-bpnr-enc bytes depth) input))
   (fn-bpcr-complete
    (fn-bpcr-make :decoding goals (cons bytes values) :tag nil 0 0 nil nil
      (+ 9 (len bytes) (nfix offset))) input)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-bpcr-word-tag-continuation-by-definition
         (tag 9) (input (append (fn-bpc-u64-bytes (len bytes)) (append bytes input))))
        (:instance fn-bpcr-eight-encoded-octet-length-turns
         (n (len bytes)) (goals (cons depth goals)) (offset (1+ (nfix offset)))
         (input (append bytes input)))
        (:instance fn-bpcr-run-preserves-completion
         (job (fn-bpcr-make :decoding (cons depth goals) values :word 9 8 0
                           nil nil (1+ (nfix offset))))
         (input (append (fn-bpc-u64-bytes (len bytes)) (append bytes input)))
         (quantum 8))
        (:instance fn-bpcr-counted-octet-continuation
         (goals (cons depth goals)) (work nil) (offset (+ 9 (nfix offset))))
        (:instance fn-bpcr-reverse-continuation
         (goals (cons depth goals)) (kind 9) (work (revappend bytes nil)) (out nil)
         (offset (+ 9 (len bytes) (nfix offset)))))
  :in-theory (e/d (fn-bpnr-enc fn-bpnr-counted fn-bpn-nth)
   (fn-bpcr-run fn-bpcr-complete fn-bpcr-make fn-bpcr-decode-tick
    fn-bpcr-action fn-bpc-u64-bytes fn-bpc-u64-from fn-ag-rev-onto
    fn-bpcr-reverse-completion-unfolds revappend-removal))))
 :rule-classes nil))

; Finite typed keywords are sealed from the actual cold vocabulary. No
; symbol/string constructor or INTERN participates in a served turn.
(local (defthm fn-bpcr-encoded-keyword-turns
 (implies (and (posp depth) (member-equal keyword *fn-bpcv-keywords*))
  (let* ((bytes (fn-bpnr-enc keyword depth)) (turns (len bytes)))
   (equal
    (fn-bpcr-run
     (fn-bpcr-make :decoding (cons depth goals) values :tag nil 0 0 nil nil offset)
     (append bytes input) turns)
    (list
     (fn-bpcr-make :decoding goals (cons keyword values) :tag nil 0 0 nil nil
                   (+ turns (nfix offset))) input turns turns))))
 :hints (("Goal" :do-not-induct t
  :expand ((:free (job input quantum) (fn-bpcr-run job input quantum)))
  :in-theory (e/d (fn-bpnr-enc fn-bpnr-counted fn-bpnr-symbol-tag fn-bpnr-codes
                   fn-bpcr-run fn-bpcr-decode-tick fn-bpcr-action
                   fn-bpcr-make fn-bpcr-leaf fn-bpcr-refuse
                   fn-bpcr-keyword-byte fn-bpcr-keyword-terminal member-equal
                   fn-bpc-u64-bytes fn-bpc-u32-octets)
                  (fn-bpcr-complete fn-bpcr-reverse-completion-unfolds
                   floor mod rewrite-floor-mod rewrite-mod-mod floor-floor-integer))))
 :rule-classes nil))

(local (defthm fn-bpcr-encoded-keyword-continuation
 (implies (and (posp depth) (member-equal keyword *fn-bpcv-keywords*))
  (equal
   (fn-bpcr-complete
    (fn-bpcr-make :decoding (cons depth goals) values :tag nil 0 0 nil nil offset)
    (append (fn-bpnr-enc keyword depth) input))
   (fn-bpcr-complete
    (fn-bpcr-make :decoding goals (cons keyword values) :tag nil 0 0 nil nil
                  (+ (len (fn-bpnr-enc keyword depth)) (nfix offset))) input)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-bpcr-encoded-keyword-turns)
        (:instance fn-bpcr-run-preserves-completion
         (job (fn-bpcr-make :decoding (cons depth goals) values :tag nil 0 0 nil nil offset))
         (input (append (fn-bpnr-enc keyword depth) input))
         (quantum (len (fn-bpnr-enc keyword depth)))))
  :in-theory (e/d (fn-bpn-nth)
   (fn-bpcr-run fn-bpcr-complete fn-bpcr-make fn-bpnr-enc
    fn-bpcr-reverse-completion-unfolds))))
 :rule-classes nil))

(local (defthm fn-bpcr-encoding-implies-positive-depth
 (implies (consp (fn-bpnr-enc value depth)) (posp depth))
 :rule-classes ((:forward-chaining :trigger-terms ((fn-bpnr-enc value depth))))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-bpnr-enc)
   (fn-bpc-u64-bytes fn-bpnr-counted fn-bpnr-codes
    fn-bpcr-complete fn-bpcr-reverse-completion-unfolds))))))

(local (defthm fn-bpcr-encoding-list-shape
 (implies (fn-bpnr-enc value depth)
  (and (consp (fn-bpnr-enc value depth))
       (true-listp (fn-bpnr-enc value depth))
       (fn-cbor-octet-listp (fn-bpnr-enc value depth))))
 :hints (("Goal" :use ((:instance fn-bpnr-enc-octets (x value) (d depth)))
                  :in-theory nil))))


(local (defthm fn-bpcr-encoded-nil-continuation-by-definition-local-rewrite
 (implies (posp depth)
  (equal
   (fn-bpcr-complete
    (fn-bpcr-make :decoding (cons depth goals) values :tag nil 0 0 nil nil offset)
    (append (fn-bpnr-enc nil depth) input))
   (fn-bpcr-complete
    (fn-bpcr-make :decoding goals (cons nil values) :tag nil 0 0 nil nil
                  (1+ (nfix offset))) input)))
 :hints (("Goal" :use fn-bpcr-encoded-nil-continuation-by-definition :in-theory nil))))

(local (defthm fn-bpcr-pair-tag-continuation-by-definition-local-rewrite
 (implies (posp depth)
  (equal
   (fn-bpcr-complete
    (fn-bpcr-make :decoding (cons depth goals) values :tag nil 0 0 nil nil offset)
    (cons 10 input))
   (fn-bpcr-complete
    (fn-bpcr-make :decoding
     (cons (1- depth) (cons (1- depth) (cons :pair goals)))
     values :tag nil 0 0 nil nil (1+ (nfix offset))) input)))
 :hints (("Goal" :use fn-bpcr-pair-tag-continuation-by-definition :in-theory nil))))

(local (defthm fn-bpcr-pair-combine-continuation-by-definition-local-rewrite
 (equal
   (fn-bpcr-complete
    (fn-bpcr-make :decoding (cons :pair goals)
      (cons right (cons left values)) :tag nil 0 0 nil nil offset) input)
   (fn-bpcr-complete
    (fn-bpcr-make :decoding goals (cons (cons left right) values)
      :tag nil 0 0 nil nil (nfix offset)) input))
 :hints (("Goal" :use fn-bpcr-pair-combine-continuation-by-definition :in-theory nil))))

(local (defthm fn-bpcr-encoded-natural-continuation-local-rewrite
 (implies (and (posp depth) (natp n) (<= n *fn-bpc-max-uint*))
  (equal
   (fn-bpcr-complete
    (fn-bpcr-make :decoding (cons depth goals) values :tag nil 0 0 nil nil offset)
    (append (fn-bpnr-enc n depth) input))
   (fn-bpcr-complete
    (fn-bpcr-make :decoding goals (cons n values) :tag nil 0 0 nil nil
      (+ 9 (nfix offset))) input)))
 :hints (("Goal" :use fn-bpcr-encoded-natural-continuation :in-theory nil))))

(local (defthm fn-bpcr-encoded-octet-list-continuation-local-rewrite
 (implies (and (posp depth) (consp bytes) (fn-cbor-octet-listp bytes)
               (<= (len bytes) *fn-bpc-max-uint*))
  (equal
   (fn-bpcr-complete
    (fn-bpcr-make :decoding (cons depth goals) values :tag nil 0 0 nil nil offset)
    (append (fn-bpnr-enc bytes depth) input))
   (fn-bpcr-complete
    (fn-bpcr-make :decoding goals (cons bytes values) :tag nil 0 0 nil nil
      (+ 9 (len bytes) (nfix offset))) input)))
 :hints (("Goal" :use fn-bpcr-encoded-octet-list-continuation :in-theory nil))))

(local (defthm fn-bpcr-encoded-keyword-continuation-local-rewrite
 (implies (and (posp depth) (member-equal keyword *fn-bpcv-keywords*))
  (equal
   (fn-bpcr-complete
    (fn-bpcr-make :decoding (cons depth goals) values :tag nil 0 0 nil nil offset)
    (append (fn-bpnr-enc keyword depth) input))
   (fn-bpcr-complete
    (fn-bpcr-make :decoding goals (cons keyword values) :tag nil 0 0 nil nil
                  (+ (len (fn-bpnr-enc keyword depth)) (nfix offset))) input)))
 :hints (("Goal" :use fn-bpcr-encoded-keyword-continuation :in-theory nil))))


(local (defthm fn-bpcr-nil-encoding-length-by-definition
 (implies (posp depth) (equal (len (fn-bpnr-enc nil depth)) 1))
 :hints (("Goal" :in-theory (enable fn-bpnr-enc)))))
(local (defthm fn-bpcr-natural-encoding-length-by-definition
 (implies (and (posp depth) (natp n) (<= n *fn-bpc-max-uint*))
  (equal (len (fn-bpnr-enc n depth)) 9))
 :hints (("Goal" :use ((:instance fn-bpc-u64-bytes-have-eight-octets))
 :in-theory (e/d (fn-bpnr-enc) (fn-bpc-u64-bytes))))))
(local (defthm fn-bpcr-octet-encoding-length-by-definition
 (implies (and (posp depth) (consp bytes) (fn-cbor-octet-listp bytes)
               (<= (len bytes) *fn-bpc-max-uint*))
  (equal (len (fn-bpnr-enc bytes depth)) (+ 9 (len bytes))))
 :hints (("Goal" :use ((:instance fn-bpc-u64-bytes-have-eight-octets (n (len bytes))))
 :in-theory (e/d (fn-bpnr-enc fn-bpnr-counted)
                         (fn-bpc-u64-bytes))))))
(local (defthm fn-bpcr-pair-encoding-length-by-definition
 (implies (and (posp depth) (consp value) (not (fn-cbor-octet-listp value))
   (fn-bpnr-enc (car value) (1- depth)) (fn-bpnr-enc (cdr value) (1- depth)))
  (equal (len (fn-bpnr-enc value depth))
   (+ 1 (len (fn-bpnr-enc (car value) (1- depth)))
        (len (fn-bpnr-enc (cdr value) (1- depth))))))
 :hints (("Goal" :expand ((fn-bpnr-enc value depth))
  :in-theory (disable fn-bpnr-enc fn-bpcr-reverse-completion-unfolds)))))


(local (defthm fn-bpcr-typed-encoding-constraints
 (implies (consp (fn-bpnr-enc value depth))
  (and (posp depth)
   (implies (natp value) (<= value *fn-bpc-max-uint*))
   (implies (and (consp value) (fn-cbor-octet-listp value))
            (<= (len value) *fn-bpc-max-uint*))))
 :rule-classes ((:forward-chaining :trigger-terms ((fn-bpnr-enc value depth))))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-bpnr-enc fn-bpnr-counted)
   (fn-bpc-u64-bytes fn-bpnr-codes fn-bpcr-reverse-completion-unfolds))))))
(local (defthm fn-bpcr-pair-encoding-unfolds
 (implies (and (posp depth) (consp value) (not (fn-cbor-octet-listp value)))
  (equal (fn-bpnr-enc value depth)
   (and (fn-bpnr-enc (car value) (1- depth))
        (fn-bpnr-enc (cdr value) (1- depth))
        (cons 10 (append (fn-bpnr-enc (car value) (1- depth))
                         (fn-bpnr-enc (cdr value) (1- depth)))))))
 :hints (("Goal" :expand ((fn-bpnr-enc value depth))
  :in-theory (disable fn-bpnr-enc fn-bpcr-reverse-completion-unfolds)))))

(local (defthm fn-bpcr-pair-encoding-has-two-children
 (implies (and (posp depth) (consp value) (not (fn-cbor-octet-listp value))
               (consp (fn-bpnr-enc value depth)))
  (and (consp (fn-bpnr-enc (car value) (1- depth)))
       (consp (fn-bpnr-enc (cdr value) (1- depth)))
       (posp (1- depth))))
 :rule-classes ((:forward-chaining :trigger-terms ((fn-bpnr-enc value depth))))
 :hints (("Goal" :use ((:instance fn-bpcr-pair-encoding-unfolds)
   (:instance fn-bpnr-enc-octets (x (car value)) (d (1- depth)))
   (:instance fn-bpnr-enc-octets (x (cdr value)) (d (1- depth)))
   (:instance fn-bpcr-encoding-implies-positive-depth
              (value (car value)) (depth (1- depth))))
  :in-theory (disable fn-bpnr-enc fn-bpcr-pair-encoding-unfolds
              fn-bpcr-reverse-completion-unfolds)))))
(local (defun fn-bpcr-value-continuation-induction
 (value depth goals values offset input)
 (declare (xargs :measure (nfix depth) :verify-guards nil))
 (if (zp depth) (list value goals values offset input)
  (if (not (consp value)) (list value goals values offset input)
   (if (fn-cbor-octet-listp value) (list value goals values offset input)
    (list
   (fn-bpcr-value-continuation-induction
    (car value) (1- depth) (cons (1- depth) (cons :pair goals)) values
    (1+ (nfix offset)) (append (fn-bpnr-enc (cdr value) (1- depth)) input))
   (fn-bpcr-value-continuation-induction
    (cdr value) (1- depth) (cons :pair goals) (cons (car value) values)
    (+ 1 (len (fn-bpnr-enc (car value) (1- depth))) (nfix offset)) input)))))))

(local (defthm fn-bpcr-typed-encoded-value-continuation
 (implies (and (posp depth) (fn-bpcv-valuep value) (consp (fn-bpnr-enc value depth)))
  (equal
   (fn-bpcr-complete
    (fn-bpcr-make :decoding (cons depth goals) values :tag nil 0 0 nil nil offset)
    (append (fn-bpnr-enc value depth) input))
   (fn-bpcr-complete
    (fn-bpcr-make :decoding goals (cons value values) :tag nil 0 0 nil nil
                  (+ (len (fn-bpnr-enc value depth)) (nfix offset))) input)))
 :hints (("Goal" :do-not-induct t
  :induct (fn-bpcr-value-continuation-induction value depth goals values offset input)
  :in-theory (e/d (fn-bpcv-valuep fn-bpnr-counted)
   (fn-cbor-octet-listp fn-cbor-octetp fn-bpnr-enc fn-bpcr-complete fn-bpcr-make fn-bpcr-run fn-bpc-u64-bytes
    fn-bpnr-codes fn-bpcr-reverse-completion-unfolds
    fn-bpcr-decode-tick fn-bpcr-action))))
 :rule-classes nil))

; The positive-depth premise is derived from actual nonempty encoding.
(local (defthm fn-bpcr-typed-encoder-reader-continuation
 (implies (and (fn-bpcv-valuep value) (consp (fn-bpnr-enc value depth)))
  (equal
   (fn-bpcr-complete
    (fn-bpcr-make :decoding (cons depth goals) values :tag nil 0 0 nil nil offset)
    (append (fn-bpnr-enc value depth) input))
   (fn-bpcr-complete
    (fn-bpcr-make :decoding goals (cons value values) :tag nil 0 0 nil nil
                  (+ (len (fn-bpnr-enc value depth)) (nfix offset))) input)))
 :hints (("Goal" :use (fn-bpcr-typed-encoded-value-continuation
                        fn-bpcr-encoding-implies-positive-depth)
                  :in-theory (theory 'minimal-theory)))
 :rule-classes nil))

(local (defthm fn-bpcr-root-completion-by-definition
 (equal
  (fn-bpcr-complete
   (fn-bpcr-make :decoding nil (list value) :tag nil 0 0 nil nil offset) input)
  (list :done
   (fn-bpcr-make :done nil (list value) :done nil 0 0 nil nil (nfix offset)) input))
 :hints (("Goal" :use ((:instance fn-bpcr-live-completion-unfolds
   (job (fn-bpcr-make :decoding nil (list value) :tag nil 0 0 nil nil offset))))
  :in-theory (e/d (fn-bpcr-action fn-bpcr-decode-tick fn-bpcr-make fn-bpn-nth)
                 (fn-bpcr-complete fn-bpcr-reverse-completion-unfolds))))))

(defthm fn-bpcr-typed-encoder-reader-endpoint
 (implies (and (fn-bpcv-valuep value) (consp (fn-bpnr-enc value depth)))
  (equal
   (fn-bpcr-complete (fn-bpcr-begin depth) (append (fn-bpnr-enc value depth) input))
   (list :done
    (fn-bpcr-make :done nil (list value) :done nil 0 0 nil nil
                  (len (fn-bpnr-enc value depth))) input)))
 :hints (("Goal"
  :use ((:instance fn-bpcr-typed-encoder-reader-continuation
          (goals nil) (values nil) (offset 0))
        (:instance fn-bpcr-encoding-implies-positive-depth))
  :in-theory (e/d (fn-bpcr-begin)
   (fn-bpcr-complete fn-bpcr-make fn-bpnr-enc
    fn-bpcr-reverse-completion-unfolds))))
 :rule-classes nil)

(local (defthm fn-bpcr-settled-completion-by-definition
 (implies (not (equal (fn-bpn-nth 1 job) :decoding))
  (equal (fn-bpcr-complete job input)
         (list (fn-bpn-nth 1 job) job input)))
 :hints (("Goal" :expand ((fn-bpcr-complete job input))
  :in-theory (disable fn-bpcr-complete fn-bpcr-action fn-bpcr-decode-tick
                     fn-bpcr-reverse-completion-unfolds)))))

; Actual host-called bounded runner: a completed quantum has the exact
; typed value, byte offset and unconsumed caller input, for any quantum.
(local (defthm fn-bpcr-run-typed-encoding-refinement
 (let ((answer (fn-bpcr-run (fn-bpcr-begin depth)
                          (append (fn-bpnr-enc value depth) input) quantum)))
  (implies (and (fn-bpcv-valuep value) (consp (fn-bpnr-enc value depth))
                (equal (fn-bpn-nth 1 (fn-bpn-nth 0 answer)) :done))
   (and
    (equal (fn-bpn-nth 0 answer)
     (fn-bpcr-make :done nil (list value) :done nil 0 0 nil nil
                   (len (fn-bpnr-enc value depth))))
    (equal (fn-bpn-nth 1 answer) input))))
 :hints (("Goal"
  :use ((:instance fn-bpcr-typed-encoder-reader-endpoint)
        (:instance fn-bpcr-run-preserves-completion
         (job (fn-bpcr-begin depth))
         (input (append (fn-bpnr-enc value depth) input))))
  :in-theory (disable fn-bpcr-run fn-bpcr-begin fn-bpcr-complete
   fn-bpcr-make fn-bpnr-enc fn-bpcr-reverse-completion-unfolds)))
 :rule-classes nil))

; Host-called continuation boundary, including yielded scheduler turns.
(defthm fn-bpcr-run-preserves-typed-encoder-endpoint
 (let ((answer (fn-bpcr-run (fn-bpcr-begin depth)
                          (append (fn-bpnr-enc value depth) input) quantum)))
  (implies (and (fn-bpcv-valuep value) (consp (fn-bpnr-enc value depth)))
   (equal (fn-bpcr-complete (fn-bpn-nth 0 answer) (fn-bpn-nth 1 answer))
    (list :done
     (fn-bpcr-make :done nil (list value) :done nil 0 0 nil nil
                   (len (fn-bpnr-enc value depth))) input))))
 :hints (("Goal"
  :use ((:instance fn-bpcr-typed-encoder-reader-endpoint)
        (:instance fn-bpcr-run-preserves-completion
         (job (fn-bpcr-begin depth))
         (input (append (fn-bpnr-enc value depth) input))))
  :in-theory (theory 'minimal-theory)))
 :rule-classes nil)
