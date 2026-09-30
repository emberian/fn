(in-package "ACL2")

(include-book "../../books/history-pool-tagged-refinement")

(defun-nx fn-hptt-tick-law (c partial pool fn-hpb)
 (declare (xargs :stobjs fn-hpb :verify-guards nil))
 (let ((next (mv-nth 2 (fn-hpe-tick c fn-hpb))) (next-partial (fn-hpert-partial-next c partial fn-hpb)) (next-buffer (mv-nth 3 (fn-hpe-tick c fn-hpb)))) (and (fn-hpert-invariantp next next-partial pool) (fn-hpbp next-buffer) (equal (fn-hpert-total next pool) (fn-hpert-total c pool)) (equal (append (fn-hpb-prefix fn-hpb) (fn-hpert-pending c partial pool)) (append (fn-hpb-prefix next-buffer) (fn-hpert-pending next next-partial pool))) (or (member-eq (mv-nth 0 (fn-hpe-tick c fn-hpb)) (quote (:continue :prepared :page-full))) (fn-hsrcb-demandp (mv-nth 0 (fn-hpe-tick c fn-hpb)))) (implies (eq (mv-nth 0 (fn-hpe-tick c fn-hpb)) :prepared) (equal (mv-nth 1 (fn-hpe-tick c fn-hpb)) (fn-hpert-total c pool))))))

(defun-nx fn-hptt-supply-law (c partial position byte pool fn-hpb)
 (declare (xargs :stobjs fn-hpb :verify-guards nil))
 (let ((next (mv-nth 1 (fn-hpe-supply c position byte fn-hpb))) (next-partial (fn-hpert-partial-supply c partial position byte fn-hpb)) (next-buffer (mv-nth 2 (fn-hpe-supply c position byte fn-hpb)))) (and (fn-hpert-invariantp next next-partial pool) (fn-hpbp next-buffer) (equal (fn-hpert-total next pool) (fn-hpert-total c pool)) (equal (append (fn-hpb-prefix fn-hpb) (fn-hpert-pending c partial pool)) (append (fn-hpb-prefix next-buffer) (fn-hpert-pending next next-partial pool))) (equal (mv-nth 0 (fn-hpe-supply c position byte fn-hpb)) (if (eq (fn-hrcur-field 0 c) :codec) (if (fn-hpb-ready fn-hpb) :page-full :continue) (quote (:refused :not-awaiting-cold-byte)))))))

(defun-nx fn-hptt-completed-trace-law (fuel c pool row fn-hpb)
 (declare (xargs :stobjs fn-hpb :verify-guards nil))
 (let ((result (fn-hpert-run fuel c nil nil pool fn-hpb))) (and (equal (append (mv-nth 2 result) (fn-hpb-prefix (mv-nth 3 result))) (fn-hper-pack (fn-scc-encode row))) (equal (fn-hrcur-field 4 (mv-nth 0 result)) (len (fn-scc-encode row))))))

(defun fn-hptt-ticks (c n)
 (declare (xargs :verify-guards nil))
 (if (zp n) c
  (mv-let (v b next) (fn-hsrcb-tick c)
   (declare (ignore v b)) (fn-hptt-ticks next (1- n)))))

; Reachable resident positive: complete tick antecedent and full output/effect law.
(defthm fn-hptt-tick-positive
 (let* ((s (create-fn-hpb)) (c (fn-hpe-begin '(:resident "HELLO") :capture :lease)) (partial nil) (pool nil))
  (and (fn-hpert-invariantp c partial pool) (fn-hpbp s) (fn-hptt-tick-law c partial pool s)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hpert-total fn-hpert-emitter-invariantp fn-hpert-invariantp fn-hpert-pending fn-hpert-partial-next fn-hpert-partial-supply fn-hpert-run
fn-hptt-tick-law fn-hptt-supply-law fn-hptt-completed-trace-law fn-hptt-ticks
fn-hpe-begin fn-hpe-shapep fn-hpe-tick fn-hpe-supply fn-hpb-put fn-hpb-prefix fn-hpb-begin fn-hper-pack
fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-tick fn-hsrcb-supply fn-hsrcb-coldp fn-hsrcb-demandp fn-hsrcb-begin
fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp fn-hrcur-cold-begin fn-hrcur-cold-tick fn-hrcur-cold-supply fn-hrcur-cold-state
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire fn-hrcur-span-tick fn-hrcur-span-supply
fn-hrcur-span-shapep fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-childp
fn-hdsn-coherent fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-find fn-hrcur-cold-name
fn-hrcur-wordp fn-hrcur-word-push fn-hrcur-word-finish) :expand ((:free (x) (hide x))))))

; Hypothesis removal, corrupted partial attribution: retained concrete premise holds.
(defthm fn-hptt-tick-remove-invariant
 (let* ((s (create-fn-hpb)) (c (list :finish '(:done (nil :capture :lease) nil :capture :lease nil) 1 42 1 :capture :lease)) (partial '(43)) (pool nil))
  (and (not (fn-hpert-invariantp c partial pool)) (fn-hpbp s) (not (fn-hptt-tick-law c partial pool s))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hpert-total fn-hpert-emitter-invariantp fn-hpert-invariantp fn-hpert-pending fn-hpert-partial-next fn-hpert-partial-supply fn-hpert-run
fn-hptt-tick-law fn-hptt-supply-law fn-hptt-completed-trace-law fn-hptt-ticks
fn-hpe-begin fn-hpe-shapep fn-hpe-tick fn-hpe-supply fn-hpb-put fn-hpb-prefix fn-hpb-begin fn-hper-pack
fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-tick fn-hsrcb-supply fn-hsrcb-coldp fn-hsrcb-demandp fn-hsrcb-begin
fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp fn-hrcur-cold-begin fn-hrcur-cold-tick fn-hrcur-cold-supply fn-hrcur-cold-state
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire fn-hrcur-span-tick fn-hrcur-span-supply
fn-hrcur-span-shapep fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-childp
fn-hdsn-coherent fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-find fn-hrcur-cold-name
fn-hrcur-wordp fn-hrcur-word-push fn-hrcur-word-finish) :expand ((:free (x) (hide x))))))

; Hypothesis removal, corrupted concrete used field; full residual carry still holds.
(defthm fn-hptt-tick-remove-concrete
 (let* ((s '((0) -1 :capture :lease)) (c (list :finish '(:done (nil :capture :lease) nil :capture :lease nil) 1 42 1 :capture :lease)) (partial '(42)) (pool nil))
  (and (fn-hpert-invariantp c partial pool) (not (fn-hpbp s)) (not (fn-hptt-tick-law c partial pool s))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hpert-total fn-hpert-emitter-invariantp fn-hpert-invariantp fn-hpert-pending fn-hpert-partial-next fn-hpert-partial-supply fn-hpert-run
fn-hptt-tick-law fn-hptt-supply-law fn-hptt-completed-trace-law fn-hptt-ticks
fn-hpe-begin fn-hpe-shapep fn-hpe-tick fn-hpe-supply fn-hpb-put fn-hpb-prefix fn-hpb-begin fn-hper-pack
fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-tick fn-hsrcb-supply fn-hsrcb-coldp fn-hsrcb-demandp fn-hsrcb-begin
fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp fn-hrcur-cold-begin fn-hrcur-cold-tick fn-hrcur-cold-supply fn-hrcur-cold-state
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire fn-hrcur-span-tick fn-hrcur-span-supply
fn-hrcur-span-shapep fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-childp
fn-hdsn-coherent fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-find fn-hrcur-cold-name
fn-hrcur-wordp fn-hrcur-word-push fn-hrcur-word-finish) :expand ((:free (x) (hide x))))))

; Reachable cold supplied-byte positive: complete five-premise antecedent and full outputs.
(defthm fn-hptt-supply-positive
 (let* ((pool '(17 23)) (codec (fn-hptt-ticks (fn-hsrcb-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 5)) (c (list :codec codec 3 131334 3 :capture :lease)) (partial '(6 1 2)) (s (create-fn-hpb)) (position 0) (byte 17))
  (and (equal c (mv-nth 0 (fn-hpert-run 5 (fn-hpe-begin '(:decoded (:span 6 0 0 2)) :capture :lease) nil nil pool (create-fn-hpb))))
       (equal partial (mv-nth 1 (fn-hpert-run 5 (fn-hpe-begin '(:decoded (:span 6 0 0 2)) :capture :lease) nil nil pool (create-fn-hpb))))
       (fn-hpert-invariantp c partial pool) (fn-hpbp s) (fn-hsrcb-demandp (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c)))) (equal position (fn-hrcur-field 1 (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c))))) (equal byte (nth position pool)) (fn-hptt-supply-law c partial position byte pool s)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hpert-total fn-hpert-emitter-invariantp fn-hpert-invariantp fn-hpert-pending fn-hpert-partial-next fn-hpert-partial-supply fn-hpert-run
fn-hptt-tick-law fn-hptt-supply-law fn-hptt-completed-trace-law fn-hptt-ticks
fn-hpe-begin fn-hpe-shapep fn-hpe-tick fn-hpe-supply fn-hpb-put fn-hpb-prefix fn-hpb-begin fn-hper-pack
fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-tick fn-hsrcb-supply fn-hsrcb-coldp fn-hsrcb-demandp fn-hsrcb-begin
fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp fn-hrcur-cold-begin fn-hrcur-cold-tick fn-hrcur-cold-supply fn-hrcur-cold-state
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire fn-hrcur-span-tick fn-hrcur-span-supply
fn-hrcur-span-shapep fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-childp
fn-hdsn-coherent fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-find fn-hrcur-cold-name
fn-hrcur-wordp fn-hrcur-word-push fn-hrcur-word-finish) :expand ((:free (x) (hide x))))))

; Hypothesis removal; corrupted invariant only, every retained hypothesis affirmed.
(defthm fn-hptt-supply-remove-invariant
 (let* ((pool '(17 23)) (codec (fn-hptt-ticks (fn-hsrcb-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 5)) (c (list :codec codec 3 131335 3 :capture :lease)) (partial '(6 1 2)) (s (create-fn-hpb)) (position 0) (byte 17))
  (and (not (fn-hpert-invariantp c partial pool)) (fn-hpbp s) (fn-hsrcb-demandp (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c)))) (equal position (fn-hrcur-field 1 (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c))))) (equal byte (nth position pool)) (not (fn-hptt-supply-law c partial position byte pool s))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hpert-total fn-hpert-emitter-invariantp fn-hpert-invariantp fn-hpert-pending fn-hpert-partial-next fn-hpert-partial-supply fn-hpert-run
fn-hptt-tick-law fn-hptt-supply-law fn-hptt-completed-trace-law fn-hptt-ticks
fn-hpe-begin fn-hpe-shapep fn-hpe-tick fn-hpe-supply fn-hpb-put fn-hpb-prefix fn-hpb-begin fn-hper-pack
fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-tick fn-hsrcb-supply fn-hsrcb-coldp fn-hsrcb-demandp fn-hsrcb-begin
fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp fn-hrcur-cold-begin fn-hrcur-cold-tick fn-hrcur-cold-supply fn-hrcur-cold-state
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire fn-hrcur-span-tick fn-hrcur-span-supply
fn-hrcur-span-shapep fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-childp
fn-hdsn-coherent fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-find fn-hrcur-cold-name
fn-hrcur-wordp fn-hrcur-word-push fn-hrcur-word-finish) :expand ((:free (x) (hide x))))))

; Hypothesis removal; corrupted concrete only, every retained hypothesis affirmed.
(defthm fn-hptt-supply-remove-concrete
 (let* ((pool '(17 23)) (codec (fn-hptt-ticks (fn-hsrcb-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 5)) (c (list :codec codec 3 131334 3 :capture :lease)) (partial '(6 1 2)) (s '((0) -1 :capture :lease)) (position 0) (byte 17))
  (and (fn-hpert-invariantp c partial pool) (not (fn-hpbp s)) (fn-hsrcb-demandp (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c)))) (equal position (fn-hrcur-field 1 (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c))))) (equal byte (nth position pool)) (not (fn-hptt-supply-law c partial position byte pool s))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hpert-total fn-hpert-emitter-invariantp fn-hpert-invariantp fn-hpert-pending fn-hpert-partial-next fn-hpert-partial-supply fn-hpert-run
fn-hptt-tick-law fn-hptt-supply-law fn-hptt-completed-trace-law fn-hptt-ticks
fn-hpe-begin fn-hpe-shapep fn-hpe-tick fn-hpe-supply fn-hpb-put fn-hpb-prefix fn-hpb-begin fn-hper-pack
fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-tick fn-hsrcb-supply fn-hsrcb-coldp fn-hsrcb-demandp fn-hsrcb-begin
fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp fn-hrcur-cold-begin fn-hrcur-cold-tick fn-hrcur-cold-supply fn-hrcur-cold-state
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire fn-hrcur-span-tick fn-hrcur-span-supply
fn-hrcur-span-shapep fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-childp
fn-hdsn-coherent fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-find fn-hrcur-cold-name
fn-hrcur-wordp fn-hrcur-word-push fn-hrcur-word-finish) :expand ((:free (x) (hide x))))))

; Hypothesis removal; corrupted demand only, every retained hypothesis affirmed.
(defthm fn-hptt-supply-remove-demand
 (let* ((pool '(17 23)) (codec (fn-hptt-ticks (fn-hsrcb-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 3)) (c (list :codec codec 3 131334 3 :capture :lease)) (partial '(6 1 2)) (s (create-fn-hpb)) (position nil) (byte 17))
  (and (fn-hpert-invariantp c partial pool) (fn-hpbp s) (not (fn-hsrcb-demandp (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c))))) (equal position (fn-hrcur-field 1 (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c))))) (equal byte (nth position pool)) (not (fn-hptt-supply-law c partial position byte pool s))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hpert-total fn-hpert-emitter-invariantp fn-hpert-invariantp fn-hpert-pending fn-hpert-partial-next fn-hpert-partial-supply fn-hpert-run
fn-hptt-tick-law fn-hptt-supply-law fn-hptt-completed-trace-law fn-hptt-ticks
fn-hpe-begin fn-hpe-shapep fn-hpe-tick fn-hpe-supply fn-hpb-put fn-hpb-prefix fn-hpb-begin fn-hper-pack
fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-tick fn-hsrcb-supply fn-hsrcb-coldp fn-hsrcb-demandp fn-hsrcb-begin
fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp fn-hrcur-cold-begin fn-hrcur-cold-tick fn-hrcur-cold-supply fn-hrcur-cold-state
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire fn-hrcur-span-tick fn-hrcur-span-supply
fn-hrcur-span-shapep fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-childp
fn-hdsn-coherent fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-find fn-hrcur-cold-name
fn-hrcur-wordp fn-hrcur-word-push fn-hrcur-word-finish) :expand ((:free (x) (hide x))))))

; Hypothesis removal; corrupted position only, every retained hypothesis affirmed.
(defthm fn-hptt-supply-remove-position
 (let* ((pool '(17 23)) (codec (fn-hptt-ticks (fn-hsrcb-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 5)) (c (list :codec codec 3 131334 3 :capture :lease)) (partial '(6 1 2)) (s (create-fn-hpb)) (position 1) (byte 23))
  (and (fn-hpert-invariantp c partial pool) (fn-hpbp s) (fn-hsrcb-demandp (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c)))) (not (equal position (fn-hrcur-field 1 (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c)))))) (equal byte (nth position pool)) (not (fn-hptt-supply-law c partial position byte pool s))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hpert-total fn-hpert-emitter-invariantp fn-hpert-invariantp fn-hpert-pending fn-hpert-partial-next fn-hpert-partial-supply fn-hpert-run
fn-hptt-tick-law fn-hptt-supply-law fn-hptt-completed-trace-law fn-hptt-ticks
fn-hpe-begin fn-hpe-shapep fn-hpe-tick fn-hpe-supply fn-hpb-put fn-hpb-prefix fn-hpb-begin fn-hper-pack
fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-tick fn-hsrcb-supply fn-hsrcb-coldp fn-hsrcb-demandp fn-hsrcb-begin
fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp fn-hrcur-cold-begin fn-hrcur-cold-tick fn-hrcur-cold-supply fn-hrcur-cold-state
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire fn-hrcur-span-tick fn-hrcur-span-supply
fn-hrcur-span-shapep fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-childp
fn-hdsn-coherent fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-find fn-hrcur-cold-name
fn-hrcur-wordp fn-hrcur-word-push fn-hrcur-word-finish) :expand ((:free (x) (hide x))))))

; Hypothesis removal; corrupted byte only, every retained hypothesis affirmed.
(defthm fn-hptt-supply-remove-byte
 (let* ((pool '(17 23)) (codec (fn-hptt-ticks (fn-hsrcb-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 5)) (c (list :codec codec 3 131334 3 :capture :lease)) (partial '(6 1 2)) (s (create-fn-hpb)) (position 0) (byte 18))
  (and (fn-hpert-invariantp c partial pool) (fn-hpbp s) (fn-hsrcb-demandp (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c)))) (equal position (fn-hrcur-field 1 (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c))))) (not (equal byte (nth position pool))) (not (fn-hptt-supply-law c partial position byte pool s))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hpert-total fn-hpert-emitter-invariantp fn-hpert-invariantp fn-hpert-pending fn-hpert-partial-next fn-hpert-partial-supply fn-hpert-run
fn-hptt-tick-law fn-hptt-supply-law fn-hptt-completed-trace-law fn-hptt-ticks
fn-hpe-begin fn-hpe-shapep fn-hpe-tick fn-hpe-supply fn-hpb-put fn-hpb-prefix fn-hpb-begin fn-hper-pack
fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-tick fn-hsrcb-supply fn-hsrcb-coldp fn-hsrcb-demandp fn-hsrcb-begin
fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp fn-hrcur-cold-begin fn-hrcur-cold-tick fn-hrcur-cold-supply fn-hrcur-cold-state
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire fn-hrcur-span-tick fn-hrcur-span-supply
fn-hrcur-span-shapep fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-childp
fn-hdsn-coherent fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-find fn-hrcur-cold-name
fn-hrcur-wordp fn-hrcur-word-push fn-hrcur-word-finish) :expand ((:free (x) (hide x))))))

; Complete cold row: complete original six-premise antecedent, exact canonical words and byte count.
(defthm fn-hptt-completed-positive
 (let* ((pool '(0 65 66 67)) (c (fn-hpe-begin '(:decoded (:span 3 0 1 3)) :capture :lease)) (s (create-fn-hpb)) (row "ABC") (fuel 30) (result (fn-hpert-run fuel c nil nil pool s)))
  (and (fn-hpert-invariantp c nil pool) (fn-hpbp s) (equal (fn-hpb-prefix s) nil) (equal (fn-hrcur-field 4 c) 0) (equal (fn-hsrcb-rest (fn-hrcur-field 1 c) pool) (fn-scc-encode row)) (equal (fn-hrcur-field 0 (mv-nth 0 result)) :prepared) (fn-hptt-completed-trace-law fuel c pool row s)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hpert-total fn-hpert-emitter-invariantp fn-hpert-invariantp fn-hpert-pending fn-hpert-partial-next fn-hpert-partial-supply fn-hpert-run
fn-hptt-tick-law fn-hptt-supply-law fn-hptt-completed-trace-law fn-hptt-ticks
fn-hpe-begin fn-hpe-shapep fn-hpe-tick fn-hpe-supply fn-hpb-put fn-hpb-prefix fn-hpb-begin fn-hper-pack
fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-tick fn-hsrcb-supply fn-hsrcb-coldp fn-hsrcb-demandp fn-hsrcb-begin
fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp fn-hrcur-cold-begin fn-hrcur-cold-tick fn-hrcur-cold-supply fn-hrcur-cold-state
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire fn-hrcur-span-tick fn-hrcur-span-supply
fn-hrcur-span-shapep fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-childp
fn-hdsn-coherent fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-find fn-hrcur-cold-name
fn-hrcur-wordp fn-hrcur-word-push fn-hrcur-word-finish) :expand ((:free (x) (hide x))))))

; Hypothesis removal; invariant counterexample, all five retained hypotheses affirmed.
(defthm fn-hptt-completed-remove-invariant
 (let* ((pool '(0 65 66 67)) (c (update-nth 0 :prepared (fn-hpe-begin '(:decoded (:span 3 0 1 3)) :capture :lease))) (s (create-fn-hpb)) (row "ABC") (fuel 30) (result (fn-hpert-run fuel c nil nil pool s)))
  (and (not (fn-hpert-invariantp c nil pool)) (fn-hpbp s) (equal (fn-hpb-prefix s) nil) (equal (fn-hrcur-field 4 c) 0) (equal (fn-hsrcb-rest (fn-hrcur-field 1 c) pool) (fn-scc-encode row)) (equal (fn-hrcur-field 0 (mv-nth 0 result)) :prepared) (not (fn-hptt-completed-trace-law fuel c pool row s))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hpert-total fn-hpert-emitter-invariantp fn-hpert-invariantp fn-hpert-pending fn-hpert-partial-next fn-hpert-partial-supply fn-hpert-run
fn-hptt-tick-law fn-hptt-supply-law fn-hptt-completed-trace-law fn-hptt-ticks
fn-hpe-begin fn-hpe-shapep fn-hpe-tick fn-hpe-supply fn-hpb-put fn-hpb-prefix fn-hpb-begin fn-hper-pack
fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-tick fn-hsrcb-supply fn-hsrcb-coldp fn-hsrcb-demandp fn-hsrcb-begin
fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp fn-hrcur-cold-begin fn-hrcur-cold-tick fn-hrcur-cold-supply fn-hrcur-cold-state
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire fn-hrcur-span-tick fn-hrcur-span-supply
fn-hrcur-span-shapep fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-childp
fn-hdsn-coherent fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-find fn-hrcur-cold-name
fn-hrcur-wordp fn-hrcur-word-push fn-hrcur-word-finish) :expand ((:free (x) (hide x))))))

; Hypothesis removal; concrete counterexample, all five retained hypotheses affirmed.
(defthm fn-hptt-completed-remove-concrete
 (let* ((pool '(0 65 66 67)) (c (fn-hpe-begin '(:decoded (:span 3 0 1 3)) :capture :lease)) (s '((0) -1 :capture :lease)) (row "ABC") (fuel 30) (result (fn-hpert-run fuel c nil nil pool s)))
  (and (fn-hpert-invariantp c nil pool) (not (fn-hpbp s)) (equal (fn-hpb-prefix s) nil) (equal (fn-hrcur-field 4 c) 0) (equal (fn-hsrcb-rest (fn-hrcur-field 1 c) pool) (fn-scc-encode row)) (equal (fn-hrcur-field 0 (mv-nth 0 result)) :prepared) (not (fn-hptt-completed-trace-law fuel c pool row s))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-hpert-total fn-hpert-emitter-invariantp fn-hpert-invariantp fn-hpert-pending fn-hpert-partial-next fn-hpert-partial-supply fn-hpert-run
fn-hptt-tick-law fn-hptt-supply-law fn-hptt-completed-trace-law fn-hptt-ticks
fn-hpe-begin fn-hpe-shapep fn-hpe-tick fn-hpe-supply fn-hpb-put fn-hpb-prefix fn-hpb-begin fn-hper-pack
fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-tick fn-hsrcb-supply fn-hsrcb-coldp fn-hsrcb-demandp fn-hsrcb-begin
fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp fn-hrcur-cold-begin fn-hrcur-cold-tick fn-hrcur-cold-supply fn-hrcur-cold-state
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire fn-hrcur-span-tick fn-hrcur-span-supply
fn-hrcur-span-shapep fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-childp
fn-hdsn-coherent fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-find fn-hrcur-cold-name
fn-hrcur-wordp fn-hrcur-word-push fn-hrcur-word-finish)
 ((:executable-counterpart fn-hpert-run) (:executable-counterpart fn-hpe-tick)
  (:executable-counterpart fn-hpe-supply) (:executable-counterpart fn-hpb-put)
  (:executable-counterpart fn-hpert-partial-next) (:executable-counterpart fn-hpert-partial-supply))) :expand ((:free (f c p done pool buf) (fn-hpert-run f c p done pool buf)) (:free (x) (hide x))))))

; Hypothesis removal; empty-prefix counterexample, all five retained hypotheses affirmed.
(defthm fn-hptt-completed-remove-empty-prefix
 (let* ((pool '(0 65 66 67)) (c (fn-hpe-begin '(:decoded (:span 3 0 1 3)) :capture :lease)) (s (mv-nth 1 (fn-hpb-put 42 (create-fn-hpb)))) (row "ABC") (fuel 30) (result (fn-hpert-run fuel c nil nil pool s)))
  (and (fn-hpert-invariantp c nil pool) (fn-hpbp s) (not (equal (fn-hpb-prefix s) nil)) (equal (fn-hrcur-field 4 c) 0) (equal (fn-hsrcb-rest (fn-hrcur-field 1 c) pool) (fn-scc-encode row)) (equal (fn-hrcur-field 0 (mv-nth 0 result)) :prepared) (not (fn-hptt-completed-trace-law fuel c pool row s))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hpert-total fn-hpert-emitter-invariantp fn-hpert-invariantp fn-hpert-pending fn-hpert-partial-next fn-hpert-partial-supply fn-hpert-run
fn-hptt-tick-law fn-hptt-supply-law fn-hptt-completed-trace-law fn-hptt-ticks
fn-hpe-begin fn-hpe-shapep fn-hpe-tick fn-hpe-supply fn-hpb-put fn-hpb-prefix fn-hpb-begin fn-hper-pack
fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-tick fn-hsrcb-supply fn-hsrcb-coldp fn-hsrcb-demandp fn-hsrcb-begin
fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp fn-hrcur-cold-begin fn-hrcur-cold-tick fn-hrcur-cold-supply fn-hrcur-cold-state
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire fn-hrcur-span-tick fn-hrcur-span-supply
fn-hrcur-span-shapep fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-childp
fn-hdsn-coherent fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-find fn-hrcur-cold-name
fn-hrcur-wordp fn-hrcur-word-push fn-hrcur-word-finish) :expand ((:free (x) (hide x))))))

; Hypothesis removal; initial-count counterexample, all five retained hypotheses affirmed.
(defthm fn-hptt-completed-remove-initial-count
 (let* ((pool '(0 65 66 67)) (c (update-nth 4 1 (fn-hpe-begin '(:decoded (:span 3 0 1 3)) :capture :lease))) (s (create-fn-hpb)) (row "ABC") (fuel 30) (result (fn-hpert-run fuel c nil nil pool s)))
  (and (fn-hpert-invariantp c nil pool) (fn-hpbp s) (equal (fn-hpb-prefix s) nil) (not (equal (fn-hrcur-field 4 c) 0)) (equal (fn-hsrcb-rest (fn-hrcur-field 1 c) pool) (fn-scc-encode row)) (equal (fn-hrcur-field 0 (mv-nth 0 result)) :prepared) (not (fn-hptt-completed-trace-law fuel c pool row s))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hpert-total fn-hpert-emitter-invariantp fn-hpert-invariantp fn-hpert-pending fn-hpert-partial-next fn-hpert-partial-supply fn-hpert-run
fn-hptt-tick-law fn-hptt-supply-law fn-hptt-completed-trace-law fn-hptt-ticks
fn-hpe-begin fn-hpe-shapep fn-hpe-tick fn-hpe-supply fn-hpb-put fn-hpb-prefix fn-hpb-begin fn-hper-pack
fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-tick fn-hsrcb-supply fn-hsrcb-coldp fn-hsrcb-demandp fn-hsrcb-begin
fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp fn-hrcur-cold-begin fn-hrcur-cold-tick fn-hrcur-cold-supply fn-hrcur-cold-state
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire fn-hrcur-span-tick fn-hrcur-span-supply
fn-hrcur-span-shapep fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-childp
fn-hdsn-coherent fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-find fn-hrcur-cold-name
fn-hrcur-wordp fn-hrcur-word-push fn-hrcur-word-finish) :expand ((:free (x) (hide x))))))

; Hypothesis removal; row-denotation counterexample, all five retained hypotheses affirmed.
(defthm fn-hptt-completed-remove-row-denotation
 (let* ((pool '(0 65 66 67)) (c (fn-hpe-begin '(:decoded (:span 3 0 1 3)) :capture :lease)) (s (create-fn-hpb)) (row "ABCD") (fuel 30) (result (fn-hpert-run fuel c nil nil pool s)))
  (and (fn-hpert-invariantp c nil pool) (fn-hpbp s) (equal (fn-hpb-prefix s) nil) (equal (fn-hrcur-field 4 c) 0) (not (equal (fn-hsrcb-rest (fn-hrcur-field 1 c) pool) (fn-scc-encode row))) (equal (fn-hrcur-field 0 (mv-nth 0 result)) :prepared) (not (fn-hptt-completed-trace-law fuel c pool row s))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hpert-total fn-hpert-emitter-invariantp fn-hpert-invariantp fn-hpert-pending fn-hpert-partial-next fn-hpert-partial-supply fn-hpert-run
fn-hptt-tick-law fn-hptt-supply-law fn-hptt-completed-trace-law fn-hptt-ticks
fn-hpe-begin fn-hpe-shapep fn-hpe-tick fn-hpe-supply fn-hpb-put fn-hpb-prefix fn-hpb-begin fn-hper-pack
fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-tick fn-hsrcb-supply fn-hsrcb-coldp fn-hsrcb-demandp fn-hsrcb-begin
fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp fn-hrcur-cold-begin fn-hrcur-cold-tick fn-hrcur-cold-supply fn-hrcur-cold-state
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire fn-hrcur-span-tick fn-hrcur-span-supply
fn-hrcur-span-shapep fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-childp
fn-hdsn-coherent fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-find fn-hrcur-cold-name
fn-hrcur-wordp fn-hrcur-word-push fn-hrcur-word-finish) :expand ((:free (x) (hide x))))))

; Hypothesis removal; completion counterexample, all five retained hypotheses affirmed.
(defthm fn-hptt-completed-remove-completion
 (let* ((pool '(0 65 66 67)) (c (fn-hpe-begin '(:decoded (:span 3 0 1 3)) :capture :lease)) (s (create-fn-hpb)) (row "ABC") (fuel 0) (result (fn-hpert-run fuel c nil nil pool s)))
  (and (fn-hpert-invariantp c nil pool) (fn-hpbp s) (equal (fn-hpb-prefix s) nil) (equal (fn-hrcur-field 4 c) 0) (equal (fn-hsrcb-rest (fn-hrcur-field 1 c) pool) (fn-scc-encode row)) (not (equal (fn-hrcur-field 0 (mv-nth 0 result)) :prepared)) (not (fn-hptt-completed-trace-law fuel c pool row s))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hpert-total fn-hpert-emitter-invariantp fn-hpert-invariantp fn-hpert-pending fn-hpert-partial-next fn-hpert-partial-supply fn-hpert-run
fn-hptt-tick-law fn-hptt-supply-law fn-hptt-completed-trace-law fn-hptt-ticks
fn-hpe-begin fn-hpe-shapep fn-hpe-tick fn-hpe-supply fn-hpb-put fn-hpb-prefix fn-hpb-begin fn-hper-pack
fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-tick fn-hsrcb-supply fn-hsrcb-coldp fn-hsrcb-demandp fn-hsrcb-begin
fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp fn-hrcur-cold-begin fn-hrcur-cold-tick fn-hrcur-cold-supply fn-hrcur-cold-state
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire fn-hrcur-span-tick fn-hrcur-span-supply
fn-hrcur-span-shapep fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-childp
fn-hdsn-coherent fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-find fn-hrcur-cold-name
fn-hrcur-wordp fn-hrcur-word-push fn-hrcur-word-finish) :expand ((:free (x) (hide x))))))

; Reachable eighth-byte positive: seven carried bytes, actual raw position5.
(defthm fn-hptt-supply-eighth-byte-positive
 (let* ((pool '(17 18 19 20 21 22 23))
        (r (fn-hpert-run 9 (fn-hpe-begin '(:decoded (:span 6 0 0 7)) :capture :lease) nil nil pool (create-fn-hpb)))
        (c (mv-nth 0 r)) (partial (mv-nth 1 r)) (s (mv-nth 3 r))
        (position 4) (byte 21))
  (and (fn-hpert-invariantp c partial pool) (fn-hpbp s)
       (equal (len partial) 7)
       (fn-hsrcb-demandp (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c))))
       (equal position (fn-hrcur-field 1 (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c)))))
       (equal byte (nth position pool))
       (fn-hptt-supply-law c partial position byte pool s)
       (equal (fn-hpb-prefix (mv-nth 2 (fn-hpe-supply c position byte s)))
              (fn-hper-pack '(6 1 7 17 18 19 20 21)))
       (equal (fn-hpert-partial-supply c partial position byte s) nil)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hpert-total fn-hpert-emitter-invariantp fn-hpert-invariantp fn-hpert-pending fn-hpert-partial-next fn-hpert-partial-supply fn-hpert-run
fn-hptt-tick-law fn-hptt-supply-law fn-hptt-completed-trace-law fn-hptt-ticks
fn-hpe-begin fn-hpe-shapep fn-hpe-tick fn-hpe-supply fn-hpb-put fn-hpb-prefix fn-hpb-begin fn-hper-pack
fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-tick fn-hsrcb-supply fn-hsrcb-coldp fn-hsrcb-demandp fn-hsrcb-begin
fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp fn-hrcur-cold-begin fn-hrcur-cold-tick fn-hrcur-cold-supply fn-hrcur-cold-state
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire fn-hrcur-span-tick fn-hrcur-span-supply
fn-hrcur-span-shapep fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-childp
fn-hdsn-coherent fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-find fn-hrcur-cold-name
fn-hrcur-wordp fn-hrcur-word-push fn-hrcur-word-finish) :expand ((:free (x) (hide x))))))

; Reachable outstanding-page supply: the complete concrete page and child stay immutable.
(defthm fn-hptt-full-page-supply-positive
 (let* ((pool '(17 23))
        (codec (fn-hptt-ticks (fn-hsrcb-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 5))
        (c (list :codec codec 3 131334 3 :capture :lease)) (partial '(6 1 2))
        (s (update-fn-hpb-used 2048 (create-fn-hpb))) (position 0) (byte 17))
  (and (fn-hpert-invariantp c partial pool) (fn-hpbp s) (fn-hpb-ready s)
       (fn-hsrcb-demandp (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c))))
       (equal position (fn-hrcur-field 1 (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c)))))
       (equal byte (nth position pool))
       (fn-hptt-supply-law c partial position byte pool s)
       (equal (fn-hpe-supply c position byte s) (mv :page-full c s))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hpert-total fn-hpert-emitter-invariantp fn-hpert-invariantp fn-hpert-pending fn-hpert-partial-next fn-hpert-partial-supply fn-hpert-run
fn-hptt-tick-law fn-hptt-supply-law fn-hptt-completed-trace-law fn-hptt-ticks
fn-hpe-begin fn-hpe-shapep fn-hpe-tick fn-hpe-supply fn-hpb-put fn-hpb-prefix fn-hpb-begin fn-hper-pack
fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-tick fn-hsrcb-supply fn-hsrcb-coldp fn-hsrcb-demandp fn-hsrcb-begin
fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp fn-hrcur-cold-begin fn-hrcur-cold-tick fn-hrcur-cold-supply fn-hrcur-cold-state
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire fn-hrcur-span-tick fn-hrcur-span-supply
fn-hrcur-span-shapep fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-childp
fn-hdsn-coherent fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-find fn-hrcur-cold-name
fn-hrcur-wordp fn-hrcur-word-push fn-hrcur-word-finish) :expand ((:free (x) (hide x))))))

; Complete resident path remains an actual tagged trace; no compatibility twin.
(defthm fn-hptt-completed-resident-positive
 (let* ((pool nil) (c (fn-hpe-begin '(:resident "ABC") :capture :lease))
        (s (create-fn-hpb)) (row "ABC") (fuel 30)
        (result (fn-hpert-run fuel c nil nil pool s)))
  (and (fn-hpert-invariantp c nil pool) (fn-hpbp s)
       (equal (fn-hpb-prefix s) nil) (equal (fn-hrcur-field 4 c) 0)
       (equal (fn-hsrcb-rest (fn-hrcur-field 1 c) pool) (fn-scc-encode row))
       (equal (fn-hrcur-field 0 (mv-nth 0 result)) :prepared)
       (fn-hptt-completed-trace-law fuel c pool row s)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hpert-total fn-hpert-emitter-invariantp fn-hpert-invariantp fn-hpert-pending fn-hpert-partial-next fn-hpert-partial-supply fn-hpert-run
fn-hptt-tick-law fn-hptt-supply-law fn-hptt-completed-trace-law fn-hptt-ticks
fn-hpe-begin fn-hpe-shapep fn-hpe-tick fn-hpe-supply fn-hpb-put fn-hpb-prefix fn-hpb-begin fn-hper-pack
fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-tick fn-hsrcb-supply fn-hsrcb-coldp fn-hsrcb-demandp fn-hsrcb-begin
fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp fn-hrcur-cold-begin fn-hrcur-cold-tick fn-hrcur-cold-supply fn-hrcur-cold-state
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire fn-hrcur-span-tick fn-hrcur-span-supply
fn-hrcur-span-shapep fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-childp
fn-hdsn-coherent fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-find fn-hrcur-cold-name
fn-hrcur-wordp fn-hrcur-word-push fn-hrcur-word-finish) :expand ((:free (x) (hide x))))))

; Full-page transfer/reset through the actual run: retained prefix precedes new cold row.
; A logical transfer alone authorizes no physical I/O ACK or resource release.
(defthm fn-hptt-run-page-reset-positive
 (let* ((pool '(0 65 66 67))
        (c (fn-hpe-begin '(:decoded (:span 3 0 1 3)) :capture :lease))
        (s (update-fn-hpb-used 2048 (create-fn-hpb)))
        (r (fn-hpert-run 30 c nil nil pool s)))
  (and (fn-hpert-invariantp c nil pool) (fn-hpbp s) (fn-hpb-ready s)
       (equal (fn-hrcur-field 0 (mv-nth 0 r)) :prepared)
       (equal (append (fn-hpb-prefix s) (fn-hpert-pending c nil pool))
              (append (mv-nth 2 r) (fn-hpb-prefix (mv-nth 3 r))
                      (fn-hpert-pending (mv-nth 0 r) (mv-nth 1 r) pool)))
       (equal (mv-nth 2 r) (fn-hpb-prefix s))
       (equal (fn-hpb-prefix (mv-nth 3 r)) (fn-hper-pack (fn-scc-encode "ABC")))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hpert-total fn-hpert-emitter-invariantp fn-hpert-invariantp fn-hpert-pending fn-hpert-partial-next fn-hpert-partial-supply fn-hpert-run
fn-hptt-tick-law fn-hptt-supply-law fn-hptt-completed-trace-law fn-hptt-ticks
fn-hpe-begin fn-hpe-shapep fn-hpe-tick fn-hpe-supply fn-hpb-put fn-hpb-prefix fn-hpb-begin fn-hper-pack
fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-tick fn-hsrcb-supply fn-hsrcb-coldp fn-hsrcb-demandp fn-hsrcb-begin
fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp fn-hrcur-cold-begin fn-hrcur-cold-tick fn-hrcur-cold-supply fn-hrcur-cold-state
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire fn-hrcur-span-tick fn-hrcur-span-supply
fn-hrcur-span-shapep fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-childp
fn-hdsn-coherent fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-find fn-hrcur-cold-name
fn-hrcur-wordp fn-hrcur-word-push fn-hrcur-word-finish) :expand ((:free (x) (hide x))))))
