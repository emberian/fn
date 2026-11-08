; FN2-OPS-CREDIT-CONSERVATION, proved: every ops operation preserves
; fn2-ops-semanticp.
(in-package "ACL2")
(include-book "vocab")
(include-book "pool")

;; ---------------------------------------------------------------------------
;; Shape of the proof. Every ops writer is, at the logical level, an
;; UPDATE-NTH-ARRAY of one column at one row or an UPDATE-NTH of one scalar.
;; The proof keeps those two forms closed and reads through them with
;; NTH-OF-UPDATE-NTH-ARRAY. The invariant's traversals are closed readers;
;; each has one frame rule per write form, stated for every field it does
;; not read, so no reader-by-writer matrix is needed. The per-row clause
;; FN2-OPS-ROW-OKP is fn2-ops-row-semanticp's body at one slot.
(defconst *fn2-ops-c-gen* 0)
(defconst *fn2-ops-c-phase* 1)
(defconst *fn2-ops-c-c0-posted* 19)
(defconst *fn2-ops-c-c0-harvested* 20)
(defconst *fn2-ops-c-c1-posted* 33)
(defconst *fn2-ops-c-c1-harvested* 34)
(defconst *fn2-ops-c-next-free* 41)
(defconst *fn2-ops-x-rows* 44)
(defconst *fn2-ops-x-out-slot* 45)
(defconst *fn2-ops-x-out-gen* 46)
(defconst *fn2-ops-x-posted-fifo* 47)
(defconst *fn2-ops-x-gen-limit* 72)
(assert-event
 (and (equal (body 'fn2-ops-gen$ai nil (w state)) '(nth i (nth '0 fn2-ops)))
      (equal (body 'fn2-ops-phase$ai nil (w state)) '(nth i (nth '1 fn2-ops)))
      (equal (body 'fn2-ops-c0-posted$ai nil (w state)) '(nth i (nth '19 fn2-ops)))
      (equal (body 'fn2-ops-c0-harvested$ai nil (w state)) '(nth i (nth '20 fn2-ops)))
      (equal (body 'fn2-ops-c1-posted$ai nil (w state)) '(nth i (nth '33 fn2-ops)))
      (equal (body 'fn2-ops-c1-harvested$ai nil (w state)) '(nth i (nth '34 fn2-ops)))
      (equal (body 'fn2-ops-next-free$ai nil (w state)) '(nth i (nth '41 fn2-ops)))
      (equal (body 'fn2-ops-wake-observation-gen$ai nil (w state)) '(nth i (nth '43 fn2-ops)))
      (equal *fn2-ops-rows* 44)
      (equal (body 'fn2-ops-out-sloti nil (w state)) '(nth i (nth '45 fn2-ops)))
      (equal (body 'fn2-ops-out-geni nil (w state)) '(nth i (nth '46 fn2-ops)))
      (equal (body 'fn2-ops-posted-fifoi nil (w state)) '(nth i (nth '47 fn2-ops)))
      (equal (body 'fn2-ops-gen-limit nil (w state)) '(nth '72 fn2-ops))))

;; The closed write forms.
(defthm fn2-ops-nth-of-update-nth-array
  (equal (nth j (update-nth-array k i v l))
         (if (equal (nfix j) (nfix k)) (update-nth i v (nth k l)) (nth j l))))
(defthm fn2-ops-len-of-update-nth-array
  (equal (len (update-nth-array k i v l))
         (if (< (nfix k) (len l)) (len l) (+ 1 (nfix k)))))

(defmacro fn2-ops-frame-theory (&rest more)
  `(e/d (fn2-ops-set-gen fn2-ops-set-phase fn2-ops-set-kind fn2-ops-set-owner-kind fn2-ops-set-owner-slot
         fn2-ops-set-owner-gen fn2-ops-set-principal fn2-ops-set-range-slot fn2-ops-set-range-gen
         fn2-ops-set-range-off fn2-ops-set-range-len fn2-ops-set-cap-index fn2-ops-set-cap-nonce
         fn2-ops-set-storage-offset fn2-ops-set-fua fn2-ops-set-may-release fn2-ops-set-cancel-slot
         fn2-ops-set-cancel-gen fn2-ops-set-cancel-requested fn2-ops-set-c0-posted fn2-ops-set-c0-harvested
         fn2-ops-set-c0-event fn2-ops-set-c0-outcome fn2-ops-set-c0-reason fn2-ops-set-c0-count
         fn2-ops-set-c0-aux0 fn2-ops-set-c0-aux1 fn2-ops-set-peer-family fn2-ops-set-peer-port
         fn2-ops-set-peer-w0 fn2-ops-set-peer-w1 fn2-ops-set-peer-w2 fn2-ops-set-peer-w3
         fn2-ops-set-c1-posted fn2-ops-set-c1-harvested fn2-ops-set-c1-event fn2-ops-set-c1-outcome
         fn2-ops-set-c1-reason fn2-ops-set-c1-count fn2-ops-set-c1-aux0 fn2-ops-set-c1-aux1
         fn2-ops-set-next-free fn2-ops-set-wake-deadline fn2-ops-set-wake-observation-gen
         update-fn2-ops-gen$ai update-fn2-ops-phase$ai update-fn2-ops-kind$ai update-fn2-ops-owner-kind$ai
         update-fn2-ops-owner-slot$ai update-fn2-ops-owner-gen$ai update-fn2-ops-principal$ai
         update-fn2-ops-range-slot$ai update-fn2-ops-range-gen$ai update-fn2-ops-range-off$ai
         update-fn2-ops-range-len$ai update-fn2-ops-cap-index$ai update-fn2-ops-cap-nonce$ai
         update-fn2-ops-storage-offset$ai update-fn2-ops-fua$ai update-fn2-ops-may-release$ai
         update-fn2-ops-cancel-slot$ai update-fn2-ops-cancel-gen$ai update-fn2-ops-cancel-requested$ai
         update-fn2-ops-c0-posted$ai update-fn2-ops-c0-harvested$ai update-fn2-ops-c0-event$ai
         update-fn2-ops-c0-outcome$ai update-fn2-ops-c0-reason$ai update-fn2-ops-c0-count$ai
         update-fn2-ops-c0-aux0$ai update-fn2-ops-c0-aux1$ai update-fn2-ops-peer-family$ai
         update-fn2-ops-peer-port$ai update-fn2-ops-peer-w0$ai update-fn2-ops-peer-w1$ai
         update-fn2-ops-peer-w2$ai update-fn2-ops-peer-w3$ai update-fn2-ops-c1-posted$ai
         update-fn2-ops-c1-harvested$ai update-fn2-ops-c1-event$ai update-fn2-ops-c1-outcome$ai
         update-fn2-ops-c1-reason$ai update-fn2-ops-c1-count$ai update-fn2-ops-c1-aux0$ai
         update-fn2-ops-c1-aux1$ai update-fn2-ops-next-free$ai update-fn2-ops-wake-deadline$ai
         update-fn2-ops-wake-observation-gen$ai ,@more)
        (update-nth-array update-nth)))
(in-theory (fn2-ops-frame-theory))

(defun fn2-ops-payload-key-okp (cell evkind outcome reason count aux0 aux1 kind may rlen)
  (declare (xargs :verify-guards nil))
  (and (unsigned-byte-p 1 cell)
       (natp evkind) (< evkind *fn2-event-count*) (natp outcome) (< outcome *fn2-outcome-count*)
       (natp reason) (< reason *fn2-reason-count*)
       (unsigned-byte-p 32 count) (unsigned-byte-p 32 aux0) (unsigned-byte-p 32 aux1)
       (fn2-event-statusp evkind outcome reason)
       (if (= cell 1)
           (and (= evkind *fn2-event-borrow-released*) (= outcome *fn2-outcome-done*)
                (= reason *fn2-reason-none*) (= count 0))
         (and (equal evkind (fn2-terminal-event kind))
              (if (= outcome *fn2-outcome-failed*)
                  (not (= reason *fn2-reason-none*)) (= reason *fn2-reason-none*))
              (implies (= reason *fn2-reason-uncertain*) (= evkind *fn2-event-write-result*))
              (implies (or (= outcome *fn2-outcome-not-found*) (= outcome *fn2-outcome-not-cancellable*))
                       (= evkind *fn2-event-cancel-result*))
              (implies (= evkind *fn2-event-send-result*)
                       (and (unsigned-byte-p 1 aux0)
                            (implies (= aux0 1) (= may 1))))
              (implies (or (= evkind *fn2-event-receive-result*) (= evkind *fn2-event-send-result*)
                           (= evkind *fn2-event-read-result*) (= evkind *fn2-event-write-result*)
                           (= evkind *fn2-event-entropy-result*))
                       (<= count rlen))))))
(defthm fn2-post-payloadp-by-key
  (equal (fn2-post-payloadp cell slot evkind outcome reason count aux0 aux1 fn2-ops)
         (fn2-ops-payload-key-okp cell evkind outcome reason count aux0 aux1
                                  (fn2-ops-kind slot fn2-ops) (fn2-ops-may-release slot fn2-ops)
                                  (fn2-ops-range-len slot fn2-ops)))
  :hints (("Goal" :expand ((fn2-post-payloadp cell slot evkind outcome reason count aux0 aux1 fn2-ops)
                           (fn2-ops-payload-key-okp cell evkind outcome reason count aux0 aux1
                                  (fn2-ops-kind slot fn2-ops) (fn2-ops-may-release slot fn2-ops)
                                  (fn2-ops-range-len slot fn2-ops)))
           :in-theory (theory 'minimal-theory))))
(in-theory (disable fn2-ops-payload-key-okp))

(defun fn2-ops-row-key-okp (phase p0 h0 p1 h1 may kind aux0 gen limit
                            e0 o0 r0 c0 a00 a01 e1 o1 r1 c1 a10 a11 rlen)
  (declare (xargs :verify-guards nil))
  (let ((pending (and (equal kind *fn2-action-send*) (equal aux0 1))))
    (and (< phase *fn2-op-phase-count*) (< kind *fn2-action-count*)
         (<= gen limit)
         (<= h0 p0) (<= h1 p1) (<= p1 may)
         (implies (equal p0 1) (fn2-ops-payload-key-okp 0 e0 o0 r0 c0 a00 a01 kind may rlen))
         (implies (equal p1 1) (fn2-ops-payload-key-okp 1 e1 o1 r1 c1 a10 a11 kind may rlen))
         (< e0 *fn2-event-count*) (< e1 *fn2-event-count*)
         (< o0 *fn2-outcome-count*) (< o1 *fn2-outcome-count*)
         (< r0 *fn2-reason-count*) (< r1 *fn2-reason-count*)
         (implies (member-equal phase (list *fn2-op-phase-free* *fn2-op-phase-reserved* *fn2-op-phase-queued*))
                  (and (equal p0 0) (equal h0 0) (equal p1 0) (equal h1 0)))
         (implies (equal phase *fn2-op-phase-submitted*) (equal h0 0))
         (implies (equal phase *fn2-op-phase-release-pending*)
                  (and (equal h0 1) (equal h1 0) (equal may 1)
                       (or pending (equal p1 1))))
         (implies (equal phase *fn2-op-phase-done*)
                  (if (fn2-action-completionp kind)
                      (and (equal h0 1) (equal p1 h1)
                           (implies pending (equal h1 1)))
                    (and (equal p0 0) (equal h0 0) (equal p1 0) (equal h1 0))))
         (implies (equal phase *fn2-op-phase-retired*)
                  (and (equal gen limit) (equal p0 h0) (equal p1 h1))))))
(defun fn2-ops-row-okp (slot fn2-ops)
  (declare (xargs :stobjs fn2-ops :verify-guards nil))
  (let* ((phase (fn2-ops-phase slot fn2-ops))
         (p0 (fn2-ops-c0-posted slot fn2-ops))
         (h0 (fn2-ops-c0-harvested slot fn2-ops))
         (p1 (fn2-ops-c1-posted slot fn2-ops))
         (h1 (fn2-ops-c1-harvested slot fn2-ops))
         (may (fn2-ops-may-release slot fn2-ops))
         (pending (and (equal (fn2-ops-kind slot fn2-ops) *fn2-action-send*)
                       (equal (fn2-ops-c0-aux0 slot fn2-ops) 1))))
    (and (< phase *fn2-op-phase-count*) (< (fn2-ops-kind slot fn2-ops) *fn2-action-count*)
         (<= (fn2-ops-gen slot fn2-ops) (fn2-ops-gen-limit fn2-ops))
         (<= h0 p0) (<= h1 p1) (<= p1 may)
         (implies (equal p0 1)
                  (fn2-post-payloadp 0 slot (fn2-ops-c0-event slot fn2-ops)
                    (fn2-ops-c0-outcome slot fn2-ops) (fn2-ops-c0-reason slot fn2-ops)
                    (fn2-ops-c0-count slot fn2-ops) (fn2-ops-c0-aux0 slot fn2-ops)
                    (fn2-ops-c0-aux1 slot fn2-ops) fn2-ops))
         (implies (equal p1 1)
                  (fn2-post-payloadp 1 slot (fn2-ops-c1-event slot fn2-ops)
                    (fn2-ops-c1-outcome slot fn2-ops) (fn2-ops-c1-reason slot fn2-ops)
                    (fn2-ops-c1-count slot fn2-ops) (fn2-ops-c1-aux0 slot fn2-ops)
                    (fn2-ops-c1-aux1 slot fn2-ops) fn2-ops))
         (< (fn2-ops-c0-event slot fn2-ops) *fn2-event-count*)
         (< (fn2-ops-c1-event slot fn2-ops) *fn2-event-count*)
         (< (fn2-ops-c0-outcome slot fn2-ops) *fn2-outcome-count*)
         (< (fn2-ops-c1-outcome slot fn2-ops) *fn2-outcome-count*)
         (< (fn2-ops-c0-reason slot fn2-ops) *fn2-reason-count*)
         (< (fn2-ops-c1-reason slot fn2-ops) *fn2-reason-count*)
         (implies (member-equal phase (list *fn2-op-phase-free* *fn2-op-phase-reserved* *fn2-op-phase-queued*))
                  (and (equal p0 0) (equal h0 0) (equal p1 0) (equal h1 0)))
         (implies (equal phase *fn2-op-phase-submitted*) (equal h0 0))
         (implies (equal phase *fn2-op-phase-release-pending*)
                  (and (equal h0 1) (equal h1 0) (equal may 1)
                       (or pending (equal p1 1))))
         (implies (equal phase *fn2-op-phase-done*)
                  (if (fn2-action-completionp (fn2-ops-kind slot fn2-ops))
                      (and (equal h0 1) (equal p1 h1)
                           (implies pending (equal h1 1)))
                    (and (equal p0 0) (equal h0 0) (equal p1 0) (equal h1 0))))
         (implies (equal phase *fn2-op-phase-retired*)
                  (and (equal (fn2-ops-gen slot fn2-ops) (fn2-ops-gen-limit fn2-ops))
                       (equal p0 h0) (equal p1 h1))))))
(defthm fn2-ops-row-okp-by-key
  (equal (fn2-ops-row-okp slot fn2-ops)
         (fn2-ops-row-key-okp (fn2-ops-phase slot fn2-ops) (fn2-ops-c0-posted slot fn2-ops)
                       (fn2-ops-c0-harvested slot fn2-ops) (fn2-ops-c1-posted slot fn2-ops)
                       (fn2-ops-c1-harvested slot fn2-ops) (fn2-ops-may-release slot fn2-ops)
                       (fn2-ops-kind slot fn2-ops) (fn2-ops-c0-aux0 slot fn2-ops)
                       (fn2-ops-gen slot fn2-ops) (fn2-ops-gen-limit fn2-ops)
                       (fn2-ops-c0-event slot fn2-ops) (fn2-ops-c0-outcome slot fn2-ops)
                       (fn2-ops-c0-reason slot fn2-ops) (fn2-ops-c0-count slot fn2-ops)
                       (fn2-ops-c0-aux0 slot fn2-ops) (fn2-ops-c0-aux1 slot fn2-ops)
                       (fn2-ops-c1-event slot fn2-ops) (fn2-ops-c1-outcome slot fn2-ops)
                       (fn2-ops-c1-reason slot fn2-ops) (fn2-ops-c1-count slot fn2-ops)
                       (fn2-ops-c1-aux0 slot fn2-ops) (fn2-ops-c1-aux1 slot fn2-ops)
                       (fn2-ops-range-len slot fn2-ops)))
  :rule-classes nil
  :hints (("Goal" :expand ((fn2-ops-row-okp slot fn2-ops)
                           (:free (a b c d e f g h i j k l m n o pp q r s2 tt u v w)
                                  (fn2-ops-row-key-okp a b c d e f g h i j k l m n o pp q r s2 tt u v w)))
           :in-theory (union-theories '(fn2-post-payloadp-by-key) (theory 'minimal-theory)))))
(in-theory (disable fn2-ops-row-key-okp))

(defun fn2-ops-rows-ok-except (n s fn2-ops)
  (declare (xargs :stobjs fn2-ops :verify-guards nil :measure (nfix n)))
  (if (zp n) t
    (and (or (equal (- n 1) s) (fn2-ops-row-okp (- n 1) fn2-ops))
         (fn2-ops-rows-ok-except (- n 1) s fn2-ops))))

(defthm fn2-ops-row-semanticp-step
  (equal (fn2-ops-row-semanticp n fn2-ops)
         (if (zp n) t
           (and (fn2-ops-row-okp (- n 1) fn2-ops)
                (fn2-ops-row-semanticp (- n 1) fn2-ops))))
  :rule-classes ((:definition :controller-alist ((fn2-ops-row-semanticp t nil))))
  :hints (("Goal" :expand ((fn2-ops-row-semanticp n fn2-ops))
           :in-theory (union-theories '(fn2-ops-row-okp (:type-prescription fn2-ops-row-semanticp)
                                        (:executable-counterpart member-equal) (:executable-counterpart equal))
                                      (theory 'minimal-theory)))))
(in-theory (disable fn2-ops-row-semanticp-step))
(defthm fn2-ops-nth-row-of-update-nth-array-other-row
  (implies (and (natp i) (natp ii) (natp j) (natp kk) (not (equal i ii)))
           (equal (nth i (nth j (update-nth-array kk ii vv l))) (nth i (nth j l)))))
(defthm fn2-ops-nth-of-update-nth-array-other
  (implies (not (equal (nfix j) (nfix kk)))
           (equal (nth j (update-nth-array kk ii vv l)) (nth j l))))
(defthm fn2-ops-row-okp-of-update-nth-array-other-row
  (implies (and (natp kk) (natp slot) (natp ii) (not (equal kk 72)) (not (equal slot ii)))
           (equal (fn2-ops-row-okp slot (update-nth-array kk ii vv fn2-ops))
                  (fn2-ops-row-okp slot fn2-ops)))
  :hints (("Goal" :use ((:instance fn2-ops-row-okp-by-key)
                        (:instance fn2-ops-row-okp-by-key (fn2-ops (update-nth-array kk ii vv fn2-ops))))
           :in-theory (e/d (fn2-ops-nth-row-of-update-nth-array-other-row fn2-ops-nth-of-update-nth-array-other)
                           (fn2-ops-row-okp fn2-ops-nth-of-update-nth-array)))))
(defthm fn2-ops-row-okp-of-update-nth
  (implies (and (natp kk) (<= 44 kk) (not (equal kk 72)))
           (equal (fn2-ops-row-okp slot (update-nth kk vv fn2-ops))
                  (fn2-ops-row-okp slot fn2-ops)))
  :hints (("Goal" :use ((:instance fn2-ops-row-okp-by-key)
                        (:instance fn2-ops-row-okp-by-key (fn2-ops (update-nth kk vv fn2-ops))))
           :in-theory (disable fn2-ops-row-okp))))
(defthm fn2-ops-row-okp-of-update-nth-array
  (implies (and (natp kk) (not (member kk '(0 1 2 10 15 19 20 21 22 23 24 25 26 33 34 35 36 37 38 39 40 72))))
           (equal (fn2-ops-row-okp slot (update-nth-array kk ii vv fn2-ops))
                  (fn2-ops-row-okp slot fn2-ops)))
  :hints (("Goal" :use ((:instance fn2-ops-row-okp-by-key)
                        (:instance fn2-ops-row-okp-by-key (fn2-ops (update-nth-array kk ii vv fn2-ops))))
           :in-theory (disable fn2-ops-row-okp))))
(in-theory (disable fn2-ops-nth-row-of-update-nth-array-other-row fn2-ops-nth-of-update-nth-array-other))
(in-theory (disable fn2-ops-row-okp))


;; Frame rules: a closed reader is unchanged by a write to a field it does
;; not read. One pair per reader, every field quantified.
(defun fn2-ops-frame-sym (d suffix)
  (declare (xargs :guard (and (symbolp d) (stringp suffix))))
  (intern-in-package-of-symbol (concatenate 'string (symbol-name d) suffix) 'fn2-ops))
(defun fn2-ops-frame-events (d formals keys induct enables)
  (declare (xargs :guard (and (symbolp d) (true-listp formals))))
  (let ((args (butlast formals 1)))
    `((defthm ,(fn2-ops-frame-sym d "-OF-UPDATE-NTH-ARRAY")
        (implies (and (natp kk) (not (member kk ',keys)))
                 (equal (,d ,@args (update-nth-array kk ii vv fn2-ops)) (,d ,@args fn2-ops)))
        :hints (("Goal" ,@(and induct `(:induct (,d ,@formals)))
                 :in-theory (fn2-ops-frame-theory ,d ,@enables))))
      (defthm ,(fn2-ops-frame-sym d "-OF-UPDATE-NTH")
        (implies (and (natp kk) (not (member kk ',keys)))
                 (equal (,d ,@args (update-nth kk vv fn2-ops)) (,d ,@args fn2-ops)))
        :hints (("Goal" ,@(and induct `(:induct (,d ,@formals)))
                 :in-theory (fn2-ops-frame-theory ,d ,@enables)))))))
(defmacro fn2-ops-frames (d formals keys &key induct enables)
  (cons 'progn (fn2-ops-frame-events d formals keys induct enables)))

(fn2-ops-frames fn2-ops-rows-ok-except (n s fn2-ops) (0 1 2 10 15 19 20 21 22 23 24 25 26 33 34 35 36 37 38 39 40 72) :induct t)
(fn2-ops-frames fn2-ops-phase-slots (n phase fn2-ops) (1) :induct t)
(fn2-ops-frames fn2-ops-free-chain (fuel slot fn2-ops) (41 44) :induct t :enables (fn2-op-slotp))
(fn2-ops-frames fn2-ops-pending-cells (n fn2-ops) (19 20 33 34) :induct t)
(fn2-ops-frames fn2-ops-queued-refsp (refs fn2-ops) (0 1 44) :induct t :enables (fn2-op-slotp))
(fn2-ops-frames fn2-ops-outbox-list-aux (left idx fn2-ops) (45 46) :induct t)
(fn2-ops-frames fn2-ops-posted-list-aux (left idx fn2-ops) (47) :induct t)

;; A write at row S leaves every other row's clause alone.
(defthm fn2-ops-rows-ok-except-of-update-nth-array-at
  (implies (and (natp s) (natp kk) (not (equal kk 72)))
           (equal (fn2-ops-rows-ok-except n s (update-nth-array kk s vv fn2-ops))
                  (fn2-ops-rows-ok-except n s fn2-ops)))
  :hints (("Goal" :induct (fn2-ops-rows-ok-except n s fn2-ops)
           :in-theory (fn2-ops-frame-theory fn2-ops-rows-ok-except))))
(in-theory (disable fn2-ops-rows-ok-except))

(defthm fn2-ops-rows-ok-except-of-row-semanticp
  (implies (fn2-ops-row-semanticp n fn2-ops) (fn2-ops-rows-ok-except n s fn2-ops))
  :hints (("Goal" :induct (fn2-ops-rows-ok-except n s fn2-ops)
           :in-theory (enable fn2-ops-rows-ok-except fn2-ops-row-semanticp-step))))
(defthm fn2-ops-row-semanticp-of-rows-ok-except
  (implies (and (fn2-ops-rows-ok-except n s fn2-ops)
                (implies (and (natp s) (< s (nfix n))) (fn2-ops-row-okp s fn2-ops)))
           (fn2-ops-row-semanticp n fn2-ops))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-ops-rows-ok-except n s fn2-ops)
           :in-theory (enable fn2-ops-rows-ok-except fn2-ops-row-semanticp-step))))
(defthm fn2-ops-row-okp-of-row-semanticp
  (implies (and (fn2-ops-row-semanticp n fn2-ops) (natp i) (< i n))
           (fn2-ops-row-okp i fn2-ops))
  :hints (("Goal" :induct (fn2-ops-rows-ok-except n i fn2-ops)
           :in-theory (enable fn2-ops-rows-ok-except fn2-ops-row-semanticp-step))))

;; Lists.
(defthm fn2-ops-member-remove
  (iff (member-equal x (remove-equal a l)) (and (member-equal x l) (not (equal x a)))))
(defthm fn2-ops-member-append
  (iff (member-equal x (append a b)) (or (member-equal x a) (member-equal x b))))
(defthm fn2-ops-subsetp-trans
  (implies (and (subsetp-equal x y) (subsetp-equal y z)) (subsetp-equal x z)))
(defthm fn2-ops-subsetp-cons-right
  (implies (subsetp-equal x y) (subsetp-equal x (cons a y))))
(defthm fn2-ops-subsetp-refl (subsetp-equal x x))
(defthm fn2-ops-subsetp-remove
  (implies (and (subsetp-equal x y) (not (member-equal a x)))
           (subsetp-equal x (remove-equal a y))))
(defthm fn2-ops-remove-subsetp
  (implies (subsetp-equal y (cons a x)) (subsetp-equal (remove-equal a y) x)))
(defthm fn2-ops-not-member-of-subsetp
  (implies (and (subsetp-equal x y) (not (member-equal a y))) (not (member-equal a x))))
(defthm fn2-ops-member-of-subsetp
  (implies (and (subsetp-equal x y) (member-equal a x)) (member-equal a y)))
(defthm fn2-ops-remove-equal-non-member
  (implies (and (true-listp l) (not (member-equal a l))) (equal (remove-equal a l) l)))
(defthm fn2-ops-no-dups-remove
  (implies (no-duplicatesp-equal l) (no-duplicatesp-equal (remove-equal a l))))
(defthm fn2-ops-subsetp-append
  (equal (subsetp-equal (append a b) c) (and (subsetp-equal a c) (subsetp-equal b c))))
(defthm fn2-ops-no-dups-append-singleton
  (equal (no-duplicatesp-equal (append a (list s)))
         (and (no-duplicatesp-equal a) (not (member-equal s a)))))

(defthm fn2-ops-len-remove-member
  (implies (and (member-equal a l) (no-duplicatesp-equal l))
           (equal (len (remove-equal a l)) (- (len l) 1))))
(defthm fn2-ops-car-not-member-cdr
  (implies (no-duplicatesp-equal l) (not (member-equal (car l) (cdr l)))))
(defthm fn2-ops-no-dups-cdr
  (implies (no-duplicatesp-equal l) (no-duplicatesp-equal (cdr l))))
(defthm fn2-ops-not-member-cdr
  (implies (not (member-equal a l)) (not (member-equal a (cdr l)))))
(defthm fn2-ops-len-cdr
  (implies (consp l) (equal (len (cdr l)) (- (len l) 1))))
(defthm fn2-ops-same-members-no-dups
  (implies (fn2-ops-same-membersp a b)
           (and (no-duplicatesp-equal a) (no-duplicatesp-equal b)
                (subsetp-equal a b) (subsetp-equal b a)))
  :rule-classes :forward-chaining)
(defthm fn2-ops-subsetp-cons-cons
  (implies (subsetp-equal x y) (subsetp-equal (cons a x) (cons a y))))
(defthm fn2-ops-subsetp-cdr
  (subsetp-equal (cdr x) x))
(defthm fn2-ops-subsetp-cons-append
  (subsetp-equal (cons s c) (append c (list s))))
(defthm fn2-ops-subsetp-cons-car-cdr
  (implies (consp c) (subsetp-equal c (cons (car c) (cdr c)))))
(defthm fn2-ops-same-members-pop
  (implies (and (consp c) (fn2-ops-same-membersp c f) (equal a (car c)))
           (fn2-ops-same-membersp (cdr c) (remove-equal a f)))
  :hints (("Goal" :do-not-induct t :in-theory (enable fn2-ops-same-membersp)
           :use ((:instance fn2-ops-subsetp-trans (x (cdr c)) (y c) (z f))
                 (:instance fn2-ops-subsetp-remove (x (cdr c)) (y f))
                 (:instance fn2-ops-subsetp-trans (x f) (y c) (z (cons (car c) (cdr c))))
                 (:instance fn2-ops-remove-subsetp (y f) (x (cdr c)))))))
(defthm fn2-ops-same-members-push
  (implies (and (fn2-ops-same-membersp c f) (not (member-equal s f))
                (member-equal s f2) (subsetp-equal f f2) (subsetp-equal f2 (cons s f))
                (no-duplicatesp-equal f2))
           (and (fn2-ops-same-membersp (cons s c) f2)
                (fn2-ops-same-membersp (append c (list s)) f2)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (enable fn2-ops-same-membersp)
           :use ((:instance fn2-ops-subsetp-trans (x c) (y f) (z f2))
                 (:instance fn2-ops-not-member-of-subsetp (x c) (y f) (a s))
                 (:instance fn2-ops-subsetp-cons-cons (x f) (y c) (a s))
                 (:instance fn2-ops-subsetp-trans (x f2) (y (cons s f)) (z (cons s c)))
                 (:instance fn2-ops-subsetp-trans (x f2) (y (cons s c)) (z (append c (list s))))))))
(in-theory (disable fn2-ops-same-membersp))

;; Phase classes.
(defthm fn2-ops-member-phase-slots
  (iff (member-equal x (fn2-ops-phase-slots n ph fn2-ops))
       (and (natp x) (< x (nfix n)) (equal (nth x (nth 1 fn2-ops)) ph))))
(defthm fn2-ops-no-dups-phase-slots
  (no-duplicatesp-equal (fn2-ops-phase-slots n ph fn2-ops)))
(defthm fn2-ops-true-listp-phase-slots
  (true-listp (fn2-ops-phase-slots n ph fn2-ops))
  :rule-classes :type-prescription)
(defthm fn2-ops-phase-slots-of-set-phase-same-value
  (implies (equal vv (nth s (nth 1 fn2-ops)))
           (equal (fn2-ops-phase-slots n ph (update-nth-array 1 s vv fn2-ops))
                  (fn2-ops-phase-slots n ph fn2-ops))))
(defthm fn2-ops-phase-slots-of-set-phase-other
  (implies (and (natp s) (not (equal vv ph)))
           (equal (fn2-ops-phase-slots n ph (update-nth-array 1 s vv fn2-ops))
                  (remove-equal s (fn2-ops-phase-slots n ph fn2-ops)))))
(defthm fn2-ops-phase-slots-of-set-phase-into
  (implies (natp s)
           (subsetp-equal (fn2-ops-phase-slots n ph (update-nth-array 1 s vv fn2-ops))
                          (cons s (fn2-ops-phase-slots n ph fn2-ops)))))
(defthm fn2-ops-subsetp-phase-slots-of-set-phase-same
  (implies (and (equal vv ph) (subsetp-equal x (fn2-ops-phase-slots n ph fn2-ops)))
           (subsetp-equal x (fn2-ops-phase-slots n ph (update-nth-array 1 s vv fn2-ops))))
  :hints (("Goal" :induct (len x))))
(defthm fn2-ops-len-phase-slots-of-set-phase
  (implies (natp s)
           (equal (len (fn2-ops-phase-slots n ph (update-nth-array 1 s vv fn2-ops)))
                  (if (< s (nfix n))
                      (+ (len (fn2-ops-phase-slots n ph fn2-ops))
                         (if (equal vv ph) 1 0)
                         (- (if (equal (nth s (nth 1 fn2-ops)) ph) 1 0)))
                    (len (fn2-ops-phase-slots n ph fn2-ops))))))
(in-theory (disable fn2-ops-phase-slots))

(defthm fn2-ops-row-okp-phase-bound
  (implies (fn2-ops-row-okp i fn2-ops) (< (nth i (nth 1 fn2-ops)) 7))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable fn2-ops-row-okp fn2-ops-row-key-okp))))
(defthm fn2-ops-row-okp-idle-cells
  (implies (and (member-equal (nth i (nth 1 fn2-ops)) '(0 1 2)) (fn2-ops-row-okp i fn2-ops))
           (and (equal (nth i (nth 19 fn2-ops)) 0) (equal (nth i (nth 20 fn2-ops)) 0)
                (equal (nth i (nth 33 fn2-ops)) 0) (equal (nth i (nth 34 fn2-ops)) 0)))
  :hints (("Goal" :in-theory (enable fn2-ops-row-okp fn2-ops-row-key-okp))))
(defthm fn2-ops-row-okp-gen-bound
  (implies (fn2-ops-row-okp i fn2-ops) (<= (nth i (nth 0 fn2-ops)) (nth 72 fn2-ops)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable fn2-ops-row-okp fn2-ops-row-key-okp))))
(defthm fn2-ops-phase-partition
  (implies (and (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops) (natp n) (<= n (fn2-ops-rows fn2-ops))
                (fn2-ops-row-semanticp n fn2-ops))
           (equal (+ (len (fn2-ops-phase-slots n 0 fn2-ops)) (len (fn2-ops-phase-slots n 1 fn2-ops))
                     (len (fn2-ops-phase-slots n 2 fn2-ops)) (len (fn2-ops-phase-slots n 3 fn2-ops))
                     (len (fn2-ops-phase-slots n 4 fn2-ops)) (len (fn2-ops-phase-slots n 5 fn2-ops))
                     (len (fn2-ops-phase-slots n 6 fn2-ops)))
                  n))
  :hints (("Goal" :induct (fn2-ops-row-semanticp n fn2-ops)
           :in-theory (enable fn2-ops-phase-slots fn2-ops-row-semanticp-step))
          ("Subgoal *1/2" :use ((:instance fn2-ops-phase-raw-nth-natp (i (- n 1)))
                                (:instance fn2-ops-row-okp-of-row-semanticp (i (- n 1)))))))

;; The free chain.
(defthm fn2-ops-free-chain-of-set-next-free
  (implies (and (natp s) (not (member-equal s (fn2-ops-free-chain f x fn2-ops))))
           (equal (fn2-ops-free-chain f x (update-nth-array 41 s vv fn2-ops))
                  (fn2-ops-free-chain f x fn2-ops)))
  :hints (("Goal" :in-theory (fn2-ops-frame-theory fn2-ops-free-chain fn2-op-slotp))))
(defthm fn2-ops-free-chain-consp
  (implies (not (equal x *fn2-none*)) (consp (fn2-ops-free-chain f x fn2-ops))))
(defun fn2-ops-chain-fuel-ind (f g x fn2-ops)
  (declare (xargs :stobjs fn2-ops :verify-guards nil :measure (nfix f)))
  (cond ((equal x *fn2-none*) nil)
        ((or (zp f) (zp g) (not (fn2-op-slotp x fn2-ops))) nil)
        (t (fn2-ops-chain-fuel-ind (- f 1) (- g 1) (fn2-ops-next-free x fn2-ops) fn2-ops))))
(defthm fn2-ops-free-chain-fuel
  (implies (and (not (member-equal :bad-chain (fn2-ops-free-chain f x fn2-ops)))
                (natp g) (<= (len (fn2-ops-free-chain f x fn2-ops)) g))
           (equal (fn2-ops-free-chain g x fn2-ops) (fn2-ops-free-chain f x fn2-ops)))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-ops-chain-fuel-ind f g x fn2-ops))))
(defthm fn2-ops-free-chain-len-bound
  (implies (and (natp f) (not (member-equal :bad-chain (fn2-ops-free-chain f x fn2-ops))))
           (<= (len (fn2-ops-free-chain f x fn2-ops)) f))
  :rule-classes :linear)
(defthm fn2-ops-free-chain-car
  (implies (and (not (equal x *fn2-none*))
                (not (member-equal :bad-chain (fn2-ops-free-chain f x fn2-ops))))
           (equal (car (fn2-ops-free-chain f x fn2-ops)) x)))
(defthm fn2-ops-free-chain-slotp
  (implies (and (not (equal x *fn2-none*))
                (not (member-equal :bad-chain (fn2-ops-free-chain f x fn2-ops))))
           (and (natp x) (< x (nth 44 fn2-ops))))
  :rule-classes nil)
(defthm fn2-ops-free-chain-tail
  (implies (and (natp n) (not (equal s *fn2-none*))
                (not (member-equal :bad-chain (fn2-ops-free-chain n s fn2-ops))))
           (equal (fn2-ops-free-chain n (nth s (nth 41 fn2-ops)) fn2-ops)
                  (cdr (fn2-ops-free-chain n s fn2-ops))))
  :hints (("Goal" :expand ((fn2-ops-free-chain n s fn2-ops))
           :use ((:instance fn2-ops-free-chain-len-bound (f (- n 1)) (x (nth s (nth 41 fn2-ops))))
                 (:instance fn2-ops-free-chain-fuel (f (- n 1)) (g n) (x (nth s (nth 41 fn2-ops))))))))
(defthm fn2-ops-free-chain-push
  (implies (and (natp s) (< s (nth 44 fn2-ops)) (not (zp n)) (not (equal s *fn2-none*))
                (not (member-equal :bad-chain (fn2-ops-free-chain n h fn2-ops)))
                (< (len (fn2-ops-free-chain n h fn2-ops)) n)
                (not (member-equal s (fn2-ops-free-chain n h fn2-ops))))
           (equal (fn2-ops-free-chain n s (update-nth-array 41 s h fn2-ops))
                  (cons s (fn2-ops-free-chain n h fn2-ops))))
  :hints (("Goal" :expand ((fn2-ops-free-chain n s (update-nth-array 41 s h fn2-ops)))
           :use ((:instance fn2-ops-free-chain-fuel (f n) (g (- n 1)) (x h))))))
(in-theory (disable fn2-ops-free-chain))

;; Ring positions. The traversals step by (mod (+ 1 idx) cap); a ring write
;; lands at (mod (+ head count) cap), which the first COUNT positions miss.
(defun fn2-ops-ring-pos (left idx cap)
  (declare (xargs :measure (nfix left) :verify-guards nil))
  (if (zp left) nil
    (cons idx (fn2-ops-ring-pos (- left 1) (mod (+ 1 (nfix idx)) cap) cap))))
(defun fn2-ops-ring-ind (left idx k cap)
  (declare (xargs :measure (nfix left) :verify-guards nil))
  (if (zp left) (list idx k cap)
    (fn2-ops-ring-ind (- left 1) (mod (+ 1 (nfix idx)) cap) (- k 1) cap)))
(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm fn2-ops-ring-next-is-mod
    (implies (and (natp i) (integerp cap) (< i cap)) (equal (fn2-ring-next i cap) (mod (+ 1 i) cap))))
  (defthm fn2-ops-mod-mod-plus
    (implies (and (natp a) (natp b) (posp c)) (equal (mod (+ b (mod a c)) c) (mod (+ a b) c))))
  (defthm fn2-ops-mod-small
    (implies (and (natp a) (< a c)) (equal (mod a c) a)))
  (defthm fn2-ops-mod-natp
    (implies (and (natp a) (posp c)) (natp (mod a c)))
    :rule-classes :type-prescription)
  (defthm fn2-ops-mod-bound
    (implies (and (natp a) (posp c)) (< (mod a c) c))
    :rule-classes :linear)
  (defthm fn2-ops-ring-pos-misses-end
    (implies (and (posp cap) (natp idx) (< idx cap) (natp left) (integerp k) (<= left k) (< k cap))
             (not (member-equal (mod (+ idx k) cap) (fn2-ops-ring-pos left idx cap))))
    :hints (("Goal" :induct (fn2-ops-ring-ind left idx k cap))))
  (defthm fn2-ops-even-not-odd
    (implies (and (integerp a) (integerp b)) (not (equal (* 2 a) (+ 1 (* 2 b))))))
  (defthm fn2-ops-even-cancel
    (implies (and (acl2-numberp a) (acl2-numberp b)) (equal (equal (* 2 a) (* 2 b)) (equal a b))))
  (defthm fn2-ops-odd-cancel
    (implies (and (acl2-numberp a) (acl2-numberp b))
             (equal (equal (+ 1 (* 2 a)) (+ 1 (* 2 b))) (equal a b))))
  (defthm fn2-ops-cell-split
    (implies (natp e)
             (and (natp (floor e 2)) (or (equal (mod e 2) 0) (equal (mod e 2) 1))
                  (equal (+ (mod e 2) (* 2 (floor e 2))) e)))
    :rule-classes nil)
  (defthm fn2-ops-ring-shape-push
    (implies (and (fn2-ops-ring-shapep cap h tl c) (< c cap))
             (fn2-ops-ring-shapep cap h (fn2-ring-next tl cap) (+ 1 c))))
  (defthm fn2-ops-ring-shape-pop
    (implies (and (fn2-ops-ring-shapep cap h tl c) (< 0 c))
             (fn2-ops-ring-shapep cap (fn2-ring-next h cap) tl (- c 1)))))
(in-theory (disable fn2-ring-next fn2-ops-ring-shapep))

;; Posted and unharvested cells.
(defthm fn2-ops-member-pending-even
  (implies (and (natp s) (natp n))
           (iff (member-equal (* 2 s) (fn2-ops-pending-cells n fn2-ops))
                (and (< s n) (equal (nth s (nth 19 fn2-ops)) 1) (equal (nth s (nth 20 fn2-ops)) 0)))))
(defthm fn2-ops-member-pending-odd
  (implies (and (natp s) (natp n))
           (iff (member-equal (+ 1 (* 2 s)) (fn2-ops-pending-cells n fn2-ops))
                (and (< s n) (equal (nth s (nth 33 fn2-ops)) 1) (equal (nth s (nth 34 fn2-ops)) 0)))))
(defthm fn2-ops-no-dups-pending
  (no-duplicatesp-equal (fn2-ops-pending-cells n fn2-ops)))
(defthm fn2-ops-true-listp-pending
  (true-listp (fn2-ops-pending-cells n fn2-ops)) :rule-classes :type-prescription)
(defthm fn2-ops-pending-of-same-status
  (implies (and (natp s) (member kk '(19 20 33 34))
                (iff (and (equal (nth s (nth 19 (update-nth-array kk s vv fn2-ops))) 1)
                          (equal (nth s (nth 20 (update-nth-array kk s vv fn2-ops))) 0))
                     (and (equal (nth s (nth 19 fn2-ops)) 1) (equal (nth s (nth 20 fn2-ops)) 0)))
                (iff (and (equal (nth s (nth 33 (update-nth-array kk s vv fn2-ops))) 1)
                          (equal (nth s (nth 34 (update-nth-array kk s vv fn2-ops))) 0))
                     (and (equal (nth s (nth 33 fn2-ops)) 1) (equal (nth s (nth 34 fn2-ops)) 0))))
           (equal (fn2-ops-pending-cells n (update-nth-array kk s vv fn2-ops))
                  (fn2-ops-pending-cells n fn2-ops))))
(defthm fn2-ops-pending-of-harvest0
  (implies (natp s)
           (equal (fn2-ops-pending-cells n (update-nth-array 20 s 1 fn2-ops))
                  (remove-equal (* 2 s) (fn2-ops-pending-cells n fn2-ops)))))
(defthm fn2-ops-pending-of-harvest1
  (implies (natp s)
           (equal (fn2-ops-pending-cells n (update-nth-array 34 s 1 fn2-ops))
                  (remove-equal (+ 1 (* 2 s)) (fn2-ops-pending-cells n fn2-ops)))))
(defthm fn2-ops-pending-of-post0
  (implies (natp s)
           (and (subsetp-equal (fn2-ops-pending-cells n fn2-ops)
                               (fn2-ops-pending-cells n (update-nth-array 19 s 1 fn2-ops)))
                (subsetp-equal (fn2-ops-pending-cells n (update-nth-array 19 s 1 fn2-ops))
                               (cons (* 2 s) (fn2-ops-pending-cells n fn2-ops))))))
(defthm fn2-ops-pending-of-post1
  (implies (natp s)
           (and (subsetp-equal (fn2-ops-pending-cells n fn2-ops)
                               (fn2-ops-pending-cells n (update-nth-array 33 s 1 fn2-ops)))
                (subsetp-equal (fn2-ops-pending-cells n (update-nth-array 33 s 1 fn2-ops))
                               (cons (+ 1 (* 2 s)) (fn2-ops-pending-cells n fn2-ops))))))
(in-theory (disable fn2-ops-pending-cells))

;; Queued references.
(defthm fn2-ops-queued-refsp-other-rows
  (implies (and (natp s) (not (equal (nfix kk) 44))
                (not (member-equal s (fn2-ops-ref-slots refs))))
           (equal (fn2-ops-queued-refsp refs (update-nth-array kk s vv fn2-ops))
                  (fn2-ops-queued-refsp refs fn2-ops)))
  :hints (("Goal" :in-theory (fn2-ops-frame-theory fn2-ops-queued-refsp fn2-op-slotp))))
(defthm fn2-ops-queued-refsp-append
  (implies (true-listp refs)
           (equal (fn2-ops-queued-refsp (append refs (list r)) fn2-ops)
                  (and (fn2-ops-queued-refsp refs fn2-ops)
                       (fn2-ops-queued-refsp (list r) fn2-ops)))))
(defthm fn2-ops-queued-refsp-true-listp
  (implies (fn2-ops-queued-refsp refs fn2-ops) (true-listp refs))
  :rule-classes :forward-chaining)
(defthm fn2-ops-queued-refsp-cdr
  (implies (fn2-ops-queued-refsp refs fn2-ops) (fn2-ops-queued-refsp (cdr refs) fn2-ops)))
(defthm fn2-ops-ref-slots-append
  (equal (fn2-ops-ref-slots (append a b)) (append (fn2-ops-ref-slots a) (fn2-ops-ref-slots b))))
(defthm fn2-ops-ref-slots-cdr
  (equal (fn2-ops-ref-slots (cdr a)) (cdr (fn2-ops-ref-slots a))))
(defthm fn2-ops-car-ref-slots
  (equal (car (fn2-ops-ref-slots a)) (car (car a))))
(defthm fn2-ops-consp-ref-slots
  (equal (consp (fn2-ops-ref-slots a)) (consp a)))


(defmacro fn2-ops-ring-list-lemmas (aux cap-col cols entry)
  `(progn
     (defthm ,(fn2-ops-frame-sym aux "-OF-RING-WRITE")
       (implies (and (natp tt) (member kk ',cols) (< tt (len (nth ,cap-col fn2-ops)))
                     (not (member-equal tt (fn2-ops-ring-pos left idx (len (nth ,cap-col fn2-ops))))))
                (equal (,aux left idx (update-nth-array kk tt vv fn2-ops)) (,aux left idx fn2-ops)))
       :hints (("Goal" :induct (,aux left idx fn2-ops) :in-theory (enable ,aux))))
     (defthm ,(fn2-ops-frame-sym aux "-SNOC")
       (implies (and (natp left) (natp idx) (< idx (len (nth ,cap-col fn2-ops))))
                (equal (,aux (+ 1 left) idx fn2-ops)
                       (append (,aux left idx fn2-ops)
                               (list ,(let ((i `(mod (+ idx left) (len (nth ,cap-col fn2-ops))))) (sublis (list (cons 'i i)) entry))))))
       :hints (("Goal" :induct (,aux left idx fn2-ops) :in-theory (enable ,aux))))
     (defthm ,(fn2-ops-frame-sym aux "-POP")
       (implies (and (not (zp left)) (natp idx) (< idx (len (nth ,cap-col fn2-ops))))
                (and (equal (car (,aux left idx fn2-ops)) ,(sublis (list (cons 'i 'idx)) entry))
                     (equal (cdr (,aux left idx fn2-ops))
                            (,aux (- left 1) (mod (+ 1 idx) (len (nth ,cap-col fn2-ops))) fn2-ops))
                     (consp (,aux left idx fn2-ops))))
       :hints (("Goal" :expand ((,aux left idx fn2-ops)))))
     (defthm ,(fn2-ops-frame-sym aux "-TRUE-LISTP")
       (true-listp (,aux left idx fn2-ops)) :rule-classes :type-prescription)
     (in-theory (disable ,aux))))
(fn2-ops-ring-list-lemmas fn2-ops-outbox-list-aux 45 (45 46) (list (nth i (nth 45 fn2-ops)) (nth i (nth 46 fn2-ops))))
(fn2-ops-ring-list-lemmas fn2-ops-posted-list-aux 47 (47) (nth i (nth 47 fn2-ops)))

;; CLEAR-ROW writes every column of one row: its contract, once.
(defun fn2-ops-clear-val (k g nx)
  (declare (xargs :guard t))
  (cond ((equal k 0) g) ((equal k 41) nx) (t 0)))
(defthm fn2-ops-nth-of-clear-row
  (implies (natp k)
           (equal (nth k (fn2-ops-clear-row s g nx fn2-ops))
                  (if (< k 44) (update-nth s (fn2-ops-clear-val k g nx) (nth k fn2-ops)) (nth k fn2-ops))))
  :hints (("Goal" :in-theory (fn2-ops-frame-theory fn2-ops-clear-row))))
(defmacro fn2-ops-clear-row-lemma (name d formals rhs &key hyps induct)
  `(defthm ,name
     (implies (and (natp s) ,@hyps)
              (equal (,d ,@(butlast formals 1) (fn2-ops-clear-row s g nx fn2-ops)) ,rhs))
     :hints (("Goal" :induct ,(or induct `(,d ,@formals)) :in-theory (enable ,d)))))
(defthm fn2-ops-row-okp-of-clear-row-other
  (implies (and (natp s) (not (equal (nfix i) s)))
           (equal (fn2-ops-row-okp i (fn2-ops-clear-row s g nx fn2-ops)) (fn2-ops-row-okp i fn2-ops)))
  :hints (("Goal" :use ((:instance fn2-ops-row-okp-by-key (slot i))
                        (:instance fn2-ops-row-okp-by-key (slot i) (fn2-ops (fn2-ops-clear-row s g nx fn2-ops)))))))
(fn2-ops-clear-row-lemma fn2-ops-rows-ok-except-of-clear-row fn2-ops-rows-ok-except (n s fn2-ops)
  (fn2-ops-rows-ok-except n s fn2-ops))
(fn2-ops-clear-row-lemma fn2-ops-phase-slots-of-clear-row fn2-ops-phase-slots (n ph fn2-ops)
  (fn2-ops-phase-slots n ph (update-nth-array 1 s 0 fn2-ops)))
(fn2-ops-clear-row-lemma fn2-ops-free-chain-of-clear-row fn2-ops-free-chain (f x fn2-ops)
  (fn2-ops-free-chain f x (update-nth-array 41 s nx fn2-ops))
  :induct (fn2-ops-free-chain f x (update-nth-array 41 s nx fn2-ops)))
(fn2-ops-clear-row-lemma fn2-ops-pending-of-clear-row fn2-ops-pending-cells (n fn2-ops)
  (fn2-ops-pending-cells n fn2-ops)
  :hyps ((not (and (equal (nth s (nth 19 fn2-ops)) 1) (equal (nth s (nth 20 fn2-ops)) 0)))
         (not (and (equal (nth s (nth 33 fn2-ops)) 1) (equal (nth s (nth 34 fn2-ops)) 0)))))
(fn2-ops-clear-row-lemma fn2-ops-queued-refsp-of-clear-row fn2-ops-queued-refsp (refs fn2-ops)
  (fn2-ops-queued-refsp refs fn2-ops)
  :hyps ((not (member-equal s (fn2-ops-ref-slots refs)))))
(fn2-ops-clear-row-lemma fn2-ops-outbox-list-aux-of-clear-row fn2-ops-outbox-list-aux (left idx fn2-ops)
  (fn2-ops-outbox-list-aux left idx fn2-ops))
(fn2-ops-clear-row-lemma fn2-ops-posted-list-aux-of-clear-row fn2-ops-posted-list-aux (left idx fn2-ops)
  (fn2-ops-posted-list-aux left idx fn2-ops))

;; The invariant with its row clause split at one row S.
(defun-nx fn2-ops-sem-facts (s fn2-ops)
  (let* ((rows (fn2-ops-rows fn2-ops))
         (qa (fn2-ops-out-slot-length fn2-ops))
         (free (fn2-ops-phase-slots rows *fn2-op-phase-free* fn2-ops))
         (reserved (fn2-ops-phase-slots rows *fn2-op-phase-reserved* fn2-ops))
         (queued (fn2-ops-phase-slots rows *fn2-op-phase-queued* fn2-ops))
         (retired (fn2-ops-phase-slots rows *fn2-op-phase-retired* fn2-ops))
         (chain (fn2-ops-free-chain rows (fn2-ops-free-head fn2-ops) fn2-ops))
         (out (fn2-ops-outbox-list fn2-ops))
         (posted (fn2-ops-posted-list fn2-ops)))
    (and (fn2-ops-rows-ok-except rows s fn2-ops)
         (implies (and (natp s) (< s rows)) (fn2-ops-row-okp s fn2-ops))
         (unsigned-byte-p 32 qa)
         (equal (fn2-ops-out-gen-length fn2-ops) qa)
         (equal (fn2-ops-posted-fifo-length fn2-ops) (* 2 rows))
         (fn2-ops-ring-shapep qa (fn2-ops-out-head fn2-ops)
                             (fn2-ops-out-tail fn2-ops) (fn2-ops-queued fn2-ops))
         (fn2-ops-ring-shapep (* 2 rows) (fn2-ops-post-head fn2-ops)
                             (fn2-ops-post-tail fn2-ops) (fn2-ops-post-count fn2-ops))
         (not (member-equal :bad-chain chain))
         (fn2-ops-same-membersp chain free)
         (equal (fn2-ops-free-count fn2-ops) (len free))
         (equal (fn2-ops-retired-count fn2-ops) (len retired))
         (equal (fn2-ops-reserved-credits fn2-ops) (len reserved))
         (equal (fn2-ops-queued fn2-ops) (len queued))
         (<= (+ (len reserved) (len queued)) qa)
         (fn2-ops-queued-refsp out fn2-ops)
         (fn2-ops-same-membersp (fn2-ops-ref-slots out) queued)
         (fn2-ops-same-membersp posted (fn2-ops-pending-cells rows fn2-ops)))))
(defthm fn2-ops-semanticp-intro
  (implies (and (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops) (fn2-ops-sem-facts s fn2-ops))
           (fn2-ops-semanticp fn2-ops))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn2-ops-phase-partition)
           :use ((:instance fn2-ops-row-semanticp-of-rows-ok-except (n (fn2-ops-rows fn2-ops)))
                 (:instance fn2-ops-phase-partition (n (fn2-ops-rows fn2-ops)))))))
(defthm fn2-ops-sem-facts-of-semanticp
  (implies (fn2-ops-semanticp fn2-ops) (fn2-ops-sem-facts s fn2-ops)))
(defthm fn2-ops-semanticp-elim
  (implies (fn2-ops-semanticp fn2-ops)
           (and (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops)
                (fn2-ops-row-semanticp (fn2-ops-rows fn2-ops) fn2-ops)))
  :rule-classes :forward-chaining)
(in-theory (disable fn2-ops-semanticp fn2-ops-sem-facts))
