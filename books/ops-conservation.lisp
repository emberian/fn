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
(encapsulate ()
(local
(defconst *fn2-ops-c-gen* 0))
(local
(defconst *fn2-ops-c-phase* 1))
(local
(defconst *fn2-ops-c-c0-posted* 19))
(local
(defconst *fn2-ops-c-c0-harvested* 20))
(local
(defconst *fn2-ops-c-c1-posted* 33))
(local
(defconst *fn2-ops-c-c1-harvested* 34))
(local
(defconst *fn2-ops-c-next-free* 41))
(local
(defconst *fn2-ops-x-rows* 44))
(local
(defconst *fn2-ops-x-out-slot* 45))
(local
(defconst *fn2-ops-x-out-gen* 46))
(local
(defconst *fn2-ops-x-posted-fifo* 47))
(local
(defconst *fn2-ops-x-gen-limit* 72))
(local
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
      (equal (body 'fn2-ops-gen-limit nil (w state)) '(nth '72 fn2-ops)))))

;; The closed write forms.
(local
(defthm fn2-ops-nth-of-update-nth-array
  (equal (nth j (update-nth-array k i v l))
         (if (equal (nfix j) (nfix k)) (update-nth i v (nth k l)) (nth j l)))))
(local
(defthm fn2-ops-car-of-update-nth-array
  (equal (car (update-nth-array k i v l))
         (if (zp k) (update-nth i v (car l)) (car l)))
  :hints (("Goal" :in-theory (enable update-nth-array)))))
(local
(defthm fn2-ops-car-of-update-nth
  (equal (car (update-nth k v l)) (if (zp k) v (car l)))))
(local
(defthm fn2-ops-len-of-update-nth-array
  (equal (len (update-nth-array k i v l))
         (if (< (nfix k) (len l)) (len l) (+ 1 (nfix k))))))

(local
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
         update-fn2-ops-wake-observation-gen$ai
         update-fn2-ops-out-head update-fn2-ops-out-tail update-fn2-ops-queued update-fn2-ops-reserved-credits update-fn2-ops-post-head update-fn2-ops-post-tail update-fn2-ops-post-count update-fn2-ops-clock-posted update-fn2-ops-clock-seen update-fn2-ops-clock-mono update-fn2-ops-clock-real update-fn2-ops-clock-flags update-fn2-ops-clock-coalesced update-fn2-ops-clock-rejected update-fn2-ops-signals update-fn2-ops-stray update-fn2-ops-seen-peer-family update-fn2-ops-seen-peer-port update-fn2-ops-seen-peer-w0 update-fn2-ops-seen-peer-w1 update-fn2-ops-seen-peer-w2 update-fn2-ops-seen-peer-w3 update-fn2-ops-free-head update-fn2-ops-free-count update-fn2-ops-gen-limit update-fn2-ops-retired-count update-fn2-ops-out-sloti update-fn2-ops-out-geni update-fn2-ops-posted-fifoi ,@more)
        (update-nth-array update-nth))))
(local
(in-theory (fn2-ops-frame-theory)))

(local
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
                       (<= count rlen)))))))
(local
(defthm fn2-post-payloadp-by-key
  (equal (fn2-post-payloadp cell slot evkind outcome reason count aux0 aux1 fn2-ops)
         (fn2-ops-payload-key-okp cell evkind outcome reason count aux0 aux1
                                  (fn2-ops-kind slot fn2-ops) (fn2-ops-may-release slot fn2-ops)
                                  (fn2-ops-range-len slot fn2-ops)))
  :hints (("Goal" :expand ((fn2-post-payloadp cell slot evkind outcome reason count aux0 aux1 fn2-ops)
                           (fn2-ops-payload-key-okp cell evkind outcome reason count aux0 aux1
                                  (fn2-ops-kind slot fn2-ops) (fn2-ops-may-release slot fn2-ops)
                                  (fn2-ops-range-len slot fn2-ops)))
           :in-theory (theory 'minimal-theory)))))
(local
(defthm fn2-ops-payload-key-okp-fields
  (implies (fn2-ops-payload-key-okp cell evkind outcome reason count aux0 aux1 kind may rlen)
           (and (or (equal cell 0) (equal cell 1))
                (natp evkind) (< evkind *fn2-event-count*) (natp outcome) (< outcome *fn2-outcome-count*)
                (natp reason) (< reason *fn2-reason-count*)
                (unsigned-byte-p 32 count) (unsigned-byte-p 32 aux0) (unsigned-byte-p 32 aux1)))
  :rule-classes :forward-chaining))
(local
(in-theory (disable fn2-ops-payload-key-okp)))

(local
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
                  (and (equal gen limit) (equal p0 h0) (equal p1 h1)))))))
(local
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
                       (equal p0 h0) (equal p1 h1)))))))
(local
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
           :in-theory (union-theories '(fn2-post-payloadp-by-key) (theory 'minimal-theory))))))
(local
(in-theory (disable fn2-ops-row-key-okp)))

(local
(defun fn2-ops-rows-ok-except (n s fn2-ops)
  (declare (xargs :stobjs fn2-ops :verify-guards nil :measure (nfix n)))
  (if (zp n) t
    (and (or (equal (- n 1) s) (fn2-ops-row-okp (- n 1) fn2-ops))
         (fn2-ops-rows-ok-except (- n 1) s fn2-ops)))))

(local
(defthm fn2-ops-row-semanticp-step
  (equal (fn2-ops-row-semanticp n fn2-ops)
         (if (zp n) t
           (and (fn2-ops-row-okp (- n 1) fn2-ops)
                (fn2-ops-row-semanticp (- n 1) fn2-ops))))
  :rule-classes ((:definition :controller-alist ((fn2-ops-row-semanticp t nil))))
  :hints (("Goal" :expand ((fn2-ops-row-semanticp n fn2-ops))
           :in-theory (union-theories '(fn2-ops-row-okp (:type-prescription fn2-ops-row-semanticp)
                                        (:executable-counterpart member-equal) (:executable-counterpart equal))
                                      (theory 'minimal-theory))))))
(local
(in-theory (disable fn2-ops-row-semanticp-step)))
(local
(defthm fn2-ops-nth-row-of-update-nth-array-other-row
  (implies (and (natp i) (natp ii) (natp j) (natp kk) (not (equal i ii)))
           (equal (nth i (nth j (update-nth-array kk ii vv l))) (nth i (nth j l))))))
(local
(defthm fn2-ops-nth-of-update-nth-array-other
  (implies (not (equal (nfix j) (nfix kk)))
           (equal (nth j (update-nth-array kk ii vv l)) (nth j l)))))
(local
(defthm fn2-ops-row-okp-of-update-nth-array-other-row
  (implies (and (natp kk) (natp slot) (natp ii) (not (equal kk 72)) (not (equal slot ii)))
           (equal (fn2-ops-row-okp slot (update-nth-array kk ii vv fn2-ops))
                  (fn2-ops-row-okp slot fn2-ops)))
  :hints (("Goal" :use ((:instance fn2-ops-row-okp-by-key)
                        (:instance fn2-ops-row-okp-by-key (fn2-ops (update-nth-array kk ii vv fn2-ops))))
           :in-theory (e/d (fn2-ops-nth-row-of-update-nth-array-other-row fn2-ops-nth-of-update-nth-array-other)
                           (fn2-ops-row-okp fn2-ops-nth-of-update-nth-array))))))
(local
(defthm fn2-ops-row-okp-of-update-nth
  (implies (and (natp kk) (not (member kk '(0 1 2 10 15 19 20 21 22 23 24 25 26 33 34 35 36 37 38 39 40 72))))
           (equal (fn2-ops-row-okp slot (update-nth kk vv fn2-ops))
                  (fn2-ops-row-okp slot fn2-ops)))
  :hints (("Goal" :use ((:instance fn2-ops-row-okp-by-key)
                        (:instance fn2-ops-row-okp-by-key (fn2-ops (update-nth kk vv fn2-ops))))
           :in-theory (disable fn2-ops-row-okp)))))
(local
(defthm fn2-ops-row-okp-of-update-nth-array
  (implies (and (natp kk) (not (member kk '(0 1 2 10 15 19 20 21 22 23 24 25 26 33 34 35 36 37 38 39 40 72))))
           (equal (fn2-ops-row-okp slot (update-nth-array kk ii vv fn2-ops))
                  (fn2-ops-row-okp slot fn2-ops)))
  :hints (("Goal" :use ((:instance fn2-ops-row-okp-by-key)
                        (:instance fn2-ops-row-okp-by-key (fn2-ops (update-nth-array kk ii vv fn2-ops))))
           :in-theory (disable fn2-ops-row-okp)))))
(local
(in-theory (disable fn2-ops-nth-row-of-update-nth-array-other-row fn2-ops-nth-of-update-nth-array-other)))
(local
(in-theory (disable fn2-ops-row-okp)))


;; Frame rules: a closed reader is unchanged by a write to a field it does
;; not read. One pair per reader, every field quantified.
(defun fn2-ops-frame-sym (d suffix)
  (declare (xargs :guard (and (symbolp d) (stringp suffix))))
  (intern-in-package-of-symbol (concatenate 'string (symbol-name d) suffix) 'fn2-ops))
(local
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
                 :in-theory (fn2-ops-frame-theory ,d ,@enables))))))))
(local
(defmacro fn2-ops-frames (d formals keys &key induct enables)
  (cons 'progn (fn2-ops-frame-events d formals keys induct enables))))

(local
(fn2-ops-frames fn2-ops-rows-ok-except (n s fn2-ops) (0 1 2 10 15 19 20 21 22 23 24 25 26 33 34 35 36 37 38 39 40 72) :induct t))
(local
(fn2-ops-frames fn2-ops-phase-slots (n phase fn2-ops) (1) :induct t))
(local
(fn2-ops-frames fn2-ops-free-chain (fuel slot fn2-ops) (41 44) :induct t :enables (fn2-op-slotp)))
(local
(fn2-ops-frames fn2-ops-pending-cells (n fn2-ops) (19 20 33 34) :induct t))
(local
(fn2-ops-frames fn2-ops-queued-refsp (refs fn2-ops) (0 1 44) :induct t :enables (fn2-op-slotp)))
(local
(fn2-ops-frames fn2-ops-outbox-list-aux (left idx fn2-ops) (45 46) :induct t))
(local
(fn2-ops-frames fn2-ops-posted-list-aux (left idx fn2-ops) (47) :induct t))

;; A write at row S leaves every other row's clause alone.
(local
(defthm fn2-ops-rows-ok-except-of-update-nth-array-at
  (implies (and (natp s) (natp kk) (not (equal kk 72)))
           (equal (fn2-ops-rows-ok-except n s (update-nth-array kk s vv fn2-ops))
                  (fn2-ops-rows-ok-except n s fn2-ops)))
  :hints (("Goal" :induct (fn2-ops-rows-ok-except n s fn2-ops)
           :in-theory (fn2-ops-frame-theory fn2-ops-rows-ok-except)))))
(local
(in-theory (disable fn2-ops-rows-ok-except)))

(local
(defthm fn2-ops-rows-ok-except-of-row-semanticp
  (implies (fn2-ops-row-semanticp n fn2-ops) (fn2-ops-rows-ok-except n s fn2-ops))
  :hints (("Goal" :induct (fn2-ops-rows-ok-except n s fn2-ops)
           :in-theory (enable fn2-ops-rows-ok-except fn2-ops-row-semanticp-step)))))
(local
(defthm fn2-ops-row-semanticp-of-rows-ok-except
  (implies (and (fn2-ops-rows-ok-except n s fn2-ops)
                (implies (and (natp s) (< s (nfix n))) (fn2-ops-row-okp s fn2-ops)))
           (fn2-ops-row-semanticp n fn2-ops))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-ops-rows-ok-except n s fn2-ops)
           :in-theory (enable fn2-ops-rows-ok-except fn2-ops-row-semanticp-step)))))
(local
(defthm fn2-ops-row-okp-of-row-semanticp
  (implies (and (fn2-ops-row-semanticp n fn2-ops) (natp i) (< i (nfix n)))
           (fn2-ops-row-okp i fn2-ops))
  :hints (("Goal" :induct (fn2-ops-rows-ok-except n i fn2-ops)
           :in-theory (enable fn2-ops-rows-ok-except fn2-ops-row-semanticp-step)))))

;; Lists.
(local
(defthm fn2-ops-member-remove
  (iff (member-equal x (remove-equal a l)) (and (member-equal x l) (not (equal x a))))))
(local
(defthm fn2-ops-member-append
  (iff (member-equal x (append a b)) (or (member-equal x a) (member-equal x b)))))
(local
(defthm fn2-ops-subsetp-trans
  (implies (and (subsetp-equal x y) (subsetp-equal y z)) (subsetp-equal x z))))
(local
(defthm fn2-ops-subsetp-cons-right
  (implies (subsetp-equal x y) (subsetp-equal x (cons a y)))))
(local
(defthm fn2-ops-subsetp-refl (subsetp-equal x x)))
(local
(defthm fn2-ops-subsetp-remove
  (implies (and (subsetp-equal x y) (not (member-equal a x)))
           (subsetp-equal x (remove-equal a y)))))
(local
(defthm fn2-ops-remove-subsetp
  (implies (subsetp-equal y (cons a x)) (subsetp-equal (remove-equal a y) x))))
(local
(defthm fn2-ops-not-member-of-subsetp
  (implies (and (subsetp-equal x y) (not (member-equal a y))) (not (member-equal a x)))))
(local
(defthm fn2-ops-member-of-subsetp
  (implies (and (subsetp-equal x y) (member-equal a x)) (member-equal a y))))
(local
(defthm fn2-ops-remove-equal-non-member
  (implies (and (true-listp l) (not (member-equal a l))) (equal (remove-equal a l) l))))
(local
(defthm fn2-ops-no-dups-remove
  (implies (no-duplicatesp-equal l) (no-duplicatesp-equal (remove-equal a l)))))
(local
(defthm fn2-ops-subsetp-append
  (equal (subsetp-equal (append a b) c) (and (subsetp-equal a c) (subsetp-equal b c)))))
(local
(defthm fn2-ops-no-dups-append-singleton
  (equal (no-duplicatesp-equal (append a (list s)))
         (and (no-duplicatesp-equal a) (not (member-equal s a))))))

(local
(defthm fn2-ops-len-remove-member
  (implies (and (member-equal a l) (no-duplicatesp-equal l))
           (equal (len (remove-equal a l)) (- (len l) 1)))))
(local
(defthm fn2-ops-car-not-member-cdr
  (implies (no-duplicatesp-equal l) (not (member-equal (car l) (cdr l))))))
(local
(defthm fn2-ops-no-dups-cdr
  (implies (no-duplicatesp-equal l) (no-duplicatesp-equal (cdr l)))))
(local
(defthm fn2-ops-not-member-cdr
  (implies (not (member-equal a l)) (not (member-equal a (cdr l))))))
(local
(defthm fn2-ops-len-cdr
  (implies (consp l) (equal (len (cdr l)) (- (len l) 1)))))
(local
(defthm fn2-ops-same-members-no-dups
  (implies (fn2-ops-same-membersp a b)
           (and (no-duplicatesp-equal a) (no-duplicatesp-equal b)
                (subsetp-equal a b) (subsetp-equal b a)))
  :rule-classes :forward-chaining))
(local
(defthm fn2-ops-subsetp-cons-cons
  (implies (subsetp-equal x y) (subsetp-equal (cons a x) (cons a y)))))
(local
(defthm fn2-ops-subsetp-cdr
  (subsetp-equal (cdr x) x)))
(local
(defthm fn2-ops-subsetp-cons-append
  (subsetp-equal (cons s c) (append c (list s)))))
(local
(defthm fn2-ops-subsetp-cons-car-cdr
  (implies (consp c) (subsetp-equal c (cons (car c) (cdr c))))))
(local
(defthm fn2-ops-same-members-pop
  (implies (and (consp c) (fn2-ops-same-membersp c f) (equal a (car c)))
           (fn2-ops-same-membersp (cdr c) (remove-equal a f)))
  :hints (("Goal" :do-not-induct t :in-theory (enable fn2-ops-same-membersp)
           :use ((:instance fn2-ops-subsetp-trans (x (cdr c)) (y c) (z f))
                 (:instance fn2-ops-subsetp-remove (x (cdr c)) (y f))
                 (:instance fn2-ops-subsetp-trans (x f) (y c) (z (cons (car c) (cdr c))))
                 (:instance fn2-ops-remove-subsetp (y f) (x (cdr c))))))))
(local
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
                 (:instance fn2-ops-subsetp-trans (x f2) (y (cons s c)) (z (append c (list s)))))))))
(local
(in-theory (disable fn2-ops-same-membersp)))

;; Phase classes.
(local
(defthm fn2-ops-member-phase-slots
  (iff (member-equal x (fn2-ops-phase-slots n ph fn2-ops))
       (and (natp x) (< x (nfix n)) (equal (nth x (nth 1 fn2-ops)) ph)))))
(local
(defthm fn2-ops-no-dups-phase-slots
  (no-duplicatesp-equal (fn2-ops-phase-slots n ph fn2-ops))))
(local
(defthm fn2-ops-true-listp-phase-slots
  (true-listp (fn2-ops-phase-slots n ph fn2-ops))
  :rule-classes :type-prescription))
(local
(defthm fn2-ops-phase-slots-of-set-phase-same-value
  (implies (equal vv (nth s (nth 1 fn2-ops)))
           (equal (fn2-ops-phase-slots n ph (update-nth-array 1 s vv fn2-ops))
                  (fn2-ops-phase-slots n ph fn2-ops)))))
(local
(defthm fn2-ops-phase-slots-of-set-phase-other
  (implies (and (natp s) (not (equal vv ph)))
           (equal (fn2-ops-phase-slots n ph (update-nth-array 1 s vv fn2-ops))
                  (remove-equal s (fn2-ops-phase-slots n ph fn2-ops))))))
(local
(defthm fn2-ops-phase-slots-of-set-phase-into
  (implies (natp s)
           (subsetp-equal (fn2-ops-phase-slots n ph (update-nth-array 1 s vv fn2-ops))
                          (cons s (fn2-ops-phase-slots n ph fn2-ops))))))
(local
(defthm fn2-ops-subsetp-phase-slots-of-set-phase-same
  (implies (and (equal vv ph) (subsetp-equal x (fn2-ops-phase-slots n ph fn2-ops)))
           (subsetp-equal x (fn2-ops-phase-slots n ph (update-nth-array 1 s vv fn2-ops))))
  :hints (("Goal" :induct (len x)))))
(local
(defthm fn2-ops-len-phase-slots-of-set-phase
  (implies (natp s)
           (equal (len (fn2-ops-phase-slots n ph (update-nth-array 1 s vv fn2-ops)))
                  (if (< s (nfix n))
                      (+ (len (fn2-ops-phase-slots n ph fn2-ops))
                         (if (equal vv ph) 1 0)
                         (- (if (equal (nth s (nth 1 fn2-ops)) ph) 1 0)))
                    (len (fn2-ops-phase-slots n ph fn2-ops)))))))
;; A phase write reads through writes to other fields beneath it.
(local
(defthm fn2-ops-phase-slots-of-set-phase-over-scalar
  (implies (and (natp kk) (not (equal kk 1)))
           (equal (fn2-ops-phase-slots n ph (update-nth-array 1 s vv (update-nth kk w fn2-ops)))
                  (fn2-ops-phase-slots n ph (update-nth-array 1 s vv fn2-ops))))))
(local
(defthm fn2-ops-phase-slots-of-set-phase-over-column
  (implies (and (natp kk) (not (equal kk 1)))
           (equal (fn2-ops-phase-slots n ph (update-nth-array 1 s vv (update-nth-array kk ii w fn2-ops)))
                  (fn2-ops-phase-slots n ph (update-nth-array 1 s vv fn2-ops))))))
(local
(in-theory (disable fn2-ops-phase-slots)))

(local
(defthm fn2-ops-row-okp-phase-bound
  (implies (fn2-ops-row-okp i fn2-ops) (< (nth i (nth 1 fn2-ops)) 7))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable fn2-ops-row-okp fn2-ops-row-key-okp)))))
(local
(defthm fn2-ops-row-okp-idle-cells
  (implies (and (member-equal (nth i (nth 1 fn2-ops)) '(0 1 2)) (fn2-ops-row-okp i fn2-ops))
           (and (equal (nth i (nth 19 fn2-ops)) 0) (equal (nth i (nth 20 fn2-ops)) 0)
                (equal (nth i (nth 33 fn2-ops)) 0) (equal (nth i (nth 34 fn2-ops)) 0)))
  :hints (("Goal" :in-theory (enable fn2-ops-row-okp fn2-ops-row-key-okp)))))
(local
(defthm fn2-ops-row-okp-gen-bound
  (implies (fn2-ops-row-okp i fn2-ops) (<= (nth i (nth 0 fn2-ops)) (nth 72 fn2-ops)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable fn2-ops-row-okp fn2-ops-row-key-okp)))))
(local
(defthm fn2-ops-small-nat-cases
  (implies (and (natp x) (< x 7))
           (or (equal x 0) (equal x 1) (equal x 2) (equal x 3) (equal x 4) (equal x 5) (equal x 6)))
  :rule-classes nil
  :hints (("Goal" :cases ((< x 1) (< x 2) (< x 3) (< x 4) (< x 5) (< x 6))))))
(local
(defthm fn2-ops-row-okp-cell-order
  (implies (fn2-ops-row-okp i fn2-ops)
           (and (<= (nth i (nth 20 fn2-ops)) (nth i (nth 19 fn2-ops)))
                (<= (nth i (nth 34 fn2-ops)) (nth i (nth 33 fn2-ops)))
                (<= (nth i (nth 33 fn2-ops)) (nth i (nth 15 fn2-ops)))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn2-ops-row-okp fn2-ops-row-key-okp)))))
(local
(defthm fn2-ops-row-okp-unposted
  (implies (and (fn2-ops-row-okp i fn2-ops)
                (natp (nth i (nth 20 fn2-ops))) (natp (nth i (nth 34 fn2-ops))))
           (and (implies (equal (nth i (nth 19 fn2-ops)) 0) (equal (nth i (nth 20 fn2-ops)) 0))
                (implies (equal (nth i (nth 33 fn2-ops)) 0) (equal (nth i (nth 34 fn2-ops)) 0))))
  :rule-classes nil
  :hints (("Goal" :use fn2-ops-row-okp-cell-order :in-theory (disable fn2-ops-row-okp-cell-order)))))
(local
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
                                (:instance fn2-ops-small-nat-cases (x (nth (- n 1) (nth 1 fn2-ops))))
                                (:instance fn2-ops-row-okp-of-row-semanticp (i (- n 1))))))))

;; The free chain.
(local
(defthm fn2-ops-free-chain-of-set-next-free
  (implies (and (natp s) (not (member-equal s (fn2-ops-free-chain f x fn2-ops))))
           (equal (fn2-ops-free-chain f x (update-nth-array 41 s vv fn2-ops))
                  (fn2-ops-free-chain f x fn2-ops)))
  :hints (("Goal" :in-theory (fn2-ops-frame-theory fn2-ops-free-chain fn2-op-slotp)))))
(local
(defthm fn2-ops-free-chain-consp
  (implies (not (equal x *fn2-none*)) (consp (fn2-ops-free-chain f x fn2-ops)))))
(local
(defun fn2-ops-chain-fuel-ind (f g x fn2-ops)
  (declare (xargs :stobjs fn2-ops :verify-guards nil :measure (nfix f)))
  (cond ((equal x *fn2-none*) nil)
        ((or (zp f) (zp g) (not (fn2-op-slotp x fn2-ops))) nil)
        (t (fn2-ops-chain-fuel-ind (- f 1) (- g 1) (fn2-ops-next-free x fn2-ops) fn2-ops)))))
(local
(defthm fn2-ops-free-chain-fuel
  (implies (and (not (member-equal :bad-chain (fn2-ops-free-chain f x fn2-ops)))
                (natp g) (<= (len (fn2-ops-free-chain f x fn2-ops)) g))
           (equal (fn2-ops-free-chain g x fn2-ops) (fn2-ops-free-chain f x fn2-ops)))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-ops-chain-fuel-ind f g x fn2-ops)
           :expand ((fn2-ops-free-chain f x fn2-ops) (fn2-ops-free-chain g x fn2-ops))))))
(local
(defthm fn2-ops-free-chain-len-bound
  (implies (and (natp f) (not (member-equal :bad-chain (fn2-ops-free-chain f x fn2-ops))))
           (<= (len (fn2-ops-free-chain f x fn2-ops)) f))
  :rule-classes :linear))
(local
(defthm fn2-ops-free-chain-car
  (implies (and (not (equal x *fn2-none*))
                (not (member-equal :bad-chain (fn2-ops-free-chain f x fn2-ops))))
           (equal (car (fn2-ops-free-chain f x fn2-ops)) x))))
(local
(defthm fn2-ops-free-chain-slotp
  (implies (and (not (equal x *fn2-none*))
                (not (member-equal :bad-chain (fn2-ops-free-chain f x fn2-ops))))
           (and (natp x) (< x (nth 44 fn2-ops))))
  :rule-classes nil))
(local
(defthm fn2-ops-free-chain-tail
  (implies (and (natp n) (not (equal s *fn2-none*))
                (not (member-equal :bad-chain (fn2-ops-free-chain n s fn2-ops))))
           (equal (fn2-ops-free-chain n (nth s (nth 41 fn2-ops)) fn2-ops)
                  (cdr (fn2-ops-free-chain n s fn2-ops))))
  :hints (("Goal" :expand ((fn2-ops-free-chain n s fn2-ops))
           :use ((:instance fn2-ops-free-chain-len-bound (f (- n 1)) (x (nth s (nth 41 fn2-ops))))
                 (:instance fn2-ops-free-chain-fuel (f (- n 1)) (g n) (x (nth s (nth 41 fn2-ops)))))))))
(local
(defthm fn2-ops-free-chain-push
  (implies (and (natp s) (< s (nth 44 fn2-ops)) (not (zp n)) (not (equal s *fn2-none*))
                (not (member-equal :bad-chain (fn2-ops-free-chain n h fn2-ops)))
                (< (len (fn2-ops-free-chain n h fn2-ops)) n)
                (not (member-equal s (fn2-ops-free-chain n h fn2-ops))))
           (equal (fn2-ops-free-chain n s (update-nth-array 41 s h fn2-ops))
                  (cons s (fn2-ops-free-chain n h fn2-ops))))
  :hints (("Goal" :expand ((fn2-ops-free-chain n s (update-nth-array 41 s h fn2-ops)))
           :use ((:instance fn2-ops-free-chain-fuel (f n) (g (- n 1)) (x h)))))))
(local
(in-theory (disable fn2-ops-free-chain)))

;; Ring positions. The traversals step by (mod (+ 1 idx) cap); a ring write
;; lands at (mod (+ head count) cap), which the first COUNT positions miss.
(local
(defun fn2-ops-ring-pos (left idx cap)
  (declare (xargs :measure (nfix left) :verify-guards nil))
  (if (zp left) nil
    (cons idx (fn2-ops-ring-pos (- left 1) (mod (+ 1 (nfix idx)) cap) cap)))))
(local
(defun fn2-ops-ring-ind (left idx k cap)
  (declare (xargs :measure (nfix left) :verify-guards nil))
  (if (zp left) (list idx k cap)
    (fn2-ops-ring-ind (- left 1) (mod (+ 1 (nfix idx)) cap) (- k 1) cap))))
(local
(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm fn2-ops-ring-next-is-mod
    (implies (and (natp i) (integerp cap) (< i cap)) (equal (fn2-ring-next i cap) (mod (+ 1 i) cap)))
    :hints (("Goal" :cases ((equal (+ 1 i) cap)) :in-theory (enable fn2-ring-next))))
  (defthm fn2-ops-mod-mod-plus
    (implies (and (natp a) (natp b) (posp c)) (equal (mod (+ b (mod a c)) c) (mod (+ a b) c))))
  (defthm fn2-ops-mod-step
    (implies (and (natp idx) (integerp left) (< 0 left) (posp c))
             (equal (mod (+ -1 left (mod (+ 1 idx) c)) c) (mod (+ idx left) c))))
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
  (defthm fn2-ops-even-not-odd-minus
    (implies (and (integerp a) (integerp b)) (not (equal (* 2 a) (+ -1 (* 2 b))))))
  (defthm fn2-ops-odd-not-even-minus
    (implies (and (integerp a) (integerp b)) (not (equal (+ 1 (* 2 a)) (+ -2 (* 2 b)))))
    :hints (("Goal" :use ((:instance fn2-ops-even-not-odd (a (- b 1)) (b a))))))
  (defthm fn2-ops-even-minus-two
    (implies (and (acl2-numberp a) (acl2-numberp b))
             (equal (equal (* 2 a) (+ -2 (* 2 b))) (equal a (+ -1 b)))))
  (defthm fn2-ops-odd-minus-one
    (implies (and (acl2-numberp a) (acl2-numberp b))
             (equal (equal (+ 1 (* 2 a)) (+ -1 (* 2 b))) (equal a (+ -1 b)))))
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
             (fn2-ops-ring-shapep cap (fn2-ring-next h cap) tl (- c 1))))))
(local
(in-theory (disable fn2-ring-next fn2-ops-ring-shapep mod floor)))

;; Posted and unharvested cells.
(local
(defthm fn2-ops-pending-cells-bound
  (implies (member-equal x (fn2-ops-pending-cells n fn2-ops))
           (and (natp x) (< x (* 2 (nfix n)))))
  :rule-classes :forward-chaining))
(local
(defthm fn2-ops-pending-cells-above
  (implies (and (natp n) (<= (* 2 n) x))
           (not (member-equal x (fn2-ops-pending-cells n fn2-ops))))
  :hints (("Goal" :use fn2-ops-pending-cells-bound :in-theory (disable fn2-ops-pending-cells-bound)))))
(local
(defthm fn2-ops-member-pending-even
  (implies (and (natp s) (natp n))
           (iff (member-equal (* 2 s) (fn2-ops-pending-cells n fn2-ops))
                (and (< s n) (equal (nth s (nth 19 fn2-ops)) 1) (equal (nth s (nth 20 fn2-ops)) 0))))
  :hints (("Goal" :induct (fn2-ops-pending-cells n fn2-ops))
          ("Subgoal *1/2" :use ((:instance fn2-ops-even-not-odd (a s) (b (- n 1)))
                                (:instance fn2-ops-even-cancel (a s) (b (- n 1))))))))
(local
(defthm fn2-ops-member-pending-odd
  (implies (and (natp s) (natp n))
           (iff (member-equal (+ 1 (* 2 s)) (fn2-ops-pending-cells n fn2-ops))
                (and (< s n) (equal (nth s (nth 33 fn2-ops)) 1) (equal (nth s (nth 34 fn2-ops)) 0))))
  :hints (("Goal" :induct (fn2-ops-pending-cells n fn2-ops))
          ("Subgoal *1/2" :use ((:instance fn2-ops-even-not-odd (b s) (a (- n 1)))
                                (:instance fn2-ops-odd-cancel (a s) (b (- n 1))))))))
(local
(defthm fn2-ops-no-dups-pending
  (no-duplicatesp-equal (fn2-ops-pending-cells n fn2-ops))
  :hints (("Goal" :induct (fn2-ops-pending-cells n fn2-ops)))))
(local
(defthm fn2-ops-true-listp-pending
  (true-listp (fn2-ops-pending-cells n fn2-ops)) :rule-classes :type-prescription))
;; A write to one cell column at row S that keeps both of S's pending bits.
(local
(defmacro fn2-ops-pending-same-status (kk)
  `(defthm ,(fn2-ops-frame-sym 'fn2-ops-pending-of-same-status (concatenate 'string "-" (coerce (explode-nonnegative-integer kk 10 nil) 'string)))
     (implies (and (natp s)
                   (iff (and (equal (nth s (nth 19 (update-nth-array ,kk s vv fn2-ops))) 1)
                             (equal (nth s (nth 20 (update-nth-array ,kk s vv fn2-ops))) 0))
                        (and (equal (nth s (nth 19 fn2-ops)) 1) (equal (nth s (nth 20 fn2-ops)) 0)))
                   (iff (and (equal (nth s (nth 33 (update-nth-array ,kk s vv fn2-ops))) 1)
                             (equal (nth s (nth 34 (update-nth-array ,kk s vv fn2-ops))) 0))
                        (and (equal (nth s (nth 33 fn2-ops)) 1) (equal (nth s (nth 34 fn2-ops)) 0))))
              (equal (fn2-ops-pending-cells n (update-nth-array ,kk s vv fn2-ops))
                     (fn2-ops-pending-cells n fn2-ops)))
     :hints (("Goal" :induct (fn2-ops-pending-cells n fn2-ops)
              :in-theory (enable fn2-ops-pending-cells))))))
(local
(fn2-ops-pending-same-status 19))
(local
(fn2-ops-pending-same-status 20))
(local
(fn2-ops-pending-same-status 33))
(local
(fn2-ops-pending-same-status 34))
(local
(defthm fn2-ops-pending-of-harvest0
  (implies (natp s)
           (equal (fn2-ops-pending-cells n (update-nth-array 20 s 1 fn2-ops))
                  (remove-equal (* 2 s) (fn2-ops-pending-cells n fn2-ops))))
  :hints (("Goal" :induct (fn2-ops-pending-cells n fn2-ops) :in-theory (enable fn2-ops-pending-cells)))))
(local
(defthm fn2-ops-pending-of-harvest1
  (implies (natp s)
           (equal (fn2-ops-pending-cells n (update-nth-array 34 s 1 fn2-ops))
                  (remove-equal (+ 1 (* 2 s)) (fn2-ops-pending-cells n fn2-ops))))
  :hints (("Goal" :induct (fn2-ops-pending-cells n fn2-ops) :in-theory (enable fn2-ops-pending-cells)))))
(local
(defthm fn2-ops-pending-of-post0
  (implies (natp s)
           (and (subsetp-equal (fn2-ops-pending-cells n fn2-ops)
                               (fn2-ops-pending-cells n (update-nth-array 19 s 1 fn2-ops)))
                (subsetp-equal (fn2-ops-pending-cells n (update-nth-array 19 s 1 fn2-ops))
                               (cons (* 2 s) (fn2-ops-pending-cells n fn2-ops)))))))
(local
(defthm fn2-ops-pending-of-post1
  (implies (natp s)
           (and (subsetp-equal (fn2-ops-pending-cells n fn2-ops)
                               (fn2-ops-pending-cells n (update-nth-array 33 s 1 fn2-ops)))
                (subsetp-equal (fn2-ops-pending-cells n (update-nth-array 33 s 1 fn2-ops))
                               (cons (+ 1 (* 2 s)) (fn2-ops-pending-cells n fn2-ops)))))))
(local
(in-theory (disable fn2-ops-pending-cells)))

;; Queued references.
(local
(defthm fn2-ops-queued-refsp-other-rows
  (implies (and (natp s) (not (equal (nfix kk) 44))
                (not (member-equal s (fn2-ops-ref-slots refs))))
           (equal (fn2-ops-queued-refsp refs (update-nth-array kk s vv fn2-ops))
                  (fn2-ops-queued-refsp refs fn2-ops)))
  :hints (("Goal" :in-theory (fn2-ops-frame-theory fn2-ops-queued-refsp fn2-op-slotp)))))
(local
(defthm fn2-ops-queued-refsp-append
  (implies (true-listp refs)
           (equal (fn2-ops-queued-refsp (append refs (list r)) fn2-ops)
                  (and (fn2-ops-queued-refsp refs fn2-ops)
                       (fn2-ops-queued-refsp (list r) fn2-ops))))))
(local
(defthm fn2-ops-queued-refsp-true-listp
  (implies (fn2-ops-queued-refsp refs fn2-ops) (true-listp refs))
  :rule-classes :forward-chaining))
(local
(defthm fn2-ops-queued-refsp-cdr
  (implies (fn2-ops-queued-refsp refs fn2-ops) (fn2-ops-queued-refsp (cdr refs) fn2-ops))))
(local
(defthm fn2-ops-ref-slots-append
  (equal (fn2-ops-ref-slots (append a b)) (append (fn2-ops-ref-slots a) (fn2-ops-ref-slots b)))))
(local
(defthm fn2-ops-ref-slots-cdr
  (equal (fn2-ops-ref-slots (cdr a)) (cdr (fn2-ops-ref-slots a)))))
(local
(defthm fn2-ops-car-ref-slots
  (equal (car (fn2-ops-ref-slots a)) (car (car a)))))
(local
(defthm fn2-ops-consp-ref-slots
  (equal (consp (fn2-ops-ref-slots a)) (consp a))))


(local
(defmacro fn2-ops-ring-list-lemmas (aux cap-col cols entry)
  `(progn
     (defthm ,(fn2-ops-frame-sym aux "-OF-RING-WRITE")
       (implies (and (natp tt) (natp idx) (member kk ',cols) (< tt (len (nth ,cap-col fn2-ops)))
                     (not (member-equal tt (fn2-ops-ring-pos left idx (len (nth ,cap-col fn2-ops))))))
                (equal (,aux left idx (update-nth-array kk tt vv fn2-ops)) (,aux left idx fn2-ops)))
       :hints (("Goal" :induct (,aux left idx fn2-ops) :in-theory (enable ,aux))))
     (defthm ,(fn2-ops-frame-sym aux "-SNOC")
       (implies (and (natp left) (natp idx) (< idx (len (nth ,cap-col fn2-ops))))
                (equal (,aux (+ 1 left) idx fn2-ops)
                       (append (,aux left idx fn2-ops)
                               (list ,(let ((i `(mod (+ idx left) (len (nth ,cap-col fn2-ops))))) (sublis (list (cons 'i i)) entry))))))
       :hints (("Goal" :induct (,aux left idx fn2-ops) :in-theory (enable ,aux)
                :expand ((,aux (+ 1 left) idx fn2-ops) (,aux 1 idx fn2-ops)))))
     (defthm ,(fn2-ops-frame-sym aux "-POP")
       (implies (and (not (zp left)) (natp idx) (< idx (len (nth ,cap-col fn2-ops))))
                (and (equal (car (,aux left idx fn2-ops)) ,(sublis (list (cons 'i 'idx)) entry))
                     (equal (cdr (,aux left idx fn2-ops))
                            (,aux (- left 1) (mod (+ 1 idx) (len (nth ,cap-col fn2-ops))) fn2-ops))
                     (consp (,aux left idx fn2-ops))))
       :hints (("Goal" :expand ((,aux left idx fn2-ops)))))
     (defthm ,(fn2-ops-frame-sym aux "-TRUE-LISTP")
       (true-listp (,aux left idx fn2-ops)) :rule-classes :type-prescription)
     (in-theory (disable ,aux)))))
(local
(fn2-ops-ring-list-lemmas fn2-ops-outbox-list-aux 45 (45 46) (list (nth i (nth 45 fn2-ops)) (nth i (nth 46 fn2-ops)))))
(local
(fn2-ops-ring-list-lemmas fn2-ops-posted-list-aux 47 (47) (nth i (nth 47 fn2-ops))))

;; CLEAR-ROW writes every column of one row: its contract, once.
(local
(defun fn2-ops-clear-val (k g nx)
  (declare (xargs :guard t))
  (cond ((equal k 0) g) ((equal k 41) nx) (t 0))))
(local
(defthm fn2-ops-nth-of-clear-row
  (implies (natp k)
           (equal (nth k (fn2-ops-clear-row s g nx fn2-ops))
                  (if (< k 44) (update-nth s (fn2-ops-clear-val k g nx) (nth k fn2-ops)) (nth k fn2-ops))))
  :hints (("Goal" :in-theory (fn2-ops-frame-theory fn2-ops-clear-row)))))
(local
(defthm fn2-ops-car-of-clear-row
  (equal (car (fn2-ops-clear-row s g nx fn2-ops)) (update-nth s g (car fn2-ops)))
  :hints (("Goal" :use ((:instance fn2-ops-nth-of-clear-row (k 0))) :in-theory (disable fn2-ops-nth-of-clear-row)))))
(local
(defmacro fn2-ops-clear-row-lemma (name d formals rhs &key hyps induct)
  `(defthm ,name
     (implies (and (natp s) ,@hyps)
              (equal (,d ,@(butlast formals 1) (fn2-ops-clear-row s g nx fn2-ops)) ,rhs))
     :hints (("Goal" :induct ,(or induct `(,d ,@formals)) :in-theory (enable ,d))))))
(local
(defthm fn2-ops-row-okp-of-clear-row-other
  (implies (and (natp s) (not (equal (nfix i) s)))
           (equal (fn2-ops-row-okp i (fn2-ops-clear-row s g nx fn2-ops)) (fn2-ops-row-okp i fn2-ops)))
  :hints (("Goal" :use ((:instance fn2-ops-row-okp-by-key (slot i))
                        (:instance fn2-ops-row-okp-by-key (slot i) (fn2-ops (fn2-ops-clear-row s g nx fn2-ops))))))))
(local
(fn2-ops-clear-row-lemma fn2-ops-rows-ok-except-of-clear-row fn2-ops-rows-ok-except (n s fn2-ops)
  (fn2-ops-rows-ok-except n s fn2-ops)))
(local
(fn2-ops-clear-row-lemma fn2-ops-phase-slots-of-clear-row fn2-ops-phase-slots (n ph fn2-ops)
  (fn2-ops-phase-slots n ph (update-nth-array 1 s 0 fn2-ops))))
(local
(fn2-ops-clear-row-lemma fn2-ops-free-chain-of-clear-row fn2-ops-free-chain (f x fn2-ops)
  (fn2-ops-free-chain f x (update-nth-array 41 s nx fn2-ops))
  :induct (fn2-ops-free-chain f x (update-nth-array 41 s nx fn2-ops))))
(local
(fn2-ops-clear-row-lemma fn2-ops-pending-of-clear-row fn2-ops-pending-cells (n fn2-ops)
  (fn2-ops-pending-cells n fn2-ops)
  :hyps ((not (and (equal (nth s (nth 19 fn2-ops)) 1) (equal (nth s (nth 20 fn2-ops)) 0)))
         (not (and (equal (nth s (nth 33 fn2-ops)) 1) (equal (nth s (nth 34 fn2-ops)) 0))))))
(local
(fn2-ops-clear-row-lemma fn2-ops-queued-refsp-of-clear-row fn2-ops-queued-refsp (refs fn2-ops)
  (fn2-ops-queued-refsp refs fn2-ops)
  :hyps ((not (member-equal s (fn2-ops-ref-slots refs))))))
(local
(fn2-ops-clear-row-lemma fn2-ops-outbox-list-aux-of-clear-row fn2-ops-outbox-list-aux (left idx fn2-ops)
  (fn2-ops-outbox-list-aux left idx fn2-ops)))
(local
(fn2-ops-clear-row-lemma fn2-ops-posted-list-aux-of-clear-row fn2-ops-posted-list-aux (left idx fn2-ops)
  (fn2-ops-posted-list-aux left idx fn2-ops)))

;; The invariant with its row clause split at one row S.
(local
(defun-nx fn2-ops-sem-rest (s fn2-ops)
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
         (fn2-ops-same-membersp posted (fn2-ops-pending-cells rows fn2-ops))))))
(local
(defun-nx fn2-ops-sem-facts (s fn2-ops)
  (and (fn2-ops-sem-rest s fn2-ops)
       (implies (and (natp s) (< s (nfix (fn2-ops-rows fn2-ops)))) (fn2-ops-row-okp s fn2-ops)))))

;; The part of the invariant outside row S is unchanged by a write to a
;; column of row S that it does not read, or to a scalar it does not read.
;; The invariant outside row S splits into the posted-ring part and the rest;
;; the rest has frame rules for every write the posting and harvesting steps make.
(local
(defun-nx fn2-ops-sem-post (fn2-ops)
  (let ((rows (fn2-ops-rows fn2-ops)))
    (and (equal (fn2-ops-posted-fifo-length fn2-ops) (* 2 rows))
         (fn2-ops-ring-shapep (* 2 rows) (fn2-ops-post-head fn2-ops)
                              (fn2-ops-post-tail fn2-ops) (fn2-ops-post-count fn2-ops))
         (fn2-ops-same-membersp (fn2-ops-posted-list fn2-ops) (fn2-ops-pending-cells rows fn2-ops))))))
(local
(defun-nx fn2-ops-sem-rows-part (s fn2-ops)
  (fn2-ops-rows-ok-except (fn2-ops-rows fn2-ops) s fn2-ops)))
(local
(defun-nx fn2-ops-sem-outring-part (fn2-ops)
  (let ((qa (fn2-ops-out-slot-length fn2-ops)))
    (and (unsigned-byte-p 32 qa)
         (equal (fn2-ops-out-gen-length fn2-ops) qa)
         (fn2-ops-ring-shapep qa (fn2-ops-out-head fn2-ops)
                              (fn2-ops-out-tail fn2-ops) (fn2-ops-queued fn2-ops))))))
(local
(defun-nx fn2-ops-sem-free-part (fn2-ops)
  (let* ((rows (fn2-ops-rows fn2-ops))
         (free (fn2-ops-phase-slots rows *fn2-op-phase-free* fn2-ops))
         (chain (fn2-ops-free-chain rows (fn2-ops-free-head fn2-ops) fn2-ops)))
    (and (not (member-equal :bad-chain chain))
         (fn2-ops-same-membersp chain free)
         (equal (fn2-ops-free-count fn2-ops) (len free))))))
(local
(defun-nx fn2-ops-sem-counts-part (fn2-ops)
  (let* ((rows (fn2-ops-rows fn2-ops))
         (qa (fn2-ops-out-slot-length fn2-ops))
         (reserved (fn2-ops-phase-slots rows *fn2-op-phase-reserved* fn2-ops))
         (queued (fn2-ops-phase-slots rows *fn2-op-phase-queued* fn2-ops))
         (retired (fn2-ops-phase-slots rows *fn2-op-phase-retired* fn2-ops)))
    (and (equal (fn2-ops-retired-count fn2-ops) (len retired))
         (equal (fn2-ops-reserved-credits fn2-ops) (len reserved))
         (equal (fn2-ops-queued fn2-ops) (len queued))
         (<= (+ (len reserved) (len queued)) qa)))))
(local
(defun-nx fn2-ops-sem-refs-part (fn2-ops)
  (let ((queued (fn2-ops-phase-slots (fn2-ops-rows fn2-ops) *fn2-op-phase-queued* fn2-ops))
        (out (fn2-ops-outbox-list fn2-ops)))
    (and (fn2-ops-queued-refsp out fn2-ops)
         (fn2-ops-same-membersp (fn2-ops-ref-slots out) queued)))))
(local
(defun-nx fn2-ops-sem-main (s fn2-ops)
  (and (fn2-ops-sem-rows-part s fn2-ops) (fn2-ops-sem-outring-part fn2-ops) (fn2-ops-sem-free-part fn2-ops)
       (fn2-ops-sem-counts-part fn2-ops) (fn2-ops-sem-refs-part fn2-ops))))
(local
(deftheory fn2-ops-sem-parts
  '(fn2-ops-sem-rows-part fn2-ops-sem-outring-part fn2-ops-sem-free-part fn2-ops-sem-counts-part
    fn2-ops-sem-refs-part)))
(local
(defthm fn2-ops-sem-rest-split
  (equal (fn2-ops-sem-rest s fn2-ops) (and (fn2-ops-sem-main s fn2-ops) (fn2-ops-sem-post fn2-ops)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-ops-sem-rest fn2-ops-sem-main fn2-ops-sem-post)
                                             (union-theories (theory 'fn2-ops-sem-parts) (theory 'minimal-theory)))))))
;; One frame per part and write form: a row write outside the columns the
;; parts read, the posted FIFO, and a scalar none reads.
(local
(defmacro fn2-ops-sem-part-frames (part args row-reads scalar-reads)
  (let* ((call (cons part args))
         (row (intern-in-package-of-symbol (concatenate 'string (symbol-name part) "-OF-ROW-WRITE") part))
         (fifo (intern-in-package-of-symbol (concatenate 'string (symbol-name part) "-OF-FIFO-WRITE") part))
         (scalar (intern-in-package-of-symbol (concatenate 'string (symbol-name part) "-OF-SCALAR-WRITE") part)))
    `(progn
       (defthm ,row
         (implies (and (natp s) (natp kk) (< kk 44) (not (member kk ',row-reads)))
                  (equal ,(subst '(update-nth-array kk s vv fn2-ops) 'fn2-ops call) ,call))
         :hints (("Goal" :in-theory (enable ,part))))
       (defthm ,fifo
         (equal ,(subst '(update-nth-array 47 ii vv fn2-ops) 'fn2-ops call) ,call)
         :hints (("Goal" :in-theory (enable ,part))))
       (defthm ,scalar
         (implies (and (natp kk) (<= 44 kk) (not (member kk ',scalar-reads)))
                  (equal ,(subst '(update-nth kk vv fn2-ops) 'fn2-ops call) ,call))
         :hints (("Goal" :in-theory (enable ,part))))))))
(local
(in-theory (disable fn2-ops-sem-rows-part fn2-ops-sem-outring-part fn2-ops-sem-free-part fn2-ops-sem-counts-part
                    fn2-ops-sem-refs-part)))
(local (fn2-ops-sem-part-frames fn2-ops-sem-rows-part (s fn2-ops) () (44 72)))
(local
(defthm fn2-ops-sem-rows-part-of-clear-row
  (implies (natp s)
           (equal (fn2-ops-sem-rows-part s (fn2-ops-clear-row s g nx fn2-ops)) (fn2-ops-sem-rows-part s fn2-ops)))
  :hints (("Goal" :in-theory (enable fn2-ops-sem-rows-part)))))
(local (fn2-ops-sem-part-frames fn2-ops-sem-outring-part (fn2-ops) () (45 46 48 49 50)))
(local (fn2-ops-sem-part-frames fn2-ops-sem-free-part (fn2-ops) (1 41) (44 70 71)))
(local (fn2-ops-sem-part-frames fn2-ops-sem-counts-part (fn2-ops) (1) (44 45 50 51 73)))
(local (fn2-ops-sem-part-frames fn2-ops-sem-refs-part (fn2-ops) (0 1) (44 45 46 48 50)))
(local
(defthm fn2-ops-sem-main-of-row-write
  (implies (and (natp s) (natp kk) (< kk 44) (not (member kk '(0 1 41))))
           (equal (fn2-ops-sem-main s (update-nth-array kk s vv fn2-ops)) (fn2-ops-sem-main s fn2-ops)))
  :hints (("Goal" :in-theory (enable fn2-ops-sem-main)))))
(local
(defthm fn2-ops-sem-main-of-fifo-write
  (equal (fn2-ops-sem-main s (update-nth-array 47 ii vv fn2-ops)) (fn2-ops-sem-main s fn2-ops))
  :hints (("Goal" :in-theory (enable fn2-ops-sem-main)))))
(local
(defthm fn2-ops-sem-main-of-scalar-write
  (implies (and (natp kk) (<= 44 kk) (not (member kk '(44 45 46 48 49 50 51 70 71 72 73))))
           (equal (fn2-ops-sem-main s (update-nth kk vv fn2-ops)) (fn2-ops-sem-main s fn2-ops)))
  :hints (("Goal" :in-theory (enable fn2-ops-sem-main)))))
(local
(defthm fn2-ops-phase-slots-of-set-phase-neither
  (implies (and (natp s) (not (equal vv ph)) (not (equal (nth s (nth 1 fn2-ops)) ph)))
           (equal (fn2-ops-phase-slots n ph (update-nth-array 1 s vv fn2-ops))
                  (fn2-ops-phase-slots n ph fn2-ops)))
  :hints (("Goal" :in-theory (enable fn2-ops-phase-slots)))))
(local
(defthm fn2-ops-sem-main-of-busy-phase
  (implies (and (natp s) (fn2-ops-sem-main s fn2-ops)
                (not (equal vv 0)) (not (equal vv 1)) (not (equal vv 2)) (not (equal vv 6))
                (not (equal (nth s (nth 1 fn2-ops)) 0)) (not (equal (nth s (nth 1 fn2-ops)) 1))
                (not (equal (nth s (nth 1 fn2-ops)) 2)) (not (equal (nth s (nth 1 fn2-ops)) 6)))
           (fn2-ops-sem-main s (update-nth-array 1 s vv fn2-ops)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-ops-sem-main fn2-ops-sem-rows-part fn2-ops-sem-outring-part fn2-ops-sem-free-part fn2-ops-sem-counts-part fn2-ops-sem-refs-part) (member-equal fn2-ops-free-chain-consp fn2-ops-phase-slots-of-set-phase-other))
           :use ((:instance fn2-ops-not-member-of-subsetp (a s)
                  (x (fn2-ops-ref-slots (fn2-ops-outbox-list fn2-ops)))
                  (y (fn2-ops-phase-slots (nth 44 fn2-ops) 2 fn2-ops))))))))
(local
(in-theory (disable fn2-ops-sem-main fn2-ops-sem-post)))


;; Facts one row's clause gives, by phase: once over the clause's key, then
;; per row through FN2-OPS-ROW-OKP-BY-KEY.
(local
(defthm fn2-ops-sem-post-of-row-write
  (implies (and (natp s) (natp kk) (< kk 44) (not (member kk '(19 20 33 34))))
           (equal (fn2-ops-sem-post (update-nth-array kk s vv fn2-ops)) (fn2-ops-sem-post fn2-ops)))
  :hints (("Goal" :in-theory (enable fn2-ops-sem-post)))))
(local
(defthm fn2-ops-sem-post-of-scalar-write
  (implies (and (natp kk) (<= 44 kk) (not (member kk '(44 47 52 53 54))))
           (equal (fn2-ops-sem-post (update-nth kk vv fn2-ops)) (fn2-ops-sem-post fn2-ops)))
  :hints (("Goal" :in-theory (enable fn2-ops-sem-post)))))
(local
(defthm fn2-ops-sem-rest-of-row-write
  (implies (and (natp s) (natp kk) (< kk 44) (not (member kk '(0 1 19 20 33 34 41))))
           (equal (fn2-ops-sem-rest s (update-nth-array kk s vv fn2-ops))
                  (fn2-ops-sem-rest s fn2-ops)))
  :hints (("Goal" :in-theory (disable fn2-ops-sem-rest)
           :use (fn2-ops-sem-rest-split
                 (:instance fn2-ops-sem-rest-split (fn2-ops (update-nth-array kk s vv fn2-ops))))))))
(local
(defthm fn2-ops-sem-rest-of-scalar-write
  (implies (and (natp kk) (<= 44 kk)
                (not (member kk '(44 45 46 47 48 49 50 51 52 53 54 70 71 72 73))))
           (equal (fn2-ops-sem-rest s (update-nth kk vv fn2-ops))
                  (fn2-ops-sem-rest s fn2-ops)))
  :hints (("Goal" :in-theory (enable fn2-ops-sem-rest)))))
(local
(defthm fn2-ops-semanticp-intro
  (implies (and (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops) (fn2-ops-sem-facts s fn2-ops))
           (fn2-ops-semanticp fn2-ops))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-ops-sem-rest) (fn2-ops-phase-partition member-equal fn2-ops-free-chain-consp))
           :use ((:instance fn2-ops-row-semanticp-of-rows-ok-except (n (fn2-ops-rows fn2-ops)))
                 (:instance fn2-ops-phase-partition (n (fn2-ops-rows fn2-ops))))))))
(local
(defthm fn2-ops-sem-facts-of-semanticp
  (implies (fn2-ops-semanticp fn2-ops) (fn2-ops-sem-facts s fn2-ops))
  :hints (("Goal" :in-theory (union-theories '(fn2-ops-semanticp fn2-ops-sem-facts fn2-ops-sem-rest) (theory 'minimal-theory))
           :use ((:instance fn2-ops-rows-ok-except-of-row-semanticp (n (fn2-ops-rows fn2-ops)))
                 (:instance fn2-ops-row-okp-of-row-semanticp (i s) (n (fn2-ops-rows fn2-ops))))))))
(local
(defthm fn2-ops-semanticp-elim
  (implies (fn2-ops-semanticp fn2-ops)
           (and (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops)
                (fn2-ops-row-semanticp (fn2-ops-rows fn2-ops) fn2-ops)))
  :rule-classes :forward-chaining))
(local
(in-theory (disable fn2-ops-semanticp fn2-ops-sem-facts fn2-ops-sem-rest)))
(local
(defthm fn2-ops-row-key-phase-facts
  (implies (and (fn2-ops-row-key-okp phase p0 h0 p1 h1 may kind aux0 gen limit
                                     e0 o0 r0 c0 a00 a01 e1 o1 r1 c1 a10 a11 rlen)
                (natp phase))
           (and (implies (and (equal p0 1) (equal h0 0)) (equal phase 3))
                (implies (and (equal p1 1) (equal h1 0)) (or (equal phase 3) (equal phase 4)))
                (implies (equal phase 3) (equal h0 0))
                (implies (or (equal phase 0) (equal phase 1) (equal phase 2) (equal phase 5) (equal phase 6))
                         (and (not (and (equal p0 1) (equal h0 0)))
                              (not (and (equal p1 1) (equal h1 0)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-ops-row-key-okp)
           :use ((:instance fn2-ops-small-nat-cases (x phase)))))))
(local
(defmacro fn2-ops-row-phase-fact (name hyps concl)
  `(defthm ,name
     (implies (and (fn2-ops-row-okp i fn2-ops) (natp (nth i (nth 1 fn2-ops))) ,@hyps) ,concl)
     :rule-classes :forward-chaining
     :hints (("Goal" :in-theory (disable fn2-ops-row-okp)
              :use ((:instance fn2-ops-row-okp-by-key (slot i))
                    (:instance fn2-ops-row-key-phase-facts
                     (phase (fn2-ops-phase i fn2-ops)) (p0 (fn2-ops-c0-posted i fn2-ops))
                     (h0 (fn2-ops-c0-harvested i fn2-ops)) (p1 (fn2-ops-c1-posted i fn2-ops))
                     (h1 (fn2-ops-c1-harvested i fn2-ops)) (may (fn2-ops-may-release i fn2-ops))
                     (kind (fn2-ops-kind i fn2-ops)) (aux0 (fn2-ops-c0-aux0 i fn2-ops))
                     (gen (fn2-ops-gen i fn2-ops)) (limit (fn2-ops-gen-limit fn2-ops))
                     (e0 (fn2-ops-c0-event i fn2-ops)) (o0 (fn2-ops-c0-outcome i fn2-ops))
                     (r0 (fn2-ops-c0-reason i fn2-ops)) (c0 (fn2-ops-c0-count i fn2-ops))
                     (a00 (fn2-ops-c0-aux0 i fn2-ops)) (a01 (fn2-ops-c0-aux1 i fn2-ops))
                     (e1 (fn2-ops-c1-event i fn2-ops)) (o1 (fn2-ops-c1-outcome i fn2-ops))
                     (r1 (fn2-ops-c1-reason i fn2-ops)) (c1 (fn2-ops-c1-count i fn2-ops))
                     (a10 (fn2-ops-c1-aux0 i fn2-ops)) (a11 (fn2-ops-c1-aux1 i fn2-ops))
                     (rlen (fn2-ops-range-len i fn2-ops)))))))))
(local
(fn2-ops-row-phase-fact fn2-ops-row-okp-pend0-phase
  ((equal (nth i (nth 19 fn2-ops)) 1) (equal (nth i (nth 20 fn2-ops)) 0))
  (equal (nth i (nth 1 fn2-ops)) 3)))
(local
(fn2-ops-row-phase-fact fn2-ops-row-okp-pend1-phase
  ((equal (nth i (nth 33 fn2-ops)) 1) (equal (nth i (nth 34 fn2-ops)) 0))
  (or (equal (nth i (nth 1 fn2-ops)) 3) (equal (nth i (nth 1 fn2-ops)) 4))))
(local
(fn2-ops-row-phase-fact fn2-ops-row-okp-submitted-h0
  ((equal (nth i (nth 1 fn2-ops)) 3))
  (equal (nth i (nth 20 fn2-ops)) 0)))
(local
(fn2-ops-row-phase-fact fn2-ops-row-okp-cells-idle
  ((member-equal (nth i (nth 1 fn2-ops)) '(0 1 2 5 6)))
  (and (not (and (equal (nth i (nth 19 fn2-ops)) 1) (equal (nth i (nth 20 fn2-ops)) 0)))
       (not (and (equal (nth i (nth 33 fn2-ops)) 1) (equal (nth i (nth 34 fn2-ops)) 0))))))

;; Counting.
(local
(defthm fn2-ops-len-remove-of-member
  (implies (member-equal x b) (< (len (remove-equal x b)) (len b)))
  :rule-classes :linear))
(local
(defthm fn2-ops-len-remove-bound
  (<= (len (remove-equal x b)) (len b))
  :rule-classes :linear))
(local
(defun fn2-ops-subset-len-ind (a b)
  (declare (xargs :verify-guards nil))
  (if (atom a) b (fn2-ops-subset-len-ind (cdr a) (remove-equal (car a) b)))))
(local
(defthm fn2-ops-subset-len
  (implies (and (no-duplicatesp-equal a) (subsetp-equal a b)) (<= (len a) (len b)))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-ops-subset-len-ind a b)))))
(local
(defthm fn2-ops-member-consp-len
  (implies (member-equal x l) (< 0 (len l)))
  :rule-classes :linear))

;; Queued references: the head reference.
(local
(defthm fn2-ops-queued-refsp-car
  (implies (and (fn2-ops-queued-refsp refs fn2-ops) (consp refs))
           (and (natp (car (car refs))) (< (car (car refs)) (nth 44 fn2-ops))
                (equal (nth (car (car refs)) (nth 1 fn2-ops)) 2)
                (equal (car (cdr (car refs))) (nth (car (car refs)) (nth 0 fn2-ops)))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn2-op-slotp)))))

;; Ring pushes and pops, stated over the ring's shape.
(local
(defthm fn2-ops-ring-shape-zero
  (implies (and (fn2-ops-ring-shapep cap h tl c) (zp cap)) (equal c 0))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn2-ops-ring-shapep)))))
(local
(defthm fn2-ops-ring-shape-elim
  (implies (and (fn2-ops-ring-shapep cap h tl c) (not (zp cap)))
           (and (natp h) (natp tl) (natp c) (< h cap) (< tl cap) (<= c cap)
                (equal tl (mod (+ h c) cap))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-ops-ring-shapep)))))
(local
(defthm fn2-ops-posted-list-push
  (implies (and (fn2-ops-ring-shapep cap h tl c) (equal cap (len (nth 47 fn2-ops))) (< c cap))
           (equal (fn2-ops-posted-list-aux (+ 1 c) h (update-nth-array 47 tl e fn2-ops))
                  (append (fn2-ops-posted-list-aux c h fn2-ops) (list e))))
  :hints (("Goal" :use ((:instance fn2-ops-ring-shape-elim)
                        (:instance fn2-ops-ring-pos-misses-end (idx h) (k c) (left c)))))))
(local
(defthm fn2-ops-outbox-list-push
  (implies (and (fn2-ops-ring-shapep cap h tl c) (equal cap (len (nth 45 fn2-ops))) (< c cap))
           (equal (fn2-ops-outbox-list-aux (+ 1 c) h (update-nth-array 46 tl g (update-nth-array 45 tl s fn2-ops)))
                  (append (fn2-ops-outbox-list-aux c h fn2-ops) (list (list s g)))))
  :hints (("Goal" :use ((:instance fn2-ops-ring-shape-elim)
                        (:instance fn2-ops-ring-pos-misses-end (idx h) (k c) (left c))
                        (:instance fn2-ops-outbox-list-aux-of-ring-write (left c) (idx h) (kk 46) (tt tl) (vv g)
                                   (fn2-ops (update-nth-array 45 tl s fn2-ops)))
                        (:instance fn2-ops-outbox-list-aux-of-ring-write (left c) (idx h) (kk 45) (tt tl) (vv s)))))))
(local
(defthm fn2-ops-posted-list-pop
  (implies (and (fn2-ops-ring-shapep cap h tl c) (equal cap (len (nth 47 fn2-ops))) (< 0 c))
           (and (equal (fn2-ops-posted-list-aux (- c 1) (fn2-ring-next h cap) fn2-ops)
                       (cdr (fn2-ops-posted-list-aux c h fn2-ops)))
                (equal (car (fn2-ops-posted-list-aux c h fn2-ops)) (nth h (nth 47 fn2-ops)))
                (consp (fn2-ops-posted-list-aux c h fn2-ops))))
  :hints (("Goal" :use ((:instance fn2-ops-ring-shape-elim))))))
(local
(defthm fn2-ops-outbox-list-pop
  (implies (and (fn2-ops-ring-shapep cap h tl c) (equal cap (len (nth 45 fn2-ops))) (< 0 c))
           (and (equal (fn2-ops-outbox-list-aux (- c 1) (fn2-ring-next h cap) fn2-ops)
                       (cdr (fn2-ops-outbox-list-aux c h fn2-ops)))
                (equal (car (fn2-ops-outbox-list-aux c h fn2-ops))
                       (list (nth h (nth 45 fn2-ops)) (nth h (nth 46 fn2-ops))))
                (consp (fn2-ops-outbox-list-aux c h fn2-ops))))
  :hints (("Goal" :use ((:instance fn2-ops-ring-shape-elim))))))


;; Per operation: its row's clause after the step (-ROW), the split
;; invariant after the step (-FACTS), then the invariant (-CONSERVATION).
(defun fn2-ops-op-result (call position)
  (declare (xargs :guard t))
  (cond ((not position) call) ((eql position 0) `(car ,call)) (t `(mv-nth ,position ,call))))
(defmacro fn2-ops-op-conservation (op formals position slot &key row-hints facts-hints (row 't))
  (let* ((call `(,op ,@formals)) (q (fn2-ops-op-result call position))
         (row-name (fn2-ops-frame-sym op "-ROW")) (facts-name (fn2-ops-frame-sym op "-FACTS")))
    `(progn
       ,@(and row
              `((local (defthm ,row-name
                  (implies (and (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops)
                                (implies (and (natp ,slot) (< ,slot (nth 44 fn2-ops)))
                                         (fn2-ops-row-okp ,slot fn2-ops)))
                           (implies (and (natp ,slot) (< ,slot (nth 44 fn2-ops)))
                                    (fn2-ops-row-okp ,slot ,q)))
                  :hints ,(or row-hints
                              `(("Goal" :in-theory (enable ,op fn2-ops-row-okp fn2-ops-row-key-okp))))))))
       (local (defthm ,facts-name
         (implies (fn2-ops-semanticp fn2-ops) (fn2-ops-sem-facts ,slot ,q))
         :hints ,(or facts-hints
                     `(("Goal" :in-theory (e/d (,op fn2-ops-sem-facts fn2-op-phase-code fn2-op-handle-code fn2-op-slotp)
                                               (fn2-ops-semanticp fn2-ops-sem-facts-of-semanticp))
                        :use (,@(and row `(,row-name))
                              fn2-ops-semanticp-elim
                              (:instance fn2-ops-sem-facts-of-semanticp (s ,slot))))))))
       (defthm ,(fn2-ops-frame-sym op "-CONSERVATION")
         (implies (fn2-ops-semanticp fn2-ops) (fn2-ops-semanticp ,q))
         :hints (("Goal" :in-theory (disable ,op)
                  :use (fn2-ops-semanticp-elim ,facts-name
                        ,(fn2-ops-frame-sym op "-PRESERVES-TYPE") ,(fn2-ops-frame-sym op "-PRESERVES-WFP")
                        (:instance fn2-ops-semanticp-intro (s ,slot) (fn2-ops ,q)))))))))

(local
(defthm fn2-ops-semanticp-rows-u32
  (implies (fn2-ops-semanticp fn2-ops)
           (and (natp (nth 44 fn2-ops)) (< (nth 44 fn2-ops) 4294967296)))
  :rule-classes :forward-chaining
  :hints (("Goal" :use (fn2-ops-semanticp-elim (:instance fn2-ops-wfp-forward))))))
(local
(defthm fn2-ops-free-chain-pop
  (implies (and (natp n) (natp h) (not (equal h 4294967295))
                (not (member-equal :bad-chain (fn2-ops-free-chain n h fn2-ops)))
                (no-duplicatesp-equal (fn2-ops-free-chain n h fn2-ops)))
           (equal (fn2-ops-free-chain n (nth h (nth 41 fn2-ops)) (update-nth-array 41 h v fn2-ops))
                  (cdr (fn2-ops-free-chain n h fn2-ops))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn2-ops-free-chain-tail (s h))
                 (:instance fn2-ops-free-chain-car (f n) (x h))
                 (:instance fn2-ops-car-not-member-cdr (l (fn2-ops-free-chain n h fn2-ops)))
                 (:instance fn2-ops-free-chain-of-set-next-free (s h) (vv v) (f n) (x (nth h (nth 41 fn2-ops)))))
           :in-theory (disable fn2-ops-free-chain-tail fn2-ops-free-chain-car fn2-ops-car-not-member-cdr
                               fn2-ops-free-chain-of-set-next-free)))))
;; Reserve pops the free chain's head into the reserved class.
(local
(defthm fn2-ops-reserve-step-rest
  (implies (and (fn2-ops-semanticp fn2-ops)
                (equal h (nth 70 fn2-ops)) (natp h) (< h (nth 44 fn2-ops))
                (equal (nth h (nth 1 fn2-ops)) 0)
                (< (+ (nth 51 fn2-ops) (nth 50 fn2-ops)) (len (nth 45 fn2-ops))))
           (fn2-ops-sem-rest h
             (update-nth 51 (+ 1 (nth 51 fn2-ops))
              (update-nth 71 (+ -1 (nth 71 fn2-ops))
               (update-nth 70 (nth h (nth 41 fn2-ops))
                (update-nth-array 15 h may-release
                 (update-nth-array 6 h principal
                  (update-nth-array 5 h ogen
                   (update-nth-array 4 h oslot
                    (update-nth-array 3 h okind
                     (update-nth-array 2 h kind
                      (update-nth-array 1 h 1
                       (fn2-ops-clear-row h (nth h (nth 0 fn2-ops)) 4294967295 fn2-ops)))))))))))))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (fn2-ops-sem-rest fn2-ops-sem-facts) (fn2-ops-semanticp fn2-ops-sem-facts-of-semanticp))
           :use (fn2-ops-semanticp-elim
                 (:instance fn2-ops-sem-facts-of-semanticp (s h))
                 (:instance fn2-ops-free-chain-car (f (nth 44 fn2-ops)) (x h))
                 (:instance fn2-ops-free-chain-tail (n (nth 44 fn2-ops)) (s h))
                 (:instance fn2-ops-car-not-member-cdr (l (fn2-ops-free-chain (nth 44 fn2-ops) h fn2-ops)))
                 (:instance fn2-ops-same-members-pop (c (fn2-ops-free-chain (nth 44 fn2-ops) h fn2-ops))
                            (f (fn2-ops-phase-slots (nth 44 fn2-ops) 0 fn2-ops)) (a h)))))))
(local
(defthm fn2-ops-reserve-step-row
  (implies (and (fn2-ops-row-okp h fn2-ops) (natp h) (natp kind) (< kind 14) (natp may-release))
           (fn2-ops-row-okp h
             (update-nth-array 15 h may-release
              (update-nth-array 6 h principal
               (update-nth-array 5 h ogen
                (update-nth-array 4 h oslot
                 (update-nth-array 3 h okind
                  (update-nth-array 2 h kind
                   (update-nth-array 1 h 1
                    (fn2-ops-clear-row h (nth h (nth 0 fn2-ops)) 4294967295 fn2-ops))))))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-ops-row-key-okp fn2-ops-clear-val) (fn2-ops-row-okp))
           :use ((:instance fn2-ops-row-okp-gen-bound (i h))
                 (:instance fn2-ops-row-okp-by-key (slot h)
                            (fn2-ops (update-nth-array 15 h may-release
              (update-nth-array 6 h principal
               (update-nth-array 5 h ogen
                (update-nth-array 4 h oslot
                 (update-nth-array 3 h okind
                  (update-nth-array 2 h kind
                   (update-nth-array 1 h 1
                    (fn2-ops-clear-row h (nth h (nth 0 fn2-ops)) 4294967295 fn2-ops)))))))))))))))
;; An operation's result is the table unchanged unless its code is :ok; on :ok
;; it is one explicit write term, under the facts its checks established.
(local
(defmacro fn2-ops-op-branches (op formals position term facts &key (code '0) (unchanged 't) enables ok-cond (else 'fn2-ops))
  (let* ((call (cons op formals)) (q (fn2-ops-op-result call position))
         (ok (or ok-cond `(equal (mv-nth ,code ,call) :ok))))
    `(progn
       ,@(and unchanged
              `((defthm ,(fn2-ops-frame-sym op "-NOT-OK")
                  (implies (not ,ok) (equal ,q ,else))
                  :hints (("Goal" :do-not-induct t :in-theory (enable ,op ,@enables))))))
       (defthm ,(fn2-ops-frame-sym op "-OK-RESULT")
         (implies ,ok (equal ,q ,term))
         :hints (("Goal" :do-not-induct t :in-theory (enable ,op ,@enables))))
       (defthm ,(fn2-ops-frame-sym op "-OK-FACTS")
         (implies ,ok (and ,@facts))
         :rule-classes nil
         :hints (("Goal" :do-not-induct t :in-theory (enable ,op ,@enables))))))))

(local
(fn2-ops-op-branches fn2-op-reserve (kind okind oslot ogen principal may-release fn2-ops) 3
  (update-nth 51 (+ 1 (nth 51 fn2-ops))
              (update-nth 71 (+ -1 (nth 71 fn2-ops))
               (update-nth 70 (nth (nth 70 fn2-ops) (nth 41 fn2-ops))
                (update-nth-array 15 (nth 70 fn2-ops) may-release
                 (update-nth-array 6 (nth 70 fn2-ops) principal
                  (update-nth-array 5 (nth 70 fn2-ops) ogen
                   (update-nth-array 4 (nth 70 fn2-ops) oslot
                    (update-nth-array 3 (nth 70 fn2-ops) okind
                     (update-nth-array 2 (nth 70 fn2-ops) kind
                      (update-nth-array 1 (nth 70 fn2-ops) 1
                       (fn2-ops-clear-row (nth 70 fn2-ops) (nth (nth 70 fn2-ops) (nth 0 fn2-ops)) 4294967295 fn2-ops)))))))))))
  ((natp (nth 70 fn2-ops)) (< (nth 70 fn2-ops) (nth 44 fn2-ops))
   (equal (nth (nth 70 fn2-ops) (nth 1 fn2-ops)) 0)
   (natp kind) (< kind 14) (natp may-release)
   (< (+ (nth 51 fn2-ops) (nth 50 fn2-ops)) (len (nth 45 fn2-ops))))
  :enables (fn2-op-slotp)))
(fn2-ops-op-conservation fn2-op-reserve (kind okind oslot ogen principal may-release fn2-ops) 3 (nth 70 fn2-ops)
  :row-hints (("Goal" :do-not-induct t
               :cases ((equal (mv-nth 0 (fn2-op-reserve kind okind oslot ogen principal may-release fn2-ops)) :ok))
               :in-theory (disable fn2-op-reserve fn2-ops-row-okp fn2-ops-reserve-step-row)
               :use (fn2-op-reserve-ok-facts (:instance fn2-ops-reserve-step-row (h (nth 70 fn2-ops))))))
  :facts-hints (("Goal" :do-not-induct t
                 :cases ((equal (mv-nth 0 (fn2-op-reserve kind okind oslot ogen principal may-release fn2-ops)) :ok))
                 :in-theory (e/d (fn2-ops-sem-facts)
                                 (fn2-op-reserve fn2-ops-semanticp fn2-ops-sem-facts-of-semanticp
                                  fn2-ops-reserve-step-rest fn2-ops-row-okp))
                 :use (fn2-op-reserve-row fn2-ops-semanticp-elim fn2-op-reserve-ok-facts
                       (:instance fn2-ops-sem-facts-of-semanticp (s (nth 70 fn2-ops)))
                       (:instance fn2-ops-reserve-step-rest (h (nth 70 fn2-ops)))))))
(local
(defthm fn2-ops-row-key-okp-unposted-rlen
  ;; a row with neither cell posted does not read its range length
  (implies (and (equal p0 0) (equal p1 0))
           (equal (fn2-ops-row-key-okp phase p0 h0 p1 h1 may kind aux0 gen limit
                                       e0 o0 r0 c0 a00 a01 e1 o1 r1 c1 a10 a11 rlen)
                  (fn2-ops-row-key-okp phase p0 h0 p1 h1 may kind aux0 gen limit
                                       e0 o0 r0 c0 a00 a01 e1 o1 r1 c1 a10 a11 0)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-ops-row-key-okp)))))
; set-range writes a reserved row's range: unposted, so its key is the old one
(fn2-ops-op-conservation fn2-op-set-range (slot gen rslot rgen off len fn2-ops) 1 slot
  :row-hints (("Goal" :do-not-induct t
               :in-theory (e/d (fn2-op-set-range fn2-op-phase-code fn2-op-slotp fn2-op-handle-code)
                               (fn2-ops-row-okp fn2-ops-row-key-okp))
               :use ((:instance fn2-ops-row-okp-idle-cells (i slot))
                     (:instance fn2-ops-row-okp-by-key)
                     (:instance fn2-ops-row-okp-by-key (fn2-ops (mv-nth 1 (fn2-op-set-range slot gen rslot rgen off len fn2-ops))))
                     (:instance fn2-ops-row-key-okp-unposted-rlen (phase (fn2-ops-phase slot fn2-ops)) (p0 (fn2-ops-c0-posted slot fn2-ops)) (h0 (fn2-ops-c0-harvested slot fn2-ops)) (p1 (fn2-ops-c1-posted slot fn2-ops)) (h1 (fn2-ops-c1-harvested slot fn2-ops)) (may (fn2-ops-may-release slot fn2-ops)) (kind (fn2-ops-kind slot fn2-ops)) (aux0 (fn2-ops-c0-aux0 slot fn2-ops)) (gen (fn2-ops-gen slot fn2-ops)) (limit (fn2-ops-gen-limit fn2-ops)) (e0 (fn2-ops-c0-event slot fn2-ops)) (o0 (fn2-ops-c0-outcome slot fn2-ops)) (r0 (fn2-ops-c0-reason slot fn2-ops)) (c0 (fn2-ops-c0-count slot fn2-ops)) (a00 (fn2-ops-c0-aux0 slot fn2-ops)) (a01 (fn2-ops-c0-aux1 slot fn2-ops)) (e1 (fn2-ops-c1-event slot fn2-ops)) (o1 (fn2-ops-c1-outcome slot fn2-ops)) (r1 (fn2-ops-c1-reason slot fn2-ops)) (c1 (fn2-ops-c1-count slot fn2-ops)) (a10 (fn2-ops-c1-aux0 slot fn2-ops)) (a11 (fn2-ops-c1-aux1 slot fn2-ops)) (rlen (fn2-ops-range-len slot fn2-ops)))
                     (:instance fn2-ops-row-key-okp-unposted-rlen (phase (fn2-ops-phase slot (mv-nth 1 (fn2-op-set-range slot gen rslot rgen off len fn2-ops)))) (p0 (fn2-ops-c0-posted slot (mv-nth 1 (fn2-op-set-range slot gen rslot rgen off len fn2-ops)))) (h0 (fn2-ops-c0-harvested slot (mv-nth 1 (fn2-op-set-range slot gen rslot rgen off len fn2-ops)))) (p1 (fn2-ops-c1-posted slot (mv-nth 1 (fn2-op-set-range slot gen rslot rgen off len fn2-ops)))) (h1 (fn2-ops-c1-harvested slot (mv-nth 1 (fn2-op-set-range slot gen rslot rgen off len fn2-ops)))) (may (fn2-ops-may-release slot (mv-nth 1 (fn2-op-set-range slot gen rslot rgen off len fn2-ops)))) (kind (fn2-ops-kind slot (mv-nth 1 (fn2-op-set-range slot gen rslot rgen off len fn2-ops)))) (aux0 (fn2-ops-c0-aux0 slot (mv-nth 1 (fn2-op-set-range slot gen rslot rgen off len fn2-ops)))) (gen (fn2-ops-gen slot (mv-nth 1 (fn2-op-set-range slot gen rslot rgen off len fn2-ops)))) (limit (fn2-ops-gen-limit (mv-nth 1 (fn2-op-set-range slot gen rslot rgen off len fn2-ops)))) (e0 (fn2-ops-c0-event slot (mv-nth 1 (fn2-op-set-range slot gen rslot rgen off len fn2-ops)))) (o0 (fn2-ops-c0-outcome slot (mv-nth 1 (fn2-op-set-range slot gen rslot rgen off len fn2-ops)))) (r0 (fn2-ops-c0-reason slot (mv-nth 1 (fn2-op-set-range slot gen rslot rgen off len fn2-ops)))) (c0 (fn2-ops-c0-count slot (mv-nth 1 (fn2-op-set-range slot gen rslot rgen off len fn2-ops)))) (a00 (fn2-ops-c0-aux0 slot (mv-nth 1 (fn2-op-set-range slot gen rslot rgen off len fn2-ops)))) (a01 (fn2-ops-c0-aux1 slot (mv-nth 1 (fn2-op-set-range slot gen rslot rgen off len fn2-ops)))) (e1 (fn2-ops-c1-event slot (mv-nth 1 (fn2-op-set-range slot gen rslot rgen off len fn2-ops)))) (o1 (fn2-ops-c1-outcome slot (mv-nth 1 (fn2-op-set-range slot gen rslot rgen off len fn2-ops)))) (r1 (fn2-ops-c1-reason slot (mv-nth 1 (fn2-op-set-range slot gen rslot rgen off len fn2-ops)))) (c1 (fn2-ops-c1-count slot (mv-nth 1 (fn2-op-set-range slot gen rslot rgen off len fn2-ops)))) (a10 (fn2-ops-c1-aux0 slot (mv-nth 1 (fn2-op-set-range slot gen rslot rgen off len fn2-ops)))) (a11 (fn2-ops-c1-aux1 slot (mv-nth 1 (fn2-op-set-range slot gen rslot rgen off len fn2-ops)))) (rlen (fn2-ops-range-len slot (mv-nth 1 (fn2-op-set-range slot gen rslot rgen off len fn2-ops)))))))))
(fn2-ops-op-conservation fn2-op-set-capability (slot gen index nonce fn2-ops) 1 slot :row nil)
(fn2-ops-op-conservation fn2-op-set-storage (slot gen offset fua fn2-ops) 1 slot :row nil)
(fn2-ops-op-conservation fn2-op-set-cancel-target (slot gen tslot tgen fn2-ops) 1 slot :row nil)
(fn2-ops-op-conservation fn2-op-set-wake (slot gen deadline observation-gen fn2-ops) 1 slot :row nil)
(fn2-ops-op-conservation fn2-op-request-cancel (slot gen fn2-ops) 1 slot :row nil)
(local
(defthm fn2-ops-sem-facts-of-scalar-write
  (implies (and (natp kk) (<= 44 kk)
                (not (member kk '(44 45 46 47 48 49 50 51 52 53 54 70 71 72 73))))
           (equal (fn2-ops-sem-facts s (update-nth kk vv fn2-ops)) (fn2-ops-sem-facts s fn2-ops)))
  :hints (("Goal" :in-theory (enable fn2-ops-sem-facts)))))
(fn2-ops-op-conservation fn2-post-clock (mono real flags fn2-ops) nil nil :row nil
  :facts-hints (("Goal" :do-not-induct t :in-theory (e/d (fn2-post-clock) (fn2-ops-sem-facts fn2-ops-semanticp))
                 :use ((:instance fn2-ops-sem-facts-of-semanticp (s nil))))))
(fn2-ops-op-conservation fn2-take-clock (fn2-ops) 4 nil :row nil
  :facts-hints (("Goal" :do-not-induct t :in-theory (e/d (fn2-take-clock) (fn2-ops-sem-facts fn2-ops-semanticp))
                 :use ((:instance fn2-ops-sem-facts-of-semanticp (s nil))))))
(fn2-ops-op-conservation fn2-post-signal (bits fn2-ops) nil nil :row nil
  :facts-hints (("Goal" :do-not-induct t :in-theory (e/d (fn2-post-signal) (fn2-ops-sem-facts fn2-ops-semanticp))
                 :use ((:instance fn2-ops-sem-facts-of-semanticp (s nil))))))
(fn2-ops-op-conservation fn2-take-signal (fn2-ops) 1 nil :row nil
  :facts-hints (("Goal" :do-not-induct t :in-theory (e/d (fn2-take-signal) (fn2-ops-sem-facts fn2-ops-semanticp))
                 :use ((:instance fn2-ops-sem-facts-of-semanticp (s nil))))))
(fn2-ops-op-conservation fn2-count-stray (fn2-ops) nil nil :row nil
  :facts-hints (("Goal" :do-not-induct t :in-theory (e/d (fn2-count-stray) (fn2-ops-sem-facts fn2-ops-semanticp))
                 :use ((:instance fn2-ops-sem-facts-of-semanticp (s nil))))))
;; fn2-op-unreserve.
(local
(defthm fn2-ops-unreserve-step-row
  (implies (and (fn2-ops-row-okp slot fn2-ops) (natp slot) )
           (fn2-ops-row-okp slot (update-nth 51 (+ -1 (nth 51 fn2-ops))
              (update-nth 71 (+ 1 (nth 71 fn2-ops))
               (update-nth 70 slot
                (fn2-ops-clear-row slot (nth slot (nth 0 fn2-ops)) (nth 70 fn2-ops) fn2-ops))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-ops-row-key-okp fn2-ops-clear-val) (fn2-ops-row-okp))
           :use ((:instance fn2-ops-row-okp-gen-bound (i slot))
                 (:instance fn2-ops-row-okp-by-key (slot slot))
                 (:instance fn2-ops-row-okp-by-key (slot slot) (fn2-ops (update-nth 51 (+ -1 (nth 51 fn2-ops))
              (update-nth 71 (+ 1 (nth 71 fn2-ops))
               (update-nth 70 slot
                (fn2-ops-clear-row slot (nth slot (nth 0 fn2-ops)) (nth 70 fn2-ops) fn2-ops)))))))))))
(local
(defthm fn2-ops-unreserve-step-rest
  (implies (and (fn2-ops-semanticp fn2-ops) (natp slot) (< slot (nth 44 fn2-ops)) (equal (nth slot (nth 1 fn2-ops)) 1) (< 0 (nth 51 fn2-ops)))
           (fn2-ops-sem-rest slot (update-nth 51 (+ -1 (nth 51 fn2-ops))
              (update-nth 71 (+ 1 (nth 71 fn2-ops))
               (update-nth 70 slot
                (fn2-ops-clear-row slot (nth slot (nth 0 fn2-ops)) (nth 70 fn2-ops) fn2-ops))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-ops-sem-rest fn2-ops-sem-facts) (fn2-ops-semanticp fn2-ops-sem-facts-of-semanticp))
           :use (fn2-ops-semanticp-elim
                 (:instance fn2-ops-sem-facts-of-semanticp (s slot))
                 (:instance fn2-ops-phase-partition (n (nth 44 fn2-ops)))
                 (:instance fn2-ops-subset-len
                            (a (fn2-ops-free-chain (nth 44 fn2-ops) (nth 70 fn2-ops) fn2-ops))
                            (b (fn2-ops-phase-slots (nth 44 fn2-ops) 0 fn2-ops)))
                 (:instance fn2-ops-same-members-push
                            (c (fn2-ops-free-chain (nth 44 fn2-ops) (nth 70 fn2-ops) fn2-ops))
                            (f (fn2-ops-phase-slots (nth 44 fn2-ops) 0 fn2-ops))
                            (f2 (fn2-ops-phase-slots (nth 44 fn2-ops) 0 (update-nth-array 1 slot 0 fn2-ops)))
                            (s slot)))))))
(local
(fn2-ops-op-branches fn2-op-unreserve (slot gen fn2-ops) 1
  (update-nth 51 (+ -1 (nth 51 fn2-ops))
              (update-nth 71 (+ 1 (nth 71 fn2-ops))
               (update-nth 70 slot
                (fn2-ops-clear-row slot (nth slot (nth 0 fn2-ops)) (nth 70 fn2-ops) fn2-ops))))
  ((natp slot) (< slot (nth 44 fn2-ops)) (equal (nth slot (nth 1 fn2-ops)) 1) (< 0 (nth 51 fn2-ops)) (not (equal (nth 71 fn2-ops) 4294967295)))
  :enables (fn2-op-slotp fn2-op-phase-code fn2-op-handle-code)))
(fn2-ops-op-conservation fn2-op-unreserve (slot gen fn2-ops) 1 slot
  :row-hints (("Goal" :do-not-induct t
               :cases ((equal (mv-nth 0 (fn2-op-unreserve slot gen fn2-ops)) :ok))
               :in-theory (disable fn2-op-unreserve fn2-ops-row-okp fn2-ops-unreserve-step-row)
               :use (fn2-op-unreserve-ok-facts fn2-ops-unreserve-step-row)))
  :facts-hints (("Goal" :do-not-induct t
                 :cases ((equal (mv-nth 0 (fn2-op-unreserve slot gen fn2-ops)) :ok))
                 :in-theory (e/d (fn2-ops-sem-facts)
                                 (fn2-op-unreserve fn2-ops-semanticp fn2-ops-sem-facts-of-semanticp
                                  fn2-ops-unreserve-step-rest fn2-ops-row-okp))
                 :use (fn2-op-unreserve-row fn2-ops-semanticp-elim fn2-op-unreserve-ok-facts
                       (:instance fn2-ops-sem-facts-of-semanticp (s slot))
                       fn2-ops-unreserve-step-rest))))
;; fn2-op-enqueue.
(local
(defthm fn2-ops-enqueue-step-row
  (implies (and (fn2-ops-row-okp slot fn2-ops) (natp slot) (equal (nth slot (nth 1 fn2-ops)) 1))
           (fn2-ops-row-okp slot (update-nth-array 1 slot 2
              (update-nth 51 (+ -1 (nth 51 fn2-ops))
               (update-nth 50 (+ 1 (nth 50 fn2-ops))
                (update-nth 49 (fn2-ring-next (nth 49 fn2-ops) (len (nth 45 fn2-ops)))
                 (update-nth-array 46 (nth 49 fn2-ops) (nth slot (nth 0 fn2-ops))
                  (update-nth-array 45 (nth 49 fn2-ops) slot fn2-ops))))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-ops-row-key-okp fn2-ops-clear-val) (fn2-ops-row-okp))
           :use ((:instance fn2-ops-row-okp-idle-cells (i slot))
                 (:instance fn2-ops-row-okp-by-key (slot slot))
                 (:instance fn2-ops-row-okp-by-key (slot slot) (fn2-ops (update-nth-array 1 slot 2
              (update-nth 51 (+ -1 (nth 51 fn2-ops))
               (update-nth 50 (+ 1 (nth 50 fn2-ops))
                (update-nth 49 (fn2-ring-next (nth 49 fn2-ops) (len (nth 45 fn2-ops)))
                 (update-nth-array 46 (nth 49 fn2-ops) (nth slot (nth 0 fn2-ops))
                  (update-nth-array 45 (nth 49 fn2-ops) slot fn2-ops)))))))))))))
(local
(defthm fn2-ops-enqueue-step-rest
  (implies (and (fn2-ops-semanticp fn2-ops) (natp slot) (< slot (nth 44 fn2-ops)) (equal (nth slot (nth 1 fn2-ops)) 1) (< 0 (nth 51 fn2-ops)) (< (nth 50 fn2-ops) (len (nth 45 fn2-ops))))
           (fn2-ops-sem-rest slot (update-nth-array 1 slot 2
              (update-nth 51 (+ -1 (nth 51 fn2-ops))
               (update-nth 50 (+ 1 (nth 50 fn2-ops))
                (update-nth 49 (fn2-ring-next (nth 49 fn2-ops) (len (nth 45 fn2-ops)))
                 (update-nth-array 46 (nth 49 fn2-ops) (nth slot (nth 0 fn2-ops))
                  (update-nth-array 45 (nth 49 fn2-ops) slot fn2-ops))))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-ops-sem-rest fn2-ops-sem-facts) (fn2-ops-semanticp fn2-ops-sem-facts-of-semanticp fn2-ops-ring-next-is-mod fn2-ops-outbox-list-aux-snoc))
           :use (fn2-ops-semanticp-elim
                 (:instance fn2-ops-sem-facts-of-semanticp (s slot))
                 (:instance fn2-ops-outbox-list-push (cap (len (nth 45 fn2-ops))) (h (nth 48 fn2-ops)) (tl (nth 49 fn2-ops))
                            (c (nth 50 fn2-ops)) (s slot) (g (nth slot (nth 0 fn2-ops))))
                 (:instance fn2-ops-ring-shape-push (cap (len (nth 45 fn2-ops))) (h (nth 48 fn2-ops)) (tl (nth 49 fn2-ops))
                            (c (nth 50 fn2-ops)))
                 (:instance fn2-ops-ring-shape-elim (cap (len (nth 45 fn2-ops))) (h (nth 48 fn2-ops)) (tl (nth 49 fn2-ops))
                            (c (nth 50 fn2-ops)))
                 (:instance fn2-ops-same-members-push
                            (c (fn2-ops-ref-slots (fn2-ops-outbox-list-aux (nth 50 fn2-ops) (nth 48 fn2-ops) fn2-ops)))
                            (f (fn2-ops-phase-slots (nth 44 fn2-ops) 2 fn2-ops))
                            (f2 (fn2-ops-phase-slots (nth 44 fn2-ops) 2 (update-nth-array 1 slot 2 fn2-ops)))
                            (s slot)))))))
(local
(fn2-ops-op-branches fn2-op-enqueue (slot gen fn2-ops) 1
  (update-nth-array 1 slot 2
              (update-nth 51 (+ -1 (nth 51 fn2-ops))
               (update-nth 50 (+ 1 (nth 50 fn2-ops))
                (update-nth 49 (fn2-ring-next (nth 49 fn2-ops) (len (nth 45 fn2-ops)))
                 (update-nth-array 46 (nth 49 fn2-ops) (nth slot (nth 0 fn2-ops))
                  (update-nth-array 45 (nth 49 fn2-ops) slot fn2-ops))))))
  ((natp slot) (< slot (nth 44 fn2-ops)) (equal (nth slot (nth 1 fn2-ops)) 1) (< 0 (nth 51 fn2-ops)) (< (nth 49 fn2-ops) (len (nth 45 fn2-ops))) (< (nth 50 fn2-ops) (len (nth 45 fn2-ops))))
  :enables (fn2-op-slotp fn2-op-phase-code fn2-op-handle-code)))
(fn2-ops-op-conservation fn2-op-enqueue (slot gen fn2-ops) 1 slot
  :row-hints (("Goal" :do-not-induct t
               :cases ((equal (mv-nth 0 (fn2-op-enqueue slot gen fn2-ops)) :ok))
               :in-theory (disable fn2-op-enqueue fn2-ops-row-okp fn2-ops-enqueue-step-row)
               :use (fn2-op-enqueue-ok-facts fn2-ops-enqueue-step-row)))
  :facts-hints (("Goal" :do-not-induct t
                 :cases ((equal (mv-nth 0 (fn2-op-enqueue slot gen fn2-ops)) :ok))
                 :in-theory (e/d (fn2-ops-sem-facts)
                                 (fn2-op-enqueue fn2-ops-semanticp fn2-ops-sem-facts-of-semanticp
                                  fn2-ops-enqueue-step-rest fn2-ops-row-okp))
                 :use (fn2-op-enqueue-row fn2-ops-semanticp-elim fn2-op-enqueue-ok-facts
                       (:instance fn2-ops-sem-facts-of-semanticp (s slot))
                       fn2-ops-enqueue-step-rest))))


;; Post-result: one cell of a submitted (or release-pending) row is posted and
;; its index pushed on the posted ring; a refused post only counts a stray.
(local
(defthm fn2-ops-post-payload-key-facts
  (implies (fn2-ops-payload-key-okp cell evkind outcome reason count aux0 aux1 kind may rlen)
           (and (< evkind *fn2-event-count*) (< outcome *fn2-outcome-count*) (< reason *fn2-reason-count*)
                (implies (equal cell 0) (fn2-action-completionp kind))
                (implies (and (equal cell 0) (equal kind *fn2-action-send*) (equal aux0 1)) (equal may 1))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-ops-payload-key-okp)))))
(local
(defthm fn2-ops-post-result-step-row
  (implies (and (fn2-ops-row-okp slot fn2-ops) (natp slot)
                (or (equal cell 0) (equal cell 1))
                (fn2-post-payloadp cell slot evkind outcome reason count aux0 aux1 fn2-ops)
                (if (equal cell 0)
                    (and (equal (nth slot (nth 1 fn2-ops)) 3) (equal (nth slot (nth 19 fn2-ops)) 0))
                  (and (equal (nth slot (nth 15 fn2-ops)) 1) (equal (nth slot (nth 33 fn2-ops)) 0)
                       (or (equal (nth slot (nth 1 fn2-ops)) 3) (equal (nth slot (nth 1 fn2-ops)) 4)))))
           (fn2-ops-row-okp slot (update-nth 54 (+ 1 (nth 54 fn2-ops))
     (update-nth 53 (fn2-ring-next (nth 53 fn2-ops) (len (nth 47 fn2-ops)))
      (update-nth-array 47 (nth 53 fn2-ops) (+ (* 2 slot) cell)
       (if (equal cell 0) (update-nth-array 26 slot aux1 (update-nth-array 25 slot aux0 (update-nth-array 24 slot count (update-nth-array 23 slot reason (update-nth-array 22 slot outcome (update-nth-array 21 slot evkind (update-nth-array 20 slot 0 (update-nth-array 19 slot 1 fn2-ops)))))))) (update-nth-array 40 slot aux1 (update-nth-array 39 slot aux0 (update-nth-array 38 slot count (update-nth-array 37 slot reason (update-nth-array 36 slot outcome (update-nth-array 35 slot evkind (update-nth-array 34 slot 0 (update-nth-array 33 slot 1 fn2-ops))))))))))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-ops-row-key-okp) (fn2-ops-row-okp))
           :use ((:instance fn2-ops-row-okp-by-key (slot slot))
                 (:instance fn2-ops-row-okp-by-key (slot slot) (fn2-ops (update-nth 54 (+ 1 (nth 54 fn2-ops))
     (update-nth 53 (fn2-ring-next (nth 53 fn2-ops) (len (nth 47 fn2-ops)))
      (update-nth-array 47 (nth 53 fn2-ops) (+ (* 2 slot) cell)
       (if (equal cell 0) (update-nth-array 26 slot aux1 (update-nth-array 25 slot aux0 (update-nth-array 24 slot count (update-nth-array 23 slot reason (update-nth-array 22 slot outcome (update-nth-array 21 slot evkind (update-nth-array 20 slot 0 (update-nth-array 19 slot 1 fn2-ops)))))))) (update-nth-array 40 slot aux1 (update-nth-array 39 slot aux0 (update-nth-array 38 slot count (update-nth-array 37 slot reason (update-nth-array 36 slot outcome (update-nth-array 35 slot evkind (update-nth-array 34 slot 0 (update-nth-array 33 slot 1 fn2-ops))))))))))))))
                 (:instance fn2-post-payloadp-by-key))))))
(local
(defthm fn2-ops-post-result-step-rest
  (implies (and (fn2-ops-semanticp fn2-ops) (natp slot) (< slot (nth 44 fn2-ops))
                (or (equal cell 0) (equal cell 1))
                (fn2-ops-row-okp slot fn2-ops)
                (if (equal cell 0)
                    (and (equal (nth slot (nth 1 fn2-ops)) 3) (equal (nth slot (nth 19 fn2-ops)) 0))
                  (and (equal (nth slot (nth 33 fn2-ops)) 0)
                       (or (equal (nth slot (nth 1 fn2-ops)) 3) (equal (nth slot (nth 1 fn2-ops)) 4))))
                (< (nth 54 fn2-ops) (len (nth 47 fn2-ops))))
           (fn2-ops-sem-rest slot (update-nth 54 (+ 1 (nth 54 fn2-ops))
     (update-nth 53 (fn2-ring-next (nth 53 fn2-ops) (len (nth 47 fn2-ops)))
      (update-nth-array 47 (nth 53 fn2-ops) (+ (* 2 slot) cell)
       (if (equal cell 0) (update-nth-array 26 slot aux1 (update-nth-array 25 slot aux0 (update-nth-array 24 slot count (update-nth-array 23 slot reason (update-nth-array 22 slot outcome (update-nth-array 21 slot evkind (update-nth-array 20 slot 0 (update-nth-array 19 slot 1 fn2-ops)))))))) (update-nth-array 40 slot aux1 (update-nth-array 39 slot aux0 (update-nth-array 38 slot count (update-nth-array 37 slot reason (update-nth-array 36 slot outcome (update-nth-array 35 slot evkind (update-nth-array 34 slot 0 (update-nth-array 33 slot 1 fn2-ops))))))))))))))
  :hints (("Goal" :do-not-induct t :cases ((equal cell 0))
           :in-theory (e/d (fn2-ops-sem-post fn2-ops-sem-facts)
                           (member-equal fn2-ops-free-chain-consp fn2-ops-sem-rest fn2-ops-sem-main fn2-ops-semanticp fn2-ops-sem-facts-of-semanticp fn2-ops-ring-next-is-mod
                            fn2-ops-posted-list-aux-snoc))
           :use (fn2-ops-semanticp-elim (:instance fn2-ops-sem-rest-split (s slot)) (:instance fn2-ops-sem-rest-split (s slot) (fn2-ops (update-nth 54 (+ 1 (nth 54 fn2-ops))
     (update-nth 53 (fn2-ring-next (nth 53 fn2-ops) (len (nth 47 fn2-ops)))
      (update-nth-array 47 (nth 53 fn2-ops) (+ (* 2 slot) cell)
       (if (equal cell 0) (update-nth-array 26 slot aux1 (update-nth-array 25 slot aux0 (update-nth-array 24 slot count (update-nth-array 23 slot reason (update-nth-array 22 slot outcome (update-nth-array 21 slot evkind (update-nth-array 20 slot 0 (update-nth-array 19 slot 1 fn2-ops)))))))) (update-nth-array 40 slot aux1 (update-nth-array 39 slot aux0 (update-nth-array 38 slot count (update-nth-array 37 slot reason (update-nth-array 36 slot outcome (update-nth-array 35 slot evkind (update-nth-array 34 slot 0 (update-nth-array 33 slot 1 fn2-ops)))))))))))))) 
                 (:instance fn2-ops-sem-facts-of-semanticp (s slot))
                 (:instance fn2-ops-row-okp-unposted (i slot))
                 (:instance fn2-ops-row-okp-submitted-h0 (i slot))
                 (:instance fn2-ops-ring-shape-elim (cap (len (nth 47 fn2-ops))) (h (nth 52 fn2-ops))
                            (tl (nth 53 fn2-ops)) (c (nth 54 fn2-ops)))
                 (:instance fn2-ops-ring-shape-push (cap (len (nth 47 fn2-ops))) (h (nth 52 fn2-ops))
                            (tl (nth 53 fn2-ops)) (c (nth 54 fn2-ops)))
                 (:instance fn2-ops-same-members-push
                            (c (fn2-ops-posted-list-aux (nth 54 fn2-ops) (nth 52 fn2-ops) fn2-ops))
                            (f (fn2-ops-pending-cells (nth 44 fn2-ops) fn2-ops))
                            (f2 (fn2-ops-pending-cells (nth 44 fn2-ops)
                                  (update-nth-array (if (equal cell 0) 19 33) slot 1 fn2-ops)))
                            (s (+ (* 2 slot) cell))))))))
(local
(fn2-ops-op-branches fn2-post-result (cell slot gen evkind outcome reason count aux0 aux1 fn2-ops) nil
  (update-nth 54 (+ 1 (nth 54 fn2-ops))
     (update-nth 53 (fn2-ring-next (nth 53 fn2-ops) (len (nth 47 fn2-ops)))
      (update-nth-array 47 (nth 53 fn2-ops) (+ (* 2 slot) cell)
       (if (equal cell 0) (update-nth-array 26 slot aux1 (update-nth-array 25 slot aux0 (update-nth-array 24 slot count (update-nth-array 23 slot reason (update-nth-array 22 slot outcome (update-nth-array 21 slot evkind (update-nth-array 20 slot 0 (update-nth-array 19 slot 1 fn2-ops)))))))) (update-nth-array 40 slot aux1 (update-nth-array 39 slot aux0 (update-nth-array 38 slot count (update-nth-array 37 slot reason (update-nth-array 36 slot outcome (update-nth-array 35 slot evkind (update-nth-array 34 slot 0 (update-nth-array 33 slot 1 fn2-ops))))))))))))
  ((natp slot) (< slot (nth 44 fn2-ops)) (or (equal cell 0) (equal cell 1))
   (fn2-post-payloadp cell slot evkind outcome reason count aux0 aux1 fn2-ops)
   (if (equal cell 0)
       (and (equal (nth slot (nth 1 fn2-ops)) 3) (equal (nth slot (nth 19 fn2-ops)) 0))
     (and (equal (nth slot (nth 15 fn2-ops)) 1) (equal (nth slot (nth 33 fn2-ops)) 0)
          (or (equal (nth slot (nth 1 fn2-ops)) 3) (equal (nth slot (nth 1 fn2-ops)) 4))))
   (< (nth 54 fn2-ops) (len (nth 47 fn2-ops))))
  :ok-cond (and (fn2-post-eligiblep cell slot gen fn2-ops)
                (fn2-post-payloadp cell slot evkind outcome reason count aux0 aux1 fn2-ops)
                (< (nth 53 fn2-ops) (len (nth 47 fn2-ops))) (< (nth 54 fn2-ops) (len (nth 47 fn2-ops)))
                (< (nth 54 fn2-ops) 1152921504606846975) (< (len (nth 47 fn2-ops)) 1152921504606846976))
  :else (fn2-count-stray fn2-ops)
  :enables (fn2-post-eligiblep fn2-op-slotp fn2-op-handle-code)))
(fn2-ops-op-conservation fn2-post-result (cell slot gen evkind outcome reason count aux0 aux1 fn2-ops) nil slot
  :row-hints (("Goal" :do-not-induct t
               :cases ((and (fn2-post-eligiblep cell slot gen fn2-ops)
                (fn2-post-payloadp cell slot evkind outcome reason count aux0 aux1 fn2-ops)
                (< (nth 53 fn2-ops) (len (nth 47 fn2-ops))) (< (nth 54 fn2-ops) (len (nth 47 fn2-ops)))
                (< (nth 54 fn2-ops) 1152921504606846975) (< (len (nth 47 fn2-ops)) 1152921504606846976)))
               :in-theory (e/d (fn2-count-stray) (fn2-post-result fn2-ops-row-okp fn2-ops-post-result-step-row))
               :use (fn2-post-result-ok-facts fn2-ops-post-result-step-row)))
  :facts-hints (("Goal" :do-not-induct t
                 :cases ((and (fn2-post-eligiblep cell slot gen fn2-ops)
                (fn2-post-payloadp cell slot evkind outcome reason count aux0 aux1 fn2-ops)
                (< (nth 53 fn2-ops) (len (nth 47 fn2-ops))) (< (nth 54 fn2-ops) (len (nth 47 fn2-ops)))
                (< (nth 54 fn2-ops) 1152921504606846975) (< (len (nth 47 fn2-ops)) 1152921504606846976)))
                 :in-theory (e/d (fn2-ops-sem-facts fn2-count-stray)
                                 (fn2-post-result fn2-ops-semanticp fn2-ops-sem-facts-of-semanticp
                                  fn2-ops-post-result-step-rest fn2-ops-row-okp))
                 :use (fn2-post-result-row fn2-ops-semanticp-elim fn2-post-result-ok-facts
                       (:instance fn2-ops-sem-facts-of-semanticp (s slot))
                       fn2-ops-post-result-step-rest))))

;; Harvest: the posted ring's head cell is marked harvested, the row moves to
;; the phase fn2-op-harvest-phase names, and the head is popped.
(local
(defthm fn2-ops-harvest-step-row
  (implies (and (fn2-ops-row-okp slot fn2-ops) (natp slot) (natp (nth slot (nth 1 fn2-ops)))
                (natp (nth slot (nth 19 fn2-ops))) (natp (nth slot (nth 20 fn2-ops)))
                (natp (nth slot (nth 33 fn2-ops))) (natp (nth slot (nth 34 fn2-ops)))
                (< (nth slot (nth 19 fn2-ops)) 2) (< (nth slot (nth 33 fn2-ops)) 2) (< (nth slot (nth 15 fn2-ops)) 2) (natp (nth slot (nth 15 fn2-ops)))
                (or (equal cell 0) (equal cell 1))
                (if (equal cell 0)
                    (and (equal (nth slot (nth 19 fn2-ops)) 1) (equal (nth slot (nth 20 fn2-ops)) 0))
                  (and (equal (nth slot (nth 33 fn2-ops)) 1) (equal (nth slot (nth 34 fn2-ops)) 0))))
           (fn2-ops-row-okp slot (update-nth 54 (+ -1 (nth 54 fn2-ops))
     (update-nth 52 (fn2-ring-next (nth 52 fn2-ops) (len (nth 47 fn2-ops)))
      (update-nth-array 1 slot (fn2-op-harvest-phase slot (fn2-ops-latch-peer cell slot (update-nth-array (if (equal cell 0) 20 34) slot 1 fn2-ops))) (fn2-ops-latch-peer cell slot (update-nth-array (if (equal cell 0) 20 34) slot 1 fn2-ops)))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-ops-row-key-okp) (fn2-ops-row-okp))
           :use ((:instance fn2-ops-row-okp-by-key (slot slot))
                 (:instance fn2-ops-row-okp-by-key (slot slot) (fn2-ops (update-nth 54 (+ -1 (nth 54 fn2-ops))
     (update-nth 52 (fn2-ring-next (nth 52 fn2-ops) (len (nth 47 fn2-ops)))
      (update-nth-array 1 slot (fn2-op-harvest-phase slot (fn2-ops-latch-peer cell slot (update-nth-array (if (equal cell 0) 20 34) slot 1 fn2-ops))) (fn2-ops-latch-peer cell slot (update-nth-array (if (equal cell 0) 20 34) slot 1 fn2-ops)))))))
                 (:instance fn2-ops-row-okp-pend0-phase (i slot))
                 (:instance fn2-ops-row-okp-pend1-phase (i slot))
                 (:instance fn2-ops-post-payload-key-facts (cell 0)
                            (evkind (nth slot (nth 21 fn2-ops))) (outcome (nth slot (nth 22 fn2-ops)))
                            (reason (nth slot (nth 23 fn2-ops))) (count (nth slot (nth 24 fn2-ops)))
                            (aux0 (nth slot (nth 25 fn2-ops))) (aux1 (nth slot (nth 26 fn2-ops)))
                            (kind (nth slot (nth 2 fn2-ops))) (may (nth slot (nth 15 fn2-ops)))
                            (rlen (nth slot (nth 10 fn2-ops)))))))))
(local
(defthm fn2-ops-harvest-step-rest
  (implies (and (fn2-ops-semanticp fn2-ops) (natp slot) (< slot (nth 44 fn2-ops))
                (or (equal cell 0) (equal cell 1))
                (equal (nth (nth 52 fn2-ops) (nth 47 fn2-ops)) (+ (* 2 slot) cell))
                (natp (nth slot (nth 1 fn2-ops)))
                (if (equal cell 0)
                    (and (equal (nth slot (nth 19 fn2-ops)) 1) (equal (nth slot (nth 20 fn2-ops)) 0))
                  (and (equal (nth slot (nth 33 fn2-ops)) 1) (equal (nth slot (nth 34 fn2-ops)) 0)))
                (< 0 (nth 54 fn2-ops)))
           (fn2-ops-sem-rest slot (update-nth 54 (+ -1 (nth 54 fn2-ops))
     (update-nth 52 (fn2-ring-next (nth 52 fn2-ops) (len (nth 47 fn2-ops)))
      (update-nth-array 1 slot (fn2-op-harvest-phase slot (fn2-ops-latch-peer cell slot (update-nth-array (if (equal cell 0) 20 34) slot 1 fn2-ops))) (fn2-ops-latch-peer cell slot (update-nth-array (if (equal cell 0) 20 34) slot 1 fn2-ops)))))))
  :hints (("Goal" :do-not-induct t :cases ((equal cell 0))
           :in-theory (e/d (fn2-ops-sem-post fn2-ops-sem-facts)
                           (member-equal fn2-ops-free-chain-consp fn2-ops-sem-rest fn2-ops-sem-main fn2-ops-semanticp fn2-ops-sem-facts-of-semanticp fn2-ops-ring-next-is-mod))
           :use (fn2-ops-semanticp-elim (:instance fn2-ops-sem-rest-split (s slot)) (:instance fn2-ops-sem-rest-split (s slot) (fn2-ops (update-nth 54 (+ -1 (nth 54 fn2-ops))
     (update-nth 52 (fn2-ring-next (nth 52 fn2-ops) (len (nth 47 fn2-ops)))
      (update-nth-array 1 slot (fn2-op-harvest-phase slot (fn2-ops-latch-peer cell slot (update-nth-array (if (equal cell 0) 20 34) slot 1 fn2-ops))) (fn2-ops-latch-peer cell slot (update-nth-array (if (equal cell 0) 20 34) slot 1 fn2-ops))))))) 
                 (:instance fn2-ops-sem-facts-of-semanticp (s slot))
                 (:instance fn2-ops-row-okp-pend0-phase (i slot))
                 (:instance fn2-ops-row-okp-pend1-phase (i slot))
                 (:instance fn2-ops-ring-shape-pop (cap (len (nth 47 fn2-ops))) (h (nth 52 fn2-ops))
                            (tl (nth 53 fn2-ops)) (c (nth 54 fn2-ops)))
                 (:instance fn2-ops-posted-list-pop (cap (len (nth 47 fn2-ops))) (h (nth 52 fn2-ops))
                            (tl (nth 53 fn2-ops)) (c (nth 54 fn2-ops)))
                 (:instance fn2-ops-same-members-pop
                            (c (fn2-ops-posted-list-aux (nth 54 fn2-ops) (nth 52 fn2-ops) fn2-ops))
                            (f (fn2-ops-pending-cells (nth 44 fn2-ops) fn2-ops))
                            (a (+ (* 2 slot) cell))))))))
(local
(fn2-ops-op-branches fn2-harvest-next (fn2-ops) 4
  (update-nth 54 (+ -1 (nth 54 fn2-ops))
     (update-nth 52 (fn2-ring-next (nth 52 fn2-ops) (len (nth 47 fn2-ops)))
      (update-nth-array 1 (floor (nth (nth 52 fn2-ops) (nth 47 fn2-ops)) 2) (fn2-op-harvest-phase (floor (nth (nth 52 fn2-ops) (nth 47 fn2-ops)) 2) (fn2-ops-latch-peer (mod (nth (nth 52 fn2-ops) (nth 47 fn2-ops)) 2) (floor (nth (nth 52 fn2-ops) (nth 47 fn2-ops)) 2) (update-nth-array (if (equal (mod (nth (nth 52 fn2-ops) (nth 47 fn2-ops)) 2) 0) 20 34) (floor (nth (nth 52 fn2-ops) (nth 47 fn2-ops)) 2) 1 fn2-ops))) (fn2-ops-latch-peer (mod (nth (nth 52 fn2-ops) (nth 47 fn2-ops)) 2) (floor (nth (nth 52 fn2-ops) (nth 47 fn2-ops)) 2) (update-nth-array (if (equal (mod (nth (nth 52 fn2-ops) (nth 47 fn2-ops)) 2) 0) 20 34) (floor (nth (nth 52 fn2-ops) (nth 47 fn2-ops)) 2) 1 fn2-ops)))))
  ((natp (floor (nth (nth 52 fn2-ops) (nth 47 fn2-ops)) 2)) (< (floor (nth (nth 52 fn2-ops) (nth 47 fn2-ops)) 2) (nth 44 fn2-ops)) (or (equal (mod (nth (nth 52 fn2-ops) (nth 47 fn2-ops)) 2) 0) (equal (mod (nth (nth 52 fn2-ops) (nth 47 fn2-ops)) 2) 1))
   (if (equal (mod (nth (nth 52 fn2-ops) (nth 47 fn2-ops)) 2) 0)
                    (and (equal (nth (floor (nth (nth 52 fn2-ops) (nth 47 fn2-ops)) 2) (nth 19 fn2-ops)) 1) (equal (nth (floor (nth (nth 52 fn2-ops) (nth 47 fn2-ops)) 2) (nth 20 fn2-ops)) 0))
                  (and (equal (nth (floor (nth (nth 52 fn2-ops) (nth 47 fn2-ops)) 2) (nth 33 fn2-ops)) 1) (equal (nth (floor (nth (nth 52 fn2-ops) (nth 47 fn2-ops)) 2) (nth 34 fn2-ops)) 0)))
   (< 0 (nth 54 fn2-ops)))
  :ok-cond (equal (mv-nth 0 (fn2-harvest-next fn2-ops)) t)
  :enables (fn2-ops-peek-posted fn2-op-slotp)))
(local
(defthm fn2-ops-posted-head-natp
  (implies (and (fn2-ops-semanticp fn2-ops) (< 0 (nth 54 fn2-ops)))
           (natp (nth (nth 52 fn2-ops) (nth 47 fn2-ops))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-ops-sem-rest fn2-ops-sem-facts fn2-ops-same-membersp)
                           (fn2-ops-semanticp fn2-ops-sem-facts-of-semanticp))
           :use ((:instance fn2-ops-sem-facts-of-semanticp (s 0))
                 (:instance fn2-ops-posted-list-pop (cap (len (nth 47 fn2-ops))) (h (nth 52 fn2-ops))
                            (tl (nth 53 fn2-ops)) (c (nth 54 fn2-ops)))
                 (:instance fn2-ops-member-of-subsetp
                            (x (fn2-ops-posted-list-aux (nth 54 fn2-ops) (nth 52 fn2-ops) fn2-ops))
                            (y (fn2-ops-pending-cells (nth 44 fn2-ops) fn2-ops))
                            (a (nth (nth 52 fn2-ops) (nth 47 fn2-ops))))
                 (:instance fn2-ops-pending-cells-bound (x (nth (nth 52 fn2-ops) (nth 47 fn2-ops))) (n (nth 44 fn2-ops))))))))
(fn2-ops-op-conservation fn2-harvest-next (fn2-ops) 4 (floor (nth (nth 52 fn2-ops) (nth 47 fn2-ops)) 2)
  :row-hints (("Goal" :do-not-induct t
               :cases ((equal (mv-nth 0 (fn2-harvest-next fn2-ops)) t))
               :in-theory (disable fn2-harvest-next fn2-ops-row-okp fn2-ops-harvest-step-row)
               :use (fn2-harvest-next-ok-facts
                     (:instance fn2-ops-phase-raw-nth-natp (i (floor (nth (nth 52 fn2-ops) (nth 47 fn2-ops)) 2)))
                     (:instance fn2-ops-c0-posted-raw-nth-natp (i (floor (nth (nth 52 fn2-ops) (nth 47 fn2-ops)) 2)))
                     (:instance fn2-ops-c0-harvested-raw-nth-natp (i (floor (nth (nth 52 fn2-ops) (nth 47 fn2-ops)) 2)))
                     (:instance fn2-ops-c1-posted-raw-nth-natp (i (floor (nth (nth 52 fn2-ops) (nth 47 fn2-ops)) 2)))
                     (:instance fn2-ops-c1-harvested-raw-nth-natp (i (floor (nth (nth 52 fn2-ops) (nth 47 fn2-ops)) 2)))
                     (:instance fn2-ops-c0-posted-raw-nth-bound (i (floor (nth (nth 52 fn2-ops) (nth 47 fn2-ops)) 2)))
                     (:instance fn2-ops-c1-posted-raw-nth-bound (i (floor (nth (nth 52 fn2-ops) (nth 47 fn2-ops)) 2)))
                     (:instance fn2-ops-may-release-raw-nth-bound (i (floor (nth (nth 52 fn2-ops) (nth 47 fn2-ops)) 2)))
                     (:instance fn2-ops-may-release-raw-nth-natp (i (floor (nth (nth 52 fn2-ops) (nth 47 fn2-ops)) 2)))
                     (:instance fn2-ops-harvest-step-row (slot (floor (nth (nth 52 fn2-ops) (nth 47 fn2-ops)) 2)) (cell (mod (nth (nth 52 fn2-ops) (nth 47 fn2-ops)) 2))))))
  :facts-hints (("Goal" :do-not-induct t
                 :cases ((equal (mv-nth 0 (fn2-harvest-next fn2-ops)) t))
                 :in-theory (e/d (fn2-ops-sem-facts)
                                 (fn2-harvest-next fn2-ops-semanticp fn2-ops-sem-facts-of-semanticp
                                  fn2-ops-harvest-step-rest fn2-ops-row-okp))
                 :use (fn2-harvest-next-row fn2-ops-semanticp-elim fn2-harvest-next-ok-facts
                       fn2-ops-posted-head-natp
                       (:instance fn2-ops-cell-split (e (nth (nth 52 fn2-ops) (nth 47 fn2-ops))))
                       (:instance fn2-ops-phase-raw-nth-natp (i (floor (nth (nth 52 fn2-ops) (nth 47 fn2-ops)) 2)))
                       (:instance fn2-ops-sem-facts-of-semanticp (s (floor (nth (nth 52 fn2-ops) (nth 47 fn2-ops)) 2)))
                       (:instance fn2-ops-harvest-step-rest (slot (floor (nth (nth 52 fn2-ops) (nth 47 fn2-ops)) 2)) (cell (mod (nth (nth 52 fn2-ops) (nth 47 fn2-ops)) 2)))))))

;; Finish: a done row is recycled into the free chain with its generation
;; advanced, or retired at the generation limit.
(local
(defthm fn2-ops-remove-phase-slots-of-set-phase
  (implies (natp s)
           (equal (remove-equal s (fn2-ops-phase-slots n ph (update-nth-array 1 s vv fn2-ops)))
                  (remove-equal s (fn2-ops-phase-slots n ph fn2-ops))))
  :hints (("Goal" :in-theory (enable fn2-ops-phase-slots)))))
(local
(defthm fn2-op-finish-other
  (implies (not (member-equal (mv-nth 0 (fn2-op-finish slot gen fn2-ops)) '(:ok :retired))) (equal (mv-nth 1 (fn2-op-finish slot gen fn2-ops)) fn2-ops))
  :hints (("Goal" :do-not-induct t :in-theory (enable fn2-op-finish fn2-op-recycle fn2-op-slotp fn2-op-phase-code fn2-op-handle-code)))))
(local
(defthm fn2-op-finish-retired-result
  (implies (equal (mv-nth 0 (fn2-op-finish slot gen fn2-ops)) :retired) (equal (mv-nth 1 (fn2-op-finish slot gen fn2-ops)) (update-nth 73 (+ 1 (nth 73 fn2-ops))
     (update-nth-array 1 slot 6 (fn2-ops-clear-row slot (nth slot (nth 0 fn2-ops)) 4294967295 fn2-ops)))))
  :hints (("Goal" :do-not-induct t :in-theory (enable fn2-op-finish fn2-op-recycle fn2-op-slotp fn2-op-phase-code fn2-op-handle-code)))))
(local
(defthm fn2-op-finish-ok-result
  (implies (equal (mv-nth 0 (fn2-op-finish slot gen fn2-ops)) :ok) (equal (mv-nth 1 (fn2-op-finish slot gen fn2-ops)) (update-nth 71 (+ 1 (nth 71 fn2-ops))
     (update-nth 70 slot (fn2-ops-clear-row slot (+ 1 (nth slot (nth 0 fn2-ops))) (nth 70 fn2-ops) fn2-ops)))))
  :hints (("Goal" :do-not-induct t :in-theory (enable fn2-op-finish fn2-op-recycle fn2-op-slotp fn2-op-phase-code fn2-op-handle-code)))))
(local
(defthm fn2-op-finish-branch-facts
  (and (implies (equal (mv-nth 0 (fn2-op-finish slot gen fn2-ops)) :retired) (and (natp slot) (< slot (nth 44 fn2-ops)) (equal (nth slot (nth 1 fn2-ops)) 5) (<= (nth 72 fn2-ops) (nth slot (nth 0 fn2-ops)))))
       (implies (equal (mv-nth 0 (fn2-op-finish slot gen fn2-ops)) :ok) (and (natp slot) (< slot (nth 44 fn2-ops)) (equal (nth slot (nth 1 fn2-ops)) 5) (< (nth slot (nth 0 fn2-ops)) (nth 72 fn2-ops))
                                     (not (equal (nth 71 fn2-ops) 4294967295)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (enable fn2-op-finish fn2-op-recycle fn2-op-slotp fn2-op-phase-code fn2-op-handle-code)))))
(local
(defthm fn2-ops-finish-retired-step-row
  (implies (and (fn2-ops-row-okp slot fn2-ops) (natp slot) (<= (nth 72 fn2-ops) (nth slot (nth 0 fn2-ops)))
                (natp (nth slot (nth 0 fn2-ops))) (natp (nth 72 fn2-ops)))
           (fn2-ops-row-okp slot (update-nth 73 (+ 1 (nth 73 fn2-ops))
     (update-nth-array 1 slot 6 (fn2-ops-clear-row slot (nth slot (nth 0 fn2-ops)) 4294967295 fn2-ops)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-ops-row-key-okp fn2-ops-clear-val) (fn2-ops-row-okp))
           :use ((:instance fn2-ops-row-okp-gen-bound (i slot))
                 (:instance fn2-ops-row-okp-by-key (slot slot) (fn2-ops (update-nth 73 (+ 1 (nth 73 fn2-ops))
     (update-nth-array 1 slot 6 (fn2-ops-clear-row slot (nth slot (nth 0 fn2-ops)) 4294967295 fn2-ops))))))))))
(local
(defthm fn2-ops-finish-ok-step-row
  (implies (and (fn2-ops-row-okp slot fn2-ops) (natp slot) (< (nth slot (nth 0 fn2-ops)) (nth 72 fn2-ops))
                (natp (nth slot (nth 0 fn2-ops))) (natp (nth 72 fn2-ops)))
           (fn2-ops-row-okp slot (update-nth 71 (+ 1 (nth 71 fn2-ops))
     (update-nth 70 slot (fn2-ops-clear-row slot (+ 1 (nth slot (nth 0 fn2-ops))) (nth 70 fn2-ops) fn2-ops)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-ops-row-key-okp fn2-ops-clear-val) (fn2-ops-row-okp))
           :use ((:instance fn2-ops-row-okp-by-key (slot slot) (fn2-ops (update-nth 71 (+ 1 (nth 71 fn2-ops))
     (update-nth 70 slot (fn2-ops-clear-row slot (+ 1 (nth slot (nth 0 fn2-ops))) (nth 70 fn2-ops) fn2-ops))))))))))
(local
(defthm fn2-ops-finish-retired-step-rest
  (implies (and (fn2-ops-semanticp fn2-ops) (natp slot) (< slot (nth 44 fn2-ops)) (equal (nth slot (nth 1 fn2-ops)) 5))
           (fn2-ops-sem-rest slot (update-nth 73 (+ 1 (nth 73 fn2-ops))
     (update-nth-array 1 slot 6 (fn2-ops-clear-row slot (nth slot (nth 0 fn2-ops)) 4294967295 fn2-ops)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-ops-sem-rest fn2-ops-sem-facts) (fn2-ops-semanticp fn2-ops-sem-facts-of-semanticp))
           :use (fn2-ops-semanticp-elim
                 (:instance fn2-ops-sem-facts-of-semanticp (s slot))
                 (:instance fn2-ops-row-okp-cells-idle (i slot))
                 (:instance fn2-ops-not-member-of-subsetp (a slot)
                            (x (fn2-ops-free-chain (nth 44 fn2-ops) (nth 70 fn2-ops) fn2-ops))
                            (y (fn2-ops-phase-slots (nth 44 fn2-ops) 0 fn2-ops))))))))
(local
(defthm fn2-ops-finish-ok-step-rest
  (implies (and (fn2-ops-semanticp fn2-ops) (natp slot) (< slot (nth 44 fn2-ops)) (equal (nth slot (nth 1 fn2-ops)) 5) (not (equal (nth 71 fn2-ops) 4294967295)))
           (fn2-ops-sem-rest slot (update-nth 71 (+ 1 (nth 71 fn2-ops))
     (update-nth 70 slot (fn2-ops-clear-row slot (+ 1 (nth slot (nth 0 fn2-ops))) (nth 70 fn2-ops) fn2-ops)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-ops-sem-rest fn2-ops-sem-facts) (fn2-ops-semanticp fn2-ops-sem-facts-of-semanticp))
           :use (fn2-ops-semanticp-elim
                 (:instance fn2-ops-sem-facts-of-semanticp (s slot))
                 (:instance fn2-ops-row-okp-cells-idle (i slot))
                 (:instance fn2-ops-phase-partition (n (nth 44 fn2-ops)))
                 (:instance fn2-ops-member-consp-len (x slot) (l (fn2-ops-phase-slots (nth 44 fn2-ops) 5 fn2-ops)))
                 (:instance fn2-ops-subset-len
                            (a (fn2-ops-free-chain (nth 44 fn2-ops) (nth 70 fn2-ops) fn2-ops))
                            (b (fn2-ops-phase-slots (nth 44 fn2-ops) 0 fn2-ops)))
                 (:instance fn2-ops-same-members-push
                            (c (fn2-ops-free-chain (nth 44 fn2-ops) (nth 70 fn2-ops) fn2-ops))
                            (f (fn2-ops-phase-slots (nth 44 fn2-ops) 0 fn2-ops))
                            (f2 (fn2-ops-phase-slots (nth 44 fn2-ops) 0 (update-nth-array 1 slot 0 fn2-ops)))
                            (s slot)))))))
(fn2-ops-op-conservation fn2-op-finish (slot gen fn2-ops) 1 slot
  :row-hints (("Goal" :do-not-induct t
               :cases ((equal (mv-nth 0 (fn2-op-finish slot gen fn2-ops)) :ok) (equal (mv-nth 0 (fn2-op-finish slot gen fn2-ops)) :retired))
               :in-theory (disable fn2-op-finish fn2-ops-row-okp fn2-ops-finish-ok-step-row fn2-ops-finish-retired-step-row)
               :use (fn2-op-finish-branch-facts fn2-ops-finish-ok-step-row fn2-ops-finish-retired-step-row
                     (:instance fn2-ops-gen-raw-nth-natp (i slot)))))
  :facts-hints (("Goal" :do-not-induct t
                 :cases ((equal (mv-nth 0 (fn2-op-finish slot gen fn2-ops)) :ok) (equal (mv-nth 0 (fn2-op-finish slot gen fn2-ops)) :retired))
                 :in-theory (e/d (fn2-ops-sem-facts)
                                 (fn2-op-finish fn2-ops-semanticp fn2-ops-sem-facts-of-semanticp
                                  fn2-ops-finish-ok-step-rest fn2-ops-finish-retired-step-rest fn2-ops-row-okp))
                 :use (fn2-op-finish-row fn2-ops-semanticp-elim fn2-op-finish-branch-facts
                       (:instance fn2-ops-sem-facts-of-semanticp (s slot))
                       fn2-ops-finish-ok-step-rest fn2-ops-finish-retired-step-rest))))

;; Ack: each step of fn2-outbox-submit-prefix pops the outbox head, whose row
;; moves from queued to the phase fn2-op-ack-phase names.
(local
(defthm fn2-ops-ack-step-row
  (implies (and (fn2-ops-row-okp slot fn2-ops) (natp slot) (equal (nth slot (nth 1 fn2-ops)) 2))
           (fn2-ops-row-okp slot
             (update-nth 50 (+ -1 (nth 50 fn2-ops))
              (update-nth 48 (fn2-ring-next (nth 48 fn2-ops) (len (nth 45 fn2-ops)))
               (update-nth-array 1 slot (fn2-op-ack-phase (nth slot (nth 2 fn2-ops))) fn2-ops)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-ops-row-key-okp) (fn2-ops-row-okp))
           :use ((:instance fn2-ops-row-okp-idle-cells (i slot))
                 (:instance fn2-ops-row-okp-by-key (slot slot))
                 (:instance fn2-ops-row-okp-by-key (slot slot)
                            (fn2-ops (update-nth 50 (+ -1 (nth 50 fn2-ops))
                                      (update-nth 48 (fn2-ring-next (nth 48 fn2-ops) (len (nth 45 fn2-ops)))
                                       (update-nth-array 1 slot (fn2-op-ack-phase (nth slot (nth 2 fn2-ops)))
                                                         fn2-ops))))))))))
(local
(defthm fn2-ops-ack-step-rest
  (implies (and (fn2-ops-semanticp fn2-ops) (< 0 (nth 50 fn2-ops))
                (equal slot (nth (nth 48 fn2-ops) (nth 45 fn2-ops))))
           (fn2-ops-sem-rest slot
             (update-nth 50 (+ -1 (nth 50 fn2-ops))
              (update-nth 48 (fn2-ring-next (nth 48 fn2-ops) (len (nth 45 fn2-ops)))
               (update-nth-array 1 slot (fn2-op-ack-phase (nth slot (nth 2 fn2-ops))) fn2-ops)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-ops-sem-main fn2-ops-sem-facts fn2-op-ack-phase fn2-ops-sem-outring-part
                            fn2-ops-sem-counts-part fn2-ops-sem-refs-part fn2-ops-sem-free-part)
                           (fn2-ops-sem-rest fn2-ops-semanticp fn2-ops-sem-facts-of-semanticp fn2-ops-ring-next-is-mod))
           :use (fn2-ops-semanticp-elim
                 (:instance fn2-ops-sem-rest-split (s slot))
                 (:instance fn2-ops-sem-rest-split (s slot) (fn2-ops (update-nth 50 (+ -1 (nth 50 fn2-ops))
              (update-nth 48 (fn2-ring-next (nth 48 fn2-ops) (len (nth 45 fn2-ops)))
               (update-nth-array 1 slot (fn2-op-ack-phase (nth slot (nth 2 fn2-ops))) fn2-ops)))))
                 (:instance fn2-ops-sem-facts-of-semanticp (s slot))
                 (:instance fn2-ops-ring-shape-pop (cap (len (nth 45 fn2-ops))) (h (nth 48 fn2-ops))
                            (tl (nth 49 fn2-ops)) (c (nth 50 fn2-ops)))
                 (:instance fn2-ops-outbox-list-pop (cap (len (nth 45 fn2-ops))) (h (nth 48 fn2-ops))
                            (tl (nth 49 fn2-ops)) (c (nth 50 fn2-ops)))
                 (:instance fn2-ops-queued-refsp-car
                            (refs (fn2-ops-outbox-list-aux (nth 50 fn2-ops) (nth 48 fn2-ops) fn2-ops)))
                 (:instance fn2-ops-car-not-member-cdr
                            (l (fn2-ops-ref-slots (fn2-ops-outbox-list-aux (nth 50 fn2-ops) (nth 48 fn2-ops) fn2-ops))))
                 (:instance fn2-ops-same-members-pop
                            (c (fn2-ops-ref-slots (fn2-ops-outbox-list-aux (nth 50 fn2-ops) (nth 48 fn2-ops) fn2-ops)))
                            (f (fn2-ops-phase-slots (nth 44 fn2-ops) 2 fn2-ops))
                            (a slot)))))))
(local
(defthm fn2-ops-ack-step-slot
  (implies (and (fn2-ops-semanticp fn2-ops) (< 0 (nth 50 fn2-ops)))
           (and (natp (nth (nth 48 fn2-ops) (nth 45 fn2-ops)))
                (< (nth (nth 48 fn2-ops) (nth 45 fn2-ops)) (nth 44 fn2-ops))
                (equal (nth (nth (nth 48 fn2-ops) (nth 45 fn2-ops)) (nth 1 fn2-ops)) 2)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-ops-sem-rest fn2-ops-sem-facts) (fn2-ops-semanticp fn2-ops-sem-facts-of-semanticp))
           :use ((:instance fn2-ops-sem-facts-of-semanticp (s 0))
                 (:instance fn2-ops-outbox-list-pop (cap (len (nth 45 fn2-ops))) (h (nth 48 fn2-ops))
                            (tl (nth 49 fn2-ops)) (c (nth 50 fn2-ops)))
                 (:instance fn2-ops-queued-refsp-car
                            (refs (fn2-ops-outbox-list-aux (nth 50 fn2-ops) (nth 48 fn2-ops) fn2-ops))))))))
(local
(defthm fn2-ops-submit-prefix-one
  (implies (and (natp (nth 50 fn2-ops)) (< 0 (nth 50 fn2-ops)) (< (nth 48 fn2-ops) (len (nth 45 fn2-ops)))
                (< (len (nth 45 fn2-ops)) 4294967296)
                (natp (nth (nth 48 fn2-ops) (nth 45 fn2-ops)))
                (< (nth (nth 48 fn2-ops) (nth 45 fn2-ops)) (nth 44 fn2-ops)))
           (equal (fn2-outbox-submit-prefix 1 fn2-ops)
                  (let ((slot (nth (nth 48 fn2-ops) (nth 45 fn2-ops))))
                    (update-nth 50 (+ -1 (nth 50 fn2-ops))
                     (update-nth 48 (fn2-ring-next (nth 48 fn2-ops) (len (nth 45 fn2-ops)))
                      (update-nth-array 1 slot (fn2-op-ack-phase (nth slot (nth 2 fn2-ops))) fn2-ops))))))
  :hints (("Goal" :do-not-induct t
           :expand ((fn2-outbox-submit-prefix 1 fn2-ops) (:free (x) (fn2-outbox-submit-prefix 0 x)))
           :in-theory (enable fn2-op-slotp)))))
(local
(defthm fn2-ops-semanticp-out-ring
  (implies (and (fn2-ops-semanticp fn2-ops) (< 0 (nth 50 fn2-ops)))
           (and (natp (nth 50 fn2-ops)) (< (nth 48 fn2-ops) (len (nth 45 fn2-ops)))
                (< (len (nth 45 fn2-ops)) 4294967296)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-ops-semanticp fn2-ops-ring-shapep)))))
(local
(defthm fn2-ops-submit-prefix-step-conservation
  (implies (and (fn2-ops-semanticp fn2-ops) (< 0 (nth 50 fn2-ops)))
           (fn2-ops-semanticp (fn2-outbox-submit-prefix 1 fn2-ops)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-ops-sem-facts) (fn2-ops-semanticp fn2-ops-sem-facts-of-semanticp
                                                 fn2-ops-ack-step-rest fn2-ops-ack-step-row
                                                 fn2-outbox-submit-prefix-preserves-type
                                                 fn2-outbox-submit-prefix-preserves-wfp))
           :use (fn2-ops-semanticp-elim fn2-ops-ack-step-slot
                 (:instance fn2-ops-sem-facts-of-semanticp (s (nth (nth 48 fn2-ops) (nth 45 fn2-ops))))
                 (:instance fn2-ops-ack-step-rest (slot (nth (nth 48 fn2-ops) (nth 45 fn2-ops))))
                 (:instance fn2-ops-ack-step-row (slot (nth (nth 48 fn2-ops) (nth 45 fn2-ops))))
                 fn2-ops-semanticp-out-ring
                 (:instance fn2-outbox-submit-prefix-preserves-type (n 1))
                 (:instance fn2-outbox-submit-prefix-preserves-wfp (n 1))
                 (:instance fn2-ops-semanticp-intro (s (nth (nth 48 fn2-ops) (nth 45 fn2-ops)))
                            (fn2-ops (fn2-outbox-submit-prefix 1 fn2-ops))))))))
(local
(defthm fn2-ops-submit-prefix-split
  (implies (and (not (zp n)) (natp (nth 50 fn2-ops)) (< 0 (nth 50 fn2-ops)) (< (nth 48 fn2-ops) (len (nth 45 fn2-ops)))
                (< (len (nth 45 fn2-ops)) 4294967296)
                (natp (nth (nth 48 fn2-ops) (nth 45 fn2-ops)))
                (< (nth (nth 48 fn2-ops) (nth 45 fn2-ops)) (nth 44 fn2-ops)))
           (equal (fn2-outbox-submit-prefix n fn2-ops)
                  (fn2-outbox-submit-prefix (- n 1) (fn2-outbox-submit-prefix 1 fn2-ops))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((fn2-outbox-submit-prefix n fn2-ops) (fn2-outbox-submit-prefix 1 fn2-ops)
                    (:free (x) (fn2-outbox-submit-prefix 0 x)))
           :in-theory (enable fn2-op-slotp)))))
(local
(defun-nx fn2-ops-submit-ind (n x)
  (declare (xargs :measure (nfix n) :verify-guards nil))
  (if (or (zp n) (zp (nth 50 x)) (>= (nth 48 x) (len (nth 45 x)))
              (>= (len (nth 45 x)) 4294967296)
              (not (natp (nth (nth 48 x) (nth 45 x))))
              (not (< (nth (nth 48 x) (nth 45 x)) (nth 44 x))))
      x
    (let ((x (fn2-outbox-submit-prefix 1 x)))
      (fn2-ops-submit-ind (- n 1) x)))))
(local
(defthm fn2-ops-submit-prefix-stop
  (implies (or (zp n) (zp (nth 50 fn2-ops)) (>= (nth 48 fn2-ops) (len (nth 45 fn2-ops)))
              (>= (len (nth 45 fn2-ops)) 4294967296)
              (not (natp (nth (nth 48 fn2-ops) (nth 45 fn2-ops))))
              (not (< (nth (nth 48 fn2-ops) (nth 45 fn2-ops)) (nth 44 fn2-ops))))
           (equal (fn2-outbox-submit-prefix n fn2-ops) fn2-ops))
  :hints (("Goal" :do-not-induct t :expand ((fn2-outbox-submit-prefix n fn2-ops))
           :in-theory (enable fn2-op-slotp)))))
(defthm fn2-ops-submit-prefix-conservation
  (implies (fn2-ops-semanticp fn2-ops)
           (fn2-ops-semanticp (fn2-outbox-submit-prefix n fn2-ops)))
  :hints (("Goal" :induct (fn2-ops-submit-ind n fn2-ops)
           :in-theory (disable fn2-ops-semanticp fn2-ops-submit-prefix-one))
          ("Subgoal *1/2" :use (fn2-ops-submit-prefix-split fn2-ops-submit-prefix-step-conservation))))
(defthm fn2-outbox-ack-conservation
  (implies (fn2-ops-semanticp fn2-ops)
           (fn2-ops-semanticp (mv-nth 1 (fn2-outbox-ack n fn2-ops))))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (fn2-outbox-ack) (fn2-ops-semanticp)))))

;; Init: every row below ROWS is a cleared free row whose next link is the
;; following row, so the free chain is 0..ROWS-1 and every other class is empty.
(local
(defun fn2-ops-asc (x n)
  (declare (xargs :measure (nfix (- (nfix n) (nfix x))) :verify-guards nil))
  (if (or (not (natp x)) (not (natp n)) (>= x n)) nil
    (cons x (fn2-ops-asc (+ 1 x) n)))))
(local
(defthm fn2-ops-member-asc
  (iff (member-equal y (fn2-ops-asc x n))
       (and (natp x) (natp n) (natp y) (<= x y) (< y n)))))
(local
(defthm fn2-ops-no-dups-asc
  (no-duplicatesp-equal (fn2-ops-asc x n))))
(local
(defthm fn2-ops-len-asc
  (implies (and (natp x) (natp n) (<= x n)) (equal (len (fn2-ops-asc x n)) (- n x)))))
(local
(in-theory (disable fn2-ops-asc)))

(local
(defun fn2-ops-down-ind (m)
  (declare (xargs :verify-guards nil))
  (if (zp m) t (fn2-ops-down-ind (- m 1)))))
(local
(defthm fn2-ops-nth-of-init-rows-column
  (implies (and (natp k) (< k 44) (natp i) (natp slot) (natp (nth 44 q)))
           (equal (nth i (nth k (fn2-ops-init-rows slot g q)))
                  (if (and (<= slot i) (< i (nth 44 q)))
                      (fn2-ops-clear-val k g (if (< (+ 1 i) (nth 44 q)) (+ 1 i) *fn2-none*))
                    (nth i (nth k q)))))
  :hints (("Goal" :induct (fn2-ops-init-rows slot g q)
           :in-theory (enable fn2-ops-init-rows)))))
(local
(defthm fn2-ops-nth-of-init-rows-scalar
  (implies (and (natp k) (<= 44 k))
           (equal (nth k (fn2-ops-init-rows slot g q)) (nth k q)))
  :hints (("Goal" :induct (fn2-ops-init-rows slot g q)
           :in-theory (enable fn2-ops-init-rows)))))
(local
(defthm fn2-ops-car-of-init-rows
  (implies (and (natp i) (natp slot) (natp (nth 44 q)))
           (equal (nth i (car (fn2-ops-init-rows slot g q)))
                  (if (and (<= slot i) (< i (nth 44 q))) g (nth i (car q)))))
  :hints (("Goal" :use ((:instance fn2-ops-nth-of-init-rows-column (k 0)))
           :in-theory (disable fn2-ops-nth-of-init-rows-column)))))
(local
(in-theory (disable fn2-ops-clear-val)))

(local
(defthm fn2-ops-row-okp-of-init-rows
  (implies (and (natp i) (< i (nth 44 q)) (natp (nth 44 q)) (natp g) (<= g (nth 72 q)))
           (fn2-ops-row-okp i (fn2-ops-init-rows 0 g q)))
  :hints (("Goal" :use ((:instance fn2-ops-row-okp-by-key (slot i) (fn2-ops (fn2-ops-init-rows 0 g q))))
           :in-theory (enable fn2-ops-clear-val fn2-ops-row-key-okp)))))
(local
(defthm fn2-ops-row-semanticp-of-init-rows
  (implies (and (natp m) (<= m (nth 44 q)) (natp (nth 44 q)) (natp g) (<= g (nth 72 q)))
           (fn2-ops-row-semanticp m (fn2-ops-init-rows 0 g q)))
  :hints (("Goal" :induct (fn2-ops-down-ind m)
           :in-theory (enable fn2-ops-row-semanticp-step)))))
(local
(defthm fn2-ops-phase-slots-of-init-rows-nonfree
  (implies (and (natp m) (<= m (nth 44 q)) (natp (nth 44 q)) (not (equal ph 0)))
           (equal (fn2-ops-phase-slots m ph (fn2-ops-init-rows 0 g q)) nil))
  :hints (("Goal" :induct (fn2-ops-down-ind m)
           :in-theory (enable fn2-ops-phase-slots fn2-ops-clear-val)))))
(local
(defthm fn2-ops-len-phase-slots-of-init-rows-free
  (implies (and (natp m) (<= m (nth 44 q)) (natp (nth 44 q)))
           (equal (len (fn2-ops-phase-slots m 0 (fn2-ops-init-rows 0 g q))) m))
  :hints (("Goal" :induct (fn2-ops-down-ind m)
           :in-theory (enable fn2-ops-phase-slots fn2-ops-clear-val)))))
(local
(defthm fn2-ops-pending-of-init-rows
  (implies (and (natp m) (<= m (nth 44 q)) (natp (nth 44 q)))
           (equal (fn2-ops-pending-cells m (fn2-ops-init-rows 0 g q)) nil))
  :hints (("Goal" :induct (fn2-ops-down-ind m)
           :in-theory (enable fn2-ops-pending-cells fn2-ops-clear-val)))))

(local
(defun fn2-ops-init-chain-ind (f x n)
  (declare (xargs :measure (nfix f) :verify-guards nil))
  (if (or (zp f) (not (natp x)) (>= (+ 1 x) (nfix n))) (list f x n)
    (fn2-ops-init-chain-ind (- f 1) (+ 1 x) n))))
(local
(defthm fn2-ops-free-chain-of-init-rows
  (implies (and (natp x) (< x (nth 44 q)) (natp (nth 44 q)) (< (nth 44 q) 4294967296)
                (natp f) (<= (- (nth 44 q) x) f))
           (equal (fn2-ops-free-chain f x (fn2-ops-init-rows 0 g q))
                  (fn2-ops-asc x (nth 44 q))))
  :hints (("Goal" :induct (fn2-ops-init-chain-ind f x (nth 44 q))
           :in-theory (enable fn2-ops-free-chain fn2-op-slotp fn2-ops-clear-val)
           :expand ((fn2-ops-asc x (nth 44 q)) (fn2-ops-asc (+ 1 x) (nth 44 q))
                    (fn2-ops-free-chain f x (fn2-ops-init-rows 0 g q)))))))
(local
(defthm fn2-ops-asc-subsetp-free-of-init-rows
  (implies (and (natp x) (natp (nth 44 q)))
           (subsetp-equal (fn2-ops-asc x (nth 44 q))
                          (fn2-ops-phase-slots (nth 44 q) 0 (fn2-ops-init-rows 0 g q))))
  :hints (("Goal" :induct (fn2-ops-asc x (nth 44 q))
           :in-theory (enable fn2-ops-asc fn2-ops-clear-val)))))
(local
(defthm fn2-ops-phase-slots-subsetp-asc
  (implies (and (natp m) (natp n) (<= m n))
           (subsetp-equal (fn2-ops-phase-slots m ph q) (fn2-ops-asc 0 n)))
  :hints (("Goal" :induct (fn2-ops-down-ind m)
           :in-theory (enable fn2-ops-phase-slots)))))
(local
(defthm fn2-ops-not-bad-chain-asc
  (not (member-equal :bad-chain (fn2-ops-asc x n)))))

(local
(defthm fn2-ops-semanticp-of-init-rows
  (implies (and (fn2-opsp (fn2-ops-init-rows 0 g q)) (fn2-ops-wfp (fn2-ops-init-rows 0 g q))
                (natp (nth 44 q)) (< 0 (nth 44 q)) (< (nth 44 q) 4294967296) (natp g) (<= g (nth 72 q))
                (unsigned-byte-p 32 (len (nth 45 q))) (equal (len (nth 46 q)) (len (nth 45 q)))
                (equal (len (nth 47 q)) (* 2 (nth 44 q)))
                (equal (nth 48 q) 0) (equal (nth 49 q) 0) (equal (nth 50 q) 0) (equal (nth 51 q) 0)
                (equal (nth 52 q) 0) (equal (nth 53 q) 0) (equal (nth 54 q) 0)
                (equal (nth 70 q) 0) (equal (nth 71 q) (nth 44 q)) (equal (nth 73 q) 0))
           (fn2-ops-semanticp (fn2-ops-init-rows 0 g q)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-ops-semanticp fn2-ops-same-membersp fn2-ops-ring-shapep
                            fn2-ops-outbox-list fn2-ops-posted-list fn2-ops-outbox-list-aux fn2-ops-posted-list-aux)
                           (fn2-ops-init-rows))
           :use ((:instance fn2-ops-row-semanticp-of-init-rows (m (nth 44 q)))
                 (:instance fn2-ops-free-chain-of-init-rows (x 0) (f (nth 44 q)))
                 (:instance fn2-ops-asc-subsetp-free-of-init-rows (x 0))
                 (:instance fn2-ops-phase-slots-subsetp-asc (m (nth 44 q)) (n (nth 44 q)) (ph 0)
                            (q (fn2-ops-init-rows 0 g q))))))))
(defthm fn2-ops-init-conservation
  (implies (and (fn2-opsp fn2-ops) (fn2-profilep profile))
           (fn2-ops-semanticp (fn2-ops-init profile fn2-ops)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-ops-init) (fn2-ops-init-rows fn2-ops-semanticp))
           :use ((:instance fn2-ops-init-type (profile profile))
                 (:instance fn2-ops-init-wfp (profile profile))
                 (:instance fn2-ops-semanticp-of-init-rows
                            (g (fn2-profile-generation-start profile))
                            (q (let* ((n (fn2-profile-o profile)) (qa (fn2-profile-qa profile))
                                      (limit (fn2-profile-generation-limit profile))
                                      (fn2-ops (fn2-ops-columns-init n fn2-ops))
                                      (fn2-ops (resize-fn2-ops-out-slot qa fn2-ops))
                                      (fn2-ops (resize-fn2-ops-out-gen qa fn2-ops))
                                      (fn2-ops (resize-fn2-ops-posted-fifo (* 2 n) fn2-ops))
                                      (fn2-ops (update-fn2-ops-out-head 0 fn2-ops))
                                      (fn2-ops (update-fn2-ops-out-tail 0 fn2-ops))
                                      (fn2-ops (update-fn2-ops-queued 0 fn2-ops))
                                      (fn2-ops (update-fn2-ops-reserved-credits 0 fn2-ops))
                                      (fn2-ops (update-fn2-ops-post-head 0 fn2-ops))
                                      (fn2-ops (update-fn2-ops-post-tail 0 fn2-ops))
                                      (fn2-ops (update-fn2-ops-post-count 0 fn2-ops))
                                      (fn2-ops (update-fn2-ops-clock-posted 0 fn2-ops))
                                      (fn2-ops (update-fn2-ops-clock-seen 0 fn2-ops))
                                      (fn2-ops (update-fn2-ops-clock-mono 0 fn2-ops))
                                      (fn2-ops (update-fn2-ops-clock-real 0 fn2-ops))
                                      (fn2-ops (update-fn2-ops-clock-flags 0 fn2-ops))
                                      (fn2-ops (update-fn2-ops-clock-coalesced 0 fn2-ops))
                                      (fn2-ops (update-fn2-ops-clock-rejected 0 fn2-ops))
                                      (fn2-ops (update-fn2-ops-signals 0 fn2-ops))
                                      (fn2-ops (update-fn2-ops-stray 0 fn2-ops))
                                      (fn2-ops (update-fn2-ops-free-head (if (zp n) *fn2-none* 0) fn2-ops))
                                      (fn2-ops (update-fn2-ops-free-count n fn2-ops))
                                      (fn2-ops (update-fn2-ops-gen-limit limit fn2-ops))
                                      (fn2-ops (update-fn2-ops-retired-count 0 fn2-ops)))
                                 fn2-ops)))))))

;; Post-accept-result: fn2-post-result's terminal post, then the peer record
;; into the row's peer columns, which the invariant does not read.
(local
(defthm fn2-ops-semanticp-of-peer-put
  (let ((r (update-nth-array 32 slot w3 (update-nth-array 31 slot w2 (update-nth-array 30 slot w1
            (update-nth-array 29 slot w0 (update-nth-array 28 slot port
             (update-nth-array 27 slot family fn2-ops))))))))
    (implies (and (fn2-ops-semanticp fn2-ops) (natp slot) (fn2-opsp r) (fn2-ops-wfp r))
             (fn2-ops-semanticp r)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-ops-sem-facts) (fn2-ops-semanticp fn2-ops-sem-facts-of-semanticp))
           :use ((:instance fn2-ops-sem-facts-of-semanticp (s slot))
                 (:instance fn2-ops-semanticp-intro (s slot)
                            (fn2-ops (update-nth-array 32 slot w3 (update-nth-array 31 slot w2 (update-nth-array 30 slot w1
                                      (update-nth-array 29 slot w0 (update-nth-array 28 slot port
                                       (update-nth-array 27 slot family fn2-ops)))))))))))))
(defthm fn2-post-accept-result-conservation
  (implies (fn2-ops-semanticp fn2-ops)
           (fn2-ops-semanticp (fn2-post-accept-result slot gen outcome reason cap-index cap-nonce
                                                      family port w0 w1 w2 w3 fn2-ops)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-post-accept-result)
                           (fn2-post-result fn2-ops-semanticp fn2-count-stray
                            fn2-post-accept-result-preserves-type fn2-post-accept-result-preserves-wfp))
           :use (fn2-ops-semanticp-elim
                 fn2-post-accept-result-preserves-type fn2-post-accept-result-preserves-wfp
                 (:instance fn2-post-result-conservation (cell 0) (evkind *fn2-event-accept-result*) (count 0)
                            (aux0 cap-index) (aux1 cap-nonce))
                 (:instance fn2-ops-semanticp-of-peer-put
                            (fn2-ops (fn2-post-result 0 slot gen *fn2-event-accept-result* outcome reason 0
                                                      cap-index cap-nonce fn2-ops)))))))

;; FN2-OPS-CREDIT-CONSERVATION: the dispatcher's every operation.
(defthm fn2-ops-credit-conservation-proved
  (implies (fn2-ops-conservation-hyps op a p)
           (fn2-ops-conservation-conclusion op a p))
  :hints (("Goal" :in-theory (e/d (fn2-ops-conservation-hyps fn2-ops-conservation-conclusion fn2-ops-operation)
                                  (fn2-ops-semanticp fn2-ops-init fn2-op-reserve fn2-op-set-range
                                   fn2-op-set-capability fn2-op-set-storage fn2-op-set-cancel-target
                                   fn2-op-set-wake fn2-op-unreserve fn2-op-enqueue fn2-outbox-ack
                                   fn2-post-result fn2-harvest-next fn2-op-finish fn2-op-request-cancel
                                   fn2-post-clock fn2-take-clock fn2-post-signal fn2-take-signal
                                   fn2-outbox-peek fn2-post-accept-result)))))
(defthm fn2-ops-credit-conservation-statement
  (fn2-ops-credit-conservation$owed op a p)
  :hints (("Goal" :in-theory '(fn2-ops-credit-conservation$owed) :use fn2-ops-credit-conservation-proved)))
(fn2-owed-discharge fn2-ops-credit-conservation fn2-ops-credit-conservation-statement)
)
