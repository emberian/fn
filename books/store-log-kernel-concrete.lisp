; fn: the record log's kernel as the host holds it: COMMITTED as its length
; (lane per-record-state, 2026-09-27; D27).
;
; The logical kernel (books/store-log-kernel.lisp) is
;   (:lgk COMMITTED LAST FRONTIER NEXT-TXID BATCH INFLIGHT ACKED PHASE)
; and its relation R, the crash theorems and the programs speak of COMMITTED,
; the list of every record the durable segment scans to.  No transition the
; served path runs reads COMMITTED's elements: the fence appends to it, the
; acknowledgement compares ACKED with its length, and the open hands it to the
; replay once.  Held for the life of the process it cost 16 octets of conses
; per history octet (measured: 38.8 MB for 1,000 POSTs of 2 KiB, section 1 of
; planning/evidence/per-record-state-2026-09-27.md), and each fence copied it
; (an O(N) append per batch).
;
; The concrete kernel keeps the COUNT in COMMITTED's place:
;   (:lgc COUNT LAST FRONTIER NEXT-TXID BATCH INFLIGHT ACKED PHASE)
; `fn-lgc-of' is the abstraction (the logical kernel's COMMITTED replaced by
; its length, every other position copied), and every transition the host
; calls commutes with it, with no hypothesis:
;
;   (fn-lgc-T (fn-lgc-of ks) args) = (fn-lgc-of (fn-lgk-T ks args))
;
; for T in prepare (txid-checked), take, consume-to, append, fence,
; fence-failed, finish-one; the observers (frontier, next txid, last, acked,
; phase, append octets, fits, admits) answer what the logical ones answer.
; KEYSTONE `fn-lgc-run-refines-the-kernel': over ANY sequence of host
; operations, the concrete kernel reached from the open is fn-lgc-of the
; logical kernel reached from the recovered kernel, so every theorem over the
; logical run (R preserved by append and fence, the crash image a prefix) is a
; theorem about the kernel the host holds.  `fn-lgc-open' answers the scan's
; records (the replay's input, dropped by the host after the replay) and the
; concrete kernel of fn-lg-open-kernel.
;
; Host: host/native/io.lisp fnn-log-open-kernel calls fn-lgc-open; fnn-log-
; prepare fn-lgc-prepare; fnn-log-append fn-lgc-append-admitsp, fn-lgc-append-
; octets, fn-lgc-append; fnn-log-fence fn-lgc-fence / fn-lgc-fence-failed;
; fnn-log-finish fn-lgc-finish-one; fnn-log-take fn-lgc-take; the open's catch
; up fn-lgc-consume-to.  No skip-proofs.

(in-package "ACL2")
(include-book "store-log-route")
(include-book "store-log-segments")
(include-book "store-log-extend")

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
;; Its work is proof time no prover step counts (docs/proof-style.md
;; 9.1); planning/evidence/tau-cost-*.json has this book's figures.
(local (in-theory (disable (tau-system))))

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:rewrite fn-lgc-octets-true-listp))))

;; -----------------------------------------------------------------------------
;; The executable framing (lane kernel-concrete-2, PRF-282).  The logical
;; framing (books/store-log.lisp fn-lg-log, fn-lg-entry, fn-lg-frame,
;; fn-lg-pack, fn-lg-last-trailer) is not guard-verified, so the host ran it
;; as *1* code whose appends recurse once per octet of their first argument: a
;; 3 MiB article exhausted the owner's control stack (input-loop-2, record
;; section 6: fnn-log-ensure-extent -> fn-lgk-fitsp -> *1* fn-lg-log, 2.79 M
;; nested binary-append frames).  Here:
;;   fn-lgc-log-len       the log's length by arithmetic over the records'
;;                        lengths and the chain head's length, guard-verified,
;;                        equal to (len (fn-lg-log ...)) with NO hypothesis
;;                        (fn-lgc-log-len-is-the-log-length); no octet built;
;;   fn-lgx-*             guard-verified twins of the framing, each equal to
;;                        its logical function with no hypothesis (the raw
;;                        Lisp append, make-list, nthcdr: no per-octet stack);
;;   fn-lgc-log-octets,   guard T: the twin when the chain head is a digest and
;;   fn-lgc-last-trailer  the records the log's, else the logical function
;;                        (ec-call); equal to fn-lg-log / fn-lg-last-trailer.

(defun fn-lgc-chunk-body-len (chunk)
  (declare (xargs :guard t))
  (if (consp chunk)
      (if (consp (cdr chunk)) (fn-lg-pack-len chunk) (len (car chunk)))
    0))

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-lgc-first-loop (n xs acc)
  (declare (xargs :guard (and (natp n) (true-listp acc)) :verify-guards nil))
  (if (zp n)
      (revappend acc nil)
    (fn-lgc-first-loop (1- n)
                       (if (consp xs) (cdr xs) nil)
                       (cons (if (consp xs) (car xs) 0) acc))))

(defun fn-lgc-first (n xs)
  (declare (xargs :verify-guards nil :guard (natp n)))
  (mbe :logic
       (if (zp n) nil
         (cons (if (consp xs) (car xs) 0) (fn-lgc-first (1- n) (if (consp xs) (cdr xs) nil))))
       :exec (fn-lgc-first-loop n xs nil)))

(local
 (defthm fn-lgc-first-loop-is-revappend
   (equal (fn-lgc-first-loop n xs acc)
          (revappend acc (fn-lgc-first n xs)))
   :hints (("Goal" :induct (fn-lgc-first-loop n xs acc)
                   :in-theory (union-theories '(fn-lgc-first-loop fn-lgc-first revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-lgc-first-loop)

(verify-guards fn-lgc-first
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-lgc-first)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-lgc-first-loop-is-revappend (acc nil))))))


(defthm fn-lgc-first-is-take
  (equal (fn-lgc-first n xs) (fn-bs-take n xs)))

(defun fn-lgc-rest (n xs)
  (declare (xargs :guard (natp n)))
  (if (zp n) xs (fn-lgc-rest (1- n) (if (consp xs) (cdr xs) nil))))

(defthm fn-lgc-rest-is-nthcdr
  (equal (fn-lgc-rest n xs) (nthcdr n xs)))

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec adds onto an accumulator.
(defun fn-lgc-log-len-loop (records prevlen unit acc)
  (declare (xargs :measure (len records) :guard (and (natp prevlen) (acl2-numberp acc)) :verify-guards nil))
  (if (consp records)
      (let* ((k (fn-lg-chunk-len records))
             (f (+ 10
                   (nfix prevlen)
                   (fn-lgc-chunk-body-len (fn-lgc-first k records))
                   *fn-frame-trailer-octets*)))
        (fn-lgc-log-len-loop (mbe :logic
                                  (nthcdr k records)
                                  :exec
                                  (fn-lgc-rest k records))
                             *fn-frame-trailer-octets*
                             unit
                             (+ (+ f (fn-lg-pad-len f unit)) acc)))
    (+ acc 0)))

(defun fn-lgc-log-len (records prevlen unit)
  (declare (xargs :verify-guards nil :guard (natp prevlen) :measure (len records)
                  :hints (("Goal" :in-theory (enable fn-lg-chunk-len)))))
  (mbe :logic
       (if (consp records)
           (let* ((k (fn-lg-chunk-len records))
                  (f (+ 10 (nfix prevlen) (fn-lgc-chunk-body-len (fn-lgc-first k records))
                        *fn-frame-trailer-octets*)))
             (+ f (fn-lg-pad-len f unit)
                (fn-lgc-log-len (mbe :logic (nthcdr k records) :exec (fn-lgc-rest k records))
                                *fn-frame-trailer-octets* unit)))
         0)
       :exec (fn-lgc-log-len-loop records prevlen unit 0)))

(local
 (defthm fn-lgc-log-len-loop-is-plus
   (implies (acl2-numberp acc)
            (equal (fn-lgc-log-len-loop records prevlen unit acc)
                   (+ acc (fn-lgc-log-len records prevlen unit))))
   :hints (("Goal" :induct (fn-lgc-log-len-loop records prevlen unit acc)
                   :in-theory (disable fn-lg-chunk-len fn-lg-pad-len fn-lgc-chunk-body-len fn-lgc-first fn-lgc-rest)))))

(verify-guards fn-lgc-log-len-loop)

(verify-guards fn-lgc-log-len
  :hints (("Goal"
           :in-theory
           (disable fn-lgc-log-len-loop
                    fn-lg-chunk-len
                    fn-lg-pad-len
                    fn-lgc-chunk-body-len
                    fn-lgc-first
                    fn-lgc-rest)
           :use
           ((:instance fn-lgc-log-len-loop-is-plus (acc 0))))))


(defthm fn-lgc-len-of-frame
  (equal (len (fn-lg-frame prev chunk))
         (+ 10 (len prev) (fn-lgc-chunk-body-len chunk) *fn-frame-trailer-octets*))
  :hints (("Goal" :in-theory (enable fn-lg-frame fn-lg-frame-body fn-frame-seal fn-frame-encode
                                     fn-frame-protected fn-frame-header))))


(defthm fn-lgc-len-of-entry
  (equal (len (fn-lg-entry prev chunk unit))
         (let ((f (+ 10 (len prev) (fn-lgc-chunk-body-len chunk) *fn-frame-trailer-octets*)))
           (+ f (fn-lg-pad-len f unit))))
  :hints (("Goal" :in-theory (e/d (fn-lg-entry) (fn-lg-frame fn-lg-pad-len)))))

(defthm fn-lgc-len-of-trailer-of-frame
  (equal (len (fn-lg-trailer (fn-lg-frame prev chunk))) *fn-frame-trailer-octets*)
  :hints (("Goal" :in-theory (e/d (fn-lg-trailer) (fn-lg-frame)))))

(defthm fn-lgc-log-len-is-the-log-length
  (equal (len (fn-lg-log records prev unit))
         (fn-lgc-log-len records (len prev) unit))
  :hints (("Goal" :induct (fn-lg-log records prev unit)
           :in-theory (e/d (fn-lg-log-unfolds) (fn-lg-entry fn-lg-frame fn-lg-trailer fn-lg-pad-len
                                               (:definition fn-lg-log) fn-lgc-chunk-body-len)))
          ("Subgoal *1/2" :expand ((fn-lg-log records prev unit)))))

(defun fn-lgx-zeros (n)
  (declare (xargs :guard (natp n) :verify-guards nil))
  (mbe :logic (fn-bs-zeros n) :exec (make-list n :initial-element 0)))

(defthm fn-lgx-zeros-cons-zero
  (equal (append (fn-bs-zeros n) (cons 0 acc)) (cons 0 (append (fn-bs-zeros n) acc)))
  :hints (("Goal" :induct (fn-bs-zeros n))))

(defthm fn-lgx-make-list-ac-is-zeros
  (equal (make-list-ac n 0 acc) (append (fn-bs-zeros n) acc))
  :hints (("Goal" :induct (make-list-ac n 0 acc))))

(defthm fn-lgx-zeros-true-listp (true-listp (fn-bs-zeros n)))

(verify-guards fn-lgx-zeros)

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-lgx-pack-loop (records acc)
  (declare (xargs :guard (and (fn-lg-recordsp records *fn-frame-max-payload*) (true-listp acc)) :verify-guards nil))
  (if (consp records)
      (fn-lgx-pack-loop (cdr records)
                        (fn-ag-rev-onto (true-list-fix (car records))
                                        (fn-ag-rev-onto (fn-cbor-u32-bytes (len (car records)))
                                                        acc)))
    (revappend acc nil)))

(defun fn-lgx-pack (records)
  (declare (xargs :verify-guards nil :guard (fn-lg-recordsp records *fn-frame-max-payload*)
                  :guard-hints (("Goal" :in-theory (enable fn-lg-recordp)))))
  (mbe :logic
       (if (consp records)
           (append (fn-cbor-u32-bytes (len (car records)))
                   (append (true-list-fix (car records)) (fn-lgx-pack (cdr records))))
         nil)
       :exec (fn-lgx-pack-loop records nil)))

(local
 (defthm fn-lgx-pack-loop-rev-onto-append
   (equal (revappend (fn-ag-rev-onto x acc) y)
          (revappend acc (append x y)))))

(local
 (defthm fn-lgx-pack-loop-is-revappend
   (equal (fn-lgx-pack-loop records acc)
          (revappend acc (fn-lgx-pack records)))
   :hints (("Goal" :induct (fn-lgx-pack-loop records acc)
                   :in-theory (union-theories '(fn-lgx-pack-loop fn-lgx-pack revappend car-cons cdr-cons fn-lgx-pack-loop-rev-onto-append)
                                              (theory 'minimal-theory))))))

(verify-guards fn-lgx-pack-loop
  :hints (("Goal" :in-theory (enable fn-lg-recordp))))

(verify-guards fn-lgx-pack
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-lgx-pack)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-lgx-pack-loop-is-revappend (acc nil))))))


(defthm fn-lgx-pack-is-pack
  (equal (fn-lgx-pack records) (fn-lg-pack records))
  :hints (("Goal" :in-theory (enable fn-lg-pack))))

(defun fn-lgx-frame-body (chunk)
  (declare (xargs :guard (fn-lg-recordsp chunk *fn-frame-max-payload*)))
  (if (and (consp chunk) (consp (cdr chunk))) (fn-lgx-pack chunk) (car chunk)))

(defthm fn-lgx-frame-body-is-frame-body
  (equal (fn-lgx-frame-body chunk) (fn-lg-frame-body chunk))
  :hints (("Goal" :in-theory (enable fn-lg-frame-body))))

(defthm fn-lgx-chunkp-recordsp
  (implies (fn-lg-chunkp chunk max) (fn-lg-recordsp chunk max))
  :rule-classes :forward-chaining)

(defun fn-lgx-frame (prev chunk)
  (declare (xargs :guard (and (fn-frame-digestp prev)
                              (fn-lg-chunkp chunk *fn-frame-max-payload*))
                  :guard-hints (("Goal" :in-theory (e/d (fn-frame-digestp) (fn-lg-chunkp fn-lg-frame-body))
                                 :use ((:instance fn-lg-chunk-body-octets (max *fn-frame-max-payload*))
                                       (:instance fn-lg-chunk-body-bound (max *fn-frame-max-payload*)))))))
  (fn-frame-seal *fn-lg-magic* *fn-lg-version* (fn-lg-frame-kind chunk)
                 (append prev (fn-lgx-frame-body chunk))))

(defthm fn-lgx-frame-is-frame
  (equal (fn-lgx-frame prev chunk) (fn-lg-frame prev chunk))
  :hints (("Goal" :in-theory (enable fn-lg-frame))))

(defthm fn-lgx-true-listp-of-seal
  (true-listp (fn-frame-seal magic version kind payload))
  :hints (("Goal" :in-theory (enable fn-frame-seal fn-frame-encode fn-frame-protected fn-frame-header)
           :use ((:instance fn-frame-digest-octet-listp
                  (octets (fn-frame-protected magic version kind payload)))))))

(defun fn-lgx-trailer (frame)
  (declare (xargs :guard (true-listp frame)))
  (nthcdr (nfix (- (len frame) *fn-frame-trailer-octets*)) frame))

(defthm fn-lgx-trailer-is-trailer
  (equal (fn-lgx-trailer frame) (fn-lg-trailer frame))
  :hints (("Goal" :in-theory (enable fn-lg-trailer))))

(defun fn-lgx-entry (prev chunk unit)
  (declare (xargs :guard (and (fn-frame-digestp prev)
                              (fn-lg-chunkp chunk *fn-frame-max-payload*))
                  :guard-hints (("Goal" :in-theory (disable fn-lgx-frame fn-lg-chunkp fn-frame-digestp)))))
  (let ((frame (fn-lgx-frame prev chunk)))
    (append frame (fn-lgx-zeros (fn-lg-pad-len (len frame) unit)))))

(defthm fn-lgx-entry-is-entry
  (equal (fn-lgx-entry prev chunk unit) (fn-lg-entry prev chunk unit))
  :hints (("Goal" :in-theory (enable fn-lg-entry))))

(defthm fn-lgx-true-listp-of-frame
  (true-listp (fn-lg-frame prev chunk))
  :hints (("Goal" :in-theory (enable fn-lg-frame))))

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-lgx-log-loop (records prev unit acc)
  (declare (xargs :measure (len records) :guard (and (and (fn-frame-digestp prev) (fn-lg-recordsp records *fn-frame-max-payload*)) (true-listp acc)) :verify-guards nil))
  (if (consp records)
      (let* ((k (fn-lg-chunk-len records))
             (chunk (fn-lgc-first k records)))
        (fn-lgx-log-loop (mbe :logic (nthcdr k records) :exec (fn-lgc-rest k records))
                         (fn-lgx-trailer (fn-lgx-frame prev chunk))
                         unit
                         (fn-ag-rev-onto (fn-lgx-entry prev chunk unit) acc)))
    (revappend acc nil)))

(defun fn-lgx-log (records prev unit)
  (declare (xargs :guard (and (fn-frame-digestp prev)
                              (fn-lg-recordsp records *fn-frame-max-payload*))
                  :measure (len records)
                  :hints (("Goal" :in-theory (enable fn-lg-chunk-len)))
                  :verify-guards nil))
  (mbe :logic
       (if (consp records)
           (let* ((k (fn-lg-chunk-len records))
                  (chunk (fn-lgc-first k records)))
             (append (fn-lgx-entry prev chunk unit)
                     (fn-lgx-log (mbe :logic (nthcdr k records) :exec (fn-lgc-rest k records))
                                 (fn-lgx-trailer (fn-lgx-frame prev chunk))
                                 unit)))
         nil)
       :exec (fn-lgx-log-loop records prev unit nil)))

(local
 (defthm fn-lgx-log-loop-rev-onto-append
   (equal (revappend (fn-ag-rev-onto x acc) y)
          (revappend acc (append x y)))))

(local
 (defthm fn-lgx-log-loop-is-revappend
   (equal (fn-lgx-log-loop records prev unit acc)
          (revappend acc (fn-lgx-log records prev unit)))
   :hints (("Goal" :induct (fn-lgx-log-loop records prev unit acc)
                   :in-theory (union-theories '(fn-lgx-log-loop fn-lgx-log revappend car-cons cdr-cons fn-lgx-log-loop-rev-onto-append)
                                              (theory 'minimal-theory))))))


(defthm fn-lgx-log-is-log
  (equal (fn-lgx-log records prev unit) (fn-lg-log records prev unit))
  :hints (("Goal" :induct (fn-lgx-log records prev unit)
           :in-theory (e/d (fn-lg-log-unfolds) (fn-lgx-entry fn-lgx-frame fn-lgx-trailer
                                               fn-lg-entry fn-lg-frame fn-lg-trailer
                                               (:definition fn-lg-log))))
          ("Subgoal *1/2" :expand ((fn-lg-log records prev unit)))))

(defthm fn-lgx-true-listp-of-entry
  (true-listp (fn-lg-entry prev chunk unit))
  :hints (("Goal" :in-theory (enable fn-lg-entry))))

(verify-guards fn-lgx-log-loop
  :hints (("Goal"
           :in-theory
           (disable fn-lgx-entry
                    fn-lgx-frame
                    fn-lgx-trailer
                    fn-lg-chunkp
                    fn-frame-digestp
                    fn-lg-recordsp
                    fn-lg-entry
                    fn-lg-frame
                    fn-lg-trailer)
           :use
           ((:instance fn-lg-chunkp-of-first-chunk (max *fn-frame-max-payload*))
            (:instance fn-lg-recordsp-of-nthcdr
                       (max *fn-frame-max-payload*)
                       (k (fn-lg-chunk-len records)))
            (:instance fn-lg-trailer-of-frame-digestp
                       (max *fn-frame-max-payload*)
                       (chunk (fn-bs-take (fn-lg-chunk-len records) records)))))))

(verify-guards fn-lgx-log
  :hints (("Goal"
           :in-theory
           (disable fn-lgx-entry
                    fn-lgx-frame
                    fn-lgx-trailer
                    fn-lg-chunkp
                    fn-frame-digestp
                    fn-lg-recordsp
                    fn-lg-entry
                    fn-lg-frame
                    fn-lg-trailer)
           :use
           ((:instance fn-lgx-log-loop-is-revappend (acc nil))
            (:instance fn-lg-chunkp-of-first-chunk (max *fn-frame-max-payload*))
            (:instance fn-lg-recordsp-of-nthcdr
                       (max *fn-frame-max-payload*)
                       (k (fn-lg-chunk-len records)))
            (:instance fn-lg-trailer-of-frame-digestp
                       (max *fn-frame-max-payload*)
                       (chunk (fn-bs-take (fn-lg-chunk-len records) records)))))))

(defun fn-lgx-last-trailer (records prev)
  (declare (xargs :guard (and (fn-frame-digestp prev)
                              (fn-lg-recordsp records *fn-frame-max-payload*))
                  :measure (len records)
                  :hints (("Goal" :in-theory (enable fn-lg-chunk-len)))
                  :verify-guards nil))
  (if (consp records)
      (let ((k (fn-lg-chunk-len records)))
        (fn-lgx-last-trailer (mbe :logic (nthcdr k records) :exec (fn-lgc-rest k records))
                             (fn-lgx-trailer (fn-lgx-frame prev (fn-lgc-first k records)))))
    prev))

(defthm fn-lgx-last-trailer-is-last-trailer
  (equal (fn-lgx-last-trailer records prev) (fn-lg-last-trailer records prev))
  :hints (("Goal" :induct (fn-lgx-last-trailer records prev)
           :in-theory (e/d (fn-lg-last-trailer-unfolds)
                           (fn-lgx-frame fn-lgx-trailer fn-lg-frame fn-lg-trailer
                            (:definition fn-lg-last-trailer))))
          ("Subgoal *1/2" :expand ((fn-lg-last-trailer records prev)))))

(verify-guards fn-lgx-last-trailer
  :hints (("Goal" :in-theory (disable fn-lgx-frame fn-lgx-trailer fn-lg-chunkp
                                      fn-frame-digestp fn-lg-recordsp fn-lg-frame fn-lg-trailer)
           :use ((:instance fn-lg-chunkp-of-first-chunk (max *fn-frame-max-payload*))
                 (:instance fn-lg-recordsp-of-nthcdr (max *fn-frame-max-payload*)
                            (k (fn-lg-chunk-len records)))
                 (:instance fn-lg-trailer-of-frame-digestp (max *fn-frame-max-payload*)
                            (chunk (fn-bs-take (fn-lg-chunk-len records) records)))))))

; The host's framing: the guard-verified twin when the chain head is a digest
; and the records are the log's, else the logical definition.
(defun fn-lgc-log-octets (records prev unit)
  (declare (xargs :guard t))
  (if (and (fn-frame-digestp prev) (fn-lg-recordsp records *fn-frame-max-payload*))
      (fn-lgx-log records prev unit)
    (ec-call (fn-lg-log records prev unit))))

(defthm fn-lgc-log-octets-is-log
  (equal (fn-lgc-log-octets records prev unit) (fn-lg-log records prev unit)))

(defun fn-lgc-last-trailer (records prev)
  (declare (xargs :guard t))
  (if (and (fn-frame-digestp prev) (fn-lg-recordsp records *fn-frame-max-payload*))
      (fn-lgx-last-trailer records prev)
    (ec-call (fn-lg-last-trailer records prev))))

(defthm fn-lgc-last-trailer-is-last-trailer
  (equal (fn-lgc-last-trailer records prev) (fn-lg-last-trailer records prev)))

(in-theory (disable fn-lgc-log-len fn-lgc-log-octets fn-lgc-last-trailer))

; -----------------------------------------------------------------------------
; The concrete state.

(defun fn-lgc-make (count last frontier next-txid batch inflight acked phase)
  (declare (xargs :guard t))
  (list :lgc count last frontier next-txid batch inflight acked phase))

(defun fn-lgc-count (c) (declare (xargs :guard (true-listp c))) (nfix (nth 1 c)))
(defun fn-lgc-last (c) (declare (xargs :guard (true-listp c))) (nth 2 c))
(defun fn-lgc-frontier (c) (declare (xargs :guard (true-listp c))) (nfix (nth 3 c)))
(defun fn-lgc-next-txid (c) (declare (xargs :guard (true-listp c))) (nfix (nth 4 c)))
(defun fn-lgc-batch (c) (declare (xargs :guard (true-listp c))) (nth 5 c))
(defun fn-lgc-inflight (c) (declare (xargs :guard (true-listp c))) (nth 6 c))
(defun fn-lgc-acked (c) (declare (xargs :guard (true-listp c))) (nfix (nth 7 c)))
(defun fn-lgc-phase (c) (declare (xargs :guard (true-listp c))) (nth 8 c))

; The abstraction: COMMITTED replaced by its length.
(defun fn-lgc-of (ks)
  (declare (xargs :guard (true-listp ks)))
  (fn-lgc-make (len (fn-lgk-committed ks)) (fn-lgk-last ks) (fn-lgk-frontier ks)
               (fn-lgk-next-txid ks) (fn-lgk-batch ks) (fn-lgk-inflight ks)
               (fn-lgk-acked ks) (fn-lgk-phase ks)))

; -----------------------------------------------------------------------------
; The transitions, each the logical one with COMMITTED's length in its place.

(defun fn-lgc-prepare (c record)
  (declare (xargs :guard (true-listp c)))
  (if (equal (fn-lgc-phase c) :fault)
      c
    (fn-lgc-make (fn-lgc-count c) (fn-lgc-last c) (fn-lgc-frontier c)
                 (1+ (fn-lgc-next-txid c))
                 (append (true-list-fix (fn-lgc-batch c)) (list record))
                 (fn-lgc-inflight c) (fn-lgc-acked c) (fn-lgc-phase c))))

; fn-lgt-prepare's txid check (the host's prepare).
(defun fn-lgc-t-prepare (c record)
  (declare (xargs :guard (true-listp c)))
  (if (equal (fn-lgt-txid record) (fn-lgc-next-txid c))
      (fn-lgc-prepare c record)
    c))

; The append's octets: the open batch's chained entries from LAST (the
; guard-verified framing).
(defun fn-lgc-append-octets (c unit)
  (declare (xargs :guard (true-listp c)))
  (fn-lgc-log-octets (fn-lgc-batch c) (fn-lgc-last c) unit))

; The append's length, by arithmetic (no octet is built): the open batch's
; log from a chain head of LAST's length.
(defun fn-lgc-append-len (c unit)
  (declare (xargs :guard (true-listp c)))
  (fn-lgc-log-len (fn-lgc-batch c) (len (fn-lgc-last c)) unit))

(defun fn-lgc-fitsp (c unit extent)
  (declare (xargs :guard (true-listp c)))
  (<= (+ (fn-lgc-frontier c) (fn-lgc-append-len c unit)) (nfix extent)))

(defun fn-lgc-append-admitsp (c unit extent)
  (declare (xargs :guard (true-listp c)))
  (and (not (consp (fn-lgc-inflight c)))
       (not (equal (fn-lgc-phase c) :fault))
       (fn-lgc-fitsp c unit extent)))

(defun fn-lgc-append (c unit extent)
  (declare (xargs :guard (true-listp c)))
  (if (or (consp (fn-lgc-inflight c)) (equal (fn-lgc-phase c) :fault)
          (not (fn-lgc-fitsp c unit extent)))
      c
    (fn-lgc-make (fn-lgc-count c) (fn-lgc-last c) (fn-lgc-frontier c)
                 (fn-lgc-next-txid c) nil (true-list-fix (fn-lgc-batch c))
                 (fn-lgc-acked c) :appended)))

; The barrier returned :ok: the count grows by the batch in flight; nothing
; is copied, and the frontier moves by the in-flight log's length computed
; without its octets.
(defun fn-lgc-fence (c unit)
  (declare (xargs :guard (true-listp c)))
  (let ((w (fn-lgc-log-len (fn-lgc-inflight c) (len (fn-lgc-last c)) unit)))
    (fn-lgc-make (+ (fn-lgc-count c) (len (fn-lgc-inflight c)))
                 (fn-lgc-last-trailer (fn-lgc-inflight c) (fn-lgc-last c))
                 (+ (fn-lgc-frontier c) w)
                 (fn-lgc-next-txid c) (fn-lgc-batch c) nil
                 (fn-lgc-acked c) :fenced)))

(defun fn-lgc-fence-failed (c)
  (declare (xargs :guard (true-listp c)))
  (fn-lgc-make (fn-lgc-count c) (fn-lgc-last c) (fn-lgc-frontier c)
               (fn-lgc-next-txid c) (fn-lgc-batch c) (fn-lgc-inflight c)
               (fn-lgc-acked c) :fault))

(defun fn-lgc-finish-one (c)
  (declare (xargs :guard (true-listp c)))
  (if (< (fn-lgc-acked c) (fn-lgc-count c))
      (fn-lgc-make (fn-lgc-count c) (fn-lgc-last c) (fn-lgc-frontier c)
                   (fn-lgc-next-txid c) (fn-lgc-batch c) (fn-lgc-inflight c)
                   (1+ (fn-lgc-acked c)) (fn-lgc-phase c))
    c))

(defun fn-lgc-consume-to (c txid)
  (declare (xargs :guard (true-listp c)))
  (if (and (natp txid) (< (fn-lgc-next-txid c) txid))
      (fn-lgc-make (fn-lgc-count c) (fn-lgc-last c) (fn-lgc-frontier c)
                   txid (fn-lgc-batch c) (fn-lgc-inflight c)
                   (fn-lgc-acked c) (fn-lgc-phase c))
    c))

(defun fn-lgc-take (c record txid count octets bmax omax unit)
  (declare (xargs :guard (true-listp c)))
  (let ((entry (fn-olr-entry-octets (len record) unit)))
    (cond ((and (posp count)
                (or (<= (nfix bmax) count)
                    (< (nfix omax) (+ (nfix octets) entry))))
           (list :full c entry))
          ((and (natp txid) (equal txid (fn-lgc-next-txid c))
                (not (equal (fn-lgc-phase c) :fault)))
           (list :taken (fn-lgc-prepare c record) entry))
          (t (list :refused c entry)))))

; The segment rotation (books/store-log-segments.lisp; host fnn-log-rotate):
; admitted when nothing is open, in flight or unacknowledged; needed when the
; active segment holds a record; the new segment's kernel keeps the chain head
; and the txid.
(defun fn-lgc-rotate-admitsp (c)
  (declare (xargs :guard (true-listp c)))
  (and (atom (fn-lgc-batch c))
       (atom (fn-lgc-inflight c))
       (equal (fn-lgc-acked c) (fn-lgc-count c))
       (not (equal (fn-lgc-phase c) :fault))))

(defun fn-lgc-rotate-needed-p (c)
  (declare (xargs :guard (true-listp c)))
  (< 0 (fn-lgc-count c)))

; The rotation entry that heads the new segment K (lane store-lineage,
; books/store-log.lisp fn-lg-rotation-entry; books/store-log-lineage.lisp),
; executably: the frame over the closed segment's last trailer and K, padded
; to the unit.  fn-lgc-rotation-octets is what the host writes at offset 0 of
; the new segment (fnn-log-rotate, cut rotate-headed; the open's completion of
; an unheaded segment, fnn-log-head-segment).
(defun fn-lgx-rotation-frame (prev k)
  (declare (xargs :guard (and (fn-frame-digestp prev) (fn-lg-rotation-indexp k))
                  :guard-hints (("Goal" :in-theory (e/d (fn-frame-digestp) (fn-cbor-u32-bytes))
                                 :use ((:instance fn-lg-rotation-payload-octets))))))
  (fn-frame-seal *fn-lg-magic* *fn-lg-version* *fn-lg-rotation-kind*
                 (append prev (fn-cbor-u32-bytes k))))

(defthm fn-lgx-rotation-frame-is-frame
  (equal (fn-lgx-rotation-frame prev k) (fn-lg-rotation-frame prev k))
  :hints (("Goal" :in-theory (enable fn-lg-rotation-frame))))

(defthm fn-lgx-rotation-frame-true-listp
  (true-listp (fn-lgx-rotation-frame prev k)))

(defun fn-lgx-rotation-entry (prev k unit)
  (declare (xargs :guard (and (fn-frame-digestp prev) (fn-lg-rotation-indexp k) (natp unit))
                  :guard-hints (("Goal" :in-theory (disable fn-lgx-rotation-frame fn-frame-digestp
                                                            fn-lg-rotation-indexp)))))
  (let ((frame (fn-lgx-rotation-frame prev k)))
    (append frame (fn-lgx-zeros (fn-lg-pad-len (len frame) unit)))))

(defthm fn-lgx-rotation-entry-is-entry
  (equal (fn-lgx-rotation-entry prev k unit) (fn-lg-rotation-entry prev k unit))
  :hints (("Goal" :in-theory (e/d (fn-lg-rotation-entry) (fn-lgx-rotation-frame fn-lg-rotation-frame)))))

(in-theory (disable fn-lgx-rotation-frame fn-lgx-rotation-entry))

(defun fn-lgc-rotation-octets (c k unit)
  (declare (xargs :guard (and (true-listp c) (fn-frame-digestp (fn-lgc-last c))
                              (fn-lg-rotation-indexp k) (natp unit))))
  (fn-lgx-rotation-entry (fn-lgc-last c) k unit))

; The new segment's kernel: no record, the frontier past the head, LAST the
; head's trailer (the F row's genesis for the segment), the txid carried.
(defun fn-lgc-rotate (c k unit)
  (declare (xargs :guard (and (true-listp c) (fn-frame-digestp (fn-lgc-last c))
                              (fn-lg-rotation-indexp k) (natp unit))))
  (fn-lgc-make 0 (fn-lgx-trailer (fn-lgx-rotation-frame (fn-lgc-last c) k))
               (len (fn-lgx-rotation-entry (fn-lgc-last c) k unit))
               (fn-lgc-next-txid c) nil nil 0 :ready))

;; The segment's extension before a seal (books/store-log-extend.lisp
;; fn-lg-extend-program; host fnn-log-ensure-extent, lane log-2): needed when
;; the open batch's append and one spare unit do not fit the extent, and then
;; grown to ACL2's target.  Both read the frontier and the append's length.
(defun fn-lgc-extension-needed-p (c extent unit)
  (declare (xargs :guard (true-listp c)))
  (fn-olr-extension-needed-p (fn-lgc-frontier c) (fn-lgc-append-len c unit) extent unit))

(defun fn-lgc-extension-target (c extent unit)
  (declare (xargs :guard (true-listp c)))
  (fn-olr-extension-target (fn-lgc-frontier c) (fn-lgc-append-len c unit) extent unit))

; The extent the seal appends into: the extension's target when one is
; needed, else the extent (host fnn-log-seal-open-batch and
; fnn-log-commit-open-batch: fnn-log-ensure-extent, then fnn-log-append).
(defun fn-lgc-sealed-extent (c extent unit)
  (declare (xargs :guard (true-listp c)))
  (if (fn-lgc-extension-needed-p c extent unit)
      (fn-lgc-extension-target c extent unit)
    extent))

; The open: the scan's records (the replay's input) and the concrete kernel.
(defun fn-lgc-open (s genesis unit max floor)
  (declare (xargs :guard (stringp s) :verify-guards nil))
  (mv-let (records consumed last) (fn-lg-decode s genesis unit max)
    (mv records
        (fn-lgc-make (len records) last (nfix consumed) (fn-lgt-next-after records floor)
                     nil nil (len records) :ready))))

; -----------------------------------------------------------------------------
; Refinement: each transition commutes with the abstraction.

(local (in-theory (disable fn-lg-log fn-lg-last-trailer fn-lg-decode
                            fn-lg-open-kernel-is-the-recovered-kernel)))

(local
 (defthm fn-lgc-len-true-list-fix
   (equal (len (true-list-fix x)) (len x))))

(local
 (defthm fn-lgc-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(defthm fn-lgc-observers-of-abstraction
  (and (equal (fn-lgc-count (fn-lgc-of ks)) (len (fn-lgk-committed ks)))
       (equal (fn-lgc-last (fn-lgc-of ks)) (fn-lgk-last ks))
       (equal (fn-lgc-frontier (fn-lgc-of ks)) (fn-lgk-frontier ks))
       (equal (fn-lgc-next-txid (fn-lgc-of ks)) (fn-lgk-next-txid ks))
       (equal (fn-lgc-batch (fn-lgc-of ks)) (fn-lgk-batch ks))
       (equal (fn-lgc-inflight (fn-lgc-of ks)) (fn-lgk-inflight ks))
       (equal (fn-lgc-acked (fn-lgc-of ks)) (fn-lgk-acked ks))
       (equal (fn-lgc-phase (fn-lgc-of ks)) (fn-lgk-phase ks))))

(defthm fn-lgc-append-octets-of-abstraction
  (equal (fn-lgc-append-octets (fn-lgc-of ks) unit) (fn-lgk-append-octets ks unit)))

(defthm fn-lgc-fitsp-of-abstraction
  (equal (fn-lgc-fitsp (fn-lgc-of ks) unit extent) (fn-lgk-fitsp ks unit extent)))

(defthm fn-lgc-append-admitsp-of-abstraction
  (equal (fn-lgc-append-admitsp (fn-lgc-of ks) unit extent)
         (fn-lg-append-admitsp ks unit extent)))

; The extension's decision over the logical kernel: the frontier and the
; length of the append the kernel would write (fn-lgk-append-octets).
(defun fn-lgk-sealed-extent (ks extent unit)
  (declare (xargs :guard (true-listp ks) :verify-guards nil))
  (let ((octets (len (fn-lgk-append-octets ks unit))))
    (if (fn-olr-extension-needed-p (fn-lgk-frontier ks) octets extent unit)
        (fn-olr-extension-target (fn-lgk-frontier ks) octets extent unit)
      extent)))

(defthm fn-lgc-append-len-of-abstraction
  (equal (fn-lgc-append-len (fn-lgc-of ks) unit) (len (fn-lgk-append-octets ks unit)))
  :hints (("Goal" :in-theory (disable fn-lgc-log-len fn-lg-log))))

(defthm fn-lgc-extension-needed-p-of-abstraction
  (equal (fn-lgc-extension-needed-p (fn-lgc-of ks) extent unit)
         (fn-olr-extension-needed-p (fn-lgk-frontier ks) (len (fn-lgk-append-octets ks unit))
                                    extent unit))
  :hints (("Goal" :in-theory (disable fn-olr-extension-needed-p fn-lgc-append-len fn-lgc-of
                                      fn-lgk-append-octets))))

(defthm fn-lgc-extension-target-of-abstraction
  (equal (fn-lgc-extension-target (fn-lgc-of ks) extent unit)
         (fn-olr-extension-target (fn-lgk-frontier ks) (len (fn-lgk-append-octets ks unit))
                                  extent unit))
  :hints (("Goal" :in-theory (disable fn-olr-extension-target fn-lgc-append-len fn-lgc-of
                                      fn-lgk-append-octets))))

(defthm fn-lgc-sealed-extent-of-abstraction
  (equal (fn-lgc-sealed-extent (fn-lgc-of ks) extent unit)
         (fn-lgk-sealed-extent ks extent unit))
  :hints (("Goal" :in-theory (disable fn-olr-extension-target fn-olr-extension-needed-p
                                      fn-lgc-extension-needed-p fn-lgc-extension-target
                                      fn-lgk-append-octets fn-lgc-of))))

(defthm fn-lgc-of-make
  (equal (fn-lgc-of (fn-lgk-make cm l f n b i a p))
         (fn-lgc-make (len cm) l (nfix f) (nfix n) b i (nfix a) p)))

(local
 (defthm fn-lgc-committed-of-lgk-make
   (equal (nth 1 (fn-lgk-make cm l f n b i a p)) cm)))

; The transitions below are proved at the field level: the abstraction and
; the constructors closed, the observers and fn-lgc-of-make rewriting.
(local (in-theory (disable fn-lgc-of fn-lgc-make fn-lgk-make fn-lgc-fitsp fn-lgk-fitsp
                           fn-lgc-append-admitsp fn-lg-append-admitsp)))

(defthm fn-lgc-prepare-refines
  (equal (fn-lgc-prepare (fn-lgc-of ks) record) (fn-lgc-of (fn-lgk-prepare ks record))))

(defthm fn-lgc-t-prepare-refines
  (equal (fn-lgc-t-prepare (fn-lgc-of ks) record) (fn-lgc-of (fn-lgt-prepare ks record)))
  :hints (("Goal" :in-theory (disable fn-lgc-prepare fn-lgk-prepare fn-lgc-of))))

(defthm fn-lgc-append-refines
  (equal (fn-lgc-append (fn-lgc-of ks) unit extent) (fn-lgc-of (fn-lgk-append ks unit extent))))

(defthm fn-lgc-fence-refines
  (equal (fn-lgc-fence (fn-lgc-of ks) unit) (fn-lgc-of (fn-lgk-fence ks unit))))

(defthm fn-lgc-fence-failed-refines
  (equal (fn-lgc-fence-failed (fn-lgc-of ks)) (fn-lgc-of (fn-lgk-fence-failed ks))))

(defthm fn-lgc-finish-one-refines
  (equal (fn-lgc-finish-one (fn-lgc-of ks)) (fn-lgc-of (fn-lgk-finish-one ks))))

(defthm fn-lgc-consume-to-refines
  (equal (fn-lgc-consume-to (fn-lgc-of ks) txid) (fn-lgc-of (fn-olr-consume-to ks txid))))

(defthm fn-lgc-take-refines
  (let ((a (fn-lgc-take (fn-lgc-of ks) record txid count octets bmax omax unit))
        (b (fn-olr-take ks record txid count octets bmax omax unit)))
    (and (equal (car a) (car b))
         (equal (cadr a) (fn-lgc-of (cadr b)))
         (equal (caddr a) (caddr b))))
  :hints (("Goal" :in-theory (disable fn-lgc-prepare fn-lgk-prepare fn-lgc-of fn-olr-entry-octets))))

(defthm fn-lgc-rotate-admitsp-of-abstraction
  (equal (fn-lgc-rotate-admitsp (fn-lgc-of ks)) (fn-lgs-rotate-admitsp ks)))

(local
 (defthm fn-lgc-positive-len-is-consp
   (equal (< 0 (len x)) (consp x))))

(defthm fn-lgc-rotate-needed-p-of-abstraction
  (equal (fn-lgc-rotate-needed-p (fn-lgc-of ks)) (fn-lgs-rotate-needed-p ks)))

(defthm fn-lgc-rotate-refines
  (equal (fn-lgc-rotate (fn-lgc-of ks) k unit) (fn-lgc-of (fn-lgs-rotate ks k unit)))
  :hints (("Goal" :in-theory (e/d (fn-lgc-rotate fn-lgs-rotate)
                                  (fn-lg-rotation-frame fn-lg-rotation-entry fn-lg-trailer)))))

; The extension program changes no kernel field: over any byte store,
; outcomes and steps, the kernel its run ends on is the one it started from,
; and the extended state it reaches does not depend on the kernel.  So the
; program's keystone over the logical kernel
; (fn-lg-extend-program-keeps-the-relation) is one about the concrete kernel
; the host holds (fn-lgc-extend-program-keeps-the-relation).
(defthm fn-lg-extend-run-keeps-the-kernel
  (implies (consp (fn-lg-extend-run bs ks steps outcomes ino))
           (equal (cdr (car (last (fn-lg-extend-run bs ks steps outcomes ino)))) ks))
  :hints (("Goal" :induct (fn-lg-extend-run bs ks steps outcomes ino)
           :in-theory (disable fn-bs-write fn-bs-fsync-file fn-bs-durable-content fn-bs-zeros))))

(defthm fn-lgc-extend-program-keeps-the-relation
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (not (consp (fn-lgc-inflight (fn-lgc-of ks))))
                (equal (mod next (fn-bs-unit bs)) 0)
                (< (len (fn-bs-durable-content bs ino)) next))
           (let* ((run (fn-lg-extend-run bs (fn-lgc-of ks) (fn-lg-extend-program next) nil ino))
                  (final (car (last run))))
             (and (equal (len run) 4)
                  (equal (cdr final) (fn-lgc-of ks))
                  (fn-lgk-relp (car final) ks ino genesis max)
                  (equal (len (fn-bs-durable-content (car final) ino)) next))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lgk-relp fn-lg-extend-run fn-lg-extend-program
                               fn-lg-extended-state fn-lg-extend-run-is-the-extended-state
                               fn-lg-extension-keeps-the-relation fn-lg-extend-run-keeps-the-kernel
                               fn-lg-extend-program-keeps-the-relation
                               fn-bs-durable-content fn-lgc-of mod len last)
           :use ((:instance fn-lgk-relp-at-rest)
                 (:instance fn-lg-extend-program-keeps-the-relation)
                 (:instance fn-lg-extend-run-is-the-extended-state)
                 (:instance fn-lg-extend-run-is-the-extended-state (ks (fn-lgc-of ks)))))))

; The seal's append is admitted by the extent it appends into: after the
; extension (or with none needed) the open batch's append fits, and the
; extent is whole units and never shrinks.  Hypotheses: a positive unit and
; an extent of whole units (fn-lg-extent-okp's; the host checks both).
(defthm fn-lgc-sealed-extent-fits-the-batch
  (implies (and (posp unit) (natp extent) (equal (mod extent unit) 0))
           (let ((next (fn-lgc-sealed-extent c extent unit)))
             (and (fn-lgc-fitsp c unit next)
                  (natp next)
                  (equal (mod next unit) 0)
                  (<= extent next))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lgc-sealed-extent fn-lgc-fitsp fn-lgc-extension-needed-p
                            fn-lgc-extension-target fn-olr-extension-needed-p)
                           (fn-olr-extension-target fn-lgc-append-len
                            fn-olr-extension-target-is-an-extent))
           :use ((:instance fn-olr-extension-target-is-an-extent
                            (frontier (fn-lgc-frontier c))
                            (octets (fn-lgc-append-len c unit)))))))

; Recovery's zeroing range read from the concrete kernel (host fnn-log-recover).
(defthm fn-lg-recover-tail-of-abstraction
  (equal (fn-lg-recover-tail (fn-lgc-of ks) extent) (fn-lg-recover-tail ks extent))
  :hints (("Goal" :in-theory (enable fn-lgc-of fn-lgc-make))))

(defthm fn-lgc-open-refines
  (mv-let (records c) (fn-lgc-open s genesis unit max floor)
    (and (equal records (fn-lgk-committed (fn-lg-open-kernel s genesis unit max floor)))
         (equal c (fn-lgc-of (fn-lg-open-kernel s genesis unit max floor))))))

(in-theory (disable fn-lgc-of fn-lgc-make fn-lgc-prepare fn-lgc-t-prepare fn-lgc-append
                    fn-lgc-fence fn-lgc-fence-failed fn-lgc-finish-one fn-lgc-consume-to
                    fn-lgc-take fn-lgc-open fn-lgc-append-octets fn-lgc-fitsp
                    fn-lgc-append-admitsp fn-lgc-rotate-admitsp fn-lgc-rotate-needed-p
                    fn-lgc-rotate fn-lgc-extension-needed-p fn-lgc-extension-target
                    fn-lgc-sealed-extent fn-lgk-sealed-extent fn-lgc-append-len))

; -----------------------------------------------------------------------------
; The keystone over any host run.  An operation is one of the host's calls:
;   (:prepare record) (:take record txid count octets bmax omax unit)
;   (:consume-to txid) (:append unit extent) (:fence unit) (:fence-failed)
;   (:finish-one) (:rotate)   -- the rotation only when admitted, as fnn-log-rotate
;   (:seal unit extent)       -- the pipelined commit's SEAL (lane log-2): the
;                                extension to the sealed extent, which changes
;                                no kernel field (fn-lg-extend-run-keeps-the-
;                                kernel), then the append into it
; The pipelined commit (host fnn-log-seal-open-batch, the syncer's
; fnn-log-sync-sealed-batch, START-NEXT's fnn-log-take behind the batch in
; flight, COMPLETE's fnn-log-batch-finish) runs these same operations, each a
; step under the log's kernel lock (fnn-log-with-kernel), so any interleaving
; of the owner and the syncer is one sequence OPS: a take behind the batch in
; flight is a :take between its :seal and its :fence.

(defun fn-lgk-host-step (ks op)
  (declare (xargs :guard t :verify-guards nil))
  (case (car op)
      (:prepare (fn-lgt-prepare ks (nth 1 op)))
      (:take (cadr (fn-olr-take ks (nth 1 op) (nth 2 op) (nth 3 op) (nth 4 op)
                                (nth 5 op) (nth 6 op) (nth 7 op))))
      (:consume-to (fn-olr-consume-to ks (nth 1 op)))
      (:append (fn-lgk-append ks (nth 1 op) (nth 2 op)))
      (:fence (fn-lgk-fence ks (nth 1 op)))
      (:fence-failed (fn-lgk-fence-failed ks))
      (:finish-one (fn-lgk-finish-one ks))
      (:rotate (if (fn-lgs-rotate-admitsp ks) (fn-lgs-rotate ks (nth 1 op) (nth 2 op)) ks))
      (:seal (fn-lgk-append ks (nth 1 op) (fn-lgk-sealed-extent ks (nth 2 op) (nth 1 op))))
      (otherwise ks)))

(defun fn-lgc-host-step (c op)
  (declare (xargs :guard t :verify-guards nil))
  (case (car op)
      (:prepare (fn-lgc-t-prepare c (nth 1 op)))
      (:take (cadr (fn-lgc-take c (nth 1 op) (nth 2 op) (nth 3 op) (nth 4 op)
                                (nth 5 op) (nth 6 op) (nth 7 op))))
      (:consume-to (fn-lgc-consume-to c (nth 1 op)))
      (:append (fn-lgc-append c (nth 1 op) (nth 2 op)))
      (:fence (fn-lgc-fence c (nth 1 op)))
      (:fence-failed (fn-lgc-fence-failed c))
      (:finish-one (fn-lgc-finish-one c))
      (:rotate (if (fn-lgc-rotate-admitsp c) (fn-lgc-rotate c (nth 1 op) (nth 2 op)) c))
      (:seal (fn-lgc-append c (nth 1 op) (fn-lgc-sealed-extent c (nth 2 op) (nth 1 op))))
      (otherwise c)))

(defun fn-lgk-host-run (ks ops)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ops) (fn-lgk-host-run (fn-lgk-host-step ks (car ops)) (cdr ops)) ks))

(defun fn-lgc-host-run (c ops)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ops) (fn-lgc-host-run (fn-lgc-host-step c (car ops)) (cdr ops)) c))

(local
 (defthm fn-lgc-of-is-true-listp
   (true-listp (fn-lgc-of ks))
   :hints (("Goal" :in-theory (enable fn-lgc-of fn-lgc-make)))))

(local
 (defthm fn-lgc-host-step-refines
   (equal (fn-lgc-host-step (fn-lgc-of ks) op) (fn-lgc-of (fn-lgk-host-step ks op)))
   :hints (("Goal" :in-theory (disable fn-lgc-take-refines fn-lgk-prepare fn-lgt-prepare fn-olr-take
                                       fn-olr-consume-to fn-lgk-append fn-lgk-fence
                                       fn-lgk-fence-failed fn-lgk-finish-one
                                       fn-lgs-rotate fn-lgs-rotate-admitsp)
                   :use ((:instance fn-lgc-take-refines
                                    (record (nth 1 op)) (txid (nth 2 op)) (count (nth 3 op))
                                    (octets (nth 4 op)) (bmax (nth 5 op)) (omax (nth 6 op))
                                    (unit (nth 7 op))))))))

(defthm fn-lgc-host-run-refines
  (equal (fn-lgc-host-run (fn-lgc-of ks) ops) (fn-lgc-of (fn-lgk-host-run ks ops)))
  :hints (("Goal" :induct (fn-lgk-host-run ks ops)
                  :in-theory (disable fn-lgc-host-step fn-lgk-host-step))))

; KEYSTONE: from the open, the host's concrete kernel after any run of its
; operations is the abstraction of the logical kernel after the same run from
; the kernel the recovery program's theorem names.
(defthm fn-lgc-run-refines-the-kernel
  (equal (fn-lgc-host-run (mv-nth 1 (fn-lgc-open s genesis unit max floor)) ops)
         (fn-lgc-of (fn-lgk-host-run (fn-lgt-recover (fn-lgd-octets s) genesis unit max floor)
                                     ops)))
  :hints (("Goal" :in-theory (disable fn-lgc-host-run fn-lgk-host-run fn-lgc-open-refines
                                      fn-lg-open-kernel-is-the-recovered-kernel fn-lgt-recover
                                      fn-lg-open-kernel)
                  :use ((:instance fn-lgc-open-refines)
                        (:instance fn-lg-open-kernel-is-the-recovered-kernel)))))
