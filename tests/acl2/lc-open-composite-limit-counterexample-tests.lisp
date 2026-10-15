; Probe A4's free MAX against the header-carried framing maximum.
; All helpers below are observations/proofs over the existing scanner.
(in-package "ACL2")
(include-book "../../books/log-checkpoint-open-bound")
(include-book "../../books/log-checkpoint-bridge")
(include-book "../../books/log-checkpoint-independent-guards")
(include-book "lc-open-fixtures")
(local (include-book "std/lists/take" :dir :system))

(local (defthm lcx-move-kind-must-match
 (implies (not (equal (nth 5 frame) *fn-lc-move-kind*))
          (not (fn-lc-move-framep frame prev max)))
 :hints (("Goal" :use ((:instance fn-lc-open-kind-is-header-kind (slice frame)))
  :in-theory (e/d (fn-lc-move-framep) (fn-frame-open fn-frame-result-kind
                                       fn-frame-result-okp))))))
(local (defthm lcx-record-kind-must-match
 (implies (not (equal (nth 5 frame) *fn-lc-record-kind*))
          (not (fn-lc-record-framep frame prev max)))
 :hints (("Goal" :use ((:instance fn-lc-open-kind-is-header-kind (slice frame)))
  :in-theory (e/d (fn-lc-record-framep) (fn-frame-open fn-frame-result-kind
                                       fn-frame-result-okp))))))
(local (defthm lcx-nth-of-take
 (implies (and (natp i) (natp n) (< i n))
  (equal (nth i (take n bytes)) (nth i bytes)))
 :hints (("Goal" :induct (fn-lc-split-nth-induction n i bytes)
  :in-theory (e/d (nth take fn-lc-split-nth-induction)
                  (fn-hp-nthcdr-of-take))))))
(local (defthm lcx-rotation-is-terminal
 (implies (and (equal (fn-lg-declared-len bytes) n)
               (posp n) (<= n (len bytes))
               (<= n (fn-lc-entry-octets-bound max))
               (equal (nth 5 bytes) *fn-lg-rotation-kind*)
               (< 5 n) (posp fuel))
  (equal (fn-lc-scan-bytes bytes prev unit max fuel)
         (list :terminal nil (list n) prev)))
 :rule-classes nil
 :hints (("Goal" :cases ((consp bytes))
  :expand ((fn-lc-scan-bytes bytes prev unit max fuel))
  :in-theory (union-theories
   '(lcx-move-kind-must-match lcx-record-kind-must-match lcx-nth-of-take
     fn-lc-at-is-nth fn-lc-head posp natp nfix zp len
     car-cons cdr-cons (:executable-counterpart equal))
   (theory 'minimal-theory))))))

; 16,777,217 payload octets, plus the 42 framing octets. Rotation is
; deliberately not accepted by LC: the request is charged before rejection.
(defun lcx-terminal-bytes ()
 (declare (xargs :guard t))
 (append '(70 78 76 71 1 3 1 0 0 1)
         (make-list 16777249 :initial-element 0)))
(in-theory (disable (:executable-counterpart lcx-terminal-bytes)))
(local (defthm lcx-len-make-list-ac
 (equal (len (make-list-ac n value acc)) (+ (nfix n) (len acc)))
 :hints (("Goal" :induct (make-list-ac n value acc)))))
(local (defthm lcx-octets-make-list-ac
 (implies (fn-cbor-octet-listp acc)
          (fn-cbor-octet-listp (make-list-ac n 0 acc)))
 :hints (("Goal" :induct (make-list-ac n 0 acc)
          :in-theory (enable fn-cbor-octet-listp)))))
(local (defthm lcx-bytes-length
 (equal (len (lcx-terminal-bytes)) 16777259)
 :hints (("Goal" :in-theory (e/d (lcx-terminal-bytes) (make-list-ac
   (:executable-counterpart make-list-ac) (:executable-counterpart lcx-terminal-bytes)
    fn-lgx-make-list-ac-is-zeros))))))
(local (defthm lcx-bytes-octets
 (fn-cbor-octet-listp (lcx-terminal-bytes))
 :hints (("Goal" :in-theory (e/d (lcx-terminal-bytes fn-cbor-octet-listp)
   (make-list-ac (:executable-counterpart make-list-ac) (:executable-counterpart lcx-terminal-bytes)
    fn-lgx-make-list-ac-is-zeros))))))
(local (defthm lcx-bytes-header
 (and (equal (fn-lg-declared-len (lcx-terminal-bytes)) 16777259)
      (equal (nth 5 (lcx-terminal-bytes)) *fn-lg-rotation-kind*)
      (consp (lcx-terminal-bytes)))
 :hints (("Goal" :in-theory (e/d (fn-lg-declared-len lcx-terminal-bytes
    fn-bs-take fn-cbor-u32-from fn-cbor-octet-listp nth)
   (make-list-ac (:executable-counterpart make-list-ac) (:executable-counterpart lcx-terminal-bytes)
    fn-lgx-make-list-ac-is-zeros))))))
(local (in-theory (disable lcx-terminal-bytes)))
(defthm lcx-terminal-scan
 (equal (fn-lc-scan-bytes (lcx-terminal-bytes) prev 1 16777217
                          16777259)
        (list :terminal nil '(16777259) prev))
 :hints (("Goal" :use ((:instance lcx-rotation-is-terminal
    (bytes (lcx-terminal-bytes)) (unit 1) (max 16777217)
    (fuel 16777259) (n 16777259)))
   :in-theory (e/d (fn-lc-entry-octets-bound fn-lg-batch-entry-bound)
     (fn-lc-scan-bytes fn-lg-declared-len)))))

(defun lcx-limit-input ()
 (declare (xargs :guard t :verify-guards nil))
 (let* ((value '(nil nil nil (nil nil nil) nil nil nil nil nil nil nil))
        (configs (list *fn-cfg-default-record*))
        (control (ec-call (fn-lc-control-of (list configs nil))))
        (header (fn-lc-snapshot-header-value value
                 (list :lc-header (list 0 0 0 8 *fn-lg-genesis*) 1 nil nil nil)
                 control))
        (header (ec-call (update-nth 5
                    (cons '(:lc-tail-policy 1 16777217) (fn-lc-at 5 header)) header)))
        (disk (ec-call (fn-lc-proof-image-disk
               (fn-lc-pages (ec-call (fn-lc-columns-value value)) header)))))
   (list disk header configs)))
(verify-guards lcx-limit-input)
(local (in-theory (disable lcx-limit-input)))
(defun lcx-limit-segs ()
 (declare (xargs :guard t))
 (list (list 0 (lcx-terminal-bytes) nil)))
(in-theory (disable (:executable-counterpart lcx-limit-segs)))

; The actual open trace projection. It does not reason about a replacement
; implementation of adoption, ownership, or replay.
(local (defthm lcx-open-trace-by-definition
 (equal (mv-nth 4 (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc))
        (take (min (+ 1 (fn-lc-outcome-ok-count outcome (len (fn-lc-open-program disk r mode segs))))
                   (len (fn-lc-open-program disk r mode segs)))
              (fn-lc-open-program disk r mode segs)))
 :hints (("Goal" :in-theory
  (union-theories '(fn-lc-open fn-lc-at-is-nth fn-lc-take-is-take fn-lc-head
     nth mv-nth not min (:executable-counterpart binary-+) (:executable-counterpart <)
     (:executable-counterpart zp) (:executable-counterpart equal)
     car-cons cdr-cons) (theory 'minimal-theory))))))

; The small metadata fixture is evaluated separately from the large octet
; list; no frame digest over that terminal list is needed by these proofs.
(encapsulate ()
 (local (defattach pgs-digest fn-lc-proof-digest))
 (assert-event
  (let* ((input (lcx-limit-input)) (disk (nth 0 input)) (header (nth 1 input)))
   (and (equal (car (pgs-open disk :lc :eager)) :ok)
        (equal (fn-lc-adopted-header disk :lc :eager) header)
        (equal (fn-lc-cold-adopted-header disk :lc :eager) header)
        (equal (fn-lc-tail-max header) 16777217)
        (equal (len (fn-lc-open-metadata-pages disk :lc :eager)) 6)
        (equal (fn-lc-entry-octets-bound 0) 16777258)))))

(defun lcx-metadata-ready-p (input)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((disk (fn-lc-at 0 input))
        (header (fn-lc-at 1 input))
        (trace (fn-lc-at 5 (fn-lc-cold-select disk :lc :eager))))
  (and (equal (fn-lc-head (pgs-open disk :lc :eager)) :ok)
       (equal (fn-lc-adopted-header disk :lc :eager) header)
       (equal (fn-lc-header-of-open (pgs-open disk :lc :eager)) header)
       (equal (fn-lc-cold-adopted-header disk :lc :eager) header)
       (fn-lc-headerp header)
       (equal (fn-lc-header-S header) (list 0 0 0 8 *fn-lg-genesis*))
       (equal (fn-lc-tail-max header) 16777217)
       (equal (fn-lc-tail-unit header) 1)
       (true-listp trace) (equal (len trace) 8)
       (equal (fn-lc-read-octets trace) 98564)
       (equal (len (fn-lc-open-metadata-pages disk :lc :eager)) 6))))
(verify-guards lcx-metadata-ready-p)
(local (in-theory (disable lcx-metadata-ready-p)))

(local (defthm lcx-tail-scan
 (implies (and (equal segs (lcx-limit-segs))
               (equal (fn-lc-header-S header) (list 0 0 0 8 *fn-lg-genesis*))
               (equal (fn-lc-tail-max header) 16777217)
               (equal (fn-lc-tail-unit header) 1))
  (equal (fn-lc-tail-scan segs header)
         (list :terminal nil '(16777259) *fn-lg-genesis*)))
 :hints (("Goal" :in-theory (e/d
  (fn-lc-tail-scan lcx-limit-segs fn-lc-scan-segments fn-lc-ordered-segments
   fn-lc-insert-segment)
  (fn-lc-scan-bytes fn-lc-header-S fn-lc-tail-max fn-lc-tail-unit
   fn-lg-declared-len lcx-terminal-bytes (:executable-counterpart lcx-limit-segs)))))))
(local (defthm lcx-segs-typed
 (fn-lc-segsp (lcx-limit-segs))
 :hints (("Goal" :in-theory (e/d
  (fn-lc-segsp fn-lb-log-model-segsp fn-lb-log-model-entriesp lcx-limit-segs)
  (lcx-terminal-bytes (:executable-counterpart lcx-limit-segs)))))))
(local (defthm lcx-tail-is-retained
 (implies (lcx-metadata-ready-p input)
  (and (fn-lc-segsp (lcx-limit-segs))
       (fn-lc-segs-retain (lcx-limit-segs) (cadr input))
       (equal (fn-lc-tail-history (lcx-limit-segs) (cadr input)) nil)))
 :hints (("Goal" :in-theory (e/d
  ((:definition lcx-metadata-ready-p) fn-lc-segsp fn-lb-log-model-segsp
   fn-lb-log-model-entriesp lcx-limit-segs fn-lc-segs-retain fn-lc-tail-history
   fn-lc-decode-tail-records)
  (lcx-limit-input lcx-terminal-bytes fn-lc-tail-scan
   fn-lc-header-S fn-lc-tail-max fn-lc-tail-unit fn-lc-headerp
   fn-lc-adopted-header fn-lc-cold-adopted-header pgs-open
   fn-lc-cold-select fn-lc-open-metadata-pages fn-lc-read-octets
   (:executable-counterpart lcx-limit-segs)))))))
(local (defthm lcx-selection
 (implies (lcx-metadata-ready-p input)
  (equal (fn-lc-open-selection (car input) :lc :eager 0
           (lcx-limit-segs) (cadr input))
         (list :checkpoint 0 (list 0 0 0 8 *fn-lg-genesis*) nil
                 (cadr input))))
 :hints (("Goal" :in-theory (e/d
  ((:definition lcx-metadata-ready-p) fn-lc-open-selection fn-lc-header-sequence)
  (lcx-limit-input lcx-terminal-bytes lcx-limit-segs fn-lc-tail-scan
   fn-lc-header-S fn-lc-tail-max fn-lc-tail-unit fn-lc-headerp
   fn-lc-adopted-header fn-lc-cold-adopted-header pgs-open fn-lc-header-of-open
   fn-lc-cold-select fn-lc-open-metadata-pages fn-lc-read-octets
   fn-lc-segs-retain fn-lc-segsp fn-lc-tail-history))))))
(local (defthm lcx-read-of-append
 (equal (fn-lc-read-octets (append a b))
        (+ (fn-lc-read-octets a) (fn-lc-read-octets b)))
 :hints (("Goal" :induct (fn-lc-read-octets a)))))
(local (defthm lcx-read-cons-unfolds
 (equal (fn-lc-read-octets (cons request trace))
  (+ (if (equal (car request) :pread) (nfix (nth 3 request)) 0)
     (fn-lc-read-octets trace)))))
(local (defthm lcx-read-nil-unfolds (equal (fn-lc-read-octets nil) 0)))
(local (defthm lcx-program-cost
 (implies (lcx-metadata-ready-p input)
  (and (true-listp (fn-lc-open-program (car input) :lc :eager (lcx-limit-segs)))
       (equal (len (fn-lc-open-program (car input) :lc :eager (lcx-limit-segs))) 9)
       (equal (fn-lc-read-octets
                 (fn-lc-open-program (car input) :lc :eager (lcx-limit-segs)))
              16875823)))
 :hints (("Goal" :in-theory (e/d
  ((:definition lcx-metadata-ready-p) fn-lc-open-program fn-lc-cold-tail-entries
   fn-lc-open-tail-program)
  (lcx-limit-input lcx-terminal-bytes lcx-limit-segs fn-lc-tail-scan
   fn-lc-header-S fn-lc-tail-max fn-lc-tail-unit fn-lc-headerp
   fn-lc-adopted-header fn-lc-cold-adopted-header pgs-open fn-lc-header-of-open
   fn-lc-cold-select fn-lc-open-metadata-pages fn-lc-read-octets))))))
(local (defthm lcx-trace-cost
 (implies (lcx-metadata-ready-p input)
  (equal (fn-lc-read-octets
    (mv-nth 4 (fn-lc-open (car input) :lc :eager
                 (caddr input) 8 4 (lcx-limit-segs)
                 '(:ok :ok :ok :ok :ok :ok :ok :ok) fn-lbc)))
         16875823))
 :hints (("Goal" :use ((:instance lcx-open-trace-by-definition
   (disk (car input)) (r :lc) (mode :eager)
   (configs (caddr input)) (frontier 8) (max-conns 4)
   (segs (lcx-limit-segs)) (outcome '(:ok :ok :ok :ok :ok :ok :ok :ok))))
  :in-theory (e/d (fn-lc-outcome-ok-count)
  (lcx-limit-input lcx-terminal-bytes lcx-limit-segs fn-lc-tail-scan
   fn-lc-open fn-lc-open-program fn-lc-read-octets
   (:executable-counterpart lcx-limit-segs)))))))

; Logical observation of ALL FIVE frozen hypotheses and A4's exact
; conclusion; MAX=0, K=0, COUNT=0. No semantic premise is added to A4.
(defun-nx lcx-a4-logical-observation (input fn-lbc)
 (let* ((disk (car input)) (header (cadr input))
        (segs (lcx-limit-segs))
        (selection (fn-lc-open-selection disk :lc :eager 0 segs header))
        (out (fn-lc-open disk :lc :eager (caddr input) 8 4 segs
                 '(:ok :ok :ok :ok :ok :ok :ok :ok) fn-lbc))
        (requested (fn-lc-read-octets (mv-nth 4 out)))
        (allowed (+ (* 2 (fn-lc-root-slot-octets))
                    (* (len (fn-lc-open-metadata-pages disk :lc :eager)) (fn-lc-page-octets))
                    (* (+ 1 0) (fn-lc-entry-octets-bound 0)))))
  (list (fn-lbc-p fn-lbc) (fn-lc-segsp segs)
        (equal (car selection) :checkpoint) (natp 0)
        (<= (len (fn-lc-selection-tail selection)) 0)
        requested allowed (<= requested allowed))))

; Scalar executable observation, verified against the logical subject
; above below. This avoids allocating a 16 MiB list just to reject its
; rotation header, or recursing once per octet through TAKE.
(defun lcx-a4-scalar-observation (input fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc)))
 (mv (if (lcx-metadata-ready-p input)
         (list (fn-lbc-p fn-lbc) t t t t 16875823 16875822 nil) nil) fn-lbc))

(defthm lcx-a4-scalar-observation-is-the-full-formula
 (implies (lcx-metadata-ready-p input)
  (equal (mv-nth 0 (lcx-a4-scalar-observation input fn-lbc))
         (lcx-a4-logical-observation input fn-lbc)))
 :hints (("Goal" :in-theory (e/d
  (lcx-a4-scalar-observation lcx-a4-logical-observation
   fn-lc-selection-tail fn-lc-root-slot-octets fn-lc-page-octets
   fn-lc-entry-octets-bound fn-lg-batch-entry-bound (:definition lcx-metadata-ready-p))
  (lcx-limit-input lcx-terminal-bytes lcx-limit-segs fn-lc-tail-scan
   fn-lc-open fn-lc-open-program fn-lc-read-octets fn-lc-open-selection
   fn-lc-open-metadata-pages fn-lc-segsp fn-lc-cold-select fn-lbc-p
   fn-lc-headerp fn-lc-header-S fn-lc-tail-max fn-lc-tail-unit
   fn-lc-adopted-header fn-lc-cold-adopted-header pgs-open fn-lc-header-of-open
   (:executable-counterpart lcx-limit-segs))))))
(defun lcx-a4-counterexample ()
 (declare (xargs :guard t))
 (with-local-stobj fn-lbc
  (mv-let (out fn-lbc) (lcx-a4-scalar-observation (lcx-limit-input) fn-lbc) out)))
(encapsulate ()
 (local (defattach pgs-digest fn-lc-proof-digest))
 (assert-event (lcx-metadata-ready-p (lcx-limit-input)))
 (assert-event (equal (lcx-a4-counterexample)
                      '(t t t t t 16875823 16875822 nil)))
 (value-triple (lcx-a4-counterexample)))
