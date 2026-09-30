; The process-local cold-read resource gate (P12 foundation).
; This is admission algebra, not yet the served allocator's refinement.
; No theorem here measures bookkeeping, funds a checkpoint, or says an I/O
; completes. The caller supplies supported budget B, baseline U, static
; rescue R and already issued credits C, all in the same named units.
;
; Vector: resident octets (collector copy included), disk octets,
; registered descriptor credits, executing worker slots, spent process-local
; read identities. The last coordinate is NOT a Store txid or a file id.
; Read identities never wrap or refund. A new process owns a new namespace;
; token lifetimes and that process boundary are a separate obligation.
;
; A registered file incarnation owns its descriptor credit. Readers of it
; own buffer/worker credits until actual completion; cancelling publication
; or timing out does not call release. A matching-completion ownership
; theorem is owed at the eventual caller (books/page-read-ownership).

(in-package "ACL2")

(defun fn-prs-nats-p (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (natp (car xs)) (fn-prs-nats-p (cdr xs)))
    (equal xs nil)))

(defun fn-prs-vectorp (x)
  (declare (xargs :guard t))
  (and (equal (len x) 5) (fn-prs-nats-p x)))

(defun fn-prs-plus (a b)
  (declare (xargs :guard t))
  (if (consp a)
      (cons (+ (nfix (car a)) (if (consp b) (nfix (car b)) 0))
            (fn-prs-plus (cdr a) (if (consp b) (cdr b) nil)))
    nil))

(defun fn-prs-below (a b)
  (declare (xargs :guard t))
  (if (consp a)
      (and (<= (nfix (car a)) (if (consp b) (nfix (car b)) 0))
           (fn-prs-below (cdr a) (if (consp b) (cdr b) nil)))
    t))

(defun fn-prs-fundedp (budget used rescue charged)
  (declare (xargs :guard t))
  (and (fn-prs-vectorp budget) (fn-prs-vectorp used)
       (fn-prs-vectorp rescue) (fn-prs-vectorp charged)
       (fn-prs-below (fn-prs-plus used (fn-prs-plus rescue charged))
                     budget)))

; Current off-lock prefetch allocates ELEN+32 protected octets. BOOKKEEPING
; is a supplied conservative bound, not a measured fact proved here. Stack
; and runtime are native octets, not copied; heap buffers/rows are doubled.
; Compressed expansion needs its own demand, not this constructor.
(defun fn-prs-worker-demand (elen bookkeeping stack-kib runtime-octets)
  (declare (xargs :guard t))
  (list (+ (* 2 (+ (nfix elen) 32 (nfix bookkeeping)))
           (* 1024 (nfix stack-kib)) (nfix runtime-octets))
        0 0 1 1))

(defun fn-prs-incarnation-demand (bookkeeping)
  (declare (xargs :guard t))
  (list (* 2 (nfix bookkeeping)) 0 1 0 0))

; Issue reserves before allocating a token, buffer or thread. LIMIT is the
; representable bound for this read namespace, supplied by the supported
; profile/runtime contract. No arbitrary storage ceiling lives in this book.
; Selected 64-bit SBCL string layout: wide character storage bounds base
; strings as well. Measurement record: paged-resource-pool/layout-hbox-sbcl-
; 2.6.8.log. 32 includes header and alignment; bookkeeping remains supplied.
; This target layout model is not a theorem about arbitrary CL allocators.
(defun fn-prs-incarnation-path-demand (bookkeeping path)
  (declare (xargs :guard t))
  (if (stringp path)
      (fn-prs-incarnation-demand (+ (nfix bookkeeping) 32 (* 4 (length path))))
    nil))

(defun fn-prs-issue (budget used rescue charged next limit demand)
  (declare (xargs :guard t))
  (cond ((not (and (fn-prs-fundedp budget used rescue charged)
                   (fn-prs-vectorp demand) (natp next) (natp limit)))
         (mv :invalid-resource-state next charged))
        ((>= next limit) (mv :read-identities-exhausted next charged))
        ((not (fn-prs-fundedp budget used rescue
                               (fn-prs-plus charged demand)))
         (mv :read-resources-unavailable next charged))
        (t (mv :admitted (+ 1 next) (fn-prs-plus charged demand)))))

; Settlement releases reusable coordinates only. The spent local read
; identity coordinate stays spent, including on cancellation/error results.
(defun fn-prs-release-reusable (charged demand)
  (declare (xargs :guard (and (true-listp charged) (true-listp demand))))
  (list (nfix (- (nfix (nth 0 charged)) (nfix (nth 0 demand))))
        (nfix (- (nfix (nth 1 charged)) (nfix (nth 1 demand))))
        (nfix (- (nfix (nth 2 charged)) (nfix (nth 2 demand))))
        (nfix (- (nfix (nth 3 charged)) (nfix (nth 3 demand))))
        (nfix (nth 4 charged))))

(local (include-book "arithmetic-5/top" :dir :system))

(local
 (defthm fn-prs-plus-length
   (equal (len (fn-prs-plus a b)) (len a))
   :hints (("Goal" :induct (fn-prs-plus a b)))))

(local
 (defthm fn-prs-plus-nats
   (fn-prs-nats-p (fn-prs-plus a b))
   :hints (("Goal" :induct (fn-prs-plus a b)))))

(defthm fn-prs-plus-vectorp
  (implies (and (fn-prs-vectorp a) (fn-prs-vectorp b))
           (fn-prs-vectorp (fn-prs-plus a b)))
  :hints (("Goal" :in-theory (disable fn-prs-plus fn-prs-nats-p))))

; Boundary algebra, deliberately not cited as a host keystone before the
; allocator establishes the supplied coordinates and ownership relation.
(defthm fn-prs-issue-preserves-static-rescue
  (implies (equal (mv-nth 0 (fn-prs-issue budget used rescue charged next limit demand))
                  :admitted)
           (and (fn-prs-fundedp budget used rescue
                                (mv-nth 2 (fn-prs-issue budget used rescue charged next limit demand)))
                (natp (mv-nth 1 (fn-prs-issue budget used rescue charged next limit demand)))
                (<= (mv-nth 1 (fn-prs-issue budget used rescue charged next limit demand)) limit)))
  :rule-classes nil)

(defthm fn-prs-issue-refused-keeps-state-by-definition
  (implies (not (equal (mv-nth 0 (fn-prs-issue budget used rescue charged next limit demand))
                       :admitted))
           (and (equal (mv-nth 1 (fn-prs-issue budget used rescue charged next limit demand)) next)
                (equal (mv-nth 2 (fn-prs-issue budget used rescue charged next limit demand)) charged)))
  :rule-classes :rewrite)

; Indefinitely repeated refused admissions consume no identities or charge.
; This does not cover response/audit allocations in an eventual host path.
(defun fn-prs-repeat (n budget used rescue charged next limit demand)
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (zp n)
      (mv next charged)
    (mv-let (verdict next charged)
      (fn-prs-issue budget used rescue charged next limit demand)
      (declare (ignore verdict))
      (fn-prs-repeat (- n 1) budget used rescue charged next limit demand))))

(defthm fn-prs-repeated-refusal-never-spends
  (implies (not (equal (mv-nth 0 (fn-prs-issue budget used rescue charged next limit demand))
                       :admitted))
           (and (equal (mv-nth 0 (fn-prs-repeat n budget used rescue charged next limit demand)) next)
                (equal (mv-nth 1 (fn-prs-repeat n budget used rescue charged next limit demand)) charged)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-prs-repeat n budget used rescue charged next limit demand)
           :in-theory (disable fn-prs-issue fn-prs-fundedp))))

(defthm fn-prs-release-never-refunds-identities
  (equal (nth 4 (fn-prs-release-reusable charged demand)) (nfix (nth 4 charged))))

(in-theory (disable fn-prs-nats-p fn-prs-vectorp fn-prs-plus fn-prs-below
                    fn-prs-fundedp fn-prs-worker-demand fn-prs-incarnation-demand fn-prs-incarnation-path-demand
                    fn-prs-issue fn-prs-release-reusable fn-prs-repeat))
