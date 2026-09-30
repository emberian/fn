; Internal scalar allocation-epoch machine. Not a runtime installer.
; Inputs called observations/allowances below are INTERNAL results of the
; selected installer, source tariff evaluator and collector wrapper. No public
; host boundary may accept them as byte counts or readiness assertions.
(in-package "ACL2")
(include-book "allocation-epoch-domain")

; Immutable installed tuple (13 cells): tag, exact runtime/image/profile/pool
; association, immediate domain, physical budget, footprint factor, footprint
; slack, collector resident reserve, external resident reserve, ordinary
; allocation headroom, Qgate, Qcollect, Qresume, dynamic collector reserve. The affine footprint envelope
; must be established by the selected allocator unit; it covers region slack,
; rounding and fragmentation. Its representation predicate is NOT authority.
(defun fn-aec-at (n x)
 (declare (xargs :guard (natp n)))
 (if (consp x) (if (zp n) (car x) (fn-aec-at (- n 1) (cdr x))) nil))

(defun fn-aec-nats-below (xs domain)
 (declare (xargs :guard t))
 (if (consp xs)
     (and (natp (car xs)) (natp domain) (<= (car xs) domain)
          (fn-aec-nats-below (cdr xs) domain))
   (equal xs nil)))

; Association6 is fixed by the genuine installer, never supplied by a request.
; Runtime coordinate binds selected executable/image/source units. Shape alone
; does not authenticate installation. Geometry is immutable in this association.
(defun fn-aec-runtime-associationp (x domain)
 (declare (xargs :guard t))
 (and (true-listp x) (equal (len x) 6)
      (eq (fn-aec-at 0 x) :allocation-epoch-association)
      (fn-aec-at 1 x) (fn-aec-at 2 x) (fn-aec-at 3 x)
      (natp domain) (posp (fn-aec-at 4 x))
      (<= (fn-aec-at 4 x) domain)
      (natp (fn-aec-at 5 x)) (<= (fn-aec-at 5 x) domain) t))

(defun fn-aec-installationp (x)
 (declare (xargs :guard t))
 (and (true-listp x) (equal (len x) 13)
      (eq (fn-aec-at 0 x) :allocation-epoch-installation)
      (fn-aec-runtime-associationp (fn-aec-at 1 x) (fn-aec-at 2 x))
      (posp (fn-aec-at 2 x))
      (and (natp (fn-aec-at 3 x)) (<= (fn-aec-at 3 x) (fn-aec-at 2 x)))
      (and (natp (fn-aec-at 4 x)) (<= (fn-aec-at 4 x) (fn-aec-at 2 x)))
      (and (natp (fn-aec-at 5 x)) (<= (fn-aec-at 5 x) (fn-aec-at 2 x)))
      (and (natp (fn-aec-at 6 x)) (<= (fn-aec-at 6 x) (fn-aec-at 2 x)))
      (and (natp (fn-aec-at 7 x)) (<= (fn-aec-at 7 x) (fn-aec-at 2 x)))
      (and (natp (fn-aec-at 8 x)) (<= (fn-aec-at 8 x) (fn-aec-at 2 x)))
      (and (natp (fn-aec-at 9 x)) (<= (fn-aec-at 9 x) (fn-aec-at 2 x)))
      (and (natp (fn-aec-at 10 x)) (<= (fn-aec-at 10 x) (fn-aec-at 2 x)))
      (and (natp (fn-aec-at 11 x)) (<= (fn-aec-at 11 x) (fn-aec-at 2 x)))
      (and (natp (fn-aec-at 12 x))
           (<= (fn-aec-at 12 x) (fn-aec-at 2 x))
           (<= (fn-aec-at 12 x) (fn-aec-at 5 (fn-aec-at 1 x))))
      (posp (fn-aec-at 4 x))
      (<= (fn-aec-at 5 x) (fn-aec-at 3 x))
      (<= (fn-aec-at 6 x) (- (fn-aec-at 3 x) (fn-aec-at 5 x)))
      (<= (fn-aec-at 7 x)
          (- (- (fn-aec-at 3 x) (fn-aec-at 5 x)) (fn-aec-at 6 x)))))

(defun fn-aec-physical-ceiling (installation)
 (declare (xargs :guard (fn-aec-installationp installation)))
 (floor (- (- (- (fn-aec-at 3 installation) (fn-aec-at 5 installation))
                 (fn-aec-at 6 installation)) (fn-aec-at 7 installation))
        (fn-aec-at 4 installation)))

; Dynamic reservation and affine physical footprint are distinct ceilings.
; The appended reserve is supplied only by the genuine qualified installer;
; collector resident reserve does not establish dynamic collector headroom.
(defun fn-aec-ceiling (installation)
 (declare (xargs :guard (fn-aec-installationp installation)))
 (min (fn-aec-physical-ceiling installation)
      (- (fn-aec-at 5 (fn-aec-at 1 installation))
         (fn-aec-at 12 installation))))

; The logical budget/grants invariant remains a distinct same-pool invariant.
; This predicate covers physical allocation only. A release of logical C is
; not an input and cannot lower A. Immutable association has no setter here.
(defun fn-aec-statep (installation mode epoch occupied allocated turns nonce)
 (declare (xargs :guard t))
 (and (or (and (not installation) (eq mode :uninstalled)
          (equal epoch 0) (equal occupied 0) (equal allocated 0)
          (equal turns 0) (not nonce))
     (and (fn-aec-installationp installation)
          (member-eq mode '(:active :draining :collecting :recovery))
          (fn-aec-nats-below (list epoch occupied allocated turns)
                            (fn-aec-at 2 installation))
          (or (not nonce) (and (natp nonce) (<= nonce (fn-aec-at 2 installation))))
          (or (not (eq mode :active)) (not nonce))
          (or (not (eq mode :collecting)) (equal turns 0))
          (fn-aed-ordinary-roomp occupied allocated 0
                                (fn-aec-ceiling installation) (fn-aec-at 2 installation)))) t))

; Constant-size scalar entry. Qgate is installed source-derived control cost,
; never a host-supplied amount. A :prepaid result covers the subsequent tariff
; evaluation, including refusal/return, and counts one allocating turn.
; The cleanup entry is an INTERNAL separately authorized operation route;
; ordinary callers cannot choose its reserved-headroom privilege.
(defun fn-aec-enter (installation mode epoch occupied allocated turns nonce cleanup)
 (declare (ignore epoch nonce) (xargs :guard (and (fn-aec-statep installation mode epoch occupied allocated turns nonce)
                            (booleanp cleanup))))
 (cond ((not (eq mode :active))
        (mv (if (eq mode :recovery) :recovery-required :yield) mode allocated turns))
       ((not (fn-aed-add-roomp turns 1 (fn-aec-at 2 installation)))
        (mv :recovery-required :recovery allocated turns))
       (t
        (mv-let (word next)
          (fn-aed-ordinary-prepay occupied allocated (fn-aec-at 9 installation)
            (if cleanup 0 (fn-aec-at 8 installation))
            (fn-aec-ceiling installation) (fn-aec-at 2 installation))
          (if (eq word :prepaid)
              (mv :prepaid :active next (+ 1 turns))
            (mv :yield :draining allocated turns))))))

; INTERNAL body prepayment after the same turn's Qgate has been paid. BODY
; comes from the selected operation/source evaluator. This is not a public
; reserve API. A refused body keeps paid gate allocation and the turn until
; the actual once-only return; it never refunds garbage accounting.
(defun fn-aec-body (installation mode epoch occupied allocated turns nonce body cleanup)
 (declare (ignore epoch nonce) (xargs :guard (and (fn-aec-statep installation mode epoch occupied allocated turns nonce)
                            (natp body) (booleanp cleanup))))
 (cond ((and (eq mode :draining) (posp turns))
        ;; The already paid gate owns its no-effect epilogue; drain forbids
        ;; new body allocation but must let that turn yield and settle.
        (mv :yield :draining allocated))
       ((or (not (eq mode :active)) (zp turns))
        (mv :recovery-required :recovery allocated))
       (t
        (mv-let (word next)
          (fn-aed-ordinary-prepay occupied allocated body
            (if cleanup 0 (fn-aec-at 8 installation))
            (fn-aec-ceiling installation) (fn-aec-at 2 installation))
          (if (eq word :prepaid) (mv :prepaid :active next)
            (mv :yield :draining allocated))))))

; INTERNAL continuation of an actual consumed allocating-turn receipt.
; The seven scalar fields alone do not authenticate completion. The composed
; caller must consume its distinct SAMEpool turn receipt once before here;
; retained connection-holder rows are not that authority. No public turn-exit
; wrapper is installed until this producer is joined.
(defun fn-aec-leave-owned (mode allocated turns)
 (declare (xargs :guard (and (natp allocated) (natp turns))))
 (if (and (member-eq mode '(:active :draining :recovery)) (posp turns))
     (mv :left mode allocated (- turns 1))
   (mv :recovery-required :recovery allocated turns)))

(defun fn-aec-drain (mode)
 (declare (xargs :guard t))
 (if (eq mode :active) :draining mode))

; Collector/control prepayment uses reserved capacity. Enter COLLECTING with
; no nonce as a retained intent, then issue the GC identity from shared PRS
; NEXT. No second request can repeat that debit. A raw escape fences, retaining
; both allocation charge and any shared-issuer intent. No new counter exists.
(defun fn-aec-collect-prepay (installation mode epoch occupied allocated turns nonce)
 (declare (xargs :guard (fn-aec-statep installation mode epoch occupied allocated turns nonce)))
 (cond ((eq mode :recovery) (mv :recovery-required :recovery allocated))
       ((not (and (eq mode :draining) (equal turns 0) (not nonce)))
        (mv :not-quiescent mode allocated))
       ((not (< epoch (fn-aec-at 2 installation)))
        (mv :recovery-required :recovery allocated))
       (t
        (mv-let (word next)
          (fn-aed-ordinary-prepay occupied allocated (fn-aec-at 10 installation) 0
            (fn-aec-ceiling installation) (fn-aec-at 2 installation))
          (if (eq word :prepaid) (mv :issue-collection-nonce :collecting next)
            ;; A promised collection/control reserve was breached.
            (mv :recovery-required :recovery allocated))))))

(defun fn-aec-collect-issued (mode turns nonce issued domain)
 (declare (xargs :guard (and (natp turns) (natp domain))))
 (if (and (eq mode :collecting) (equal turns 0) (not nonce)
          (natp issued) (<= issued domain))
     (mv :collect :collecting issued)
   (mv :recovery-required :recovery nonce)))

; INTERNAL primitive observation projection. Public completion takes only its
; nonce and reads the selected installed observer; no public byte count or
; Boolean can enter this function. Observation/nonce/epoch/association must be
; from that SAME completed collection while process allocation admission stays
; closed. Automatic GC never invokes this reset.
(defun fn-aec-collect-complete
 (installation mode epoch occupied allocated turns nonce
  observed-association observed-epoch observed-nonce status observed-occupied)
 (declare (xargs :guard (fn-aec-statep installation mode epoch occupied allocated turns nonce)))
 (cond
  ((not (and (eq mode :collecting) (equal turns 0) (natp nonce)
             (equal observed-association (fn-aec-at 1 installation))
             (equal observed-epoch epoch) (equal observed-nonce nonce)
             (eq status :completed) (< epoch (fn-aec-at 2 installation))
             (natp observed-occupied)
             (fn-aed-ordinary-roomp observed-occupied (fn-aec-at 11 installation) 0
                                   (fn-aec-ceiling installation) (fn-aec-at 2 installation))))
   (mv :recovery-required :recovery epoch occupied allocated nonce))
  (t
   (let ((resume (fn-aec-at 11 installation)))
    (mv-let (word ignored)
      (fn-aed-ordinary-prepay observed-occupied resume (fn-aec-at 9 installation)
        (fn-aec-at 8 installation) (fn-aec-ceiling installation) (fn-aec-at 2 installation))
      (declare (ignore ignored))
      (if (eq word :prepaid)
          (mv :resume :active (+ 1 epoch) observed-occupied resume nil)
        ;; Keep barrier closed and completed nonce retained. A subsequent
        ;; collect-prepay cannot loop on this capacity-unavailable epoch.
        (mv :resource-unavailable :draining (+ 1 epoch) observed-occupied resume nonce)))))))

; Fault/unknown outcome changes only mode in the actual pool wrapper. No
; rollback of the prepayment, live turn count, or collector identity occurs.
(defun fn-aec-uncertain ()
 (declare (xargs :guard t))
 :recovery)

(defthm fn-aec-enter-preserves-allocation-state
 (implies (fn-aec-statep i m e l a n g)
  (mv-let (word next-mode next-a next-n) (fn-aec-enter i m e l a n g cleanup)
   (declare (ignore word))
   (and (fn-aec-statep i next-mode e l next-a next-n g)
        (<= a next-a))))
 :hints (("Goal" :in-theory (disable fn-aec-installationp fn-aec-ceiling fn-aec-at)))
 :rule-classes nil)

(defthm fn-aec-body-preserves-allocation-state
 (implies (and (fn-aec-statep i m e l a n g)
               (not (eq m :uninstalled)))
  (mv-let (word next-mode next-a) (fn-aec-body i m e l a n g body cleanup)
   (declare (ignore word))
   (and (fn-aec-statep i next-mode e l next-a n g)
        (<= a next-a))))
 :hints (("Goal" :in-theory (disable fn-aec-installationp fn-aec-ceiling fn-aec-at)))
 :rule-classes nil)

; This theorem's consumed-turn producer obligation is the composed caller's
; precondition, not a Boolean argument to the scalar function.
(defthm fn-aec-consumed-turn-settlement-preserves-state
 (implies (and (fn-aec-statep i m e l a n g)
               (posp n))
  (mv-let (word next-mode next-a next-n) (fn-aec-leave-owned m a n)
   (and (eq word :left) (equal next-a a) (equal next-n (- n 1))
        (fn-aec-statep i next-mode e l next-a next-n g))))
 :hints (("Goal" :in-theory (disable fn-aec-installationp fn-aec-ceiling fn-aec-at)))
 :rule-classes nil)

(defthm fn-aec-collector-mismatch-keeps-accounting
 (implies (not (and (eq m :collecting) (equal n 0) (natp g)
                    (equal oi (fn-aec-at 1 i)) (equal oe e) (equal og g)
                    (eq status :completed)))
  (equal (fn-aec-collect-complete i m e l a n g oi oe og status ol)
         (list :recovery-required :recovery e l a g)))
 :hints (("Goal" :in-theory (disable fn-aec-ceiling fn-aec-at)))
 :rule-classes nil)

(defthm fn-aec-collector-reset-preserves-state
 (implies (fn-aec-statep i m e l a n g)
  (mv-let (word nm ne nl na ng)
   (fn-aec-collect-complete i m e l a n g oi oe og status ol)
   (implies (member-eq word '(:resume :resource-unavailable))
    (and (fn-aec-statep i nm ne nl na 0 ng)
         (equal ne (+ 1 e)) (equal nl ol)
         (equal na (fn-aec-at 11 i))))))
 :hints (("Goal" :in-theory (disable fn-aec-installationp fn-aec-ceiling fn-aec-at)))
 :rule-classes nil)

(defthm fn-aec-collect-prepay-preserves-state
 (implies (and (fn-aec-statep i m e l a n g) (not (eq m :uninstalled)))
  (mv-let (word nm na) (fn-aec-collect-prepay i m e l a n g)
   (declare (ignore word))
   (and (fn-aec-statep i nm e l na n g) (<= a na))))
 :hints (("Goal" :in-theory (disable fn-aec-installationp fn-aec-ceiling fn-aec-at)))
 :rule-classes nil)

(defthm fn-aec-collection-issue-preserves-state
 (implies (and (fn-aec-statep i m e l a n g) (not (eq m :uninstalled)))
  (mv-let (word nm ng) (fn-aec-collect-issued m n g issued (fn-aec-at 2 i))
   (declare (ignore word))
   (fn-aec-statep i nm e l a n ng)))
 :hints (("Goal" :in-theory (disable fn-aec-installationp fn-aec-ceiling fn-aec-at)))
 :rule-classes nil)

(defthm fn-aec-raw-uncertainty-preserves-state
 (implies (and (fn-aec-statep i m e l a n g) (not (eq m :uninstalled)))
          (fn-aec-statep i (fn-aec-uncertain) e l a n g))
 :hints (("Goal" :in-theory (disable fn-aec-installationp fn-aec-ceiling fn-aec-at)))
 :rule-classes nil)

; Algebraic consequence of the qualified affine envelope. The runtime must
; establish that envelope for its allocator geometry; this is not an RSS or
; empirical-runtime theorem. Arithmetic rules stay local to this proof.
(encapsulate ()
 (local (include-book "arithmetic-5/top" :dir :system))
 (local
  (defthm fn-aec-floor-envelope
   (implies (and (natp x) (natp b) (posp f) (<= x (floor b f)))
            (<= (* f x) b))
   :hints (("Goal" :nonlinearp t)) :rule-classes nil))
 (defthm fn-aec-state-footprint-bound
  (implies (fn-aec-statep i m e l a n g)
   (<= (+ (* (fn-aec-at 4 i) (+ l a))
          (fn-aec-at 5 i) (fn-aec-at 6 i) (fn-aec-at 7 i))
       (fn-aec-at 3 i)))
  :hints (("Goal"
   :in-theory (set-difference-theories
               (current-theory 'fn-aec-raw-uncertainty-preserves-state) '(fn-aec-at))
   :use ((:instance fn-aec-floor-envelope
            (x (+ l a))
            (b (- (- (- (fn-aec-at 3 i) (fn-aec-at 5 i))
                        (fn-aec-at 6 i)) (fn-aec-at 7 i)))
            (f (fn-aec-at 4 i))))))
  :rule-classes nil))

(defthm fn-aec-collector-reset-quiescence-by-definition
 (implies (member-eq (mv-nth 0 (fn-aec-collect-complete i m e l a n g oi oe og status ol))
                     '(:resume :resource-unavailable))
          (equal n 0))
 :hints (("Goal" :in-theory (disable fn-aec-at fn-aec-ceiling)))
 :rule-classes nil)
