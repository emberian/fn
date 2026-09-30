(in-package "ACL2")

(include-book "../../books/post-identity-captured-agent-join")

(include-book "post-identity-captured-tests")

; Full antecedent/conclusion teeth for producer, progress, reader, and
; retained-context seams. Corrupted continuations and effect mutations
; below are distinct from authorized readonly native input.

(defun pic-ajt-observation (c incoming)
 (let ((d (fn-pic-demand c)))
  (if (equal d :control) :control
   (list :incoming-byte (fn-pic-get incoming-token c) (fn-pic-at 1 d)
    (nth (fn-pic-at 1 d) incoming)))))

(defun pic-ajt-initial (incoming)
 (fn-pic-begin *pic-test-selected* *pic-test-grant*
  (pic-test-held "<m>" nil *pic-test-binding*) *pic-test-incoming*
  (len incoming) "<m>" *pic-test-binding* nil))

(defun pic-ajt-length (c)
 (list :payload-length (fn-pic-get selected c) (fn-pic-get grant c)
  (fn-record-payload (fn-pic-get held c)) 145))

(defun pic-ajt-start (incoming)
 (nth 1 (mv-list 3 (fn-pic-feed-funded (pic-ajt-initial incoming)
  (pic-ajt-length (pic-ajt-initial incoming)) 1))))

(defun pic-ajt-drive (c incoming ticks)
 (declare (xargs :measure (nfix ticks) :verify-guards nil))
 (if (zp ticks) c
  (pic-ajt-drive (nth 1 (mv-list 3 (fn-pic-feed-funded c (pic-ajt-observation c incoming) 1)))
   incoming (1- ticks))))

(defconst *pic-ajt-start* (pic-ajt-start *pic-test-stamped*))

(defconst *pic-ajt-ticks*
 (1- (fn-psc-model-agent-cost (fn-pic-agent-trace-start *pic-ajt-start* *pic-test-stamped*) *pic-test-stamped*)))

(defconst *pic-ajt-before* (pic-ajt-drive *pic-ajt-start* *pic-test-stamped* *pic-ajt-ticks*))

(defconst *pic-ajt-entry* (nth 1 (mv-list 3 (fn-pic-feed-funded *pic-ajt-before* (pic-ajt-observation *pic-ajt-before* *pic-test-stamped*) 1))))

(defthm pic-ajt-producer-positive
 (let* ((c (pic-ajt-initial *pic-test-stamped*)) (obs (pic-ajt-length c)))
  (and (true-listp *pic-test-stamped*) (stringp "<m>") (not (zp 1))
       (equal (fn-pic-get phase c) :held-length) (fn-pic-observation-okp c (fn-pic-demand c) obs)
       (fn-pic-agent-tracep (nth 1 (mv-list 3 (fn-pic-feed-funded c obs 1))) 0 *pic-test-stamped*))) :rule-classes nil)

(defthm pic-ajt-trace-completion-positive
 (let ((p (fn-psc-step (fn-pic-parser *pic-ajt-before*)
            (fn-psc-model-demanded-byte (fn-pic-parser *pic-ajt-before*) *pic-test-stamped* nil))))
  (and (fn-pic-agent-tracep *pic-ajt-before* *pic-ajt-ticks* *pic-test-stamped*)
       (not (equal (fn-psc-result p) :pending))
       (fn-psc-agent-resultp (fn-psc-result p) (len *pic-test-stamped*))
       (equal (fn-psc-model-agent-span-octets p *pic-test-stamped*)
        (fn-pb-path-agent *pic-test-stamped* (fn-record-string-octets "<m>"))))) :rule-classes nil)

(defthm pic-ajt-funded-completion-positive
 (let* ((c *pic-ajt-before*) (obs (pic-ajt-observation c *pic-test-stamped*))
        (d (nth 1 (mv-list 3 (fn-pic-feed-funded c obs 1)))))
  (and (fn-pic-agent-tracep c *pic-ajt-ticks* *pic-test-stamped*) (not (zp 1))
       (fn-pic-observation-okp c (fn-pic-demand c) obs)
       (equal (fn-pic-observed-byte (fn-pic-demand c) obs)
              (fn-psc-model-demanded-byte (fn-pic-parser c) *pic-test-stamped* nil))
       (not (equal (fn-psc-result (fn-psc-step (fn-pic-parser c)
         (fn-psc-model-demanded-byte (fn-pic-parser c) *pic-test-stamped* nil))) :pending))
       (equal (fn-pic-get phase d) :source-incoming)
       (fn-pic-source-contextp d *pic-test-stamped*)
       (equal (fn-pic-retained-agent d *pic-test-stamped*)
              (fn-pb-path-agent *pic-test-stamped* (fn-record-string-octets "<m>")))
       (equal (fn-pic-get phase *pic-ajt-entry*) :source-incoming)
       (fn-pic-agent-contextp *pic-ajt-entry* *pic-test-stamped*)
       (equal (fn-pic-retained-agent *pic-ajt-entry* *pic-test-stamped*) '(97 98 99)))) :rule-classes nil)

(defthm pic-ajt-pending-positive
 (let* ((c *pic-ajt-start*) (obs (pic-ajt-observation c *pic-test-stamped*))
        (p (fn-psc-step (fn-pic-parser c) (fn-psc-model-demanded-byte (fn-pic-parser c) *pic-test-stamped* nil))))
  (and (fn-pic-agent-tracep c 0 *pic-test-stamped*) (not (zp 1))
       (fn-pic-observation-okp c (fn-pic-demand c) obs)
       (equal (fn-pic-observed-byte (fn-pic-demand c) obs)
              (fn-psc-model-demanded-byte (fn-pic-parser c) *pic-test-stamped* nil))
       (equal (fn-psc-result p) :pending)
       (fn-pic-agent-tracep (nth 1 (mv-list 3 (fn-pic-feed-funded c obs 1))) 1 *pic-test-stamped*))) :rule-classes nil)

(defthm pic-ajt-reader-trace-removal-corrupted-span
 (let* ((p (fn-pic-parser *pic-ajt-before*))
        (c (fn-pic-set parser (fn-psc-set agent-start (+ 1 (fn-psc-get agent-start p)) p) *pic-ajt-before*))
        (d (nth 1 (mv-list 3 (fn-pic-next c 1 *pic-test-stamped*)))))
  (and (not (fn-pic-agent-tracep c *pic-ajt-ticks* *pic-test-stamped*))
       (equal (fn-pic-get phase d) :source-incoming)
       (fn-pic-source-contextp d *pic-test-stamped*)
       (not (equal (fn-pic-retained-agent d *pic-test-stamped*)
                   (fn-pb-path-agent *pic-test-stamped* (fn-record-string-octets "<m>"))))
       (not (fn-pic-agent-contextp d *pic-test-stamped*)))) :rule-classes nil)

; Full actual readonly source-entry antecedent and conclusion.
(defthm pic-ajt-readonly-source-entry-positive
 (let ((d (mv-nth 1 (fn-pic-next *pic-ajt-before* 1 *pic-test-stamped*))))
  (and (fn-pic-agent-tracep *pic-ajt-before* *pic-ajt-ticks* *pic-test-stamped*)
       (equal (fn-pic-get phase d) :source-incoming)
       (fn-pic-source-contextp d *pic-test-stamped*)
       (equal (fn-pic-retained-agent d *pic-test-stamped*)
              (fn-pb-path-agent *pic-test-stamped* (fn-record-string-octets "<m>")))
       (fn-pic-agent-contextp d *pic-test-stamped*))) :rule-classes nil)

; Producer removals affirm every remaining antecedent and failed conclusion.
(defthm pic-ajt-begin-proper-input-removal
 (let* ((incoming '(80 . 9)) (c (pic-ajt-initial incoming)) (obs (pic-ajt-length c)))
  (and (not (true-listp incoming)) (stringp "<m>") (not (zp 1))
       (fn-pic-observation-okp c (fn-pic-demand c) obs)
       (not (fn-pic-agent-tracep (mv-nth 1 (fn-pic-feed-funded c obs 1)) 0 incoming)))) :rule-classes nil)

(defthm pic-ajt-begin-msgid-type-removal
 (let* ((c (fn-pic-begin *pic-test-selected* *pic-test-grant*
             (pic-test-held 9 nil *pic-test-binding*) *pic-test-incoming*
             (len *pic-test-stamped*) 9 *pic-test-binding* nil)) (obs (pic-ajt-length c)))
  (and (true-listp *pic-test-stamped*) (not (stringp 9)) (not (zp 1))
       (fn-pic-observation-okp c (fn-pic-demand c) obs)
       (not (fn-pic-agent-tracep (mv-nth 1 (fn-pic-feed-funded c obs 1)) 0 *pic-test-stamped*)))) :rule-classes nil)

(defthm pic-ajt-begin-zero-fuel-removal
 (let* ((c (pic-ajt-initial *pic-test-stamped*)) (obs (pic-ajt-length c)))
  (and (true-listp *pic-test-stamped*) (stringp "<m>") (zp 0)
       (fn-pic-observation-okp c (fn-pic-demand c) obs)
       (not (fn-pic-agent-tracep (mv-nth 1 (fn-pic-feed-funded c obs 0)) 0 *pic-test-stamped*)))) :rule-classes nil)

; Mutated selected token: valid input/type/fuel, invalid typed effect.
(defthm pic-ajt-begin-effect-removal-mutated-selected-token
 (let* ((c (pic-ajt-initial *pic-test-stamped*)) (obs (update-nth 1 :other-selected (pic-ajt-length c))))
  (and (true-listp *pic-test-stamped*) (stringp "<m>") (not (zp 1))
       (not (fn-pic-observation-okp c (fn-pic-demand c) obs))
       (not (fn-pic-agent-tracep (mv-nth 1 (fn-pic-feed-funded c obs 1)) 0 *pic-test-stamped*)))) :rule-classes nil)

(defthm pic-ajt-pending-zero-fuel-removal
 (let* ((c *pic-ajt-start*) (obs (pic-ajt-observation c *pic-test-stamped*)))
  (and (fn-pic-agent-tracep c 0 *pic-test-stamped*) (zp 0)
       (fn-pic-observation-okp c (fn-pic-demand c) obs)
       (equal (fn-pic-observed-byte (fn-pic-demand c) obs)
              (fn-psc-model-demanded-byte (fn-pic-parser c) *pic-test-stamped* nil))
       (equal (fn-psc-result (fn-psc-step (fn-pic-parser c)
         (fn-psc-model-demanded-byte (fn-pic-parser c) *pic-test-stamped* nil))) :pending)
       (not (fn-pic-agent-tracep (mv-nth 1 (fn-pic-feed-funded c obs 0)) 1 *pic-test-stamped*)))) :rule-classes nil)

; Invalid control effect preserves the observed/model NIL byte premise.
(defthm pic-ajt-pending-effect-removal
 (let ((c *pic-ajt-start*) (obs '(:bad-control)))
  (and (fn-pic-agent-tracep c 0 *pic-test-stamped*) (not (zp 1))
       (not (fn-pic-observation-okp c (fn-pic-demand c) obs))
       (equal (fn-pic-observed-byte (fn-pic-demand c) obs)
              (fn-psc-model-demanded-byte (fn-pic-parser c) *pic-test-stamped* nil))
       (equal (fn-psc-result (fn-psc-step (fn-pic-parser c)
         (fn-psc-model-demanded-byte (fn-pic-parser c) *pic-test-stamped* nil))) :pending)
       (not (fn-pic-agent-tracep (mv-nth 1 (fn-pic-feed-funded c obs 1)) 1 *pic-test-stamped*)))) :rule-classes nil)

; Typed token/offset/octet effect disagrees with the immutable source.
(defthm pic-ajt-pending-byte-removal-mutated-observation
 (let* ((c (pic-ajt-drive *pic-ajt-start* *pic-test-stamped* 1))
        (obs (update-nth 3 67 (pic-ajt-observation c *pic-test-stamped*))))
  (and (fn-pic-agent-tracep c 1 *pic-test-stamped*) (not (zp 1))
       (fn-pic-observation-okp c (fn-pic-demand c) obs)
       (not (equal (fn-pic-observed-byte (fn-pic-demand c) obs)
                   (fn-psc-model-demanded-byte (fn-pic-parser c) *pic-test-stamped* nil)))
       (equal (fn-psc-result (fn-psc-step (fn-pic-parser c)
         (fn-psc-model-demanded-byte (fn-pic-parser c) *pic-test-stamped* nil))) :pending)
       (not (fn-pic-agent-tracep (mv-nth 1 (fn-pic-feed-funded c obs 1)) 2 *pic-test-stamped*)))) :rule-classes nil)

(defthm pic-ajt-pending-phase-removal-real-completion
 (let* ((c *pic-ajt-before*) (obs (pic-ajt-observation c *pic-test-stamped*)))
  (and (fn-pic-agent-tracep c *pic-ajt-ticks* *pic-test-stamped*) (not (zp 1))
       (fn-pic-observation-okp c (fn-pic-demand c) obs)
       (equal (fn-pic-observed-byte (fn-pic-demand c) obs)
              (fn-psc-model-demanded-byte (fn-pic-parser c) *pic-test-stamped* nil))
       (not (equal (fn-psc-result (fn-psc-step (fn-pic-parser c)
         (fn-psc-model-demanded-byte (fn-pic-parser c) *pic-test-stamped* nil))) :pending))
       (not (fn-pic-agent-tracep (mv-nth 1 (fn-pic-feed-funded c obs 1)) (+ 1 *pic-ajt-ticks*) *pic-test-stamped*)))) :rule-classes nil)

; Corrupted parser position, with all other pending-feedback premises kept.
(defthm pic-ajt-pending-trace-removal-corrupted-position
 (let* ((a (pic-ajt-drive *pic-ajt-start* *pic-test-stamped* 1))
        (c (fn-pic-set parser (fn-psc-set pos 1 (fn-pic-parser a)) a))
        (obs (pic-ajt-observation c *pic-test-stamped*)))
  (and (not (fn-pic-agent-tracep c 1 *pic-test-stamped*)) (not (zp 1))
       (fn-pic-observation-okp c (fn-pic-demand c) obs)
       (equal (fn-pic-observed-byte (fn-pic-demand c) obs)
              (fn-psc-model-demanded-byte (fn-pic-parser c) *pic-test-stamped* nil))
       (equal (fn-psc-result (fn-psc-step (fn-pic-parser c)
         (fn-psc-model-demanded-byte (fn-pic-parser c) *pic-test-stamped* nil))) :pending)
       (not (fn-pic-agent-tracep (mv-nth 1 (fn-pic-feed-funded c obs 1)) 2 *pic-test-stamped*)))) :rule-classes nil)

; Geometry is established by BEGIN and carried through the actual reader
; and funded feeder without presuming an inverse-parser interpretation.
(defthm pic-ajt-source-context-producer-and-read-positive
 (let* ((c (pic-ajt-initial *pic-test-stamped*))
        (a *pic-ajt-entry*) (obs (pic-ajt-observation a *pic-test-stamped*)))
  (and (true-listp *pic-test-stamped*) (fn-pic-source-contextp c *pic-test-stamped*)
       (fn-pic-source-contextp a *pic-test-stamped*)
       (fn-pic-source-contextp (mv-nth 1 (fn-pic-feed-funded a obs 1)) *pic-test-stamped*)
       (fn-pic-source-contextp (mv-nth 1 (fn-pic-next a 1 *pic-test-stamped*)) *pic-test-stamped*))) :rule-classes nil)

(defthm pic-ajt-source-context-begin-hypothesis-removal
 (let* ((incoming '(80 . 9)) (c (pic-ajt-initial incoming)))
  (and (not (true-listp incoming)) (not (fn-pic-source-contextp c incoming)))) :rule-classes nil)

; Corrupted captured extent: no valid source-context premise remains.
(defthm pic-ajt-source-context-feedback-and-read-removal
 (let* ((c (fn-pic-set incoming-n (+ 1 (len *pic-test-stamped*)) *pic-ajt-entry*))
        (obs (pic-ajt-observation c *pic-test-stamped*)))
  (and (not (fn-pic-source-contextp c *pic-test-stamped*))
       (not (fn-pic-source-contextp (mv-nth 1 (fn-pic-feed-funded c obs 1)) *pic-test-stamped*))
       (not (fn-pic-source-contextp (mv-nth 1 (fn-pic-next c 1 *pic-test-stamped*)) *pic-test-stamped*)))) :rule-classes nil)

(defun pic-ajt-digest-context-positive ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj pgs-digest-state
  (mv-let (ok pgs-digest-state)
   (let ((c (fn-pic-hash-start nil *pic-ajt-entry*)))
    (mv-let (status d left pgs-digest-state) (fn-pic-digest-next c 2 pgs-digest-state)
     (declare (ignore status left))
     (mv (and (fn-pic-source-contextp c *pic-test-stamped*)
              (fn-pic-agent-contextp c *pic-test-stamped*)
              (equal (fn-pic-get phase d) :digest-next)
              (fn-pic-source-contextp d *pic-test-stamped*)
              (fn-pic-agent-contextp d *pic-test-stamped*)) pgs-digest-state)))
   ok)))
(assert-event (pic-ajt-digest-context-positive))

; Zero-effect yield still requires the retained context; it does not repair
; a corrupted incoming extent or agent. These are logical state mutations.
(defthm pic-ajt-digest-source-context-removal
 (let ((c (fn-pic-set incoming-n (+ 1 (len *pic-test-stamped*)) (fn-pic-hash-start nil *pic-ajt-entry*))))
  (and (not (fn-pic-source-contextp c *pic-test-stamped*))
       (not (fn-pic-source-contextp (mv-nth 1 (fn-pic-digest-next c 1 pgs-digest-state)) *pic-test-stamped*)))) :rule-classes nil)

(defthm pic-ajt-digest-agent-context-removal
 (let* ((a (fn-pic-get agent *pic-ajt-entry*))
        (c (fn-pic-set agent (list :agent (+ 1 (fn-pic-at 1 a)) (fn-pic-at 2 a))
             (fn-pic-hash-start nil *pic-ajt-entry*))))
  (and (not (fn-pic-agent-contextp c *pic-test-stamped*))
       (not (fn-pic-agent-contextp (mv-nth 1 (fn-pic-digest-next c 1 pgs-digest-state)) *pic-test-stamped*)))) :rule-classes nil)

(defthm pic-ajt-reader-entry-removal-pending
 (let ((d (nth 1 (mv-list 3 (fn-pic-next *pic-ajt-start* 1 *pic-test-stamped*)))))
  (and (fn-pic-agent-tracep *pic-ajt-start* 0 *pic-test-stamped*)
       (not (equal (fn-pic-get phase d) :source-incoming))
       (not (equal (fn-pic-retained-agent d *pic-test-stamped*)
                   (fn-pb-path-agent *pic-test-stamped* (fn-record-string-octets "<m>"))))
       (not (fn-pic-agent-contextp d *pic-test-stamped*)))) :rule-classes nil)

(defthm pic-ajt-carried-agent-context-positive
 (let* ((c *pic-ajt-entry*) (obs (pic-ajt-observation c *pic-test-stamped*))
        (a (nth 1 (mv-list 3 (fn-pic-feed-funded c obs 1))))
        (b (nth 1 (mv-list 3 (fn-pic-next c 1 *pic-test-stamped*)))))
  (and (fn-pic-agent-contextp c *pic-test-stamped*) (not (equal (fn-pic-get phase c) :agent))
       (fn-pic-agent-contextp a *pic-test-stamped*) (fn-pic-agent-contextp b *pic-test-stamped*))) :rule-classes nil)

(defthm pic-ajt-retained-context-removal-corrupted-span
 (let* ((a (fn-pic-get agent *pic-ajt-entry*))
        (c (fn-pic-set agent (list :agent (+ 1 (fn-pic-at 1 a)) (fn-pic-at 2 a)) *pic-ajt-entry*))
        (d (nth 1 (mv-list 3 (fn-pic-next c 1 *pic-test-stamped*)))))
  (and (not (fn-pic-agent-contextp c *pic-test-stamped*))
       (not (equal (fn-pic-get phase c) :agent))
       (not (fn-pic-agent-contextp d *pic-test-stamped*)))) :rule-classes nil)

(defthm pic-ajt-agent-phase-boundary-removal
 (let* ((p (fn-pic-parser *pic-ajt-before*))
        (c (fn-pic-set agent (fn-pic-get agent *pic-ajt-entry*)
             (fn-pic-set parser (fn-psc-set agent-start (+ 1 (fn-psc-get agent-start p)) p) *pic-ajt-before*)))
        (d (nth 1 (mv-list 3 (fn-pic-next c 1 *pic-test-stamped*)))))
  (and (fn-pic-agent-contextp c *pic-test-stamped*)
       (equal (fn-pic-get phase c) :agent)
       (not (fn-pic-agent-contextp d *pic-test-stamped*)))) :rule-classes nil)
