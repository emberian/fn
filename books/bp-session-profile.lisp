; Explicit BP retained-context admission profile, separate from held custody.
(in-package "ACL2")
(include-book "bp-node-budget-input")
(include-book "bp-node-profile")
(defun fn-bpsp-profilep (p)
 (declare (xargs :guard t))
 (and (true-listp p) (equal (len p) 6)
      (natp (first p)) (natp (second p))
      (< 0 (+ (first p) (second p)))
      (< (+ 2 (first p) (second p)) (expt 2 32))
      (or (null (third p)) (and (posp (third p)) (< (third p) (expt 2 64))))
      (posp (fourth p)) (< (fourth p) (expt 2 64))
      (posp (fifth p)) (< (fifth p) (expt 2 32))
      (posp (sixth p)) (< (sixth p) (expt 2 32))))
; Rows: inbound outbound resident outbound-ms passive-ms stall-ms (S025: the two
; no-progress bounds of an established session, books/tcpcl-retained-turn.lisp).
(defun fn-bpsp-row (line rows)
 (declare (xargs :guard (and (true-listp rows) (equal (len rows) 6))))
 (if (null line) rows
  (let ((r (fn-bpnb-row line nil)))
   (cond
    ((equal (first r) '(105 110 98 111 117 110 100))
     (and (not (first rows)) (list (second r) (second rows) (third rows) (fourth rows) (fifth rows) (sixth rows))))
    ((equal (first r) '(111 117 116 98 111 117 110 100))
     (and (not (second rows)) (list (first rows) (second r) (third rows) (fourth rows) (fifth rows) (sixth rows))))
    ((equal (first r) '(114 101 115 105 100 101 110 116))
     (and (not (third rows)) (list (first rows) (second rows) (second r) (fourth rows) (fifth rows) (sixth rows))))
    ((equal (first r) '(111 117 116 98 111 117 110 100 45 109 115))
     (and (not (fourth rows)) (list (first rows) (second rows) (third rows) (second r) (fifth rows) (sixth rows))))
    ((equal (first r) '(112 97 115 115 105 118 101 45 109 115))
     (and (not (fifth rows)) (list (first rows) (second rows) (third rows) (fourth rows) (second r) (sixth rows))))
    ((equal (first r) '(115 116 97 108 108 45 109 115))
     (and (not (sixth rows)) (list (first rows) (second rows) (third rows) (fourth rows) (fifth rows) (second r))))
    (t nil)))))
(defthm fn-bpsp-row-keeps-six
 (implies (and (true-listp rows) (equal (len rows) 6) (fn-bpsp-row line rows))
  (and (true-listp (fn-bpsp-row line rows)) (equal (len (fn-bpsp-row line rows)) 6))))
(defun fn-bpsp-lines (xs line rows)
 (declare (xargs :guard (and (true-listp line) (true-listp rows) (equal (len rows) 6))))
 (if (consp xs)
  (if (equal (car xs) 10)
   (let ((r (fn-bpsp-row (reverse line) rows)))
    (and r (fn-bpsp-lines (cdr xs) nil r)))
   (fn-bpsp-lines (cdr xs) (cons (car xs) line) rows))
  (and (null xs) (fn-bpsp-row (reverse line) rows))))
(defthm fn-bpsp-lines-keeps-six
 (implies (and (true-listp rows) (equal (len rows) 6) (fn-bpsp-lines xs line rows))
  (and (true-listp (fn-bpsp-lines xs line rows)) (equal (len (fn-bpsp-lines xs line rows)) 6))))
(defun fn-bpsp-read (octets)
 (declare (xargs :guard t))
 (and (<= (len octets) 256)
  (let* ((r (fn-bpsp-lines octets nil '(nil nil nil nil nil nil)))
         (p (and r (list (if (first r) (first r) 2)
                         (if (second r) (second r) 1) (third r)
                         (if (fourth r) (fourth r) 30000)
                         (if (fifth r) (fifth r) 120000)
                         (if (sixth r) (sixth r) 600000)))))
   (and (fn-bpsp-profilep p) p))))
; The session's no-progress bounds, read once at startup (host: fnn-bp-session-install).
(defun fn-bpsp-passive-ms (profile) (declare (xargs :guard (true-listp profile))) (fifth profile))
(defun fn-bpsp-stall-ms (profile) (declare (xargs :guard (true-listp profile))) (sixth profile))
;; S025: the incoming class is contended when a peer is waiting at a listener and
;; every incoming slot is held.  A free slot is never contention: the waiting
;; peer is drawn on the next turn.
(defun fn-bpsp-incoming-contended (waiting held capacity)
 (declare (xargs :guard t))
 (and waiting (natp held) (natp capacity) (<= capacity held) t))
(defthm fn-bpsp-free-incoming-slot-is-not-contention
 (implies (and (natp held) (natp capacity) (< held capacity))
  (not (fn-bpsp-incoming-contended waiting held capacity))))
(defthm fn-bpsp-nobody-waiting-is-not-contention
 (not (fn-bpsp-incoming-contended nil held capacity)))
(defthm fn-bpsp-contention-needs-a-waiter-and-a-full-class-by-definition
 (implies (fn-bpsp-incoming-contended waiting held capacity)
  (and waiting (natp held) (natp capacity) (<= capacity held)))
 :rule-classes nil)
(defun fn-bpsp-session-resident (transfer segment)
 (declare (xargs :guard t))
 ; A named layout projection: list aliases, legacy flatten/carry and encoded
 ; output, plus fixed context/closures. Full semantic decode/collector tariff
 ; refinement remains open, so this is a staged transport projection.
 (+ 65536 (* 64 (+ (nfix transfer) (nfix segment))) 8192))
;; THE sizing of a node's BP sessions, from the profiles.  The startup check and
;; the launcher's heap probe (books/bp-heap-command.lisp) both read this one
;; figure; the host only supplies what it observed.
(defun fn-bpsp-table (profile)
 (declare (xargs :guard (fn-bpsp-profilep profile)))
 (+ 8192 (* 272 (+ 2 (first profile) (second profile)))))
(defun fn-bpsp-minimum (profile transfer segment)
 (declare (xargs :guard (fn-bpsp-profilep profile)))
 (+ (fn-bpsp-table profile)
    (* (+ (first profile) (second profile)) (fn-bpsp-session-resident transfer segment))))
; The session allowance the node holds: the profile's resident figure, or the
; minimum when it names none.  NIL when the profile or the spans are invalid,
; or when the figure is below the minimum or unrepresentable.
(defun fn-bpsp-allowance (profile transfer segment)
 (declare (xargs :guard t))
 (and (fn-bpsp-profilep profile) (posp transfer) (posp segment)
      (let ((allowance (if (third profile) (third profile)
                         (fn-bpsp-minimum profile transfer segment))))
       (and (<= (fn-bpsp-minimum profile transfer segment) allowance)
            (< allowance (expt 2 64))
            allowance))))
(defun fn-bpsp-startup (profile transfer segment dynamic store-need bp-held-need)
 (declare (xargs :guard t))
 (cond
  ((not (and (fn-bpsp-profilep profile) (posp transfer) (posp segment)
             (natp dynamic) (natp store-need) (natp bp-held-need)))
   (list :refused :invalid-bp-session-profile))
  (t
   (let ((allowance (fn-bpsp-allowance profile transfer segment)))
    (cond ((not allowance)
           (list :refused :bp-session-profile-too-small))
          ((< dynamic (+ store-need bp-held-need allowance))
           (list :refused :bp-session-capacity-not-held))
          (t (list :hold allowance (fn-bpsp-table profile)
                   (fn-bpsp-session-resident transfer segment)
                   (first profile) (second profile) (fourth profile))))))))
; Fixed receipt record; neither a timeout nor a protocol outcome fabricates
; a physical receipt. SLOT/GEN are the typed bank's draw token.
(defun fn-bpsg-row (slot gen class)
 (declare (xargs :guard t)) (list :bp-session-grant slot gen class nil nil))
(defun fn-bpsg-step (row observation)
 (declare (xargs :guard t))
 (if (not (and (true-listp row) (equal (len row) 6)
               (equal (first row) :bp-session-grant)))
  (list :fault row)
  (if (equal observation :rearm-socket)
   (if (and (not (fifth row)) (sixth row))
    (list :retain (list :bp-session-grant (second row) (third row) (fourth row) nil nil))
    (list :fault row))
  (let* ((logical (fifth row)) (physical (sixth row))
        (logical (or logical (member-equal observation '(:no-context :released-context))))
        (physical (or physical (member-equal observation '(:no-socket :socket-closed))))
        (next (list :bp-session-grant (second row) (third row) (fourth row)
                    (and logical t) (and physical t))))
  (list (if (and logical physical) :settle :retain) next)))))
(defun fn-bpsg-release-ready (finished source-pending source-root source-token held messages data)
 (declare (xargs :guard t))
 (and finished (not source-pending) (not source-root) (not source-token)
      (not held) (not messages) (not data)))
(defthm fn-bpsp-startup-hold-protects-baseline-and-all-contexts
 (implies (equal (car (fn-bpsp-startup profile transfer segment dynamic store-need bp-held-need)) :hold)
  (let ((g (fn-bpsp-startup profile transfer segment dynamic store-need bp-held-need)))
   (and (<= (+ store-need bp-held-need (second g)) dynamic)
        (<= (+ (third g) (* (+ (fifth g) (sixth g)) (fourth g))) (second g))))))
(defthm fn-bpsg-physical-alone-cannot-settle-context
 (implies (and (not (fifth row))
               (member-equal observation '(:no-socket :socket-closed)))
  (not (equal (car (fn-bpsg-step row observation)) :settle))))
(defun fn-bpsp-file-name () (declare (xargs :guard t)) "bp-session-profile")
(defun fn-bpsp-read-bound () (declare (xargs :guard t)) 256)
(defun fn-bpsp-held-projection (held rows adu)
 (declare (xargs :guard t))
 (+ (* 32 (nfix held)) (* 512 (nfix rows)) (* 64 (nfix adu))))
(defun fn-bpsp-digits (n acc fuel)
 (declare (xargs :guard (and (natp n) (true-listp acc) (natp fuel)) :measure (nfix fuel)))
 (cond ((or (not (natp n)) (< n 10)) (cons (+ 48 (nfix n)) acc))
       ((zp fuel) nil)
       (t (fn-bpsp-digits (floor n 10) (cons (+ 48 (mod n 10)) acc) (- fuel 1)))))
(defthm fn-bpsp-digits-true-list
 (implies (true-listp acc) (true-listp (fn-bpsp-digits n acc fuel)))
 :hints (("Goal" :induct (fn-bpsp-digits n acc fuel)
                  :in-theory (disable floor mod))))
(defun fn-bpsp-write (incoming outgoing resident outbound-ms passive-ms stall-ms)
 (declare (xargs :guard t))
 (and (fn-bpsp-profilep (list incoming outgoing resident outbound-ms passive-ms stall-ms))
      (append '(105 110 98 111 117 110 100 32) (fn-bpsp-digits incoming nil 20) '(10)
              '(111 117 116 98 111 117 110 100 32) (fn-bpsp-digits outgoing nil 20) '(10)
              (and resident
                   (append '(114 101 115 105 100 101 110 116 32)
                           (fn-bpsp-digits resident nil 20) '(10)))
              '(111 117 116 98 111 117 110 100 45 109 115 32)
              (fn-bpsp-digits outbound-ms nil 20) '(10)
              '(112 97 115 115 105 118 101 45 109 115 32)
              (fn-bpsp-digits passive-ms nil 20) '(10)
              '(115 116 97 108 108 45 109 115 32)
              (fn-bpsp-digits stall-ms nil 20) '(10))))
(defun fn-bpsg-slots (grant)
 (declare (xargs :guard (true-listp grant)))
 (+ 2 (nfix (fifth grant)) (nfix (sixth grant))))
(defun fn-bpsg-key (row)
 (declare (xargs :guard (true-listp row)))
 (list :bp-session (second row) (third row) (fourth row)))

(defun fn-bpsp-captured-wire-span (transfer bundle)
 (declare (xargs :guard t))
 ; Both negotiated receive range and a complete retained outbound fragment
 ; plan fit this conservative sum; the stored bundle may exceed contact MRU.
 (+ (nfix transfer) (nfix bundle)))

;; The BP terms of a node serve, as one figure.  PROFILE is the session profile,
;; NODE the node profile, TRANSFER-MRU the contact's transfer MRU, SEGMENT the
;; segment MRU.  NIL when the terms are invalid or unfunded.
(defun fn-bpsp-capacity-octets (profile transfer segment held rows adu)
 (declare (xargs :guard t))
 (let ((allowance (fn-bpsp-allowance profile transfer segment)))
  (and allowance (natp held) (natp rows) (natp adu)
       (+ (fn-bpsp-held-projection held rows adu) allowance))))
(defun fn-bpsp-node-wire-span (node transfer-mru)
 (declare (xargs :guard t))
 (fn-bpsp-captured-wire-span transfer-mru (fn-bpnpf-bundle-octets node)))
(defun fn-bpsp-node-capacity (profile node transfer-mru segment)
 (declare (xargs :guard t))
 (fn-bpsp-capacity-octets profile (fn-bpsp-node-wire-span node transfer-mru) segment
  (fn-bpnpf-held-octets node) (fn-bpnpf-rows node) (fn-bpnpf-adu-octets node)))
; The startup check as the node runs it (host: fnn-bp-session-install).
(defun fn-bpsp-node-startup (profile node transfer-mru segment dynamic store-need)
 (declare (xargs :guard t))
 (fn-bpsp-startup profile (fn-bpsp-node-wire-span node transfer-mru) segment dynamic store-need
  (fn-bpsp-held-projection (fn-bpnpf-held-octets node) (fn-bpnpf-rows node)
                           (fn-bpnpf-adu-octets node))))

(defthm fn-bpsp-capacity-octets-natp
 (implies (fn-bpsp-capacity-octets profile transfer segment held rows adu)
          (natp (fn-bpsp-capacity-octets profile transfer segment held rows adu)))
 :rule-classes :forward-chaining)
(defthm fn-bpsp-node-capacity-natp
 (implies (fn-bpsp-node-capacity profile node transfer-mru segment)
          (natp (fn-bpsp-node-capacity profile node transfer-mru segment)))
 :rule-classes :forward-chaining
 :hints (("Goal" :in-theory (enable fn-bpsp-node-capacity))))
; KEYSTONE (the figure is the check): the node holds its sessions exactly when
; the dynamic space holds the store figure plus the one capacity figure.
(defthm fn-bpsp-node-startup-holds-the-capacity
 (implies (and (natp dynamic) (natp store-need)
               (fn-bpsp-node-capacity profile node transfer-mru segment)
               (<= (+ store-need (fn-bpsp-node-capacity profile node transfer-mru segment)) dynamic))
          (equal (car (fn-bpsp-node-startup profile node transfer-mru segment dynamic store-need))
                 :hold)))
; TEETH: a dynamic space below it is refused by name.
(defthm fn-bpsp-node-startup-refuses-below-the-capacity
 (implies (and (natp dynamic) (natp store-need)
               (fn-bpsp-node-capacity profile node transfer-mru segment)
               (< dynamic (+ store-need (fn-bpsp-node-capacity profile node transfer-mru segment))))
          (equal (fn-bpsp-node-startup profile node transfer-mru segment dynamic store-need)
                 '(:refused :bp-session-capacity-not-held))))

(defun fn-bpsp-root-release-ready (held)
 (declare (xargs :guard t)) (and (natp held) (equal held 0)))

; The single writer has disabled TURN/FINISH before consuming this plan.
; Ordinary input/output aliases can be retired without a new publication.
; Source operations and ambiguous publication remain their own recovery debt.
(defun fn-bpsg-context-abort-plan (source-pending root token source-held fenced)
 (declare (xargs :guard t))
 (if (or source-pending root token source-held fenced) :retain-context :retire-context))
(defthm fn-bpsg-context-abort-retains-every-publication-debt-by-definition
 (implies (or source-pending root token source-held fenced)
  (equal (fn-bpsg-context-abort-plan source-pending root token source-held fenced) :retain-context))
 :rule-classes nil)
