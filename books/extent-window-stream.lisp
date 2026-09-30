; Core composition: bounded positional read + concrete digest + private window.
; PRF-1109. Native ownership and semantic carry remain separately named boundaries.
(in-package "ACL2")
(include-book "extent-window-capture")
(include-book "pagestore-digest-byte-cursor")
(include-book "blake3-stobj")

; The immutable descriptor/owner tuple is retained in the digest continuation.
; No prefix bytes, original payload, or growing processed list is retained here.
(defun fn-ews-capture (s)
  (declare (xargs :guard (true-listp s)))
  (list (nth 1 s) (nth 2 s) (nth 3 s) (nth 4 s) (nth 5 s)
        (nth 6 s) (nth 8 s) (nth 9 s) (nth 10 s)
        (nth 11 s) (nth 12 s) (nth 13 s)))

(defun fn-ews-begin (file eoff elen poff plen offset ticket incarnation lease expected pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state
                  :guard (and (natp file) (natp eoff) (natp elen)
                              (natp poff) (natp plen) (natp offset) (natp expected))))
  (let* ((s (fn-ewp-begin file eoff elen poff plen offset ticket incarnation lease expected))
         (pgs-digest-state (pgs-dcb-begin 0 0 elen (fn-ews-capture s) lease pgs-digest-state)))
    (mv s pgs-digest-state)))

; Constant-many scalar/identity checks, not traversal of an extent or buffer.
; This checks the actual incremental primitive's guard before every call.
(defun fn-ews-boundp (s pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :guard (true-listp s)))
  (and (natp (nth 3 s)) (natp (nth 5 s)) (<= (nth 5 s) 16384)
       (natp (nth 7 s)) (<= (nth 7 s) (nth 3 s))
       (equal (pgs-dc-capture pgs-digest-state) (fn-ews-capture s))
       (equal (pgs-dc-lease pgs-digest-state) (nth 10 s))
       (equal (pgs-dc-total pgs-digest-state) (pgs-dcb-word-count (nth 3 s)))
       (<= (pgs-dc-start pgs-digest-state) (pgs-dc-pos pgs-digest-state))
       (<= (pgs-dc-pos pgs-digest-state) (pgs-dc-end pgs-digest-state))
       (<= (pgs-dc-end pgs-digest-state) (pgs-dc-total pgs-digest-state))
       (<= (* 8 (pgs-dc-pos pgs-digest-state)) (nth 3 s))))

(defun fn-ews-effect (s pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :guard (true-listp s)))
  (and (fn-ews-boundp s pgs-digest-state)
       (or (and (eq (nth 0 s) :scan)
                (pgs-dc-needs-block pgs-digest-state)
                (equal (nth 7 s) (pgs-dcb-next-byte-offset pgs-digest-state))
                (equal (fn-ewp-demand s) (pgs-dcb-read-demand (nth 3 s) pgs-digest-state)))
           (and (eq (nth 0 s) :trailer)
                (equal (nth 7 s) (nth 3 s))
                (eq (pgs-dc-mode pgs-digest-state) :done)))
       (fn-ewp-effect s)))

(defun fn-ews-tick (s pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :guard (true-listp s)
                  :verify-guards nil))
  (cond ((not (member-eq (nth 0 s) '(:scan :trailer)))
         (mv (nth 0 s) s pgs-digest-state))
        ((not (fn-ews-boundp s pgs-digest-state))
         (mv :state (fn-ewp-with-phase-pos :state (nth 7 s) s) pgs-digest-state))
        ((fn-ews-effect s pgs-digest-state) (mv :read s pgs-digest-state))
        ((or (pgs-dc-needs-block pgs-digest-state) (eq (pgs-dc-mode pgs-digest-state) :done))
         (mv :state (fn-ewp-with-phase-pos :state (nth 7 s) s) pgs-digest-state))
        (t (mv-let (status pgs-digest-state)
             (pgs-dcb-step (nth 3 s) nil pgs-digest-state)
             (if (eq status :invalid)
                 (mv :state (fn-ewp-with-phase-pos :state (nth 7 s) s) pgs-digest-state)
               (mv :continue s pgs-digest-state))))))

(verify-guards fn-ews-tick :hints (("Goal" :in-theory (enable fn-ews-boundp))))

(defun fn-ews-read-trailer (k p fn-octets)
  (declare (xargs :stobjs fn-octets :measure (nfix k)
                  :guard (and (natp k) (<= k 32) (natp p)
                              (<= (+ p k) (fn-octets-len fn-octets)))))
  (if (zp k) nil
    (cons (fn-octets-get p fn-octets)
          (fn-ews-read-trailer (1- k) (1+ p) fn-octets))))

; Only this entry consumes an I/O completion. The host supplies bytes and
; the completion status; the digest is obtained from the actual core cursor.
; Input length is the actual read result, never a claimed count from the host.
(defun fn-ews-read (effect io-status s fn-octets pgs-digest-state fn-ew-buffer)
  (declare (xargs :stobjs (fn-octets pgs-digest-state fn-ew-buffer)
                  :guard (true-listp s) :verify-guards nil))
  (let ((issued (fn-ews-effect s pgs-digest-state)))
    (cond ((or (not issued) (not (equal effect issued)))
           (mv :stale s pgs-digest-state fn-ew-buffer))
          ((or (not (eq io-status :ok))
               (not (equal (fn-octets-len fn-octets) (fn-ewp-demand s))))
           (mv :read (fn-ewp-with-phase-pos :read (nth 7 s) s) pgs-digest-state fn-ew-buffer))
          ((eq (nth 0 s) :scan)
           (let* ((block (fn-b3x-words 16 0 (fn-ewp-demand s) nil 0 0 fn-octets))
                  (fn-ew-buffer (fn-ewb-capture s fn-octets fn-ew-buffer)))
             (mv-let (hash-status pgs-digest-state)
               (pgs-dcb-step (nth 3 s) block pgs-digest-state)
               (if (eq hash-status :invalid)
                   (mv :state (fn-ewp-with-phase-pos :state (nth 7 s) s) pgs-digest-state fn-ew-buffer)
                 (mv-let (status s)
                   (fn-ewp-complete-read effect (fn-octets-len fn-octets) :ok s)
                   (mv status s pgs-digest-state fn-ew-buffer))))))
          (t (let ((read (fn-ews-read-trailer 32 0 fn-octets))
                   (digest (pgs-dcb-result-octets pgs-digest-state)))
               (mv-let (status s)
                 (fn-ewp-finish read digest (fn-ewp-with-phase-pos :digest (nth 7 s) s))
                 (mv status s pgs-digest-state fn-ew-buffer)))))))

(verify-guards fn-ews-read
  :hints (("Goal" :in-theory (enable fn-ews-effect fn-ews-boundp fn-ewp-demand)
                   :use fn-ewp-demand-bounded)))

(in-theory (disable fn-ews-capture fn-ews-begin fn-ews-boundp fn-ews-effect
                    fn-ews-tick fn-ews-read-trailer fn-ews-read))

(defthm fn-ews-stale-completion-preserves-all-effects
  (implies (or (not (fn-ews-effect s pgs-digest-state))
               (not (equal effect (fn-ews-effect s pgs-digest-state))))
           (equal (fn-ews-read effect io-status s fn-octets pgs-digest-state fn-ew-buffer)
                  (list :stale s pgs-digest-state fn-ew-buffer)))
  :hints (("Goal" :in-theory (enable fn-ews-read))))

(defthm fn-ews-read-publication-requires-core-integrity
  (implies
    (and (not (fn-ewp-publication s))
         (fn-ewp-publication
           (mv-nth 1 (fn-ews-read effect io-status s fn-octets pgs-digest-state fn-ew-buffer))))
    (and (equal (nth 0 s) :trailer)
         (equal (pgs-dc-mode pgs-digest-state) :done)
         (equal (nth 7 s) (nth 3 s))
         (equal effect (fn-ews-effect s pgs-digest-state))
         (equal io-status :ok)
         (equal (fn-octets-len fn-octets) 32)
         (equal (fn-bch-pack (fn-ews-read-trailer 32 0 fn-octets)) (nth 6 s))
         (equal (pgs-dcb-result-octets pgs-digest-state) (fn-ews-read-trailer 32 0 fn-octets))))
  :hints (("Goal" :in-theory (enable fn-ews-read fn-ews-effect fn-ewp-demand
                                    fn-ewp-publication fn-ewp-finish fn-ewp-complete-read)))
  :rule-classes nil)

(defthm fn-ews-read-exact-window-output-and-effects
  (implies (natp j)
           (let ((span (fn-ewp-window-span s)))
             (equal
               (nth j (nth 0 (mv-nth 3 (fn-ews-read effect io-status s fn-octets pgs-digest-state fn-ew-buffer))))
               (if (and (fn-ews-effect s pgs-digest-state)
                        (equal effect (fn-ews-effect s pgs-digest-state))
                        (equal io-status :ok)
                        (equal (fn-octets-len fn-octets) (fn-ewp-demand s))
                        (equal (nth 0 s) :scan)
                        (<= (caddr span) j) (< j (+ (caddr span) (cadr span))))
                   (nth (+ (car span) (- j (caddr span))) fn-octets)
                 (nth j (nth 0 fn-ew-buffer))))))
  :hints (("Goal" :in-theory (enable fn-ews-read)
                   :use fn-ewb-capture-exact-output-and-effects))
  :rule-classes nil)
